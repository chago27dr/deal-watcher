#!/usr/bin/env python3
"""抽選・予約・リリース情報の監視 → Discord通知。

情報源(RSS / HTMLページ)を順番に巡回し、まだ通知していない新着だけを
Discord の Webhook へ Embed 形式で送る。通知済みの記録は notified_history.json に残す。

使い方:
    python main.py --dry-run      # 取得と判定だけ行い、Discordへは送らない(履歴も書き換えない)
    python main.py                # 本番実行(環境変数 DISCORD_WEBHOOK_URL が必要)

監視対象を増やしたいときは、下の SOURCES に情報源を1行足す。
"""
from __future__ import annotations

import argparse
import json
import logging
import os
import random
import re
import sys
import time
import unicodedata
from dataclasses import dataclass
from datetime import datetime, timedelta, timezone
from pathlib import Path
from urllib.parse import parse_qsl, urlencode, urljoin, urlsplit, urlunsplit
from urllib.robotparser import RobotFileParser

import feedparser
import requests
from bs4 import BeautifulSoup
from requests.adapters import HTTPAdapter
from urllib3.util.retry import Retry

log = logging.getLogger("deal-watcher")

JST = timezone(timedelta(hours=9))
BASE_DIR = Path(__file__).resolve().parent

# ---------------------------------------------------------------------------
# 設定値
# ---------------------------------------------------------------------------

# 相手サーバーに「誰がアクセスしているか」を伝えるUser-Agent。環境変数 USER_AGENT で変更できる。
USER_AGENT = os.environ.get(
    "USER_AGENT", "Mozilla/5.0 (compatible; DealWatcher/1.0; personal-use notifier)"
)
ROBOTS_AGENT = "DealWatcher"  # robots.txt の判定に使う短い名前

DEFAULT_INTERVAL_SEC = 3.0  # リクエスト同士の最短間隔(秒)。実際は最大+1秒ほどゆらがせる
REQUEST_TIMEOUT_SEC = 20
HISTORY_KEEP_DAYS = 90  # この日数のあいだ一度も見かけなかった履歴は削除する
MAX_NOTIFY_PER_RUN = 20  # 1回の実行で通知する最大件数。超えた分は次回以降に回す
EMBEDS_PER_MESSAGE = 10  # Discordは1メッセージに最大10個のEmbed
EMBED_CHARS_PER_MESSAGE = 5500  # Discordの上限は6000文字(全Embed合計)。余裕を持たせる
SOURCE_FAIL_ALERT_STREAK = 6  # 同じ情報源がこの回数だけ連続で失敗したらDiscordへ警告する

CATEGORY_CARD = "トレーディングカード"
CATEGORY_SNEAKER = "スニーカー"
CATEGORY_LIQUOR = "お酒"
CATEGORY_WATCH = "時計"
CATEGORY_CAR = "車"
CATEGORY_COLORS = {
    CATEGORY_CARD: 0xF1C40F,
    CATEGORY_SNEAKER: 0x3498DB,
    CATEGORY_LIQUOR: 0xE67E22,
    CATEGORY_WATCH: 0x9B59B6,
    CATEGORY_CAR: 0xE74C3C,
}
DEFAULT_COLOR = 0x95A5A6

# タイトルにこのどれかが含まれるものだけを通す(情報源ごとに include= で指定する)
LOTTERY_KEYWORDS = ("抽選", "予約", "応募", "受付", "先着", "再販")
RELEASE_KEYWORDS = LOTTERY_KEYWORDS + ("発売", "販売")
# 「抽選で当たる」系の懸賞・プレゼント企画は、商品の抽選販売ではないので除外する(exclude= で指定する)
PRIZE_KEYWORDS = ("当たる", "プレゼント", "懸賞", "景品", "チケット")
CAMPAIGN_KEYWORDS = PRIZE_KEYWORDS + ("キャンペーン",)
# 実際の通知で目立った雑音(コンビニの腕時計、自治体のマンホール抽選など)。時計・車のニュース検索で除外する
NOISE_KEYWORDS = CAMPAIGN_KEYWORDS + ("ファミマ", "ファミリーマート", "コンビニ", "マンホール", "ガラポン", "ガンダム", "プラモ")

# 同じページでもURLの末尾だけが違う、を同一扱いにするため取り除くパラメータ
TRACKING_PARAMS = {"fbclid", "gclid", "yclid", "mc_cid", "mc_eid", "igshid"}

# Discord Webhook URL の形式チェック。これ以外のURLには絶対に送らない(誤設定・悪用の防止)
WEBHOOK_URL_RE = re.compile(
    r"^https://(?:(?:canary|ptb)\.)?discord(?:app)?\.com/api/(?:v\d+/)?webhooks/\d+/[\w-]+/?(?:\?.*)?$"
)
# ログにWebhookのトークンが出ないよう伏せるための正規表現
WEBHOOK_TOKEN_RE = re.compile(r"(/webhooks/\d+/)[\w-]+")


# ---------------------------------------------------------------------------
# 小さな共通関数
# ---------------------------------------------------------------------------


def clean_text(text: str) -> str:
    """連続する空白・改行を1つの空白にまとめる(全角半角の変換はしない)。"""
    return re.sub(r"\s+", " ", text).strip()


def truncate(text: str, limit: int) -> str:
    return text if len(text) <= limit else text[: limit - 1] + "…"


def normalize_url(url: str) -> str:
    """重複判定用にURLを整える(大文字小文字・末尾スラッシュ・追跡パラメータ・#以降を無視)。"""
    parts = urlsplit(url.strip())
    query = [
        (k, v)
        for k, v in parse_qsl(parts.query, keep_blank_values=True)
        if not k.lower().startswith("utm_") and k.lower() not in TRACKING_PARAMS
    ]
    path = parts.path.rstrip("/") or "/"
    return urlunsplit((parts.scheme.lower(), parts.netloc.lower(), path, urlencode(query), ""))


def normalize_title(title: str) -> str:
    """重複判定用にタイトルを整える(全角半角・大文字小文字・記号・空白の違いを無視)。"""
    return re.sub(r"[\W_]+", "", unicodedata.normalize("NFKC", title).lower())


def describe_error(exc: Exception) -> str:
    return f"{type(exc).__name__}: {exc}"


class MaskWebhookFilter(logging.Filter):
    """ログに Discord Webhook のトークンが混ざっても、伏せ字にする。"""

    def filter(self, record: logging.LogRecord) -> bool:
        record.msg = WEBHOOK_TOKEN_RE.sub(r"\1***", record.getMessage())
        record.args = ()
        return True


# ---------------------------------------------------------------------------
# データ構造と、通知済みの記録
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class Item:
    title: str
    url: str
    category: str
    source: str  # 情報源の名前(Embedの「情報源」に表示)
    detail: str = ""  # 補足(発売日・配信元など)


class HistoryError(Exception):
    pass


class History:
    """通知済みの記録(notified_history.json)。

    URL(整形済み)をキーに保存し、タイトルが同じものも「通知済み」として扱う。
    `last_seen` は「情報源にまだ載っている間は更新される日付」で、
    長いあいだ載らなくなったものだけを削除する。(載り続けている古い記事を消して
    再通知してしまう事故を防ぐため、単純な件数上限や登録日では消さない)
    """

    def __init__(self, path: Path):
        self.path = path
        self.existed = path.exists()
        self.items: dict[str, dict] = {}
        self.health: dict[str, int] = {}  # 情報源ごとの「連続失敗回数」(失敗中のものだけ)
        self.sources: set[str] = set()  # 一度でも巡回した情報源の名前(初めての情報源は既読登録だけにするため)
        self._titles: set[str] = set()
        self._saved_text: str | None = None
        if self.existed:
            self._load()
            self._saved_text = self._dump()

    def _load(self) -> None:
        try:
            data = json.loads(self.path.read_text(encoding="utf-8"))
            self.items = dict(data.get("items", {}))
            self.health = {k: int(v) for k, v in data.get("source_health", {}).items()}
            if "sources" in data:
                self.sources = {str(name) for name in data["sources"]}
            else:  # 古い形式の履歴: 記録済みの項目から「見たことのある情報源」を復元する
                self.sources = {str(e["source"]) for e in self.items.values() if e.get("source")}
        except (OSError, ValueError, AttributeError, TypeError, KeyError) as exc:
            # 黙って空扱いにすると、過去分が全部「新着」になって大量通知されてしまう
            raise HistoryError(f"{self.path.name} を読み込めません。内容を確認してください: {exc}") from exc
        self._rebuild_titles()

    def _rebuild_titles(self) -> None:
        self._titles = {t for t in (normalize_title(e.get("title", "")) for e in self.items.values()) if t}

    def _dump(self) -> str:
        data = {"version": 1, "sources": sorted(self.sources), "source_health": self.health, "items": self.items}
        return json.dumps(data, ensure_ascii=False, indent=1) + "\n"

    def seen(self, item: Item) -> bool:
        return normalize_url(item.url) in self.items or normalize_title(item.title) in self._titles

    def add(self, item: Item, now: datetime) -> None:
        self.items[normalize_url(item.url)] = {
            "title": item.title,
            "category": item.category,
            "source": item.source,
            "first_seen": now.isoformat(timespec="seconds"),
            "last_seen": now.date().isoformat(),
        }
        title_key = normalize_title(item.title)
        if title_key:
            self._titles.add(title_key)

    def touch(self, item: Item, now: datetime) -> None:
        """通知済みのものが今回も載っていた、という印を付ける(1日1回までしか書き換えない)。"""
        entry = self.items.get(normalize_url(item.url))
        if entry is not None:
            entry["last_seen"] = now.date().isoformat()

    def record_success(self, source_name: str) -> None:
        self.health.pop(source_name, None)

    def record_failure(self, source_name: str) -> int:
        self.health[source_name] = self.health.get(source_name, 0) + 1
        return self.health[source_name]

    def prune(self, now: datetime) -> None:
        cutoff = (now - timedelta(days=HISTORY_KEEP_DAYS)).date().isoformat()
        kept = {
            key: entry
            for key, entry in self.items.items()
            if (entry.get("last_seen") or entry.get("first_seen", "9999")[:10]) >= cutoff
        }
        if len(kept) != len(self.items):
            log.info("履歴から %d 件の古い記録を削除しました", len(self.items) - len(kept))
            self.items = kept
            self._rebuild_titles()

    def save(self) -> None:
        text = self._dump()
        if text == self._saved_text:
            return
        tmp = self.path.with_name(self.path.name + ".tmp")
        tmp.write_text(text, encoding="utf-8")
        os.replace(tmp, self.path)  # 書き込み途中で止まっても履歴が壊れないよう、置き換えで保存
        self._saved_text = text


# ---------------------------------------------------------------------------
# HTTP(相手サーバーに負担をかけない取得)
# ---------------------------------------------------------------------------


class RobotsDisallowed(Exception):
    pass


class Http:
    """User-Agentの設定、リクエスト間隔の確保、失敗時の控えめなリトライをまとめた入口。"""

    def __init__(self, interval: float = DEFAULT_INTERVAL_SEC, timeout: float = REQUEST_TIMEOUT_SEC):
        self.interval = interval
        self.timeout = timeout
        self.session = requests.Session()
        self.session.headers.update({"User-Agent": USER_AGENT, "Accept-Language": "ja,en;q=0.8"})
        retry = Retry(
            total=2,
            backoff_factor=2,
            status_forcelist=(429, 500, 502, 503, 504),
            allowed_methods=("GET",),
            respect_retry_after_header=True,
        )
        adapter = HTTPAdapter(max_retries=retry)
        self.session.mount("https://", adapter)
        self.session.mount("http://", adapter)
        self._last_request = float("-inf")
        self._robots: dict[str, RobotFileParser | None] = {}

    def _throttle(self) -> None:
        if self.interval <= 0:
            return
        wait = self._last_request + self.interval - time.monotonic()
        if wait > 0:
            time.sleep(wait + random.uniform(0, 1))

    def _fetch(self, url: str) -> requests.Response:
        self._throttle()
        try:
            return self.session.get(url, timeout=self.timeout)
        finally:
            self._last_request = time.monotonic()

    def _robots_allows(self, url: str) -> bool:
        parts = urlsplit(url)
        origin = f"{parts.scheme}://{parts.netloc}"
        if origin not in self._robots:
            resp = self._fetch(origin + "/robots.txt")
            if resp.status_code == 200:
                parser = RobotFileParser()
                parser.parse(resp.text.splitlines())
                self._robots[origin] = parser
            elif 400 <= resp.status_code < 500:
                self._robots[origin] = None  # robots.txt が無いサイトは、制限なしとして扱う
            else:
                raise RobotsDisallowed(f"robots.txt を確認できません(HTTP {resp.status_code}): {origin}")
        parser = self._robots[origin]
        return parser is None or parser.can_fetch(ROBOTS_AGENT, url)

    def get(self, url: str, *, check_robots: bool = False) -> requests.Response:
        """URLを取得する。check_robots=True のときは robots.txt が許可している場合だけ取得する。

        RSSは「機械が読む前提」で公開されているので確認しない。HTMLページは確認する。
        """
        if check_robots and not self._robots_allows(url):
            raise RobotsDisallowed(f"robots.txt で禁止されています: {url}")
        resp = self._fetch(url)
        resp.raise_for_status()
        return resp


# ---------------------------------------------------------------------------
# 情報源(ここを増やすと監視対象が増える)
# ---------------------------------------------------------------------------


@dataclass(kw_only=True)
class Source:
    name: str
    category: str
    url: str
    include: tuple[str, ...] = ()  # タイトルにどれか含まれるものだけ通す(空なら全部通す)
    exclude: tuple[str, ...] = ()  # タイトルにどれか含まれるものは通さない(include より優先)

    def fetch(self, http: Http) -> list[Item]:
        raise NotImplementedError

    def accepts(self, title: str) -> bool:
        text = _fold(title)
        if any(_fold(keyword) in text for keyword in self.exclude):
            return False
        if not self.include:
            return True
        return any(_fold(keyword) in text for keyword in self.include)


def _fold(text: str) -> str:
    """全角・半角や大文字・小文字の違いを無視して比べるための正規化(タイトルにもキーワードにも同じものを使う)。"""
    return unicodedata.normalize("NFKC", text).lower()


@dataclass(kw_only=True)
class RssSource(Source):
    """RSS / Atom フィード。Google ニュースの検索RSSもこれで扱える。"""

    max_age_days: int | None = None  # 公開日がこの日数より古い記事は無視する(日付が無ければ通す)

    def fetch(self, http: Http) -> list[Item]:
        resp = http.get(self.url)
        feed = feedparser.parse(resp.content)
        # 記事が0件でも、正しいRSSなら version が入る。空なのに形式が判別できない/壊れているときは、
        # アクセス拒否のページなどが返ってきたと考え、「0件で成功」にせず失敗として扱う
        if not feed.entries and (feed.bozo or not feed.get("version")):
            raise ValueError("RSSとして読み取れませんでした(アクセス拒否のページなどが返った可能性があります)")
        cutoff = datetime.now(timezone.utc) - timedelta(days=self.max_age_days) if self.max_age_days else None
        items: list[Item] = []
        for entry in feed.entries:
            title = clean_text(entry.get("title", ""))
            link = entry.get("link", "")
            if not title or not link:
                continue
            published = entry.get("published_parsed")
            if cutoff and published and datetime(*published[:6], tzinfo=timezone.utc) < cutoff:
                continue
            detail = ""
            media = clean_text((entry.get("source") or {}).get("title", ""))
            if media:  # Googleニュースは「タイトル - 媒体名」の形なので、媒体名を分ける
                title = title.removesuffix(f" - {media}")
                detail = f"配信元: {media}"
            items.append(Item(title, link, self.category, self.name, detail))
        return items


@dataclass(kw_only=True)
class HtmlListSource(Source):
    """記事一覧ページ。CSSセレクタで「記事へのリンク(<a>)」を指定して読み取る。"""

    item_selector: str  # 記事リンク(<a>)を指すCSSセレクタ
    title_selector: str | None = None  # <a>の中でタイトルを含む部分(省略なら<a>全体)
    strip_selectors: tuple[str, ...] = ()  # タイトルから取り除く部分(日付やラベルなど)

    def fetch(self, http: Http) -> list[Item]:
        resp = http.get(self.url, check_robots=True)
        soup = BeautifulSoup(resp.content, "html.parser")
        items: dict[str, Item] = {}
        for link in soup.select(self.item_selector):
            href = link.get("href")
            node = link.select_one(self.title_selector) if self.title_selector else link
            if not href or node is None:
                continue
            for junk in node.select(", ".join(self.strip_selectors)) if self.strip_selectors else []:
                junk.decompose()
            title = clean_text(node.get_text(" "))
            url = urljoin(self.url, href)
            if title and url not in items:  # 同じ記事が一覧の複数の場所に載っていることがある
                items[url] = Item(title, url, self.category, self.name)
        if not items:
            raise ValueError("記事が1件も見つかりません(サイトの構造が変わった可能性があります)")
        return list(items.values())


NIKE_METHOD_LABELS = {"DRAW": "抽選(DRAW)", "LINE": "並び(LINE)"}


@dataclass(kw_only=True)
class NikeSnkrsSource(Source):
    """Nike SNKRS のローンチ一覧(https://www.nike.com/jp/launch)。

    商品カードは画像だけで、名前などは後から画面に描かれる。ただしページのHTMLには
    同じ内容が __NEXT_DATA__ というJSONで埋め込まれているので、そこから読み取る。
    """

    def fetch(self, http: Http) -> list[Item]:
        resp = http.get(self.url, check_robots=True)
        items = parse_nike_launch(resp.content, self.url, self.category, self.name)
        if not items:
            raise ValueError("ローンチ情報が1件も見つかりません(サイトの構造が変わった可能性があります)")
        return items


def parse_nike_launch(html: bytes | str, base_url: str, category: str, source_name: str) -> list[Item]:
    soup = BeautifulSoup(html, "html.parser")
    try:
        data = json.loads(soup.find("script", id="__NEXT_DATA__").string)
        state = data["props"]["pageProps"]["initialState"]
        if isinstance(state, str):  # JSONが文字列として二重に入っている
            state = json.loads(state)
        threads = state["product"]["threads"]["data"]["items"].values()
        # 商品データは補足(発売日など)にしか使わないので、無くても題名とURLは取れるようにする
        products = ((state["product"].get("products") or {}).get("data") or {}).get("items") or {}
        items = []
        for thread in threads:
            seo = thread.get("seo") or {}
            slug = seo.get("slug")
            title = _nike_clean_title(seo.get("title") or thread.get("title") or "")
            if slug and title:
                url = urljoin(base_url, f"/jp/launch/t/{slug}")
                items.append(Item(title, url, category, source_name, _nike_detail(thread, products)))
        return items
    except (AttributeError, KeyError, TypeError, ValueError) as exc:
        # 埋め込みJSONの構造が変わったときの保険。リンクだけ拾い、URLの末尾から題名を作る
        log.warning("Nikeの埋め込みデータを読めませんでした(%s)。リンクから簡易的に取得します", describe_error(exc))
    items = {}
    for link in soup.select('a[href*="/launch/t/"]'):
        url = urljoin(base_url, link["href"])
        slug = urlsplit(url).path.rstrip("/").rsplit("/", 1)[-1]
        items.setdefault(url, Item(slug.replace("-", " "), url, category, source_name))
    return list(items.values())


def _nike_clean_title(title: str) -> str:
    title = clean_text(title).removeprefix("【NIKE公式】").strip()
    return re.sub(r"\s*発売日$", "", title)


def _nike_detail(thread: dict, products: dict) -> str:
    """商品データから「販売開始日時」と「抽選/並びの有無」を補足として作る。"""
    starts: list[datetime] = []
    methods: set[str] = set()
    for pid in [thread.get("productId"), *(thread.get("productIds") or [])]:
        product = products.get(pid) or {}
        try:
            starts.append(datetime.fromisoformat(product["commerceStartDate"].replace("Z", "+00:00")))
        except (KeyError, AttributeError, ValueError):
            pass  # 日付が無い・読めない商品は、日付なしで通知する
        methods.update(sku["method"] for sku in product.get("skus") or [] if sku.get("method"))
    parts = []
    if starts:
        parts.append("販売開始: " + min(starts).astimezone(JST).strftime("%Y-%m-%d %H:%M") + " JST")
    labels = [NIKE_METHOD_LABELS[m] for m in ("DRAW", "LINE") if m in methods]
    if labels:
        parts.append("方式: " + "・".join(labels))
    return " / ".join(parts)


def google_news_url(query: str) -> str:
    """Googleニュースの検索RSS。`when:7d` で直近7日の記事に絞る。"""
    params = {"q": f"{query} when:7d", "hl": "ja", "gl": "JP", "ceid": "JP:ja"}
    return "https://news.google.com/rss/search?" + urlencode(params)


def news_source(query: str, category: str, *, include=LOTTERY_KEYWORDS, exclude=PRIZE_KEYWORDS) -> RssSource:
    """Googleニュース検索を情報源にする(検索語は `OR` でつなげられる)。"""
    return RssSource(
        name=f"Googleニュース「{query}」", category=category, url=google_news_url(query), include=include, exclude=exclude
    )


SOURCES: list[Source] = [
    # --- トレーディングカード ---
    HtmlListSource(
        name="ポケモンカード公式 お知らせ",
        category=CATEGORY_CARD,
        url="https://www.pokemon-card.com/info/",
        item_selector="a.List_item_inner",
        title_selector=".List_body",
        strip_selectors=(".Calendar_Label", ".Date"),
        include=RELEASE_KEYWORDS,
    ),
    # ポケモンセンターオンラインは、トップページの「お知らせ」欄に抽選販売の案内が載る
    # (お知らせ専用の一覧ページは無く、robots.txt は全ページ許可)
    HtmlListSource(
        name="ポケモンセンターオンライン お知らせ",
        category=CATEGORY_CARD,
        url="https://www.pokemoncenter-online.com/",
        item_selector='ul.noticeUl a[href^="/news/?id="]',
        title_selector=".ttl",
        include=RELEASE_KEYWORDS,
    ),
    HtmlListSource(
        name="遊戯王OCG公式 ニュース",
        category=CATEGORY_CARD,
        url="https://www.yugioh-card.com/japan/news/",
        item_selector="section.news-list a.news",
        strip_selectors=("time",),
        include=RELEASE_KEYWORDS,
    ),
    # プレミアムバンダイ(ワンピース・ドラゴンボールの公式抽選販売)は、GitHub Actions(海外)から一覧ページを
    # 読むと記事が返ってこなかったので、Googleニュース経由にしている。フィギュア・プラモの抽選は除外
    news_source(
        "プレバン カード 抽選",
        CATEGORY_CARD,
        exclude=PRIZE_KEYWORDS + ("ガンダム", "フィギュア", "プラモ", "ROBOT"),
    ),
    # ゲオのお知らせ(ポケカ・ワンピースの再販抽選を定期的に告知。応募には本人確認あり)
    HtmlListSource(
        name="ゲオ お知らせ(抽選販売)",
        category=CATEGORY_CARD,
        url="https://geo-online.co.jp/news/",
        item_selector='section ul li a[href^="/news/"]',
        title_selector=".infoTitle",
        include=("抽選",),
    ),
    news_source("ポケカ 抽選", CATEGORY_CARD),
    news_source("ワンピースカード 抽選", CATEGORY_CARD),
    news_source("遊戯王 抽選", CATEGORY_CARD),
    news_source("ドラゴンボール カードゲーム 抽選 OR 予約", CATEGORY_CARD),
    news_source("マジック・ザ・ギャザリング OR MTG 抽選 OR 予約", CATEGORY_CARD),
    # --- スニーカー・ファッション ---
    NikeSnkrsSource(
        name="Nike SNKRS ローンチ",
        category=CATEGORY_SNEAKER,
        url="https://www.nike.com/jp/launch",
    ),
    # atmos の抽選一覧(https://www.atmos-tokyo.com/raffles)は GitHub Actions(海外)からは 403 で読めず、
    # Googleニュース「atmos 抽選」も過去記事の再掲が週40件と多いので、どちらも入れていない
    # Googleニュース「スニーカー 抽選」も7日で60件超と雑音が多く、Nike を直接読むので外した
    # --- お酒(ウイスキー・プレミア日本酒) ---
    news_source("ウイスキー 抽選販売", CATEGORY_LIQUOR),
    news_source("日本酒 抽選販売", CATEGORY_LIQUOR),
    # --- 時計(限定モデルの抽選販売) ---
    news_source("腕時計 抽選販売", CATEGORY_WATCH, exclude=NOISE_KEYWORDS),
    news_source("ロレックス OR グランドセイコー OR オメガ 時計 抽選 OR 限定", CATEGORY_WATCH, include=RELEASE_KEYWORDS, exclude=NOISE_KEYWORDS),
    news_source("G-SHOCK OR カシオ 限定 抽選 OR 発売", CATEGORY_WATCH, include=RELEASE_KEYWORDS, exclude=NOISE_KEYWORDS),
    # --- 車(限定車・抽選販売車) ---
    news_source("限定車 抽選販売", CATEGORY_CAR, exclude=NOISE_KEYWORDS),
    news_source("トヨタ OR 日産 OR ホンダ OR マツダ OR スバル 抽選販売", CATEGORY_CAR, exclude=NOISE_KEYWORDS),
    news_source("GRヤリス OR GRカローラ OR ランドクルーザー OR GT-R OR フェアレディZ 抽選", CATEGORY_CAR, exclude=NOISE_KEYWORDS),
]


# ---------------------------------------------------------------------------
# Discord
# ---------------------------------------------------------------------------


class DiscordError(Exception):
    pass


class DiscordNotifier:
    MAX_ATTEMPTS = 3

    def __init__(self, webhook_url: str, timeout: float = 15):
        self.webhook_url = webhook_url
        self.timeout = timeout

    def send(self, payload: dict) -> None:
        last_problem = ""
        for attempt in range(1, self.MAX_ATTEMPTS + 1):
            try:
                resp = requests.post(self.webhook_url, json=payload, timeout=self.timeout)
            except requests.RequestException as exc:
                # 例外の文章にはWebhook URL(=秘密)が入ることがあるので、種類だけを記録する
                last_problem = f"通信エラー({type(exc).__name__})"
                time.sleep(2 * attempt)
                continue
            if resp.status_code in (200, 204):
                return
            if resp.status_code == 429:  # 送りすぎ。指定された秒数だけ待つ
                last_problem = "レート制限(HTTP 429)"
                time.sleep(min(self._retry_after(resp), 30))
                continue
            if resp.status_code >= 500:
                last_problem = f"Discord側のエラー(HTTP {resp.status_code})"
                time.sleep(2 * attempt)
                continue
            raise DiscordError(f"Discordに拒否されました(HTTP {resp.status_code}): {truncate(resp.text, 200)}")
        raise DiscordError(f"Discordへの送信に失敗しました: {last_problem}")

    @staticmethod
    def _retry_after(resp: requests.Response) -> float:
        try:
            return float(resp.json().get("retry_after", 1))
        except (ValueError, AttributeError, TypeError):
            pass
        try:
            return float(resp.headers.get("Retry-After", 1))
        except (ValueError, TypeError):
            return 1.0


def build_embed(item: Item, fetched_at: datetime) -> dict:
    description = item.url if not item.detail else f"{item.url}\n{item.detail}"
    return {
        "title": truncate(item.title, 256),
        "url": item.url,
        "description": truncate(description, 2000),
        "color": CATEGORY_COLORS.get(item.category, DEFAULT_COLOR),
        "fields": [
            {"name": "カテゴリ", "value": truncate(item.category, 1024), "inline": True},
            {"name": "情報源", "value": truncate(item.source, 1024), "inline": True},
            {"name": "取得日時", "value": fetched_at.strftime("%Y-%m-%d %H:%M") + " JST", "inline": True},
        ],
        "timestamp": fetched_at.astimezone(timezone.utc).isoformat(),
    }


def embed_size(embed: dict) -> int:
    fields = sum(len(f["name"]) + len(f["value"]) for f in embed.get("fields", []))
    return len(embed.get("title", "")) + len(embed.get("description", "")) + fields


def batch_embeds(pairs: list[tuple[Item, dict]]) -> list[list[tuple[Item, dict]]]:
    """Discordの制限(10個まで・合計6000文字まで)に収まるよう、メッセージ単位に分ける。"""
    batches: list[list[tuple[Item, dict]]] = []
    current: list[tuple[Item, dict]] = []
    size = 0
    for pair in pairs:
        pair_size = embed_size(pair[1])
        if current and (len(current) >= EMBEDS_PER_MESSAGE or size + pair_size > EMBED_CHARS_PER_MESSAGE):
            batches.append(current)
            current, size = [], 0
        current.append(pair)
        size += pair_size
    if current:
        batches.append(current)
    return batches


def text_payload(content: str) -> dict:
    # allowed_mentions で @everyone などが誤って発動しないようにする(取得した文章は信用しない)
    return {"content": content, "allowed_mentions": {"parse": []}}


# ---------------------------------------------------------------------------
# 実行の流れ
# ---------------------------------------------------------------------------


def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="抽選・予約・リリース情報を監視してDiscordへ通知します")
    parser.add_argument("--dry-run", action="store_true", help="Discordへ送信せず、履歴も書き換えず、内容だけ表示する")
    parser.add_argument("--no-baseline", action="store_true", help="初回実行でも既存分を通知する(通常は既読登録だけ行う)")
    parser.add_argument("--only", metavar="名前", help="名前にこの文字を含む情報源だけを実行する")
    parser.add_argument("--history", type=Path, default=BASE_DIR / "notified_history.json", help="履歴ファイルの場所")
    parser.add_argument("--interval", type=float, default=DEFAULT_INTERVAL_SEC, help="リクエスト間隔(秒)")
    parser.add_argument("-v", "--verbose", action="store_true", help="詳しいログを出す")
    return parser.parse_args(argv)


def setup_logging(verbose: bool) -> None:
    handler = logging.StreamHandler(sys.stderr)
    handler.setFormatter(logging.Formatter("%(asctime)s %(levelname)s %(message)s", "%H:%M:%S"))
    handler.addFilter(MaskWebhookFilter())
    logging.basicConfig(level=logging.DEBUG if verbose else logging.INFO, handlers=[handler], force=True)


def run(args: argparse.Namespace, sources: list[Source] | None = None) -> int:
    """終了コード: 0=正常 / 1=取得や送信の失敗 / 2=設定の誤り"""
    sources = list(SOURCES if sources is None else sources)
    if args.only:
        sources = [s for s in sources if args.only in s.name]
        if not sources:
            log.error("--only %r に一致する情報源がありません", args.only)
            return 2

    webhook_url = os.environ.get("DISCORD_WEBHOOK_URL", "").strip()
    webhook_ok = bool(WEBHOOK_URL_RE.match(webhook_url))
    if not webhook_ok and not args.dry_run:
        log.error("環境変数 DISCORD_WEBHOOK_URL が未設定、または Discord Webhook の形式ではありません")
        return 2
    if not webhook_ok:
        log.warning("DISCORD_WEBHOOK_URL が未設定か形式が違いますが、dry-runなので続行します")
    notifier = DiscordNotifier(webhook_url)

    try:
        history = History(args.history)
    except HistoryError as exc:
        log.error("%s", exc)
        return 1

    now = datetime.now(JST)
    http = Http(args.interval)

    # 1) 情報源を順番に巡回する(1つ失敗しても、ほかは続ける)
    collected: list[Item] = []
    failed: list[str] = []
    alerts: list[str] = []
    for source in sources:
        try:
            matched = [item for item in source.fetch(http) if source.accepts(item.title)]
        except Exception as exc:  # noqa: BLE001 - 情報源ごとの失敗を全体に広げない
            streak = history.record_failure(source.name)
            failed.append(source.name)
            log.warning("[%s] 取得に失敗しました(連続%d回目): %s", source.name, streak, describe_error(exc))
            if streak == SOURCE_FAIL_ALERT_STREAK:
                alerts.append(source.name)
            continue
        history.record_success(source.name)
        log.info("[%s] 条件に合う情報: %d件", source.name, len(matched))
        collected.extend(matched)

    if len(failed) == len(sources):
        log.error("すべての情報源の取得に失敗しました")
        return 1

    # 2) 新着(まだ通知していないもの)だけを選ぶ。今回の取得分どうしの重複も除く
    #    後から追加された情報源(履歴に名前がない)の分は、通知せず既読登録だけにする
    fetched_names = {s.name for s in sources if s.name not in failed}
    new_source_names = [] if args.no_baseline else sorted(fetched_names - history.sources)
    fresh: list[Item] = []
    fresh_from_new_sources: list[Item] = []
    batch_keys: set[str] = set()
    for item in collected:
        if history.seen(item):
            history.touch(item, now)
            continue
        keys = {"u:" + normalize_url(item.url), "t:" + normalize_title(item.title)}
        if keys & batch_keys:
            continue
        batch_keys |= keys
        (fresh_from_new_sources if item.source in new_source_names else fresh).append(item)
    log.info("新着: %d件", len(fresh))

    status = 0
    persist = history.existed  # 履歴ファイルを新しく作ってよいか(初回の開始通知が成功したときだけ true)
    try:
        if not history.existed and not args.no_baseline:
            _register_baseline(history, fresh + fresh_from_new_sources, notifier, now, args.dry_run)
            history.sources |= fetched_names
            persist = True  # 送信に失敗すると上で例外になり、ここには来ない
        else:
            if new_source_names:
                _register_new_sources(history, new_source_names, fresh_from_new_sources, notifier, now, args.dry_run)
            status = _notify_new_items(history, fresh, notifier, now, args.dry_run)
        if alerts:
            _send_health_alert(alerts, notifier, args.dry_run)
    except DiscordError as exc:
        log.error("%s", exc)
        status = 1
    finally:
        # 途中まで送れた分の記録も残す。次回は続きから通知される。
        # ただし初回の送信に失敗したときは、空の履歴を作らない(次回もう一度「初回」から始めるため)
        if not args.dry_run and (persist or history.items):
            history.prune(now)
            history.save()
    return status


def _register_baseline(history: History, fresh: list[Item], notifier: DiscordNotifier, now: datetime, dry_run: bool) -> None:
    """初回は、いま載っている情報を通知せずに「既読」にする(過去分の大量通知を防ぐ)。"""
    message = (
        f"✅ 抽選・予約ウォッチャーの監視を開始しました。現在掲載中の{len(fresh)}件は通知せず既読にしました。"
        "これ以降は新着だけをお知らせします。"
    )
    if dry_run:
        log.info("[DRY-RUN] 初回実行のため、%d件を通知せず既読登録する動きになります", len(fresh))
        print(json.dumps(text_payload(message), ensure_ascii=False, indent=2))
        return
    notifier.send(text_payload(message))  # 先に送る。Webhookが間違っていれば、ここで失敗して記録は残らない
    for item in fresh:
        history.add(item, now)
    log.info("初回実行: %d件を既読登録しました", len(fresh))


def _register_new_sources(
    history: History, names: list[str], items: list[Item], notifier: DiscordNotifier, now: datetime, dry_run: bool
) -> None:
    """後から追加した情報源も、初回は「既読登録だけ」にする(その時点の掲載分を一気に通知しないため)。"""
    lines = "\n".join(f"・{name}" for name in names)
    message = f"🆕 情報源を{len(names)}件追加しました。現在掲載中の{len(items)}件は通知せず既読にしました。\n{lines}"
    if dry_run:
        log.info("[DRY-RUN] 新しい情報源 %d件の %d件を通知せず既読登録する動きになります", len(names), len(items))
        print(json.dumps(text_payload(message), ensure_ascii=False, indent=2))
        return
    notifier.send(text_payload(message))  # 送れなかったときは記録せず、次回もう一度「初回」として扱う
    for item in items:
        history.add(item, now)
    history.sources |= set(names)
    log.info("新しい情報源 %d件: %d件を既読登録しました", len(names), len(items))


def _notify_new_items(history: History, fresh: list[Item], notifier: DiscordNotifier, now: datetime, dry_run: bool) -> int:
    to_send = fresh[:MAX_NOTIFY_PER_RUN]
    deferred = len(fresh) - len(to_send)
    if deferred:
        log.info("1回の上限(%d件)を超えた %d件は、次回以降に通知します", MAX_NOTIFY_PER_RUN, deferred)
    if not to_send:
        return 0

    header = f"🔔 新着情報 {len(to_send)}件" + (f"(ほか{deferred}件は次回以降にお知らせします)" if deferred else "")
    batches = batch_embeds([(item, build_embed(item, now)) for item in to_send])
    for index, batch in enumerate(batches):
        payload = {"embeds": [embed for _, embed in batch], "allowed_mentions": {"parse": []}}
        if index == 0:
            payload["content"] = header
        if dry_run:
            log.info("[DRY-RUN] %d通目(Embed %d個)を送る予定です", index + 1, len(batch))
            print(json.dumps(payload, ensure_ascii=False, indent=2))
            continue
        notifier.send(payload)
        for item, _ in batch:
            history.add(item, now)
        history.save()  # 1通送るごとに記録する。途中で失敗しても二重通知にならない
        log.info("%d通目を送信しました(%d件)", index + 1, len(batch))
        time.sleep(1)  # Discordへの連続送信を避ける
    return 0


def _send_health_alert(names: list[str], notifier: DiscordNotifier, dry_run: bool) -> None:
    lines = "\n".join(f"・{name}" for name in names)
    message = (
        f"⚠️ 次の情報源が{SOURCE_FAIL_ALERT_STREAK}回連続で取得できていません。サイトの仕様変更や、"
        f"アクセス拒否の可能性があります。\n{lines}"
    )
    if dry_run:
        print(json.dumps(text_payload(message), ensure_ascii=False, indent=2))
        return
    try:
        notifier.send(text_payload(message))
    except DiscordError as exc:  # 警告が送れなくても、本来の処理は止めない
        log.warning("警告の送信に失敗しました: %s", exc)


def main(argv: list[str] | None = None) -> int:
    args = parse_args(argv)
    setup_logging(args.verbose)
    return run(args)


if __name__ == "__main__":
    sys.exit(main())
