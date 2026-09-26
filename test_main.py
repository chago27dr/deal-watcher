"""main.py のオフラインテスト(ネットにも Discord にも接続しない)。

実行: python -m unittest -v
"""
from __future__ import annotations

import argparse
import json
import logging
import os
import tempfile
import unittest
from datetime import datetime, timedelta
from pathlib import Path
from unittest import mock

import requests

import main
from main import (
    DiscordError,
    DiscordNotifier,
    History,
    HistoryError,
    HtmlListSource,
    Item,
    JST,
    RssSource,
    Source,
    batch_embeds,
    build_embed,
    embed_size,
    normalize_title,
    normalize_url,
    parse_nike_launch,
)

DUMMY_WEBHOOK = "https://discord.com/api/webhooks/000000000000000000/DUMMY_token-for_tests"
NOW = datetime(2026, 9, 25, 14, 0, tzinfo=JST)


class FakeResponse:
    def __init__(self, content: bytes = b"", status_code: int = 200, json_data=None, text: str = ""):
        self.content = content
        self.status_code = status_code
        self._json = json_data
        self.text = text
        self.headers: dict = {}

    def json(self):
        if self._json is None:
            raise ValueError("no json")
        return self._json


class FakeHttp:
    """Http の代わり。指定した中身を返すだけ。"""

    def __init__(self, content: bytes):
        self.content = content
        self.calls: list[tuple[str, bool]] = []

    def get(self, url: str, *, check_robots: bool = False):
        self.calls.append((url, check_robots))
        return FakeResponse(self.content)


class NormalizeTests(unittest.TestCase):
    def test_url_ignores_tracking_case_slash_fragment(self):
        a = normalize_url("HTTPS://Example.com/path/?utm_source=x&id=1&fbclid=z#top")
        b = normalize_url("https://example.com/path?id=1")
        self.assertEqual(a, b)

    def test_url_keeps_meaningful_query(self):
        self.assertNotEqual(normalize_url("https://e.com/a?id=1"), normalize_url("https://e.com/a?id=2"))

    def test_title_ignores_width_case_and_symbols(self):
        self.assertEqual(normalize_title("【ポケカ】Ｐｒｏｍｏ 抽選！"), normalize_title("ポケカ promo  抽選"))


class HistoryTests(unittest.TestCase):
    def setUp(self):
        self.dir = tempfile.TemporaryDirectory()
        self.path = Path(self.dir.name) / "h.json"

    def tearDown(self):
        self.dir.cleanup()

    def item(self, title="抽選のお知らせ", url="https://e.com/1"):
        return Item(title, url, "お酒", "src")

    def test_round_trip_and_seen_by_url_or_title(self):
        h = History(self.path)
        self.assertFalse(h.existed)
        h.add(self.item(), NOW)
        h.save()
        h2 = History(self.path)
        self.assertTrue(h2.existed)
        self.assertTrue(h2.seen(self.item()))  # 同じURL
        self.assertTrue(h2.seen(self.item(url="https://other.com/x")))  # 同じタイトル
        self.assertFalse(h2.seen(self.item(title="別の抽選", url="https://e.com/2")))

    def test_unchanged_history_is_not_rewritten(self):
        h = History(self.path)
        h.add(self.item(), NOW)
        h.save()
        before = self.path.stat().st_mtime_ns
        History(self.path).save()
        self.assertEqual(before, self.path.stat().st_mtime_ns)

    def test_corrupted_file_raises_instead_of_resetting(self):
        self.path.write_text("{ broken", encoding="utf-8")
        with self.assertRaises(HistoryError):
            History(self.path)

    def test_prune_uses_last_seen_not_first_seen(self):
        h = History(self.path)
        h.add(self.item(url="https://e.com/old"), NOW - timedelta(days=200))  # 200日前に登録
        h.add(self.item(title="B", url="https://e.com/keep"), NOW - timedelta(days=200))
        h.touch(self.item(title="B", url="https://e.com/keep"), NOW)  # こちらは今も載っている
        h.prune(NOW)
        self.assertEqual(list(h.items), ["https://e.com/keep"])
        self.assertFalse(h.seen(self.item(title="全然違う", url="https://e.com/old")))

    def test_health_streak(self):
        h = History(self.path)
        self.assertEqual(h.record_failure("s"), 1)
        self.assertEqual(h.record_failure("s"), 2)
        h.record_success("s")
        self.assertEqual(h.health, {})


RSS = """<?xml version="1.0" encoding="UTF-8"?>
<rss version="2.0"><channel><title>t</title>
<item><title>ウイスキー限定 抽選販売のお知らせ - グルメ Watch</title>
<link>https://news.example/a?utm_source=x</link><pubDate>Thu, 24 Sep 2026 03:00:00 GMT</pubDate>
<source url="https://gw.example">グルメ Watch</source></item>
<item><title>ただの新商品ニュース - PR TIMES</title>
<link>https://news.example/b</link><pubDate>Thu, 24 Sep 2026 03:00:00 GMT</pubDate>
<source url="https://pr.example">PR TIMES</source></item>
<item><title>古い抽選の記事 - 媒体</title>
<link>https://news.example/c</link><pubDate>Mon, 01 Jan 2024 03:00:00 GMT</pubDate></item>
</channel></rss>""".encode("utf-8")


class RssSourceTests(unittest.TestCase):
    def test_parses_strips_media_suffix_and_filters_old(self):
        src = RssSource(name="rss", category="お酒", url="https://feed.example/", include=("抽選",))
        items = src.fetch(FakeHttp(RSS))
        titles = [i.title for i in items]
        self.assertIn("ウイスキー限定 抽選販売のお知らせ", titles)  # 媒体名の接尾辞が外れている
        self.assertEqual(items[0].detail, "配信元: グルメ Watch")
        matched = [i for i in items if src.accepts(i.title)]
        self.assertEqual(len(matched), 2)  # 「ただの新商品ニュース」は除外される

    def test_exclude_beats_include(self):
        src = RssSource(name="rss", category="時計", url="https://feed.example/", include=("抽選",), exclude=("当たる",))
        self.assertTrue(src.accepts("限定モデルの抽選販売を開始"))
        self.assertFalse(src.accepts("抽選で腕時計が当たるキャンペーン"))  # 懸賞は商品の抽選販売ではない
        self.assertFalse(src.accepts("新作を発売"))

    def test_max_age_drops_old_entries(self):
        src = RssSource(name="rss", category="お酒", url="https://feed.example/", max_age_days=30)
        with mock.patch.object(main, "datetime", wraps=datetime) as fake:
            fake.now.return_value = datetime(2026, 9, 25, tzinfo=JST)
            titles = [i.title for i in src.fetch(FakeHttp(RSS))]
        self.assertNotIn("古い抽選の記事", titles)
        self.assertEqual(len(titles), 2)

    def test_non_rss_pages_raise_but_empty_valid_feed_does_not(self):
        src = RssSource(name="rss", category="お酒", url="https://feed.example/")
        for body in (b"<html><body>Access Denied</body></html>", b"<Error><Code>AccessDenied</Code></Error>", b""):
            with self.assertRaises(ValueError, msg=body):
                src.fetch(FakeHttp(body))
        empty_feed = b'<?xml version="1.0"?><rss version="2.0"><channel><title>t</title></channel></rss>'
        self.assertEqual(src.fetch(FakeHttp(empty_feed)), [])  # 該当記事が無いだけなのでエラーにしない


HTML_LIST = """<html><body><ul>
<li class="List_item"><a class="List_item_inner" href="/info/005452.html"><div class="List_body">
  <div class="Calendar_Label">イベント</div> 「ポケカ」抽選販売のお知らせ <span class="Date">2026.9.25</span></div></a></li>
<li class="List_item"><a class="List_item_inner" href="/info/005452.html"><div class="List_body">
  <div class="Calendar_Label">イベント</div> 「ポケカ」抽選販売のお知らせ <span class="Date">2026.9.25</span></div></a></li>
<li class="List_item"><a class="List_item_inner" href="/info/005690.html"><div class="List_body">
  <div class="Calendar_Label">その他</div> 優勝者インタビュー <span class="Date">2026.9.25</span></div></a></li>
</ul></body></html>""".encode("utf-8")


class HtmlListSourceTests(unittest.TestCase):
    def make(self):
        return HtmlListSource(
            name="html", category="トレーディングカード", url="https://site.example/info/",
            item_selector="a.List_item_inner", title_selector=".List_body",
            strip_selectors=(".Calendar_Label", ".Date"), include=("抽選",),
        )

    def test_clean_title_absolute_url_and_dedupe(self):
        http = FakeHttp(HTML_LIST)
        items = self.make().fetch(http)
        self.assertEqual([i.url for i in items], ["https://site.example/info/005452.html", "https://site.example/info/005690.html"])
        self.assertEqual(items[0].title, "「ポケカ」抽選販売のお知らせ")  # ラベルと日付が外れている
        self.assertEqual(http.calls, [("https://site.example/info/", True)])  # HTMLは robots.txt を確認する

    def test_empty_result_is_an_error(self):
        with self.assertRaises(ValueError):
            self.make().fetch(FakeHttp("<html><body>構造が変わった</body></html>".encode("utf-8")))

    def test_pokemon_center_online_notice_list(self):
        src = next(s for s in main.SOURCES if s.name == "ポケモンセンターオンライン お知らせ")
        html = """<html><body><ul class="noticeUl">
        <li><a href="/news/?id=20260904"><span class="time">2026年09月04日</span><span class="ttl">30周年記念商品の追加抽選販売について</span></a></li>
        <li><a href="/news/?id=20260915_2"><span class="time">2026年09月15日</span><span class="ttl">営業と発送スケジュールについて</span></a></li>
        <li><a href="/product/123">商品ページ(お知らせではない)</a></li>
        </ul></body></html>""".encode("utf-8")
        items = [i for i in src.fetch(FakeHttp(html)) if src.accepts(i.title)]
        self.assertEqual([(i.title, i.url) for i in items],
                         [("30周年記念商品の追加抽選販売について", "https://www.pokemoncenter-online.com/news/?id=20260904")])

    def test_premium_bandai_geo_and_atmos_lists(self):
        cases = {
            "プレミアムバンダイ カード抽選": (
                '<div class="article"><div class="article_photo"><a href="/item/item-1/"><img alt="x"/></a></div>'
                '<p class="article_title"><a href="/item/item-1/">【抽選販売】ONE PIECEカードゲーム 4th Anniversary Set</a></p>'
                '<p class="article_title"><a href="/item/item-2/">ONE PIECEカードゲーム 通常商品</a></p></div>',
                [("【抽選販売】ONE PIECEカードゲーム 4th Anniversary Set", "https://p-bandai.jp/item/item-1/")],
            ),
            "ゲオ お知らせ(抽選販売)": (
                '<section><ul><li><a href="/news/783"><span class="date">2026/09/18</span>'
                '<span class="infoTitle">ポケモンカード 抽選販売受付のお知らせ</span></a></li>'
                '<li><a href="/news/776"><span class="date">2026/07/16</span><span class="infoTitle">なりすましにご注意</span></a></li></ul></section>',
                [("ポケモンカード 抽選販売受付のお知らせ", "https://geo-online.co.jp/news/783")],
            ),
            "atmos 抽選一覧": (
                '<ul class="raffles-lists"><li class="raffles-lists-item"><a href="https://www.atmos-tokyo.com/raffles/abc">'
                '<div class="raffles-lists-label"><span>2026.9.30 8:59 終了</span></div><h3 class="raffles-lists-title">crocs ROY</h3>'
                '<p class="raffles-lists-price">￥13,200</p></a></li></ul>',
                [("crocs ROY", "https://www.atmos-tokyo.com/raffles/abc")],
            ),
        }
        for name, (html, expected) in cases.items():
            src = next(s for s in main.SOURCES if s.name == name)
            page = f'<html><head><meta charset="utf-8"></head><body>{html}</body></html>'.encode("utf-8")
            items = [i for i in src.fetch(FakeHttp(page)) if src.accepts(i.title)]
            self.assertEqual([(i.title, i.url) for i in items], expected, name)

    def test_yugioh_news_list_strips_time(self):
        src = next(s for s in main.SOURCES if s.name == "遊戯王OCG公式 ニュース")
        html = """<html><body><section class="news-list"><ul class="news-list">
        <li><a class="news" href="//www.yugioh-card.com/japan/products/x/"><time>2026.09.20</time>限定パックの予約受付について</a></li>
        <li><a class="news" href="/japan/event/a/"><time>2026.09.19</time>大会結果</a></li>
        </ul></section></body></html>""".encode("utf-8")
        items = [i for i in src.fetch(FakeHttp(html)) if src.accepts(i.title)]
        self.assertEqual([(i.title, i.url) for i in items],
                         [("限定パックの予約受付について", "https://www.yugioh-card.com/japan/products/x/")])


def nike_page(threads: dict, products: dict, *, double_encoded=True) -> bytes:
    state = {"product": {"threads": {"data": {"items": threads}}, "products": {"data": {"items": products}}}}
    page_props = {"initialState": json.dumps(state) if double_encoded else state}
    next_data = json.dumps({"props": {"pageProps": page_props}})
    return f'<html><body><script id="__NEXT_DATA__" type="application/json">{next_data}</script></body></html>'.encode()


class NikeTests(unittest.TestCase):
    THREADS = {
        "t1": {"seo": {"slug": "air-jordan-1-royal", "title": "【NIKE公式】エア ジョーダン 1 'Royal' (IQ5495-005) 発売日"}, "productIds": ["p1"]},
        "t2": {"seo": {"slug": "story-x", "title": "ストーリー"}, "productIds": []},
    }
    PRODUCTS = {
        "p1": {"commerceStartDate": "2026-10-10T00:00:00.000Z", "skus": [{"method": "SHIP"}, {"method": "DRAW"}]},
    }

    def test_parses_title_url_date_and_draw(self):
        items = parse_nike_launch(nike_page(self.THREADS, self.PRODUCTS), "https://www.nike.com/jp/launch", "スニーカー", "nike")
        first = items[0]
        self.assertEqual(first.title, "エア ジョーダン 1 'Royal' (IQ5495-005)")  # 接頭辞と「発売日」が外れている
        self.assertEqual(first.url, "https://www.nike.com/jp/launch/t/air-jordan-1-royal")
        self.assertEqual(first.detail, "販売開始: 2026-10-10 09:00 JST / 方式: 抽選(DRAW)")  # UTC→日本時間
        self.assertEqual(items[1].detail, "")

    def test_bad_date_and_missing_products_do_not_break_titles(self):
        products = {"p1": {"commerceStartDate": "not-a-date", "skus": []}}
        items = parse_nike_launch(nike_page(self.THREADS, products), "https://www.nike.com/jp/launch", "c", "n")
        self.assertEqual(len(items), 2)
        self.assertEqual(items[0].detail, "")

    def test_state_may_be_plain_object(self):
        items = parse_nike_launch(nike_page(self.THREADS, self.PRODUCTS, double_encoded=False), "https://www.nike.com/jp/launch", "c", "n")
        self.assertEqual(len(items), 2)

    def test_falls_back_to_anchor_links(self):
        html = '<html><body><a href="/jp/launch/t/air-max-90-black">x</a><a href="/jp/launch/t/air-max-90-black">x</a></body></html>'
        with self.assertLogs("deal-watcher", level="WARNING"):
            items = parse_nike_launch(html, "https://www.nike.com/jp/launch", "c", "n")
        self.assertEqual([(i.title, i.url) for i in items], [("air max 90 black", "https://www.nike.com/jp/launch/t/air-max-90-black")])


class DiscordFormatTests(unittest.TestCase):
    def test_embed_has_required_fields_and_limits(self):
        item = Item("あ" * 500, "https://e.com/x", "お酒", "情報源", "配信元: 媒体")
        embed = build_embed(item, NOW)
        self.assertLessEqual(len(embed["title"]), 256)
        self.assertEqual(embed["url"], "https://e.com/x")
        self.assertIn("https://e.com/x", embed["description"])
        self.assertEqual({f["name"] for f in embed["fields"]}, {"カテゴリ", "情報源", "取得日時"})
        self.assertIn("2026-09-25 14:00 JST", [f["value"] for f in embed["fields"]])
        self.assertTrue(embed["timestamp"].startswith("2026-09-25T05:00:00"))  # UTC表記

    def test_batches_respect_count_and_size(self):
        pairs = [(Item(f"t{i}", f"https://e.com/{i}", "お酒", "s"), build_embed(Item(f"t{i}", f"https://e.com/{i}", "お酒", "s"), NOW)) for i in range(25)]
        batches = batch_embeds(pairs)
        self.assertEqual([len(b) for b in batches], [10, 10, 5])
        big = [(None, {"title": "a" * 256, "description": "b" * 2000, "fields": []}) for _ in range(10)]
        for batch in batch_embeds(big):
            self.assertLessEqual(sum(embed_size(e) for _, e in batch), main.EMBED_CHARS_PER_MESSAGE)

    def test_webhook_url_validation(self):
        self.assertTrue(main.WEBHOOK_URL_RE.match(DUMMY_WEBHOOK))
        for bad in ("https://evil.example/api/webhooks/1/x", "http://discord.com/api/webhooks/1/x", "", "https://discord.com/api/webhooks/abc/x"):
            self.assertFalse(main.WEBHOOK_URL_RE.match(bad), bad)

    def test_log_filter_masks_webhook_token(self):
        record = logging.LogRecord("x", logging.ERROR, "", 0, "失敗 %s", (DUMMY_WEBHOOK,), None)
        main.MaskWebhookFilter().filter(record)
        self.assertNotIn("DUMMY_token", record.getMessage())
        self.assertIn("/webhooks/000000000000000000/***", record.getMessage())


class DiscordNotifierTests(unittest.TestCase):
    def setUp(self):
        patcher = mock.patch.object(main.time, "sleep")
        self.sleep = patcher.start()
        self.addCleanup(patcher.stop)

    def test_success_204(self):
        with mock.patch.object(requests, "post", return_value=FakeResponse(status_code=204)) as post:
            DiscordNotifier(DUMMY_WEBHOOK).send({"content": "x"})
        post.assert_called_once()

    def test_rate_limit_then_success(self):
        replies = [FakeResponse(status_code=429, json_data={"retry_after": 0.5}), FakeResponse(status_code=204)]
        with mock.patch.object(requests, "post", side_effect=replies) as post:
            DiscordNotifier(DUMMY_WEBHOOK).send({"content": "x"})
        self.assertEqual(post.call_count, 2)
        self.sleep.assert_called_with(0.5)

    def test_client_error_is_not_retried(self):
        with mock.patch.object(requests, "post", return_value=FakeResponse(status_code=404, text='{"message": "Unknown Webhook"}')) as post:
            with self.assertRaises(DiscordError):
                DiscordNotifier(DUMMY_WEBHOOK).send({"content": "x"})
        self.assertEqual(post.call_count, 1)

    def test_connection_error_does_not_leak_webhook_url(self):
        boom = requests.ConnectionError(f"Max retries exceeded with url: {DUMMY_WEBHOOK}")
        with mock.patch.object(requests, "post", side_effect=boom):
            with self.assertRaises(DiscordError) as ctx:
                DiscordNotifier(DUMMY_WEBHOOK).send({"content": "x"})
        self.assertNotIn("DUMMY_token", str(ctx.exception))


class StubSource(Source):
    def __init__(self, items: list[Item], fail: bool = False):
        super().__init__(name="stub", category="お酒", url="https://stub.example/")
        self.items, self.fail = items, fail

    def fetch(self, http):
        if self.fail:
            raise ConnectionError("down")
        return list(self.items)


def make_args(history: Path, **overrides) -> argparse.Namespace:
    values = dict(dry_run=False, no_baseline=False, only=None, history=history, interval=0, verbose=False)
    values.update(overrides)
    return argparse.Namespace(**values)


class RunTests(unittest.TestCase):
    """run() 全体の流れ。Discordへの送信は requests.post をすり替えて確認する。"""

    def setUp(self):
        self.dir = tempfile.TemporaryDirectory()
        self.history = Path(self.dir.name) / "notified_history.json"
        env = mock.patch.dict(os.environ, {"DISCORD_WEBHOOK_URL": DUMMY_WEBHOOK})
        env.start()
        self.addCleanup(env.stop)
        sleep = mock.patch.object(main.time, "sleep")
        sleep.start()
        self.addCleanup(sleep.stop)
        self.addCleanup(self.dir.cleanup)
        self.a = Item("A 抽選のお知らせ", "https://e.com/a", "お酒", "stub")
        self.b = Item("B 抽選のお知らせ", "https://e.com/b", "お酒", "stub", "配信元: 媒体")

    def run_main(self, items, *, post_status=204, **overrides):
        replies = mock.Mock(return_value=FakeResponse(status_code=post_status, text="err"))
        with mock.patch.object(requests, "post", replies):
            code = main.run(make_args(self.history, **overrides), sources=[StubSource(items)])
        return code, replies

    def test_first_run_is_baseline_then_only_new_items_are_sent(self):
        code, post = self.run_main([self.a])
        self.assertEqual(code, 0)
        self.assertEqual(post.call_count, 1)  # 開始のお知らせだけ
        self.assertNotIn("embeds", post.call_args.kwargs["json"])
        self.assertTrue(self.history.exists())

        code, post = self.run_main([self.a])  # 変化なし → 何も送らない
        self.assertEqual((code, post.call_count), (0, 0))

        code, post = self.run_main([self.a, self.b])  # Bだけが新着
        self.assertEqual((code, post.call_count), (0, 1))
        payload = post.call_args.kwargs["json"]
        self.assertEqual([e["title"] for e in payload["embeds"]], [self.b.title])
        self.assertEqual(payload["allowed_mentions"], {"parse": []})

        code, post = self.run_main([self.a, self.b])  # 送信済みなので二重通知しない
        self.assertEqual(post.call_count, 0)

    def test_added_source_is_baselined_even_when_history_exists(self):
        self.run_main([self.a])  # 既存の情報源 "stub" で初回(既読登録)
        # 古い形式の履歴(sources キーなし)からでも、見たことのある情報源を復元できること
        data = json.loads(self.history.read_text(encoding="utf-8"))
        del data["sources"]
        self.history.write_text(json.dumps(data, ensure_ascii=False), encoding="utf-8")

        added = StubSource([Item("新ソースの古い記事 抽選", "https://n.com/old", "時計", "新しい情報源")])
        added.name = "新しい情報源"
        with mock.patch.object(requests, "post", return_value=FakeResponse(status_code=204)) as post:
            code = main.run(make_args(self.history), sources=[StubSource([self.a, self.b]), added])
        self.assertEqual((code, post.call_count), (0, 2))
        first, second = (c.kwargs["json"] for c in post.call_args_list)
        self.assertIn("情報源を1件追加しました", first["content"])  # 新ソース分は通知せず既読登録
        self.assertEqual([e["title"] for e in second["embeds"]], [self.b.title])  # 既存ソースの新着は通常どおり
        self.assertIn("新しい情報源", History(self.history).sources)

        new_item = Item("新ソースの新着 抽選", "https://n.com/new", "時計", "新しい情報源")
        added.items.append(new_item)
        with mock.patch.object(requests, "post", return_value=FakeResponse(status_code=204)) as post:
            main.run(make_args(self.history), sources=[StubSource([self.a, self.b]), added])
        self.assertEqual([e["title"] for e in post.call_args.kwargs["json"]["embeds"]], [new_item.title])

    def test_dry_run_sends_nothing_and_writes_nothing(self):
        code, post = self.run_main([self.a], dry_run=True, no_baseline=True)
        self.assertEqual((code, post.call_count), (0, 0))
        self.assertFalse(self.history.exists())

    def test_failed_baseline_send_leaves_no_history_so_next_run_retries(self):
        code, _ = self.run_main([self.a], post_status=404)
        self.assertEqual(code, 1)
        self.assertFalse(self.history.exists())

    def test_failed_send_keeps_item_unrecorded_for_retry(self):
        self.run_main([self.a])  # 初回(既読登録)
        code, _ = self.run_main([self.a, self.b], post_status=500)
        self.assertEqual(code, 1)
        self.assertFalse(History(self.history).seen(self.b))
        code, post = self.run_main([self.a, self.b])  # 復旧後に、取りこぼさず通知される
        self.assertEqual((code, post.call_count), (0, 1))

    def test_cap_defers_extra_items_to_next_run(self):
        self.run_main([self.a])
        many = [Item(f"品{i} 抽選", f"https://e.com/n{i}", "お酒", "stub") for i in range(main.MAX_NOTIFY_PER_RUN + 3)]
        _, post = self.run_main(many)
        sent = sum(len(c.kwargs["json"]["embeds"]) for c in post.call_args_list)
        self.assertEqual(sent, main.MAX_NOTIFY_PER_RUN)
        _, post = self.run_main(many)
        self.assertEqual(sum(len(c.kwargs["json"]["embeds"]) for c in post.call_args_list), 3)

    def test_same_title_from_two_urls_is_sent_once(self):
        self.run_main([self.a])
        dup = Item(self.b.title, "https://other.example/b", "お酒", "stub")
        _, post = self.run_main([self.b, dup])
        self.assertEqual(len(post.call_args.kwargs["json"]["embeds"]), 1)

    def test_all_sources_failing_returns_error(self):
        with mock.patch.object(requests, "post") as post:
            code = main.run(make_args(self.history), sources=[StubSource([], fail=True)])
        self.assertEqual((code, post.call_count), (1, 0))

    def test_alert_after_repeated_failures(self):
        self.run_main([self.a])
        h = History(self.history)
        h.health["stub"] = main.SOURCE_FAIL_ALERT_STREAK - 1
        h.save()
        good, bad = StubSource([self.a]), StubSource([], fail=True)
        bad.name = "壊れた情報源"
        h = History(self.history)
        h.health["壊れた情報源"] = main.SOURCE_FAIL_ALERT_STREAK - 1
        h.save()
        with mock.patch.object(requests, "post", return_value=FakeResponse(status_code=204)) as post:
            code = main.run(make_args(self.history), sources=[good, bad])
        self.assertEqual(code, 0)
        self.assertIn("壊れた情報源", post.call_args.kwargs["json"]["content"])

    def test_missing_webhook_is_config_error_unless_dry_run(self):
        with mock.patch.dict(os.environ, {"DISCORD_WEBHOOK_URL": ""}):
            self.assertEqual(main.run(make_args(self.history), sources=[StubSource([self.a])]), 2)
            self.assertEqual(main.run(make_args(self.history, dry_run=True), sources=[StubSource([self.a])]), 0)

    def test_corrupted_history_stops_run(self):
        self.history.write_text("not json", encoding="utf-8")
        code, post = self.run_main([self.a])
        self.assertEqual((code, post.call_count), (1, 0))


class SourcesConfigTests(unittest.TestCase):
    def test_every_source_is_well_formed(self):
        names = [s.name for s in main.SOURCES]
        self.assertEqual(len(names), len(set(names)))
        for s in main.SOURCES:
            self.assertTrue(s.url.startswith("https://"), s.name)
            self.assertIn(s.category, main.CATEGORY_COLORS)
        self.assertEqual(
            {s.category for s in main.SOURCES},
            {main.CATEGORY_CARD, main.CATEGORY_SNEAKER, main.CATEGORY_LIQUOR, main.CATEGORY_WATCH, main.CATEGORY_CAR},
        )

    def test_google_news_url_is_encoded(self):
        url = main.google_news_url("ポケカ 抽選")
        self.assertTrue(url.startswith("https://news.google.com/rss/search?q="))
        self.assertNotIn(" ", url)
        self.assertIn("when%3A7d", url)


if __name__ == "__main__":
    unittest.main()
