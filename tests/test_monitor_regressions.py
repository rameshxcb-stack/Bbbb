import importlib.util
import sys
import unittest
from datetime import datetime, timedelta, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("monitor_under_test", ROOT / "monitor.py")
monitor = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = monitor
SPEC.loader.exec_module(monitor)


class MonitorRegressionTests(unittest.TestCase):
    def test_tracking_variants_share_identity_but_keep_fetch_url_intact(self):
        base = "https://EXAMPLE.com/notice?id=42"
        tracked = "https://example.com/notice?utm_source=wa&id=42&lang=hi"
        self.assertEqual(monitor.canonical_identity_url(base), monitor.canonical_identity_url(tracked))
        self.assertIn("lang=hi", monitor.canonical_url(tracked))

    def test_query_order_is_normalized_for_identity(self):
        a = "https://example.com/file?id=2&name=notice.pdf"
        b = "https://example.com/file?name=notice.pdf&id=2"
        self.assertEqual(monitor.canonical_identity_url(a), monitor.canonical_identity_url(b))

    def test_tracking_variants_produce_same_item_id(self):
        a = "https://example.com/notice?id=42&utm_source=whatsapp"
        b = "https://example.com/notice?lang=hi&id=42"
        self.assertEqual(monitor.item_id("chatra", a, "Recruitment notice 2026", "same context"),
                         monitor.item_id("chatra", b, "Recruitment notice 2026", "same context"))

    def test_old_year_only_notice_is_marked_stale(self):
        self.assertTrue(monitor._is_stale_notice(
            "Recruitment notice 2025", "",
            "https://chatra.nic.in/notice/recruitment-2025.pdf"
        ))

    def test_old_batch_with_current_year_revision_is_not_auto_rejected(self):
        self.assertFalse(monitor._is_stale_notice(
            "2023 batch corrigendum revised 2026", "",
            "https://chatra.nic.in/notice/2023-revised-2026.pdf"
        ))

    def test_old_archive_title_not_overridden_by_current_year_footer_or_upload_date(self):
        self.assertTrue(monitor._is_stale_notice(
            "Name Of Candidates 2019-2020",
            "DEO Portal | Last Updated: 2026 | Government of Jharkhand",
            "https://bokaro.nic.in/name-of-candidates/",
            upload_date=datetime.now(timezone.utc) - timedelta(days=1)
        ))

    def test_old_archive_title_with_explicit_current_year_revision_is_allowed(self):
        self.assertFalse(monitor._is_stale_notice(
            "Name Of Candidates 2019-2020",
            "Revised in 2026; current corrigendum published",
            "https://bokaro.nic.in/name-of-candidates/"
        ))

    def test_explicit_old_publication_date_marks_notice_stale(self):
        self.assertTrue(monitor._is_stale_notice(
            "Recruitment notice", "Published on 01/01/2020",
            "https://chatra.nic.in/notice/example.html"
        ))

    def test_old_publication_date_not_hidden_by_recent_application_deadline(self):
        self.assertTrue(monitor._is_stale_notice(
            "Recruitment notice", "Published on 01/01/2020; Last date 30/12/2026",
            "https://chatra.nic.in/notice/example.html"
        ))

    def test_recent_listing_upload_date_keeps_old_batch_eligible(self):
        self.assertFalse(monitor._is_stale_notice(
            "2025 batch updated notice", "",
            "https://chatra.nic.in/notice/example.html",
            upload_date=datetime.now(timezone.utc) - timedelta(days=1)
        ))

    def test_pdf_stale_gate_ignores_unlabelled_exam_dates(self):
        self.assertEqual(monitor._extract_explicit_issue_dates("Exam will be held on 01/01/2020"), [])
        self.assertEqual(len(monitor._extract_explicit_issue_dates("Published on 01/01/2020")), 1)

    def test_cosmetic_metadata_change_is_ignored(self):
        self.assertFalse(monitor._meaningful_metadata_change(
            "Notice 2025.", "Notice 2025", "same context", "same context"
        ))

    def test_substantive_title_change_is_detected(self):
        self.assertTrue(monitor._meaningful_metadata_change(
            "Recruitment notice for laboratory assistants 2026",
            "Corrigendum recruitment notice for laboratory assistants 2026",
            "same context", "same context"
        ))

    def test_html_and_pdf_with_same_long_title_can_match_across_paths(self):
        rows = [("item-1", "Important notice for recruitment of teachers in Chatra district 2026",
                 "https://chatra.nic.in/notice/important-notice.html")]
        self.assertEqual(monitor.find_fuzzy_match(
            rows, "Important notice for recruitment of teachers in Chatra district 2026",
            "https://chatra.nic.in/downloads/important-notice.pdf"
        ), "item-1")

    def test_short_unrelated_cross_path_titles_are_not_fuzzy_merged(self):
        rows = [("item-1", "Teacher Recruitment 2026", "https://chatra.nic.in/notice/a.html")]
        self.assertIsNone(monitor.find_fuzzy_match(
            rows, "Teacher Recruitment 2026", "https://chatra.nic.in/files/b.pdf"
        ))

    def test_persisted_pending_item_is_requeued_when_not_in_current_candidates(self):
        state = {
            "items": {"pending-1": {"status": "pending", "site_id": "chatra", "attempts": 1}},
            "sites": {"chatra": {"baseline_complete": True}},
        }
        result = monitor.enqueue_persisted_pending(state, [], 72, {"chatra"})
        self.assertEqual([iid for iid, _ in result], ["pending-1"])

    def test_stale_persisted_pending_and_ready_items_are_suppressed(self):
        state = {"items": {
            "old-pending": {"status": "pending", "site_id": "chatra", "attempts": 1,
                            "title": "Recruitment notice 2025", "url": "https://chatra.nic.in/notice/2025.pdf"},
            "old-ready": {"status": "ready", "site_id": "chatra", "attempts": 1,
                          "title": "Result notice 2024", "url": "https://chatra.nic.in/notice/2024.pdf"},
        }}
        self.assertEqual(monitor.suppress_stale_pending_and_ready(state), 2)
        self.assertEqual(state["items"]["old-pending"]["status"], "baseline")
        self.assertEqual(state["items"]["old-ready"]["status"], "baseline")

    def test_pending_priority_ages_old_items_to_reduce_starvation(self):
        now = datetime.now(timezone.utc)
        old = {"title": "notice", "url": "https://example.com/old", "context": "",
               "first_seen": (now - timedelta(days=1)).isoformat()}
        aged_old = {**old, "first_seen": (now - timedelta(days=30)).isoformat()}
        fresh_high = {"title": "recruitment vacancy result admit card scholarship", "url": "https://example.com/new",
                      "context": "notification tender", "first_seen": now.isoformat()}
        keywords = ["recruitment", "vacancy", "result", "admit card", "scholarship", "notification", "tender"]
        old_priority = monitor.pending_priority(old, keywords, now)
        aged_priority = monitor.pending_priority(aged_old, keywords, now)
        fresh_priority = monitor.pending_priority(fresh_high, keywords, now)
        self.assertGreater(fresh_priority[0], old_priority[0])
        self.assertGreater(aged_priority[0], fresh_priority[0])

    def test_pending_queue_deduplicates_ids(self):
        record = {"status": "pending", "site_id": "chatra", "attempts": 1}
        state = {"items": {"pending-1": record}, "sites": {"chatra": {"baseline_complete": True}}}
        result = monitor.enqueue_persisted_pending(state, [("pending-1", record)], 72, {"chatra"})
        self.assertEqual(len(result), 1)

    def test_telegram_backoff_is_respected(self):
        now = datetime.now(timezone.utc)
        record = {
            "telegram_attempts": 2,
            "telegram_first_failed_at": now.isoformat(),
            "telegram_next_attempt_at": (now + timedelta(minutes=40)).isoformat(),
        }
        self.assertFalse(monitor._telegram_retry_due(record, now))
        self.assertTrue(monitor._telegram_retry_due(record, now + timedelta(minutes=41)))

    def test_telegram_retry_window_expiry_is_respected(self):
        now = datetime.now(timezone.utc)
        record = {"telegram_attempts": 3, "telegram_first_failed_at": (now - timedelta(hours=74)).isoformat()}
        self.assertFalse(monitor._telegram_retry_due(record, now))

    def test_expired_telegram_delivery_becomes_visible_terminal_error(self):
        now = datetime.now(timezone.utc)
        state = {"items": {"item-1": {
            "status": "ready", "telegram_attempts": 4,
            "telegram_first_failed_at": (now - timedelta(hours=74)).isoformat(),
            "first_seen": now.isoformat(), "url": "https://example.com/notice",
        }}}
        monitor.prune_state(state, retention_days=90, max_items=3000, max_pending_attempts=72, max_bytes=3000000)
        self.assertEqual(state["items"]["item-1"]["status"], "permanent_error")
        self.assertIn("retry window", state["items"]["item-1"]["last_error"].lower())


    @unittest.skipIf(monitor.fitz is None, "PyMuPDF unavailable")
    def test_pdf_etag_change_with_same_visual_content_is_not_a_change(self):
        import tempfile
        from pathlib import Path

        doc = monitor.fitz.open()
        page = doc.new_page()
        page.insert_text((72, 72), "Jharkhand Recruitment Notice 2026")
        old_pdf = doc.tobytes()
        doc.set_metadata({"title": "regenerated metadata", "producer": "changed producer"})
        new_pdf = doc.tobytes()
        doc.close()
        fingerprint = monitor._pdf_content_fingerprint(old_pdf)

        class Response:
            status_code = 200
            headers = {}
            def __enter__(self): return self
            def __exit__(self, *args): return False
            def iter_content(self, chunk_size): yield new_pdf

        class Session:
            def head(self, *args, **kwargs):
                class Head:
                    headers = {"etag": '"new-etag"', "last-modified": "Tue, 08 Oct 2026 10:00:00 GMT"}
                return Head()
            def get(self, *args, **kwargs): return Response()

        record = {"is_pdf": True, "etag": '"old-etag"', "last_modified": "Mon, 07 Oct 2026 10:00:00 GMT",
                  "pdf_hash": fingerprint, "pdf_hash_kind": fingerprint.split(":", 1)[0]}
        changed, etag, last_modified = monitor._check_url_changed(Session(), "https://example.com/a.pdf", record)
        self.assertFalse(changed)
        self.assertEqual(etag, '"new-etag"')
        self.assertEqual(record["pdf_hash"], fingerprint)

    @unittest.skipIf(monitor.fitz is None, "PyMuPDF unavailable")
    def test_pdf_content_change_is_detected_when_etag_and_last_modified_stay_same(self):
        def make_pdf(text):
            doc = monitor.fitz.open()
            page = doc.new_page()
            page.insert_text((72, 72), text)
            data = doc.tobytes()
            doc.close()
            return data

        old_pdf = make_pdf("Old Jharkhand recruitment notice 2026")
        new_pdf = make_pdf("Revised Jharkhand recruitment notice 2026")
        old_hash = monitor._pdf_content_fingerprint(old_pdf)

        class Response:
            status_code = 200
            headers = {}
            def __enter__(self): return self
            def __exit__(self, *args): return False
            def iter_content(self, chunk_size): yield new_pdf

        class Session:
            def head(self, *args, **kwargs):
                class Head:
                    headers = {"etag": '"stable-etag"',
                               "last-modified": "Tue, 08 Oct 2026 10:00:00 GMT"}
                return Head()
            def get(self, *args, **kwargs): return Response()

        record = {"is_pdf": True, "etag": '"stable-etag"',
                  "last_modified": "Tue, 08 Oct 2026 10:00:00 GMT",
                  "pdf_hash": old_hash,
                  "pdf_hash_kind": old_hash.split(":", 1)[0]}
        changed, etag, last_modified = monitor._check_url_changed(
            Session(), "https://example.com/a.pdf", record
        )
        self.assertTrue(changed)
        self.assertEqual(etag, '"stable-etag"')
        self.assertNotEqual(record["pdf_hash"], old_hash)

    @unittest.skipIf(monitor.fitz is None, "PyMuPDF unavailable")
    def test_pdf_unchanged_content_with_unchanged_headers_is_not_a_change(self):
        doc = monitor.fitz.open()
        page = doc.new_page()
        page.insert_text((72, 72), "Same Jharkhand recruitment notice 2026")
        content = doc.tobytes()
        doc.close()
        old_hash = monitor._pdf_content_fingerprint(content)

        class Response:
            status_code = 200
            headers = {}
            def __enter__(self): return self
            def __exit__(self, *args): return False
            def iter_content(self, chunk_size): yield content

        class Session:
            def head(self, *args, **kwargs):
                class Head:
                    headers = {"etag": '"stable-etag"',
                               "last-modified": "Tue, 08 Oct 2026 10:00:00 GMT"}
                return Head()
            def get(self, *args, **kwargs): return Response()

        record = {"is_pdf": True, "etag": '"stable-etag"',
                  "last_modified": "Tue, 08 Oct 2026 10:00:00 GMT",
                  "pdf_hash": old_hash,
                  "pdf_hash_kind": old_hash.split(":", 1)[0]}
        changed, _, _ = monitor._check_url_changed(
            Session(), "https://example.com/a.pdf", record
        )
        self.assertFalse(changed)
        self.assertEqual(record["pdf_hash"], old_hash)

    def test_atomic_save_rejects_oversized_state_without_replacing_old_file(self):
        import tempfile
        from pathlib import Path
        with tempfile.TemporaryDirectory() as tmpdir:
            path = Path(tmpdir) / "state.json"
            path.write_text('{"known_good": true}\n', encoding="utf-8")
            old = path.read_bytes()
            with self.assertRaises(RuntimeError):
                monitor.atomic_save_json(path, {"payload": "x" * 1000}, max_bytes=20)
            self.assertEqual(path.read_bytes(), old)
            self.assertFalse(path.with_suffix(".json.tmp").exists())

    @unittest.skipIf(monitor.fitz is None, "PyMuPDF unavailable")
    def test_pdf_metadata_only_change_does_not_change_visual_fingerprint(self):
        def make_pdf(title, author):
            doc = monitor.fitz.open()
            page = doc.new_page()
            page.insert_text((72, 72), "Jharkhand Recruitment Notice 2026")
            doc.set_metadata({"title": title, "author": author, "producer": "Test"})
            data = doc.tobytes()
            doc.close()
            return data
        a = make_pdf("metadata A", "author A")
        b = make_pdf("metadata B", "author B")
        self.assertEqual(monitor._pdf_content_fingerprint(a), monitor._pdf_content_fingerprint(b))


if __name__ == "__main__":
    unittest.main(verbosity=2)


class FinalSpecificationTests(unittest.TestCase):
    def test_empty_state_starts_uninitialized_and_baseline_is_not_complete(self):
        state = monitor.default_state()
        self.assertFalse(state["initialized"])
        self.assertEqual(state["items"], {})
        self.assertFalse(monitor.baseline_can_complete(True, ["pagination page failed"]))
        self.assertFalse(monitor.baseline_can_complete(False, []))
        self.assertTrue(monitor.baseline_can_complete(True, []))

    def test_12_day_old_notice_is_stale_under_10_day_policy(self):
        old_dt = datetime.now(timezone.utc) - timedelta(days=12)
        self.assertTrue(monitor._is_stale_notice(
            "Recruitment Notice", "", "https://example.nic.in/notice/recruitment", upload_date=old_dt
        ))

    def test_pdf_hash_fingerprint_is_content_not_raw_metadata(self):
        self.assertTrue(hasattr(monitor, "_pdf_content_fingerprint"))
        self.assertTrue(callable(monitor._pdf_content_fingerprint))

    def test_corrigendum_and_deadline_are_meaningful_changes(self):
        old = "Last date to apply: 15 October 2026\nCorrigendum No. 1"
        new = "Last date to apply: 25 October 2026\nCorrigendum No. 2"
        details = monitor.meaningful_change_details(old, new)
        self.assertTrue(details)
        self.assertTrue(monitor._meaningful_metadata_change("Recruitment", "Recruitment", old, new))

    def test_failed_telegram_attempt_is_scheduled_for_retry(self):
        record = {"telegram_attempts": 1}
        monitor._schedule_telegram_retry(record)
        self.assertTrue(record.get("telegram_next_attempt_at"))
        self.assertTrue(monitor._telegram_retry_due({"telegram_next_attempt_at": "2000-01-01T00:00:00+00:00"}))

    def test_review_queue_persists_ambiguous_record(self):
        state = monitor.default_state()
        record = {"site_id": "chatra", "site_name": "Chatra", "url": "https://chatra.nic.in/x",
                  "title": "Notice", "context": "Dates conflict: 01/02/2026 and 02/01/2026"}
        monitor.add_review_item(state, record, "ambiguous_date")
        self.assertEqual(len(state["review_queue"]), 1)
        entry = next(iter(state["review_queue"].values()))
        self.assertEqual(entry["status"], "open")
        self.assertEqual(entry["reason"], "ambiguous_date")

    # ------------------------------------------------------------------
    # UPDATED: workflow now uses monitor-state branch + git worktree
    # instead of state.json.new + retry loop.
    # ------------------------------------------------------------------
    def test_workflow_has_serialized_run_and_state_branch(self):
        workflow = (ROOT / ".github/workflows/monitor.yml").read_text(encoding="utf-8")
        self.assertIn("concurrency:", workflow)
        self.assertIn("git push", workflow)
        self.assertIn("monitor-state", workflow)
        self.assertIn("worktree", workflow)
        self.assertIn("if: always()", workflow)
