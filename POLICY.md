# Jharkhand District Notification Monitor — Technical Policy

## Scope
- Monitor configured Jharkhand NIC district websites, listing pages, bounded pagination/archive discovery and sitemaps.
- Scan every 20 minutes. Discovery is broad but bounded by `websites.json` budgets; it is not a guarantee that every page on every website is crawled.
- Process notices with a 10-day freshness priority. Explicit old publication dates/archive titles are suppressed; older items may still be stored for deduplication.

## Baseline and notification safety
- A site baseline is complete only after a successful scan with no partial scan errors.
- A failed or partial first scan remains pending and does not classify or notify its candidates. It must be retried.
- First baseline records are marked `baseline`, not sent. Once all configured sites have completed baseline, later genuinely new/meaningfully changed items can enter classification.
- Never delete the persistent `monitor-state` branch merely to reset the bot. Back up state first and use a deliberate migration/reset procedure.

## Meaningful changes and duplicate detection
- Ignore cosmetic HTML changes and PDF metadata-only changes where the visual/content fingerprint is unchanged.
- Compare high-value fields where present: application deadline, eligibility/qualification, age limit, vacancy count, corrigendum/amendment number, exam date and result date.
- Use canonical URL identity, normalized query parameters, title similarity and PDF content fingerprints. Fuzzy matching is a safety net, not proof that two notices are identical.
- Archive/navigation pages such as `/past-notices`, `/whats-new`, `/notice_category`, `/document-category` and `/archive` are not treated as direct notice PDFs.

## Review queue
- Unresolved classification and explicit ambiguity must be persisted in `review_queue` with URL, site, reason, extracted fields/dates, model output, diff summary, status, retry count and timestamps.
- Review items are not silently converted to sent notifications.

## Retries and delivery
- Persist pending classification records and requeue them even if the source listing no longer shows them.
- Retry transient Telegram failures with backoff. A successful send whose response is lost can still produce a duplicate on retry; Telegram delivery is not exactly-once.
- Persist notification attempt counters and make failures visible in logs/metrics.

## State and workflow safety
- Write state to `state.json.new`, flush it, validate JSON/size, then atomically replace `state.json`.
- GitHub Actions runs are serialized by a workflow concurrency group. State persistence validates JSON and size before updating the single-commit `monitor-state` branch, and retries push failures.
- A state-save failure fails the job; do not replace persistent state with malformed or oversized data.
- Retention targets: sent 90 days, ignored 30 days, baseline 60 days. Active pending/ready items are retained for retry; review queue is bounded and open items are retained.

## Metrics and operations
- Track site successes/failures, parsing errors, sent/failed notifications, duplicate rejects, pending counts, open review items and state-save errors.
- Check GitHub Actions logs and Telegram output after deploying. Tests passing does not replace a live run.
- Production-ready status requires all automated tests passing and at least one verified live GitHub Actions run.

## Known limitations
- No system can guarantee that all remote site content is discoverable when a site blocks requests, changes markup, or fails during scanning.
- Telegram send is not idempotent; exactly-once delivery cannot be guaranteed.
- Semantic field extraction is heuristic. Important or ambiguous updates should be reviewed rather than blindly trusted.
