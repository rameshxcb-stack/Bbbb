# Jharkhand District Notification Monitor

Python + GitHub Actions monitor for configured Jharkhand NIC district websites. It discovers candidate notices from the configured landing pages, bounded linked pages, pagination/archive routes and sitemaps; extracts PDF text with pdfplumber/PyMuPDF/RapidOCR where available; optionally uses Gemini for classification; and sends relevant updates to Telegram.

## Files
- `monitor.py` — scanner, classification, PDF handling, retries, deduplication, review queue and state management.
- `websites.json` — enabled district websites, scan budgets, keywords and retention settings.
- `state.json` — initial state shape for first deployment. In normal operation, `.github/workflows/monitor.yml` loads the persistent state from `monitor-state`.
- `.github/workflows/monitor.yml` — 20-minute scheduled workflow, tests, run and guarded state persistence.
- `tests/` — offline regression tests.
- `POLICY.md` — frozen technical specification and known limitations.

## Required GitHub Actions secrets
- `TELEGRAM_BOT_TOKEN`
- `TELEGRAM_CHAT_ID`
- `GEMINI_API_KEY`

## Deployment
1. Commit the whole project, including `.github/workflows/monitor.yml` and `POLICY.md`.
2. Add the three repository secrets above.
3. Enable GitHub Actions and run `Jharkhand District Notification Monitor` manually once.
4. Check the first run carefully. Sites are baselined without bulk notification only after their scan succeeds without partial errors. Incomplete sites remain pending for another run.
5. Confirm the `monitor-state` branch has a valid `state.json` after the run.
6. Review Telegram messages and Actions logs before calling it production-ready.

## State safety
- Do not delete `monitor-state` to fix a notification issue. Back it up before any intentional reset.
- State writes use a validated temporary file and atomic replacement. Workflow persistence rejects invalid JSON and state over 3.1 MB.
- Workflow concurrency serializes scheduled/manual runs. Transient Git push errors are retried.

## Test locally
```bash
python -m pip install -r requirements.txt
python -m unittest discover -s tests -v
python -m py_compile monitor.py
