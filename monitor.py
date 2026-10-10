# -*- coding: utf-8 -*-
import base64
import hashlib
import html
import io
import json
import os
import re
import sys
import time
from collections import Counter
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime, timezone, timedelta
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple
from urllib.parse import urljoin, urlparse, urlunparse, unquote, parse_qsl, urlencode
from urllib.robotparser import RobotFileParser

import pdfplumber
import requests
from bs4 import BeautifulSoup
from rapidfuzz import fuzz
from rapidfuzz.distance import Levenshtein
from requests.adapters import HTTPAdapter
from urllib3.util.retry import Retry

try:
    import fitz
except ImportError:
    fitz = None

try:
    from rapidocr_onnxruntime import RapidOCR
    _RAPIDOCR_AVAILABLE = True
except ImportError:
    RapidOCR = None
    _RAPIDOCR_AVAILABLE = False


BASE = Path(__file__).resolve().parent
CONFIG_FILE = BASE / "websites.json"
STATE_FILE = BASE / "state.json"

FALLBACK_MODELS = [
    "gemini-3.5-flash-lite",
    "gemini-3.1-flash-lite",
]

FUZZY_DUPLICATE_THRESHOLD = 94
FUZZY_CROSS_PATH_THRESHOLD = 96
TELEGRAM_MAX_ATTEMPTS = 100
TELEGRAM_RETRY_WINDOW_HOURS = 72
TELEGRAM_RETRY_BASE_MINUTES = 20
TELEGRAM_RETRY_MAX_MINUTES = 360

MAX_PDF_SEND_BYTES = 45 * 1024 * 1024
MAX_GEMINI_PDF_BYTES = 18 * 1024 * 1024
MAX_PDF_PAGES = int(os.getenv("MAX_PDF_PAGES", "8"))
MAX_PDF_TEXT_CHARS = 4000
MAX_PDF_ATTEMPTS = 3
TELEGRAM_SAFE_LIMIT = 4000
TELEGRAM_CAPTION_LIMIT = 1024

_RUNTIME_PDF_CACHE_MAX_ITEMS = 50

GEMINI_MAX_OUTPUT_TOKENS = int(os.getenv("GEMINI_MAX_OUTPUT_TOKENS", "16384"))

OCR_ENABLED = os.getenv("OCR_ENABLED", "true").strip().lower() == "true"
OCR_DPI = int(os.getenv("OCR_DPI", "150"))
OCR_MIN_TEXT_CHARS = int(os.getenv("OCR_MIN_TEXT_CHARS", "200"))
OCR_MAX_WORKERS = int(os.getenv("OCR_MAX_WORKERS", "2"))
_OCR_MAX_PAGES = int(os.getenv("OCR_MAX_PAGES", "4"))

GEMINI_PDF_OCR_ENABLED = os.getenv("GEMINI_PDF_OCR_ENABLED", "true").strip().lower() == "true"
SEND_PDF_ENABLED = os.getenv("SEND_PDF_ENABLED", "true").strip().lower() == "true"

NOTIFY_LANGUAGE = os.getenv("NOTIFY_LANGUAGE", "both").strip().lower()
if NOTIFY_LANGUAGE not in {"both", "hi", "en"}:
    NOTIFY_LANGUAGE = "both"

STALE_NOTICE_DAYS = int(os.getenv("STALE_NOTICE_DAYS", "10"))
OLD_YEAR_HINT_YEARS_BACK = int(os.getenv("OLD_YEAR_HINT_YEARS_BACK", "2"))
ETAG_CHECK_MAX_AGE_DAYS = int(os.getenv("ETAG_CHECK_MAX_AGE_DAYS", "14"))

USER_AGENT = os.getenv(
    "MONITOR_USER_AGENT",
    "Mozilla/5.0 (compatible; JharkhandNoticeMonitor/9.3)"
)

STRONG_KEYWORDS = [
    "recruitment", "vacancy", "post", "job", "result",
    "admit card", "answer key", "merit", "selection",
    "scholarship", "admission", "counselling",
    "notification", "notice", "tender", "appointment",
    "भर्ती", "परिणाम", "नियुक्ति", "प्रवेश", "छात्रवृत्ति",
    "सूचना", "नोटिस", "निविदा"
]

_RUNTIME_PDF_CACHE: Dict[str, bytes] = {}
_GEMINI_API_KEY = ""
_GEMINI_KEYS_POOL: List[str] = []
_GEMINI_KEY_INDEX: int = 0
_GEMINI_DEAD_KEYS: set = set()
_GEMINI_KEY_LOCK = __import__("threading").Lock()

_MODELS_DISCOVERED: bool = False
_DYNAMIC_MODELS: List[str] = []
_DEAD_MODELS: set = set()
_GEMINI_QUOTA_EXHAUSTED: bool = False

_RAPIDOCR_INSTANCE = None
_ROBOTS_CACHE = {}


def _get_rapidocr():
    global _RAPIDOCR_INSTANCE
    if _RAPIDOCR_INSTANCE is None and _RAPIDOCR_AVAILABLE:
        try:
            _RAPIDOCR_INSTANCE = RapidOCR()
        except Exception as exc:
            print(f"[WARN] RapidOCR init failed: {exc}", file=sys.stderr)
            return None
    return _RAPIDOCR_INSTANCE


def _cache_put(url, content):
    if url in _RUNTIME_PDF_CACHE:
        return
    if len(_RUNTIME_PDF_CACHE) >= _RUNTIME_PDF_CACHE_MAX_ITEMS:
        try:
            first_key = next(iter(_RUNTIME_PDF_CACHE))
            del _RUNTIME_PDF_CACHE[first_key]
        except (StopIteration, KeyError):
            pass
    _RUNTIME_PDF_CACHE[url] = content


def _load_gemini_keys():
    keys = []
    seen = set()

    def add(raw):
        key = (raw or "").strip()
        if key and key not in seen:
            seen.add(key)
            keys.append(key)

    for part in os.getenv("GEMINI_API_KEYS", "").split(","):
        add(part)
    for i in range(1, 11):
        add(os.getenv(f"GEMINI_API_KEY_{i}", ""))
    add(os.getenv("GEMINI_API_KEY", ""))
    return keys


def _get_next_gemini_key():
    global _GEMINI_KEY_INDEX
    with _GEMINI_KEY_LOCK:
        total = len(_GEMINI_KEYS_POOL)
        if not total:
            return None
        for _ in range(total):
            idx = _GEMINI_KEY_INDEX % total
            _GEMINI_KEY_INDEX = (idx + 1) % total
            key = _GEMINI_KEYS_POOL[idx]
            if key not in _GEMINI_DEAD_KEYS:
                return key
    return None


def _has_live_gemini_keys():
    with _GEMINI_KEY_LOCK:
        return any(key not in _GEMINI_DEAD_KEYS for key in _GEMINI_KEYS_POOL)


def _mark_gemini_key_dead(key, reason="quota exhausted"):
    if not key:
        return
    with _GEMINI_KEY_LOCK:
        if key in _GEMINI_DEAD_KEYS:
            return
        _GEMINI_DEAD_KEYS.add(key)
        remaining = max(0, len(_GEMINI_KEYS_POOL) - len(_GEMINI_DEAD_KEYS))
    try:
        index = _GEMINI_KEYS_POOL.index(key) + 1
    except ValueError:
        index = 0
    print(f"[GEMINI] Key #{index} skipped for this run ({reason}); {remaining} key(s) remain.", file=sys.stderr)


def _gemini_post_with_rotation(endpoint, payload, timeout):
    if not _GEMINI_KEYS_POOL:
        return None, None, "no_keys"
    attempted = set()
    last_reason = "all_keys_failed"
    for _ in range(len(_GEMINI_KEYS_POOL)):
        key = _get_next_gemini_key()
        if key is None:
            return None, None, "all_keys_quota_exhausted"
        if key in attempted:
            continue
        attempted.add(key)
        headers = {"x-goog-api-key": key, "Content-Type": "application/json"}
        try:
            response = requests.post(endpoint, headers=headers, json=payload, timeout=timeout)
        except requests.RequestException as exc:
            last_reason = "network_error"
            print(f"[WARN] Gemini network error on key #{_GEMINI_KEYS_POOL.index(key)+1}: {type(exc).__name__}", file=sys.stderr)
            continue
        if response.status_code == 429:
            try:
                err = response.json().get("error", {})
                msg = str(err.get("message", "")).lower()
                status = str(err.get("status", "")).upper()
            except Exception:
                msg, status = response.text.lower(), ""
            quota = status == "RESOURCE_EXHAUSTED" or any(term in msg for term in ("quota", "daily limit", "per day", "limit: 0"))
            if quota:
                _mark_gemini_key_dead(key, "quota exhausted")
                last_reason = "quota_exhausted"
                continue
            last_reason = "rate_limited"
            print(f"[WARN] Gemini key #{_GEMINI_KEYS_POOL.index(key)+1} rate-limited; trying another key.", file=sys.stderr)
            continue
        if response.status_code in (401, 403):
            _mark_gemini_key_dead(key, f"HTTP {response.status_code} authentication/permission failure")
            last_reason = "key_rejected"
            continue
        return response, key, None
    return None, None, last_reason


def _discover_models():
    global _MODELS_DISCOVERED, _DYNAMIC_MODELS

    if _MODELS_DISCOVERED:
        return

    print("[INFO] Discovering available Gemini models...", file=sys.stderr)

    try:
        data = None
        for _ in range(max(1, len(_GEMINI_KEYS_POOL))):
            key = _get_next_gemini_key()
            if key is None:
                break
            try:
                response = requests.get(
                    "https://generativelanguage.googleapis.com/v1beta/models",
                    headers={"x-goog-api-key": key}, timeout=15,
                )
                if response.status_code == 429:
                    try:
                        err = response.json().get("error", {})
                        msg = str(err.get("message", "")).lower()
                        status = str(err.get("status", "")).upper()
                    except Exception:
                        msg, status = response.text.lower(), ""
                    if status == "RESOURCE_EXHAUSTED" or any(t in msg for t in ("quota", "daily limit", "per day", "limit: 0")):
                        _mark_gemini_key_dead(key, "model-discovery quota exhausted")
                    else:
                        print(f"[WARN] Model discovery rate-limited for key #{_GEMINI_KEYS_POOL.index(key)+1}", file=sys.stderr)
                    continue
                if response.status_code in (401, 403):
                    _mark_gemini_key_dead(key, f"model-discovery HTTP {response.status_code}")
                    continue
                response.raise_for_status()
                data = response.json()
                break
            except Exception as exc:
                print(f"[WARN] Model discovery failed for key #{_GEMINI_KEYS_POOL.index(key)+1}: {type(exc).__name__}", file=sys.stderr)
        if data is None:
            raise RuntimeError("No configured Gemini key succeeded during model discovery")

        valid_models = []
        for model in data.get("models", []):
            methods = model.get("supportedGenerationMethods", [])
            if "generateContent" not in methods:
                continue
            model_id = model["name"].replace("models/", "")
            if any(skip in model_id.lower() for skip in ("embedding", "aqa", "imagen", "veo")):
                continue
            valid_models.append(model_id)

        def _priority(mid):
            m = mid.lower()
            if "flash-lite" in m:
                return 0
            if "flash" in m:
                return 1
            if "pro" in m:
                return 2
            return 3

        _DYNAMIC_MODELS = sorted(valid_models, key=lambda m: (_priority(m), m))

        if _DYNAMIC_MODELS:
            print(
                f"[INFO] Discovered {len(_DYNAMIC_MODELS)} models. "
                f"Top 3: {_DYNAMIC_MODELS[:3]}",
                file=sys.stderr,
            )
        else:
            print("[WARN] No models found. Using hardcoded fallback.", file=sys.stderr)
            _DYNAMIC_MODELS = list(FALLBACK_MODELS)

    except Exception as exc:
        print(f"[WARN] Model discovery failed: {exc}. Using fallback.", file=sys.stderr)
        _DYNAMIC_MODELS = list(FALLBACK_MODELS)

    _MODELS_DISCOVERED = True


def _pdf_content_fingerprint(content):
    if not content:
        return ""
    if fitz is not None:
        try:
            digest = hashlib.sha256()
            with fitz.open(stream=content, filetype="pdf") as doc:
                for page in doc[:MAX_PDF_PAGES]:
                    pix = page.get_pixmap(
                        matrix=fitz.Matrix(0.75, 0.75),
                        colorspace=fitz.csGRAY,
                        alpha=False,
                    )
                    digest.update(f"{pix.width}x{pix.height}:".encode("ascii"))
                    digest.update(pix.samples)
            return "visual-v1:" + digest.hexdigest()
        except Exception as exc:
            print(f"[WARN] PDF visual fingerprint failed: {exc}", file=sys.stderr)
    try:
        text = _extract_pdf_text_plumber(content)
        normalized = re.sub(r"\s+", " ", text or "").strip().casefold()
        if len(normalized) >= 30:
            return "text-v1:" + hashlib.sha256(normalized.encode("utf-8")).hexdigest()
    except Exception as exc:
        print(f"[WARN] PDF text fingerprint failed: {exc}", file=sys.stderr)
    return "bytes-v1:" + hashlib.sha256(content).hexdigest()


def _parse_utc_timestamp(value):
    if not value:
        return None
    try:
        dt = datetime.fromisoformat(str(value).replace("Z", "+00:00"))
        if dt.tzinfo is None:
            dt = dt.replace(tzinfo=timezone.utc)
        return dt.astimezone(timezone.utc)
    except (TypeError, ValueError, OverflowError):
        return None


def _telegram_retry_due(record, now=None):
    now = now or datetime.now(timezone.utc)
    first_failed = _parse_utc_timestamp(record.get("telegram_first_failed_at"))
    if first_failed and (now - first_failed).total_seconds() > TELEGRAM_RETRY_WINDOW_HOURS * 3600:
        return False
    next_attempt = _parse_utc_timestamp(record.get("telegram_next_attempt_at"))
    return next_attempt is None or next_attempt <= now


def _schedule_telegram_retry(record, now=None):
    now = now or datetime.now(timezone.utc)
    if not record.get("telegram_first_failed_at"):
        record["telegram_first_failed_at"] = now.isoformat()
    attempts = max(1, int(record.get("telegram_attempts", 1) or 1))
    delay_minutes = min(
        TELEGRAM_RETRY_BASE_MINUTES * (2 ** min(attempts - 1, 8)),
        TELEGRAM_RETRY_MAX_MINUTES,
    )
    record["telegram_next_attempt_at"] = (now + timedelta(minutes=delay_minutes)).isoformat()


def _meaningful_metadata_change(old_title, new_title, old_context, new_context):
    details = meaningful_change_details("\n".join([old_title or "", old_context or ""]),
                                        "\n".join([new_title or "", new_context or ""]))
    if details:
        return True
    old_t = re.sub(r"[^\w]+", " ", (old_title or "").casefold()).strip()
    new_t = re.sub(r"[^\w]+", " ", (new_title or "").casefold()).strip()
    if old_t and new_t and old_t != new_t:
        distance = Levenshtein.distance(old_t, new_t)
        ratio = fuzz.ratio(old_t, new_t)
        if distance >= 8 and ratio < 92:
            return True

    old_c = re.sub(r"\s+", " ", (old_context or "").casefold()).strip()
    new_c = re.sub(r"\s+", " ", (new_context or "").casefold()).strip()
    if old_c and new_c and old_c != new_c:
        distance = Levenshtein.distance(old_c, new_c)
        ratio = fuzz.ratio(old_c, new_c)
        if distance >= 30 and ratio < 78:
            return True
    return False


MEANINGFUL_FIELDS = {
    "application_deadline": [r"(?:last date|last date to apply|apply(?:ing)? till|closing date|अंतिम तिथि|आवेदन की अंतिम तिथि)\s*[:：-]?\s*([^\n,;]{1,50})"],
    "exam_date": [r"(?:exam(?:ination)? date| परीक्षा तिथि|परीक्षा दिनांक)\s*[:：-]?\s*([^\n,;]{1,50})"],
    "result_date": [r"(?:result date|परिणाम तिथि|रिजल्ट जारी)\s*[:：-]?\s*([^\n,;]{1,50})"],
    "vacancy_count": [r"(?:total vacancies?|no\. of vacancies?|vacancies|पदों की संख्या|कुल पद|रिक्त पद)\s*[:：-]?\s*([\d,]+)"],
    "age_limit": [r"(?:age limit|आयु सीमा)\s*[:：-]?\s*([^\n,;]{1,70})"],
    "eligibility": [r"(?:eligibility|educational qualification|योग्यता|शैक्षणिक योग्यता)\s*[:：-]?\s*([^\n;]{1,120})"],
    "corrigendum_number": [r"(?:corrigendum|amendment|शुद्धिपत्र|संशोधन)\s*(?:no\.?|number|संख्या)?\s*[:#-]?\s*([A-Z0-9/-]{1,30})"],
}

def extract_meaningful_fields(text):
    source = clean_text(text or "", 12000).casefold()
    found = {}
    for field, patterns in MEANINGFUL_FIELDS.items():
        for pattern in patterns:
            match = re.search(pattern, source, flags=re.I)
            if match:
                value = re.sub(r"\s+", " ", match.group(1)).strip(" .:-")
                if value:
                    found[field] = value
                    break
    return found

def meaningful_change_details(old_text, new_text):
    old_fields = extract_meaningful_fields(old_text)
    new_fields = extract_meaningful_fields(new_text)
    changed = {k: {"old": old_fields.get(k), "new": new_fields.get(k)}
               for k in set(old_fields) | set(new_fields)
               if old_fields.get(k) != new_fields.get(k)}
    if not changed:
        old_norm = re.sub(r"\s+", " ", (old_text or "").casefold()).strip()
        new_norm = re.sub(r"\s+", " ", (new_text or "").casefold()).strip()
        if old_norm and new_norm and old_norm != new_norm:
            ratio = fuzz.ratio(old_norm[:2000], new_norm[:2000])
            if ratio < 78 and Levenshtein.distance(old_norm[:2000], new_norm[:2000]) >= 30:
                changed["substantive_text"] = {"old": old_norm[:160], "new": new_norm[:160]}
    return changed

def baseline_can_complete(scan_success, errors):
    return bool(scan_success) and not bool(errors)

def add_review_item(state, record, reason, details=None):
    queue = state.setdefault("review_queue", {})
    key = hashlib.sha256((record.get("site_id", "") + "|" + record.get("url", "")).encode("utf-8")).hexdigest()
    previous = queue.get(key, {})
    queue[key] = {
        "site_id": record.get("site_id"), "site_name": record.get("site_name"),
        "url": record.get("url"), "title": record.get("title"),
        "reason": clean_text(str(reason), 500),
        "detected_dates": extract_meaningful_fields("\n".join([record.get("title", ""), record.get("context", ""), record.get("pdf_text", "")])) ,
        "gemini_output": record.get("classification"),
        "diff_summary": details or record.get("meaningful_diff", {}),
        "status": "open", "retry_count": int(previous.get("retry_count", 0)) + (1 if previous else 0),
        "first_seen": previous.get("first_seen", utc_now()), "updated_at": utc_now(),
    }


def _check_url_changed(session, url, record):
    try:
        head = session.head(url, timeout=8, allow_redirects=True)
        new_etag = head.headers.get("etag")
        new_lm = head.headers.get("last-modified")

        old_etag = record.get("etag")
        old_lm = record.get("last_modified")

        changed = False
        if new_etag and old_etag and new_etag != old_etag:
            changed = True
        elif new_lm and old_lm and new_lm != old_lm:
            changed = True

        if record.get("is_pdf"):
            try:
                with session.get(url, timeout=20, allow_redirects=True, stream=True) as response:
                    if response.status_code < 400:
                        chunks = []
                        total = 0
                        prefix = b""
                        too_large = False
                        for chunk in response.iter_content(chunk_size=64 * 1024):
                            if not chunk:
                                continue
                            if len(prefix) < 8:
                                prefix += chunk[:8 - len(prefix)]
                            total += len(chunk)
                            if total > MAX_PDF_SEND_BYTES:
                                too_large = True
                                break
                            chunks.append(chunk)
                        if not too_large and prefix.startswith(b"%PDF"):
                            content = b"".join(chunks)
                            new_hash = _pdf_content_fingerprint(content)
                            old_hash = record.get("pdf_hash")
                            old_kind = record.get("pdf_hash_kind")
                            new_kind = new_hash.split(":", 1)[0]
                            if old_hash and old_kind == new_kind:
                                changed = new_hash != old_hash
                            elif old_hash and not old_kind:
                                changed = False
                            record["pdf_hash"] = new_hash
                            record["pdf_hash_kind"] = new_kind
            except Exception as exc:
                print(f"[WARN] PDF hash check failed for {url[:80]}: {exc}", file=sys.stderr)

        return changed, new_etag, new_lm
    except Exception:
        return False, None, None


# ---------------------------------------------------------------------------
# URL filters
# ---------------------------------------------------------------------------

_NON_NOTICE_URL_PATTERNS = [
    re.compile(r"/page/\d+/?$", re.I),
    re.compile(r"/page/?$", re.I),
    re.compile(r"/notice_category(/|$)", re.I),
    re.compile(r"/notice-category(/|$)", re.I),
    re.compile(r"/document-category(/|$)", re.I),
    re.compile(r"/document_category(/|$)", re.I),
    re.compile(r"/past-notices(/|$)", re.I),
    re.compile(r"/past_notices(/|$)", re.I),
    re.compile(r"/whats-new(/|$)", re.I),
    re.compile(r"/whats_new(/|$)", re.I),
    re.compile(r"/category/[^/]+/?$", re.I),
    re.compile(r"/tag/[^/]+/?$", re.I),
    re.compile(r"/archive/?$", re.I),
    re.compile(r"/search(/|$)", re.I),
    re.compile(r"[?&]page=\d+", re.I),
    re.compile(r"[?&]paged=\d+", re.I),
    re.compile(r"/(hi|en|hn|ur|bn|ta|te|mr|gu|kn|ml|pa|or|as)(/|$).*(past[-_]?notices|whats[-_]?new|archive|category|notice[-_]?category|document[-_]?category|search)", re.I),
    re.compile(r"/(hi|en|hn|ur|bn|ta|te|mr|gu|kn|ml|pa|or|as)/?$", re.I),
]

_ARCHIVE_URL_PATTERNS = [
    re.compile(r"/past-notices(/|$)", re.I),
    re.compile(r"/past_notices(/|$)", re.I),
    re.compile(r"/whats-new(/|$)", re.I),
    re.compile(r"/whats_new(/|$)", re.I),
    re.compile(r"/notice_category(/|$)", re.I),
    re.compile(r"/notice-category(/|$)", re.I),
    re.compile(r"/document-category(/|$)", re.I),
    re.compile(r"/document_category(/|$)", re.I),
    re.compile(r"/archive/?$", re.I),
    re.compile(r"/page/\d+/?$", re.I),
    re.compile(r"/page/?$", re.I),
    re.compile(r"[?&]page=\d+", re.I),
    re.compile(r"[?&]paged=\d+", re.I),
]

_GENERIC_TITLES = {
    "archive", "more", "more...", "more…", "more....",
    "»", "«", ">>", "<<", "next", "previous", "prev",
    "back", "forward", "home", "contact", "about",
    "about us", "contact us", "read more", "view more",
    "click here", "here", "link",
}

_LANGUAGE_SELECTOR_TITLES = {
    "hindi", "english", "santali", "santhali", "urdu", "bengali",
    "bangla", "odia", "oriya", "tamil", "telugu", "marathi",
    "gujarati", "kannada", "malayalam", "punjabi", "assamese",
    "kashmiri", "konkani", "manipuri", "nepali", "sanskrit",
    "sindhi", "bodo", "dogri", "maithili", "rajasthani",
    "हिन्दी", "हिंदी", "हिन्दी में", "हिंदी में",
    "अंग्रेजी", "अंग्रेज़ी", "अंग्रेजी में",
    "संताली", "संथाली", "उर्दू", "बंगाली", "बांग्ला",
    "उड़िया", "ओड़िया", "तमिल", "तेलुगु", "मराठी",
    "गुजराती", "कन्नड़", "मलयालम", "पंजाबी", "असमिया",
    "कश्मीरी", "कोंकणी", "मणिपुरी", "नेपाली", "संस्कृत",
    "सिंधी", "बोडो", "डोगरी", "मैथिली", "राजस्थानी",
}

_EMPTY_PAGE_PHRASES = [
    "sorry, no notice matched",
    "no notice matched this category",
    "no records found",
    "no data found",
    "no notices found",
    "no results found",
]


def _is_navigation_url(url):
    try:
        parsed = urlparse(url)
        target = (parsed.path or "") + ("?" + parsed.query if parsed.query else "")
    except Exception:
        return False
    for pat in _NON_NOTICE_URL_PATTERNS:
        if pat.search(target):
            return True
    return False


def _is_archive_url(url):
    try:
        parsed = urlparse(url)
        target = (parsed.path or "") + ("?" + parsed.query if parsed.query else "")
    except Exception:
        return False
    for pat in _ARCHIVE_URL_PATTERNS:
        if pat.search(target):
            return True
    return False


def _is_generic_title(title):
    t = (title or "").strip().lower()
    if not t:
        return True
    if t in _GENERIC_TITLES:
        return True
    if t.isdigit() and len(t) <= 3:
        return True
    if len(t) <= 2 and not any(c.isalnum() for c in t):
        return True
    return False


def _is_language_selector(title):
    t = (title or "").strip().lower()
    if not t:
        return False
    if t in _LANGUAGE_SELECTOR_TITLES:
        return True
    for sep in (" - ", " | ", " / ", "(", ")"):
        for part in t.split(sep):
            p = part.strip()
            if p and p in _LANGUAGE_SELECTOR_TITLES and len(t) <= 40:
                return True
    return False


def _is_empty_page_text(html_text):
    if not html_text:
        return False
    sample = html_text[:8000].lower()
    return any(phrase in sample for phrase in _EMPTY_PAGE_PHRASES)


def _title_from_url(url, min_len=8):
    try:
        path = unquote(urlparse(url).path or "")
    except Exception:
        return ""
    slug = path.rstrip("/").rsplit("/", 1)[-1]
    if not slug or slug.lower().endswith(".pdf"):
        slug = slug.rsplit(".", 1)[0] if "." in slug else slug
    slug = re.sub(r"[-_]+", " ", slug)
    slug = re.sub(r"\s+", " ", slug).strip()
    slug = clean_text(slug, 200)
    if len(slug) < min_len:
        return ""
    if _is_generic_title(slug):
        return ""
    return slug


# ---------------------------------------------------------------------------
# PDF detection helpers
# ---------------------------------------------------------------------------

_PDF_URL_HINTS = (
    "downloadfile", "download_file", "downloadpdf", "download_pdf",
    "showpdf", "viewpdf", "getpdf", "filedownload", "getfile",
)


def _looks_like_pdf_url(url):
    if not url:
        return False
    u = url.lower()
    if ".pdf" in u:
        return True
    try:
        path = (urlparse(url).path or "").lower()
    except Exception:
        return False
    if any(kw in path for kw in _PDF_URL_HINTS):
        return True
    return False


def _looks_like_pdf_response(content, content_type, url=""):
    if not content:
        return False
    ct = (content_type or "").lower()
    if "application/pdf" in ct:
        return True
    if content[:4] == b"%PDF":
        return True
    if "application/octet-stream" in ct and content[:5] == b"%PDF-":
        return True
    if ("download" in ct or "x-download" in ct) and content[:4] == b"%PDF":
        return True
    if _looks_like_pdf_url(url) and content[:4] == b"%PDF":
        return True
    return False


def _collect_all_pdf_candidates(html_text, base_url, max_candidates=15):
    if not html_text:
        return []
    try:
        soup = BeautifulSoup(html_text, "html.parser")
    except Exception:
        return []

    def _valid(href):
        if not href or not isinstance(href, str):
            return False
        h = href.strip().lower()
        if not h:
            return False
        if h.startswith(("#", "javascript:", "mailto:", "tel:", "data:", "whatsapp:", "fb:", "blob:")):
            return False
        return True

    def _is_html_page(href):
        h = href.lower()
        for ext in (".html", ".htm", ".asp", ".aspx", ".jsp", ".php", ".cgi", ".shtml", ".css", ".js"):
            if h.endswith(ext) or ext + "?" in h:
                return True
        return False

    def _abs(href):
        return canonical_url(urljoin(base_url, href))

    candidates: Dict[str, int] = {}

    def _add(href, priority):
        if not _valid(href) or _is_html_page(href):
            return
        abs_url = _abs(href)
        if abs_url == canonical_url(base_url):
            return
        if _is_navigation_url(abs_url):
            return
        if candidates.get(abs_url, 0) < priority:
            candidates[abs_url] = priority

    for tag in soup.find_all(["iframe", "embed", "object", "source"]):
        src = tag.get("src") or tag.get("data") or ""
        if src and not src.lower().startswith(("javascript:", "#", "data:")):
            _add(src, 100)

    for tag in soup.find_all(onclick=True):
        onclick = tag.get("onclick", "") or ""
        for pat in (
            r"window\.open\(\s*['\"]([^'\"]+)['\"]",
            r"location\.href\s*=\s*['\"]([^'\"]+)['\"]",
            r"window\.location\s*=\s*['\"]([^'\"]+)['\"]",
            r"window\.location\.href\s*=\s*['\"]([^'\"]+)['\"]",
        ):
            m = re.search(pat, onclick, re.I)
            if m:
                _add(m.group(1), 95)

    for a in soup.find_all("a", href=True):
        href = a.get("href", "")
        if ".pdf" in href.lower() or _looks_like_pdf_url(href):
            _add(href, 90)

    _PDF_PATH_HINTS = (
        "/writereaddata/", "/uploadfile/", "/uploads/", "/upload/",
        "/downloadfile/", "/download_file/", "/getfile/", "/showfile/",
        "/viewfile/", "/filedownload/", "/files/", "/media/",
        "/attachment/", "/attachments/", "/docs/", "/documents/",
        "/file/", "/pdf/", "/download/", "/downloads/",
    )
    for a in soup.find_all("a", href=True):
        href = a.get("href", "")
        href_lower = href.lower()
        if any(hint in href_lower for hint in _PDF_PATH_HINTS):
            _add(href, 80)

    _TEXT_KEYWORDS = (
        "view", "download", "click here", "click", "open", "get",
        "see file", "show", "read", "attachment", "file", "link",
        "देखें", "डाउनलोड", "देखे", "खोलें", "फ़ाइल", "फाइल",
        "विवरण", "डाउनलोड करें", "देखें यहाँ", "यहाँ देखें", "खोलिये",
    )
    for a in soup.find_all("a", href=True):
        href = a.get("href", "")
        text = a.get_text(" ", strip=True).lower()
        if not text:
            continue
        if any(kw in text for kw in _TEXT_KEYWORDS):
            priority = 70
            if re.search(r"\d+\s*(kb|mb|bytes)", text, re.I):
                priority = 75
            _add(href, priority)

    for a in soup.find_all("a", href=True):
        href = a.get("href", "")
        img = a.find("img")
        if not img:
            continue
        img_attrs = " ".join([
            str(img.get("src") or ""),
            str(img.get("alt") or ""),
            " ".join(img.get("class") or []),
            str(img.get("title") or ""),
        ]).lower()
        if any(kw in img_attrs for kw in ("pdf", "document", "file", "download", "attachment", "doc")):
            _add(href, 65)

    _FILE_LABEL_RE = re.compile(
        r"^(file|फ़ाइल|फाइल|attachment|संलग्नक|file\s*name|फ़ाइल\s*नाम)\s*[:\-]?\s*$",
        re.I,
    )
    for label in soup.find_all(["td", "th", "label", "b", "strong", "span", "div", "dt"]):
        label_text = label.get_text(" ", strip=True).strip()
        if not _FILE_LABEL_RE.match(label_text):
            continue
        parent = label.find_parent(["tr", "li", "div", "p", "dl"]) or label.parent
        if not parent:
            continue
        for a in parent.find_all("a", href=True):
            _add(a.get("href", ""), 60)

    for a in soup.find_all("a", href=True, target="_blank"):
        _add(a.get("href", ""), 50)

    for a in soup.find_all("a", href=True):
        href = a.get("href", "")
        _add(href, 30)

    ranked = sorted(candidates.items(), key=lambda x: -x[1])
    return ranked[:max_candidates]


def _find_pdf_link_in_html(html_text, base_url):
    ranked = _collect_all_pdf_candidates(html_text, base_url, max_candidates=1)
    return ranked[0][0] if ranked else None


def _download_with_pdf_resolution(session, url, timeout, depth=0, _visited=None):
    if _visited is None:
        _visited = set()

    canon = canonical_url(url)
    if canon in _visited:
        return None, url, "already_visited"
    _visited.add(canon)

    if depth > 3:
        return None, url, "max_depth_exceeded"

    try:
        head = session.head(url, timeout=min(10, timeout), allow_redirects=True)
        cl = head.headers.get("content-length")
        if cl:
            try:
                if int(cl) > MAX_PDF_SEND_BYTES:
                    return None, url, "size_limit_head"
            except (TypeError, ValueError):
                pass
    except Exception:
        pass

    try:
        response = session.get(url, timeout=timeout, allow_redirects=True)
    except requests.RequestException as exc:
        return None, url, f"request_error:{type(exc).__name__}"

    if response.status_code >= 400:
        return None, url, f"http_{response.status_code}"

    content = response.content
    content_type = response.headers.get("content-type", "").lower()
    final_url = response.url

    if _looks_like_pdf_response(content, content_type, final_url):
        return content, final_url, "direct_pdf"

    if "html" in content_type or "xhtml" in content_type or not content_type:
        try:
            html_text = content.decode("utf-8", errors="ignore")
        except Exception:
            return None, url, "html_decode_error"

        candidates = _collect_all_pdf_candidates(html_text, final_url, max_candidates=10)

        for cand_url, priority in candidates:
            sub_content, sub_url, sub_method = _download_with_pdf_resolution(
                session, cand_url, timeout, depth + 1, _visited
            )
            if sub_content:
                return sub_content, sub_url, f"html_wrap(p{priority})->{sub_method}"

        return None, url, "html_no_pdf_found"

    if content[:4] == b"%PDF":
        return content, final_url, "magic_bytes"

    return None, url, f"unsupported:{content_type[:40]}"


# ---------------------------------------------------------------------------
# Dates
# ---------------------------------------------------------------------------

_MONTH_NAMES = {
    "january": 1, "jan": 1, "february": 2, "feb": 2,
    "march": 3, "mar": 3, "april": 4, "apr": 4,
    "may": 5, "june": 6, "jun": 6, "july": 7, "jul": 7,
    "august": 8, "aug": 8, "september": 9, "sep": 9, "sept": 9,
    "october": 10, "oct": 10, "november": 11, "nov": 11,
    "december": 12, "dec": 12,
    "जनवरी": 1, "फरवरी": 2, "मार्च": 3, "अप्रैल": 4,
    "मई": 5, "जून": 6, "जुलाई": 7, "अगस्त": 8,
    "सितंबर": 9, "सितम्बर": 9, "अक्टूबर": 10, "अक्तूबर": 10,
    "नवंबर": 11, "नवम्बर": 11, "दिसंबर": 12, "दिसम्बर": 12,
}

_MONTH_REGEX = (
    r"jan|feb|mar|apr|may|jun|jul|aug|sep|sept|oct|nov|dec|"
    r"january|february|march|april|june|july|august|"
    r"september|october|november|december|"
    r"जनवरी|फरवरी|मार्च|अप्रैल|मई|जून|जुलाई|अगस्त|"
    r"सितंबर|सितम्बर|अक्टूबर|अक्तूबर|नवंबर|नवम्बर|दिसंबर|दिसम्बर"
)

_FULL_DATE_PATTERNS = [
    re.compile(r"\b(\d{1,2})[/\-.](\d{1,2})[/\-.](\d{4})\b"),
    re.compile(r"\b(\d{4})-(\d{1,2})-(\d{1,2})\b"),
    re.compile(r"\b(\d{1,2})(?:st|nd|rd|th)?[\s\-]+(" + _MONTH_REGEX + r")[\s\-,]+(\d{4})\b", re.I),
    re.compile(r"\b(" + _MONTH_REGEX + r")[\s\-]+(\d{1,2})(?:st|nd|rd|th)?[\s\-,]+(\d{4})\b", re.I),
]


def _extract_full_dates(text):
    if not text:
        return []
    dates = []
    for pat in _FULL_DATE_PATTERNS:
        for m in pat.finditer(text):
            try:
                g = m.groups()
                if len(g) != 3:
                    continue
                a, b, c = g
                if a.isdigit() and len(a) == 4:
                    y, mo, d = int(a), int(b), int(c)
                elif b.isalpha() or (b and not b.isdigit()):
                    d = int(a); mo = _MONTH_NAMES.get(b.lower(), 0); y = int(c)
                elif a and not a.isdigit():
                    mo = _MONTH_NAMES.get(a.lower(), 0); d = int(b); y = int(c)
                else:
                    d, mo, y = int(a), int(b), int(c)
                if not (1 <= mo <= 12 and 1 <= d <= 31):
                    continue
                if not (1990 <= y <= 2100):
                    continue
                dates.append(datetime(y, mo, d, tzinfo=timezone.utc))
            except (ValueError, IndexError, TypeError, AttributeError):
                continue
    return dates


_UPLOAD_DATE_TEXT_PATTERNS = [
    re.compile(r"(?:published|posted|uploaded|issued|dated)\s*(?:on|at|:|\-)?\s*(\d{1,2}[/\-.]\d{1,2}[/\-.]\d{4})", re.I),
    re.compile(r"(?:published|posted|uploaded|issued|dated)\s*(?:on|at|:|\-)?\s*(\d{1,2}(?:st|nd|rd|th)?\s+(?:" + _MONTH_REGEX + r")\s+\d{4})", re.I),
    re.compile(r"(?:दिनांक|प्रकाशित|जारी|अपलोड|अद्यतन)\s*[:\-]?\s*(\d{1,2}[/\-.]\d{1,2}[/\-.]\d{4})", re.I),
]


def _extract_explicit_issue_dates(text):
    if not text:
        return []
    dates = []
    for pattern in _UPLOAD_DATE_TEXT_PATTERNS:
        for match in pattern.finditer(text):
            dates.extend(_extract_full_dates(match.group(1)))
    return sorted(set(dates))


def _extract_upload_date(anchor_tag):
    try:
        search_root = (
            anchor_tag.find_parent("tr")
            or anchor_tag.find_parent("li")
            or anchor_tag.find_parent("article")
            or anchor_tag.find_parent(["div", "section"])
            or anchor_tag.parent
        )
        if not search_root:
            return None
        time_tag = search_root.find("time")
        if time_tag:
            raw = time_tag.get("datetime") or time_tag.get_text(strip=True)
            if raw:
                try:
                    iso = raw.replace("Z", "+00:00").strip()
                    dt = datetime.fromisoformat(iso)
                    if dt.tzinfo is None:
                        dt = dt.replace(tzinfo=timezone.utc)
                    return dt
                except Exception:
                    pass
                ds = _extract_full_dates(raw)
                if ds:
                    return max(ds)
        text = search_root.get_text(" ", strip=True)
        for pat in _UPLOAD_DATE_TEXT_PATTERNS:
            m = pat.search(text)
            if m:
                ds = _extract_full_dates(m.group(1))
                if ds:
                    return max(ds)
    except Exception:
        pass
    return None


def _is_stale_notice(title, context, url, upload_date=None, pdf_text=None):
    now = datetime.now(timezone.utc)
    cutoff = now - timedelta(days=STALE_NOTICE_DAYS)
    title_text = str(title or "")
    context_text = str(context or "")
    url_text = str(url or "")
    haystack = f"{title_text} {context_text} {url_text}".strip()
    full_text = f"{haystack} {pdf_text or ''}".strip()

    title_years = [int(y) for y in re.findall(r"(?<!\d)(?:19|20)\d{2}(?!\d)", title_text)]
    current_year = now.year
    update_words = r"(?:updated|update|revised|revision|corrigendum|addendum|amended|modified|नया संशोधन|संशोधित|अद्यतन|शुद्धिपत्र)"
    current_year_update = bool(re.search(
        rf"(?:revised|revision|corrigendum|addendum|amended|modified|संशोधित|शुद्धिपत्र).{{0,50}}{current_year}|{current_year}.{{0,50}}(?:revised|revision|corrigendum|addendum|amended|modified|संशोधित|शुद्धिपत्र)",
        f"{title_text} {context_text}", re.I
    ))
    title_has_old_range = len(title_years) >= 2 and max(title_years) < current_year
    title_has_very_old_year = bool(title_years) and max(title_years) < current_year - 1
    if (title_has_old_range or title_has_very_old_year) and not current_year_update:
        return True

    issue_dates = _extract_explicit_issue_dates(full_text)
    past_issue_dates = [d for d in issue_dates if d <= now]
    if past_issue_dates:
        return max(past_issue_dates) < cutoff
    if issue_dates:
        return False

    if upload_date is not None:
        if upload_date.tzinfo is None:
            upload_date = upload_date.replace(tzinfo=timezone.utc)
        else:
            upload_date = upload_date.astimezone(timezone.utc)
        return upload_date < cutoff

    years = [int(y) for y in re.findall(r"(?<!\d)(?:19|20)\d{2}(?!\d)", full_text)]
    if years and max(years) < now.year:
        return True
    return False


# ---------------------------------------------------------------------------
# Utilities
# ---------------------------------------------------------------------------

def utc_now():
    return datetime.now(timezone.utc).isoformat()


def clean_text(value, limit=500):
    value = re.sub(r"\s+", " ", value or "").strip()
    return value[:limit]


def load_json(path, default):
    try:
        with path.open("r", encoding="utf-8") as f:
            return json.load(f)
    except FileNotFoundError:
        return default
    except json.JSONDecodeError as exc:
        raise RuntimeError(f"Invalid JSON in {path.name}: {exc}") from exc


def atomic_save_json(path, data, max_bytes=None):
    tmp = path.with_suffix(path.suffix + ".new")
    try:
        with tmp.open("w", encoding="utf-8") as f:
            json.dump(data, f, ensure_ascii=False, indent=2)
            f.write("\n")
            f.flush()
            os.fsync(f.fileno())
        if max_bytes is not None:
            size = tmp.stat().st_size
            if size > max_bytes:
                raise RuntimeError(f"Serialized state exceeds byte cap: {size} > {max_bytes}")
        os.replace(tmp, path)
    except Exception:
        try:
            tmp.unlink(missing_ok=True)
        except OSError:
            pass
        raise


def canonical_url(raw):
    raw = (raw or "").strip()
    p = urlparse(raw)
    if not p.scheme or not p.netloc:
        return raw
    return urlunparse((p.scheme.lower(), p.netloc.lower(), p.path or "/", "", p.query, ""))


def canonical_identity_url(raw):
    normalized = canonical_url(raw)
    p = urlparse(normalized)
    if not p.scheme or not p.netloc:
        return normalized
    tracking_exact = {
        "fbclid", "gclid", "dclid", "msclkid", "yclid", "mc_cid", "mc_eid",
        "ref", "referrer", "lang", "language", "_ga", "_gl", "igshid",
    }
    pairs = []
    for key, value in parse_qsl(p.query, keep_blank_values=True):
        key_lower = key.casefold()
        if key_lower in tracking_exact or key_lower.startswith("utm_"):
            continue
        pairs.append((key, value))
    pairs.sort(key=lambda pair: (pair[0].casefold(), pair[1]))
    return urlunparse((p.scheme.lower(), p.netloc.lower(), p.path or "/", "", urlencode(pairs, doseq=True), ""))


def same_host(a, b):
    return urlparse(a).netloc.lower() == urlparse(b).netloc.lower()


def is_http_url(url):
    return urlparse(url).scheme in {"http", "https"}


def is_pdf(url):
    return urlparse(url).path.lower().endswith(".pdf")


def make_session():
    session = requests.Session()
    retry = Retry(
        total=3, connect=3, read=3, status=3,
        backoff_factor=0.7,
        status_forcelist=(429, 500, 502, 503, 504),
        allowed_methods=frozenset({"GET", "HEAD"}),
        respect_retry_after_header=True,
        raise_on_status=False,
    )
    adapter = HTTPAdapter(max_retries=retry, pool_connections=20, pool_maxsize=20)
    session.mount("http://", adapter)
    session.mount("https://", adapter)
    session.headers.update({
        "User-Agent": USER_AGENT,
        "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
        "Accept-Language": "en-IN,en;q=0.8,hi;q=0.7",
        "Cache-Control": "no-cache",
    })
    return session


# ---------------------------------------------------------------------------
# Config
# ---------------------------------------------------------------------------

def get_config():
    cfg = load_json(CONFIG_FILE, {})
    if not isinstance(cfg, dict):
        raise RuntimeError("websites.json root must be an object")
    scan = cfg.get("scan") or {}
    defaults = {
        "request_timeout_seconds": 25,
        "max_workers": 10,
        "max_items_per_site": 100,
        "max_discovery_pages_per_site": 10,
        "max_archive_pages_per_site": 12,
        "max_pagination_per_archive": 3,
        "max_new_items_per_run": 25,
        "gemini_batch_size": 3,
        "gemini_max_calls_per_run": 15,
        "retention_days": 90,
        "sent_retention_days": 90,
        "ignored_retention_days": 30,
        "baseline_retention_days": 60,
        "domain_delay_seconds": 1.0,
        "max_state_items": 3000,
        "max_state_bytes": 3000000,
        "max_pending_attempts": 72,
        "stale_notice_days": 10,
        "site_alert_threshold": 3,
        "site_alert_cooldown_hours": 6,
        "keywords": [],
        "discovery_keywords": [],
        "sitemap_enabled": True,
    }
    for key, value in defaults.items():
        scan.setdefault(key, value)

    scan["request_timeout_seconds"] = max(5, int(scan["request_timeout_seconds"]))
    scan["max_workers"] = max(1, int(scan["max_workers"]))
    scan["max_items_per_site"] = max(1, int(scan["max_items_per_site"]))
    scan["max_discovery_pages_per_site"] = max(1, int(scan["max_discovery_pages_per_site"]))
    scan["max_archive_pages_per_site"] = max(0, int(scan["max_archive_pages_per_site"]))
    scan["max_pagination_per_archive"] = max(0, int(scan["max_pagination_per_archive"]))
    scan["max_new_items_per_run"] = max(1, int(scan["max_new_items_per_run"]))
    scan["gemini_batch_size"] = max(1, min(20, int(scan["gemini_batch_size"])))
    scan["gemini_max_calls_per_run"] = max(1, int(scan["gemini_max_calls_per_run"]))
    scan["retention_days"] = max(7, int(scan["retention_days"]))
    scan["sent_retention_days"] = max(7, int(scan["sent_retention_days"]))
    scan["ignored_retention_days"] = max(7, int(scan["ignored_retention_days"]))
    scan["baseline_retention_days"] = max(7, int(scan["baseline_retention_days"]))
    scan["domain_delay_seconds"] = max(0.0, min(10.0, float(scan["domain_delay_seconds"])))
    scan["max_state_items"] = max(500, min(10000, int(scan["max_state_items"])))
    scan["max_state_bytes"] = max(500000, min(3000000, int(scan["max_state_bytes"])))
    scan["max_pending_attempts"] = max(1, int(scan["max_pending_attempts"]))
    scan["stale_notice_days"] = max(1, int(scan["stale_notice_days"]))
    scan["site_alert_threshold"] = max(1, int(scan["site_alert_threshold"]))
    scan["site_alert_cooldown_hours"] = max(1, int(scan["site_alert_cooldown_hours"]))
    scan["sitemap_enabled"] = bool(scan["sitemap_enabled"])
    scan["keywords"] = [clean_text(str(x), 80).lower() for x in scan.get("keywords", []) if str(x).strip()]
    scan["discovery_keywords"] = [clean_text(str(x), 80).lower() for x in scan.get("discovery_keywords", []) if str(x).strip()]
    cfg["scan"] = scan

    sites = cfg.get("websites")
    if not isinstance(sites, list):
        raise RuntimeError("websites.json must contain a 'websites' array")

    enabled = []
    ids = set()
    for raw_site in sites:
        if not isinstance(raw_site, dict) or not raw_site.get("enabled", True):
            continue
        site = dict(raw_site)
        site["name"] = clean_text(str(site.get("name", "Unnamed Site")), 120)
        site["url"] = canonical_url(str(site.get("url", "")))
        site["id"] = clean_text(str(site.get("id", site["name"])), 100)
        if not site["name"] or not is_http_url(site["url"]):
            print(f"[WARN] Skipping invalid site: {raw_site}")
            continue
        if site["id"] in ids:
            print(f"[WARN] Duplicate site id skipped: {site['id']}")
            continue
        ids.add(site["id"])
        site["keywords"] = [clean_text(str(x), 80).lower() for x in site.get("keywords", []) if str(x).strip()]
        site["discovery_keywords"] = [clean_text(str(x), 80).lower() for x in site.get("discovery_keywords", []) if str(x).strip()]
        enabled.append(site)
    cfg["websites"] = enabled
    return cfg


# ---------------------------------------------------------------------------
# State
# ---------------------------------------------------------------------------

def default_state():
    return {
        "version": 28,
        "initialized": False,
        "last_run": None,
        "items": {},
        "sites": {},
        "review_queue": {},
        "metrics": {"site_scan_success": {}, "site_scan_failure": {}, "parse_errors": 0,
                     "sent_notifications": 0, "failed_notifications": 0,
                     "duplicate_rejects": 0, "state_save_failures": 0},
        "stats": {"runs": 0, "sent": 0, "ignored": 0, "pending": 0, "errors": 0},
    }


def load_state():
    state = load_json(STATE_FILE, default_state())
    if not isinstance(state, dict):
        state = default_state()
    state.setdefault("version", 1)
    state.setdefault("initialized", False)
    state.setdefault("last_run", None)
    state.setdefault("items", {})
    state.setdefault("sites", {})
    state.setdefault("review_queue", {})
    state.setdefault("metrics", {})
    state["metrics"].setdefault("site_scan_success", {})
    state["metrics"].setdefault("site_scan_failure", {})
    for _metric in ("parse_errors", "sent_notifications", "failed_notifications", "duplicate_rejects", "state_save_failures"):
        state["metrics"].setdefault(_metric, 0)
    state.setdefault("stats", {})
    for key in ("runs", "sent", "ignored", "pending", "errors"):
        state["stats"].setdefault(key, 0)
    for record in state["items"].values():
        if not isinstance(record, dict):
            continue
        if "status" not in record:
            if record.get("sent") is True:
                record["status"] = "sent"
            elif record.get("ignored") is True:
                record["status"] = "ignored"
            else:
                record["status"] = "baseline"
        record["_loaded_status"] = record.get("status")
        record.setdefault("attempts", 0)
        record.setdefault("last_error", None)
        record.setdefault("summary", "")
        record.setdefault("classification", None)
        record.setdefault("pdf_extracted", False)
        record.setdefault("pdf_text", "")
        record.setdefault("pdf_attempts", 0)
        record.setdefault("ocr_used", False)
        record.setdefault("pdf_method", "")
        record.setdefault("telegram_attempts", 0)
        record.setdefault("pdf_sent", False)
        record.setdefault("upload_date", None)
        record.setdefault("first_seen", utc_now())
        record.setdefault("last_seen", record["first_seen"])
        record.setdefault("etag", None)
        record.setdefault("last_modified", None)
        record.setdefault("pdf_hash", None)
        record.setdefault("pdf_hash_kind", None)
        record.setdefault("last_content_check_at", None)
        if not record.get("last_content_check_at"):
            record["last_content_check_at"] = (
                record.get("last_seen") or record.get("first_seen") or utc_now()
            )
    state["version"] = 29
    return state


def site_state(state, site_id):
    s = state.setdefault("sites", {}).setdefault(site_id, {})
    s.setdefault("baseline_complete", False)
    s.setdefault("consecutive_failures", 0)
    s.setdefault("total_failures", 0)
    s.setdefault("last_success", None)
    s.setdefault("last_error", None)
    s.setdefault("last_error_at", None)
    s.setdefault("last_item_count", 0)
    s.setdefault("alert_active", False)
    s.setdefault("last_alert_at", None)
    s.setdefault("last_recovery_at", None)
    return s


def mark_site_success(state, site_id, count):
    s = site_state(state, site_id)
    s["consecutive_failures"] = 0
    s["last_success"] = utc_now()
    s["last_error"] = None
    s["last_error_at"] = None
    s["last_item_count"] = count


def mark_site_failure(state, site_id, error):
    s = site_state(state, site_id)
    s["consecutive_failures"] += 1
    s["total_failures"] += 1
    s["last_error"] = clean_text(error, 500)
    s["last_error_at"] = utc_now()


def _check_and_send_site_alerts(state, cfg, token, chat_id, threshold=3, cooldown_hours=6):
    now = datetime.now(timezone.utc)
    failing_candidates = []
    recovered_candidates = []

    for site in cfg["websites"]:
        sid = site["id"]
        st = site_state(state, sid)
        failures = int(st.get("consecutive_failures", 0))
        if failures >= threshold and not st.get("alert_active", False):
            last_alert = st.get("last_alert_at")
            cooled = True
            if last_alert:
                try:
                    last_dt = datetime.fromisoformat(last_alert.replace("Z", "+00:00"))
                    if last_dt.tzinfo is None:
                        last_dt = last_dt.replace(tzinfo=timezone.utc)
                    cooled = (now - last_dt).total_seconds() >= cooldown_hours * 3600
                except Exception:
                    cooled = True
            if cooled:
                failing_candidates.append((sid, site["name"], failures, st.get("last_error")))
        elif failures == 0 and st.get("alert_active", False):
            recovered_candidates.append((sid, site["name"]))

    if failing_candidates:
        lines = ["⚠️ <b>Site Failure Alert</b>", "", f"{len(failing_candidates)} site(s) failing:", ""]
        for sid, name, count, err in failing_candidates[:10]:
            lines.append(f"• <b>{html.escape(name)}</b> — {count} fails")
            if err:
                lines.append(f"  <i>{html.escape(str(err)[:100])}</i>")
        ok, _permanent, detail = send_telegram(token, chat_id, "\n".join(lines))
        if ok:
            for sid, _name, _count, _err in failing_candidates:
                st = site_state(state, sid)
                st["alert_active"] = True
                st["last_alert_at"] = utc_now()
        else:
            print(f"[WARN] Site failure alert not delivered; will retry: {detail}", file=sys.stderr)

    if recovered_candidates:
        lines = ["✅ <b>Site Recovery</b>", "", f"{len(recovered_candidates)} site(s) recovered:", ""]
        for sid, name in recovered_candidates[:10]:
            lines.append(f"• {html.escape(name)}")
        ok, _permanent, detail = send_telegram(token, chat_id, "\n".join(lines))
        if ok:
            for sid, _name in recovered_candidates:
                st = site_state(state, sid)
                st["alert_active"] = False
                st["last_recovery_at"] = utc_now()
        else:
            print(f"[WARN] Site recovery alert not delivered; will retry: {detail}", file=sys.stderr)


# ---------------------------------------------------------------------------
# Scoring / IDs / Dedup
# ---------------------------------------------------------------------------

def local_score(title, url, context, keywords):
    text = f"{title} {url} {context}".lower()
    return sum(1 for kw in keywords if kw and kw in text)


def pending_priority(record, keywords, now=None):
    now = now or datetime.now(timezone.utc)
    first_seen = _parse_utc_timestamp(record.get("first_seen"))
    age_days = max(0.0, (now - first_seen).total_seconds() / 86400) if first_seen else 0.0
    score = local_score(
        record.get("title", ""), record.get("url", ""), record.get("context", ""), keywords
    )
    age_bonus = min(age_days, 30.0)
    return score + age_bonus, age_days


def item_id(site_id, url, title, context=""):
    fingerprint = hashlib.sha256(
        clean_text(f"{title}|{context}", 900).lower().encode()
    ).hexdigest()[:12]
    raw = f"{site_id}|{canonical_identity_url(url)}|{fingerprint}"
    return hashlib.sha256(raw.encode("utf-8")).hexdigest()[:32]


def _normalize_title(title):
    return re.sub(r"[^\w\s]", " ", (title or "").lower()).strip()


def _url_path_segments(url):
    try:
        path = urlparse(url).path.strip("/").lower()
        return {seg for seg in path.split("/") if seg and len(seg) > 2}
    except Exception:
        return set()


def build_site_index(state):
    index = {}
    permanent = {}
    for iid, record in state.get("items", {}).items():
        if not isinstance(record, dict):
            continue
        sid = record.get("site_id")
        if not sid:
            continue
        row = (iid, record.get("title", ""), record.get("url", ""))
        target = permanent if record.get("status") == "permanent_error" else index
        target.setdefault(sid, []).append(row)
    for sid, rows in permanent.items():
        index.setdefault(sid, []).extend(rows)
    return index


def find_url_match(site_items, url):
    target = canonical_identity_url(url)
    if not target:
        return None
    for iid, _title, existing_url in site_items or []:
        if canonical_identity_url(existing_url) == target:
            return iid
    return None


def find_fuzzy_match(site_items, title, url):
    if not site_items or not title:
        return None
    new_title = _normalize_title(title)
    new_segs = _url_path_segments(url)
    if len(new_title) < 12:
        return None

    best = None
    best_score = 0
    for iid, existing_title, existing_url in site_items:
        existing_norm = _normalize_title(existing_title)
        if len(existing_norm) < 12:
            continue
        existing_segs = _url_path_segments(existing_url)
        overlap = bool(new_segs and existing_segs and (new_segs & existing_segs))
        score = fuzz.token_sort_ratio(new_title, existing_norm)
        threshold = FUZZY_DUPLICATE_THRESHOLD if overlap else FUZZY_CROSS_PATH_THRESHOLD
        if not overlap and min(len(new_title), len(existing_norm)) < 30:
            continue
        if score >= threshold and score > best_score:
            best_score = score
            best = iid
    return best


# ---------------------------------------------------------------------------
# HTML extraction
# ---------------------------------------------------------------------------

def extract_candidates(html_text, page_url, site, scan):
    soup = BeautifulSoup(html_text, "html.parser")
    for tag in soup(["script", "style", "noscript", "svg", "template"]):
        tag.decompose()
    keywords = list(dict.fromkeys(scan["keywords"] + site.get("keywords", [])))
    out = []
    seen = set()
    for a in soup.find_all("a", href=True):
        href = canonical_url(urljoin(page_url, a.get("href", "")))
        if not is_http_url(href) or not same_host(page_url, href):
            continue
        if _is_navigation_url(href):
            continue
        title = clean_text(a.get_text(" ", strip=True), 300)
        if _is_generic_title(title):
            continue

        parent = a.find_parent("tr")
        if parent is None:
            parent = a.find_parent(["li", "article", "section"])
        if parent is None:
            parent = a.find_parent(["div", "td"])
        context = clean_text(parent.get_text(" ", strip=True) if parent else "", 700)

        if _is_language_selector(title):
            parent_text = clean_text(parent.get_text(" ", strip=True) if parent else "", 300)
            for lang in _LANGUAGE_SELECTOR_TITLES:
                pattern = re.compile(re.escape(lang), re.IGNORECASE)
                parent_text = pattern.sub("", parent_text).strip()
            parent_text = clean_text(parent_text, 300)
            if (parent_text and not _is_language_selector(parent_text)
                and not _is_generic_title(parent_text) and len(parent_text) >= 8):
                title = parent_text
            else:
                url_title = _title_from_url(href, min_len=8)
                if url_title:
                    title = url_title
                else:
                    continue

        score = local_score(title, href, context, keywords)
        href_lower = href.lower()
        pdf_bonus = 0
        if is_pdf(href) or _looks_like_pdf_url(href):
            pdf_bonus = 2
        elif any(kw in href_lower for kw in (
            "/notice/", "/document", "/writereaddata/",
            "/uploadfile/", "/uploads/", "/upload/",
            "/downloadfile/", "/download_file/", "/getfile/",
            "/showfile/", "/viewfile/", "/filedownload/",
            "/files/", "/media/", "/file/",
            "/attachment/", "/attachments/", "/docs/",
            "/download/", "/downloads/",
        )):
            pdf_bonus = 1
        else:
            pdf_bonus = 1

        if score <= 0 and pdf_bonus == 0:
            continue
        if href in seen:
            continue
        seen.add(href)
        upload_dt = _extract_upload_date(a)

        is_pdf_or_notice = bool(pdf_bonus > 0)

        out.append({
            "url": href,
            "title": title or clean_text(context, 180) or href.rsplit("/", 1)[-1],
            "context": context,
            "source_page": page_url,
            "is_pdf": is_pdf_or_notice,
            "score": score + pdf_bonus,
            "upload_date": upload_dt.isoformat() if upload_dt else None,
        })
    out.sort(key=lambda x: (-x["score"], x["title"].lower()))
    return out[: scan["max_items_per_site"]]


def discover_from_sitemap(session, base_url, scan):
    if not scan.get("sitemap_enabled"):
        return []
    parsed = urlparse(base_url)
    root = f"{parsed.scheme}://{parsed.netloc}"
    sitemap_url = urljoin(root + "/", "sitemap.xml")
    try:
        response = session.get(sitemap_url, timeout=scan["request_timeout_seconds"])
        if response.status_code >= 400:
            return []
        soup = BeautifulSoup(response.text, "xml")
        urls = []
        for loc in soup.find_all("loc")[:100]:
            url = canonical_url(loc.get_text(strip=True))
            if is_http_url(url) and same_host(base_url, url):
                if _is_navigation_url(url):
                    continue
                if any(kw in url.lower() for kw in scan["discovery_keywords"] if kw):
                    urls.append(url)
        return urls[: scan["max_discovery_pages_per_site"] * 3]
    except Exception:
        return []


def _robots_allowed(session, url, timeout):
    parsed = urlparse(url)
    origin = f"{parsed.scheme}://{parsed.netloc}"
    if origin not in _ROBOTS_CACHE:
        parser = RobotFileParser()
        robots_url = origin + "/robots.txt"
        try:
            response = session.get(robots_url, timeout=min(10, timeout), allow_redirects=True)
            if response.status_code < 400 and response.text:
                parser.set_url(robots_url)
                parser.parse(response.text.splitlines())
                _ROBOTS_CACHE[origin] = parser
            else:
                _ROBOTS_CACHE[origin] = None
        except Exception:
            _ROBOTS_CACHE[origin] = None
    parser = _ROBOTS_CACHE.get(origin)
    if parser is None:
        return True
    try:
        return parser.can_fetch(USER_AGENT, url)
    except Exception:
        return True

def discover_site(session, site, scan):
    base_url = site["url"]
    timeout = scan["request_timeout_seconds"]
    max_pages = scan["max_discovery_pages_per_site"]
    max_archive_pages = scan.get("max_archive_pages_per_site", 5)
    max_pagination_per_archive = scan.get("max_pagination_per_archive", 3)

    discovery_keywords = list(dict.fromkeys(
        scan["discovery_keywords"] + site.get("discovery_keywords", []) + scan["keywords"]
    ))

    queue = [base_url]
    queue.extend(discover_from_sitemap(session, base_url, scan))
    visited = set()
    archive_visited_count = 0
    pagination_tracker = {}
    candidates = {}
    errors = []
    successful_pages = 0
    total_budget = max_pages + max_archive_pages
    normal_visited_count = 0

    while queue and len(visited) < total_budget:
        page = canonical_url(queue.pop(0))
        if page in visited or not same_host(base_url, page):
            continue

        is_archive = _is_archive_url(page)
        if is_archive and archive_visited_count >= max_archive_pages:
            continue
        if not is_archive and normal_visited_count >= max_pages:
            continue
        visited.add(page)

        if is_archive:
            is_pagination = bool(re.search(r"/page/\d+|[?&](?:page|paged)=\d+", page, re.I))
            if is_pagination:
                prefix = re.sub(r"/page/\d+/?", "/", page)
                prefix = re.sub(r"[?&]page=\d+", "", prefix)
                prefix = re.sub(r"[?&]paged=\d+", "", prefix).rstrip("?&")
                current = pagination_tracker.get(prefix, 0)
                if current >= max_pagination_per_archive:
                    continue
                pagination_tracker[prefix] = current + 1

            archive_visited_count += 1
        else:
            normal_visited_count += 1

        try:
            if not _robots_allowed(session, page, timeout):
                print(f"[ROBOTS-SKIP] {page}", file=sys.stderr)
                continue
            domain_delay = float(scan.get("domain_delay_seconds", 1.0) or 0.0)
            if domain_delay > 0 and visited:
                time.sleep(min(domain_delay, 10.0))
            response = session.get(page, timeout=timeout, allow_redirects=True)
            if response.status_code >= 400:
                raise RuntimeError(f"HTTP {response.status_code}")
            final_url = canonical_url(response.url)
            content_type = response.headers.get("content-type", "").lower()

            if _looks_like_pdf_response(response.content, content_type, final_url):
                filename = final_url.rsplit("/", 1)[-1] or "PDF Notice"
                candidates[final_url] = {
                    "url": final_url, "title": clean_text(filename, 300),
                    "context": "Direct PDF notice", "source_page": page,
                    "is_pdf": True, "score": 3, "upload_date": None,
                }
                successful_pages += 1
                continue

            if content_type and "html" not in content_type and "xhtml" not in content_type:
                continue
            if _is_empty_page_text(response.text):
                successful_pages += 1
                continue

            found = extract_candidates(response.text, final_url, site, scan)
            for row in found:
                old = candidates.get(row["url"])
                if old is None or row["score"] > old["score"]:
                    candidates[row["url"]] = row
            successful_pages += 1

            soup = BeautifulSoup(response.text, "html.parser")
            for a in soup.find_all("a", href=True):
                href = canonical_url(urljoin(final_url, a.get("href", "")))
                if (not is_http_url(href) or not same_host(base_url, href)
                    or href in visited or href in queue):
                    continue

                if re.search(r"/(login|logout|register|search|tag)/", href, re.I):
                    continue

                if _is_archive_url(href):
                    if len(queue) < total_budget * 3:
                        queue.append(href)
                    continue

                anchor = clean_text(a.get_text(" ", strip=True), 220).lower()
                path = urlparse(href).path.lower()
                haystack = f"{anchor} {path}"
                if any(kw in haystack for kw in discovery_keywords if kw):
                    queue.append(href)
                    if len(queue) >= total_budget * 2:
                        break
        except Exception as exc:
            errors.append(f"{page}: {clean_text(str(exc), 250)}")

    values = list(candidates.values())
    values.sort(key=lambda x: (-x["score"], x["title"].lower()))
    return (site["id"], values[: scan["max_items_per_site"]], errors, successful_pages > 0)


def scan_site(site, scan):
    return discover_site(make_session(), site, scan)


# ---------------------------------------------------------------------------
# PDF extraction
# ---------------------------------------------------------------------------

def _extract_pdf_text_plumber(content):
    parts = []
    try:
        with pdfplumber.open(io.BytesIO(content)) as pdf:
            for idx, page in enumerate(pdf.pages[:MAX_PDF_PAGES]):
                try:
                    t = page.extract_text() or ""
                    if t.strip():
                        parts.append(t)
                except Exception as exc:
                    print(f"[WARN] Page {idx+1} text extract failed: {exc}", file=sys.stderr)
                try:
                    tables = page.extract_tables() or []
                    for table in tables:
                        for row in table:
                            cells = [str(c).strip() for c in row if c]
                            if cells:
                                parts.append(" | ".join(cells))
                except Exception as exc:
                    print(f"[WARN] Page {idx+1} table extract failed: {exc}", file=sys.stderr)
    except Exception as exc:
        print(f"[WARN] pdfplumber open failed: {exc}", file=sys.stderr)
    return "\n".join(parts)


def _extract_pdf_text_rapidocr(content):
    if not OCR_ENABLED or not _RAPIDOCR_AVAILABLE:
        return ""
    ocr = _get_rapidocr()
    if ocr is None:
        return ""
    parts = []
    try:
        doc = fitz.open(stream=content, filetype="pdf")
        pages_to_process = min(len(doc), MAX_PDF_PAGES, _OCR_MAX_PAGES)
        for page_num in range(pages_to_process):
            try:
                page = doc.load_page(page_num)
                pix = page.get_pixmap(dpi=OCR_DPI)
                img_bytes = pix.tobytes("png")
                result, _ = ocr(img_bytes)
                if result:
                    page_lines = [line[1] for line in result if len(line) > 1]
                    if page_lines:
                        parts.append("\n".join(page_lines))
            except Exception as exc:
                print(f"[WARN] RapidOCR page {page_num+1} failed: {exc}", file=sys.stderr)
        doc.close()
    except Exception as exc:
        print(f"[WARN] RapidOCR PDF processing failed: {exc}", file=sys.stderr)
    return "\n".join(parts)


def _extract_with_gemini_pdf(pdf_bytes):
    global _GEMINI_QUOTA_EXHAUSTED
    if not GEMINI_PDF_OCR_ENABLED or not _GEMINI_KEYS_POOL:
        return ""
    if _GEMINI_QUOTA_EXHAUSTED:
        return ""
    if len(pdf_bytes) > MAX_GEMINI_PDF_BYTES:
        print(f"[INFO] PDF too large for Gemini ({len(pdf_bytes)} bytes), skipping", file=sys.stderr)
        return ""
    try:
        pdf_b64 = base64.b64encode(pdf_bytes).decode("utf-8")
        prompt = (
            "Extract ALL text from this government notice PDF. "
            "May be in Hindi, English, or both. May contain tables. "
            "Return extracted text verbatim, preserving structure. "
            "Do NOT summarize. Do NOT invent. Just extract the text."
        )
        payload = {"contents": [{"parts": [
            {"text": prompt},
            {"inline_data": {"mime_type": "application/pdf", "data": pdf_b64}}
        ]}], "generationConfig": {"temperature": 0.0, "maxOutputTokens": 16384}}
        for model in _DYNAMIC_MODELS:
            if model in _DEAD_MODELS:
                continue
            endpoint = f"https://generativelanguage.googleapis.com/v1beta/models/{model}:generateContent"
            for attempt in range(2):
                response, key_used, reason = _gemini_post_with_rotation(endpoint, payload, timeout=90)
                if response is None:
                    if reason == "all_keys_quota_exhausted":
                        _GEMINI_QUOTA_EXHAUSTED = True
                        print("[QUOTA] All configured Gemini keys exhausted for this run; using local OCR fallback.", file=sys.stderr)
                    elif reason == "rate_limited":
                        print("[WARN] Gemini keys are temporarily rate-limited; using local OCR fallback for this PDF.", file=sys.stderr)
                    else:
                        print(f"[WARN] Gemini request unavailable ({reason}); using local OCR fallback for this PDF.", file=sys.stderr)
                    return ""
                if response.status_code == 404:
                    _DEAD_MODELS.add(model)
                    print(f"[WARN] Gemini model unavailable ({model}); trying next model.", file=sys.stderr)
                    break
                if response.status_code >= 500:
                    print(f"[WARN] Gemini server HTTP {response.status_code} ({model}), attempt {attempt+1}/2", file=sys.stderr)
                    if attempt == 0:
                        time.sleep(1.5)
                        continue
                    break
                if response.status_code >= 400:
                    print(f"[WARN] Gemini HTTP {response.status_code} ({model}): {response.text[:150]}", file=sys.stderr)
                    break
                try:
                    data = response.json()
                    extracted = _extract_gemini_text(data)
                    if extracted and len(extracted.strip()) > 50:
                        key_index = _GEMINI_KEYS_POOL.index(key_used) + 1 if key_used in _GEMINI_KEYS_POOL else "?"
                        print(f"[INFO] Gemini PDF OCR succeeded ({model}, key #{key_index})", file=sys.stderr)
                        return extracted
                    candidates = data.get("candidates") or []
                    finish_reason = candidates[0].get("finishReason", "unknown") if candidates else "unknown"
                    print(f"[WARN] Gemini empty ({model}), finishReason={finish_reason}", file=sys.stderr)
                    break
                except Exception as exc:
                    print(f"[WARN] Gemini response parse failed ({model}): {type(exc).__name__}", file=sys.stderr)
                    break
    except Exception as exc:
        print(f"[WARN] Gemini PDF OCR failed: {type(exc).__name__}", file=sys.stderr)
    return ""


def _text_looks_thin(text):
    stripped = (text or "").strip()
    if len(stripped) < OCR_MIN_TEXT_CHARS:
        return True
    words = re.findall(r"\w+", stripped, re.UNICODE)
    if len(words) < 20:
        return True
    if not re.search(r"\d", stripped):
        return True
    if stripped.count("\n") < 3:
        return True
    char_counts = Counter(stripped.lower())
    if char_counts:
        most_common_count = char_counts.most_common(1)[0][1]
        if most_common_count > len(stripped) * 0.5:
            return True
    return False


def download_pdf_content(pdf_url, timeout=30):
    global _RUNTIME_PDF_CACHE
    if pdf_url in _RUNTIME_PDF_CACHE:
        content = _RUNTIME_PDF_CACHE[pdf_url]
    else:
        try:
            session = make_session()
            content, actual_url, method = _download_with_pdf_resolution(session, pdf_url, timeout)
            if not content:
                return None, "", False, method
            if len(content) > MAX_PDF_SEND_BYTES:
                return None, "", False, "size_limit"
            _cache_put(pdf_url, content)
            if actual_url and actual_url != pdf_url:
                _cache_put(actual_url, content)
        except Exception as exc:
            print(f"[WARN] PDF download failed for {pdf_url}: {exc}", file=sys.stderr)
            return None, "", False, "download_error"

    text = _extract_pdf_text_plumber(content)
    extraction_method = "plumber"

    if _text_looks_thin(text):
        print(f"[INFO] PDF thin ({len(text)} chars). Trying Gemini PDF OCR...", file=sys.stderr)
        gemini_text = _extract_with_gemini_pdf(content)
        if gemini_text and len(gemini_text.strip()) > len(text.strip()):
            text = f"{text}\n\n--- GEMINI OCR ---\n\n{gemini_text}" if text.strip() else gemini_text
            extraction_method = "gemini"
            print(f"[INFO] Gemini OCR succeeded ({len(gemini_text)} chars)", file=sys.stderr)
        else:
            if OCR_ENABLED and _RAPIDOCR_AVAILABLE:
                print("[INFO] Gemini failed/skipped. Trying RapidOCR...", file=sys.stderr)
                rocr_text = _extract_pdf_text_rapidocr(content)
                if rocr_text and len(rocr_text.strip()) > len(text.strip()):
                    text = f"{text}\n\n--- RAPIDOCR ---\n\n{rocr_text}" if text.strip() else rocr_text
                    extraction_method = "rapidocr"
                    print(f"[INFO] RapidOCR succeeded ({len(rocr_text)} chars)", file=sys.stderr)
                else:
                    print("[WARN] All OCR methods failed", file=sys.stderr)
            else:
                print("[INFO] RapidOCR disabled or unavailable", file=sys.stderr)

    return (content, clean_text(text, MAX_PDF_TEXT_CHARS), extraction_method != "plumber", extraction_method)


# ---------------------------------------------------------------------------
# Gemini
# ---------------------------------------------------------------------------

def keyword_fallback(items):
    result = {}
    for index, item in enumerate(items):
        text = (f"{item.get('title', '')} {item.get('url', '')} "
                f"{item.get('context', '')} {item.get('pdf_text', '')}").lower()
        important = any(kw in text for kw in STRONG_KEYWORDS if kw)
        category = "notice"
        if any(k in text for k in ("recruitment", "vacancy", "भर्ती")):
            category = "vacancy"
        elif any(k in text for k in ("result", "परिणाम")):
            category = "result"
        elif "admit card" in text:
            category = "admit_card"
        elif "answer key" in text:
            category = "answer_key"
        elif any(k in text for k in ("scholarship", "छात्रवृत्ति")):
            category = "scholarship"
        elif any(k in text for k in ("admission", "प्रवेश")):
            category = "admission"
        elif any(k in text for k in ("tender", "निविदा")):
            category = "tender"
        elif any(k in text for k in ("gazette", "राजपत्र")):
            category = "gazette"
        elif any(k in text for k in ("land acquisition", "भू-अर्जन", "revenue notification")):
            category = "land_revenue"
        elif any(k in text for k in ("press release", "प्रेस विज्ञप्ति")):
            category = "press_release"
        elif any(k in text for k in ("announcement", "advertisement", "घोषणा")):
            category = "announcement"
        elif "publication" in text:
            category = "publication"
        result[str(index)] = {
            "important": important, "category": category,
            "summary": clean_text(item.get("title", ""), 180),
            "title_hi": None,
        }
    return result


def _build_prompt(prompt_items):
    return (
        "You classify and extract details from links on official "
        "Jharkhand district websites (nic.in). "
        "Return JSON only using the exact schema below.\n\n"
        "CRITICAL — set important=false for ALL of these:\n"
        "- Language selector links (titles like 'हिन्दी', 'English')\n"
        "- Category listing pages, archive pages, pagination pages\n"
        "- Navigation pages (Home, Contact, About, Gallery)\n"
        "- Pages with titles like 'Archive', 'More', '»', numbers, empty\n"
        "- 'Sorry, no notice matched', 'no records found', 'no data found'\n"
        "- Generic descriptions like 'listing page', 'category page'\n"
        "- Birth and death figures, COVID-19 updates, cause lists, "
        "tour programs, holiday lists, generic events\n\n"
        "Set important=true ONLY for genuine, specific notices.\n\n"
        "For EACH item determine:\n"
        "1. important (true/false)\n"
        "2. category — one of: 'vacancy', 'result', 'admit_card', 'answer_key', "
        "'admission', 'counselling', 'scholarship', 'exam_schedule', "
        "'tender', 'gazette', 'land_revenue', 'press_release', "
        "'announcement', 'publication', 'notice', 'other'\n"
        "3. summary — 1-line summary (<= 150 chars)\n"
        "4. title_hi — Hindi (Devanagari) translation of the title.\n\n"
        "IMPORTANT: If 'pdf_text' is provided, treat it as PRIMARY source.\n\n"
        "── UNIVERSAL FIELDS ──\n"
        "reference_number, issuing_authority, issuing_date, "
        "contact_person, contact_number, email, helpline_number, "
        "official_address, important_instructions\n\n"
        "── CATEGORY-SPECIFIC EXTRACTION ──\n\n"
        "VACANCY: total_posts (int), post_details (array of "
        "{post_name, category (UR/OBC/SC/ST/EWS), vacancies}), "
        "qualification, age_limit, age_relaxation, pay_scale, salary_type, "
        "application_fee, application_start_date, last_date, apply_link, "
        "advertisement_no, how_to_apply, documents_required, "
        "selection_process, experience_required, posting_location, "
        "reservation_details, bond_details, interview_date, "
        "interview_time, venue, reporting_time, engagement_type\n\n"
        "RESULT: result_for, exam_name, session, semester, result_date, "
        "result_link, result_type, merit_list_link, cutoff_marks, "
        "total_selected, next_stage, next_stage_date, roll_no_required, "
        "rechecking_last_date, rechecking_link, rechecking_fee, rechecking_mode\n\n"
        "ADMIT_CARD: exam_name, session, semester, exam_date, exam_time, "
        "exam_duration, exam_pattern, exam_center, reporting_time, "
        "download_start_date, download_last_date, roll_no_required, "
        "admit_card_link, instructions, helpline_number, download_mode\n\n"
        "ANSWER_KEY: exam_name, session, exam_date, total_questions, "
        "answer_key_link, objection_start_date, objection_last_date, "
        "objection_fee, per_question_fee, objection_mode, objection_address, "
        "payment_mode, answer_key_type\n\n"
        "ADMISSION: course_name, course_duration, session, university_name, "
        "eligibility, eligibility_marks, age_criteria, application_fee, "
        "fee_structure, apply_start_date, last_date, counselling_date, "
        "apply_link, admission_mode, total_seats, entrance_exam_name, "
        "hostel_available, documents_required, prospectus_link\n\n"
        "COUNSELLING: course_name, round, counselling_date, counselling_time, "
        "venue, apply_link, seat_matrix, registration_fee, "
        "choice_filling_dates, required_documents, reporting_time, "
        "counselling_mode, next_round_date\n\n"
        "SCHOLARSHIP: scheme_name, scholarship_amount, scholarship_duration, "
        "eligibility, applicable_category, income_limit, last_date, "
        "apply_link, apply_mode, portal_name, disbursement_mode, "
        "renewal_criteria, documents_required, income_certificate_required, "
        "caste_certificate_required, selection_criteria, helpline\n\n"
        "EXAM_SCHEDULE: exam_name, session, semester, course, "
        "exam_start_date, exam_end_date, exam_time, exam_center, "
        "timetable_link, subject_list, paper_code, practical_dates, "
        "viva_dates, reporting_time, instructions\n\n"
        "TENDER: tender_no, tender_type, work_description, issuing_authority, "
        "estimated_cost, emd_amount, emd_mode, tender_fee, tender_fee_mode, "
        "submission_last_date, opening_date, pre_bid_meeting_date, "
        "pre_bid_meeting_venue, submission_mode, apply_link, "
        "tender_document_link, bid_validity, completion_period, "
        "payment_terms, eligibility_criteria\n\n"
        "GAZETTE: gazette_no, gazette_type, subject, issuing_authority, "
        "publication_date, gazette_link, effective_date, gazette_content\n\n"
        "LAND_REVENUE: notification_no, subject, land_location, affected_area, "
        "plot_numbers, khasra_no, thana_no, district, tehsil, village, "
        "notification_type, issuing_authority, effective_date, order_link, "
        "compensation_details, objections_last_date, objections_address, land_type\n\n"
        "PRESS_RELEASE: subject, issuing_department, release_date, "
        "reference_no, release_link, full_content, category\n\n"
        "ANNOUNCEMENT: subject, issuing_authority, reference_no, "
        "effective_date, apply_link, announcement_type, target_audience, "
        "action_required, action_deadline\n\n"
        "PUBLICATION: publication_name, publication_type, publisher, "
        "publication_date, download_link, author, pages, language, "
        "edition, isbn, price\n\n"
        "NOTICE: subject, reference_no, issuing_authority, effective_date, "
        "order_link, notice_type, applicable_to, action_required, "
        "action_deadline, supersedes\n\n"
        "── EXTRA DETAILS ──\n"
        "Extract ALL other fields into 'extra_details' as array of "
        "{\"label\": \"...\", \"value\": \"...\"}. Limit 10 per item.\n\n"
        "Do NOT invent facts. Use null when unsure.\n\n"
        "Schema:\n"
        '{"items":[{'
        '"id":"0","important":true,"category":"vacancy","summary":"...","title_hi":"...",'
        '"reference_number":null,"issuing_authority":null,"issuing_date":null,'
        '"contact_person":null,"contact_number":null,"email":null,'
        '"helpline_number":null,"official_address":null,"important_instructions":null,'
        '"total_posts":null,"post_details":[],"qualification":null,'
        '"age_limit":null,"age_relaxation":null,"pay_scale":null,"salary_type":null,'
        '"application_fee":null,"application_start_date":null,"last_date":null,'
        '"apply_link":null,"advertisement_no":null,"how_to_apply":null,'
        '"documents_required":null,"selection_process":null,'
        '"experience_required":null,"posting_location":null,'
        '"reservation_details":null,"bond_details":null,'
        '"interview_date":null,"interview_time":null,"venue":null,'
        '"reporting_time":null,"engagement_type":null,'
        '"result_for":null,"exam_name":null,"session":null,"semester":null,'
        '"result_date":null,"result_link":null,"result_type":null,'
        '"merit_list_link":null,"cutoff_marks":null,"total_selected":null,'
        '"next_stage":null,"next_stage_date":null,"roll_no_required":null,'
        '"rechecking_last_date":null,"rechecking_link":null,'
        '"rechecking_fee":null,"rechecking_mode":null,'
        '"exam_date":null,"exam_time":null,"exam_duration":null,'
        '"exam_pattern":null,"exam_center":null,'
        '"download_start_date":null,"download_last_date":null,'
        '"admit_card_link":null,"instructions":null,"download_mode":null,'
        '"total_questions":null,"answer_key_link":null,'
        '"objection_start_date":null,"objection_last_date":null,'
        '"objection_fee":null,"per_question_fee":null,"objection_mode":null,'
        '"objection_address":null,"payment_mode":null,"answer_key_type":null,'
        '"course_name":null,"course_duration":null,"university_name":null,'
        '"eligibility":null,"eligibility_marks":null,"age_criteria":null,'
        '"fee_structure":null,"apply_start_date":null,"counselling_date":null,'
        '"admission_mode":null,"total_seats":null,"entrance_exam_name":null,'
        '"hostel_available":null,"prospectus_link":null,'
        '"round":null,"counselling_time":null,"seat_matrix":null,'
        '"registration_fee":null,"choice_filling_dates":null,'
        '"required_documents":null,"counselling_mode":null,"next_round_date":null,'
        '"scheme_name":null,"scholarship_amount":null,"scholarship_duration":null,'
        '"applicable_category":null,"income_limit":null,"apply_mode":null,'
        '"portal_name":null,"disbursement_mode":null,"renewal_criteria":null,'
        '"income_certificate_required":null,"caste_certificate_required":null,'
        '"selection_criteria":null,"helpline":null,'
        '"exam_start_date":null,"exam_end_date":null,"timetable_link":null,'
        '"subject_list":null,"paper_code":null,"practical_dates":null,'
        '"viva_dates":null,'
        '"tender_no":null,"tender_type":null,"work_description":null,'
        '"estimated_cost":null,"emd_amount":null,"emd_mode":null,'
        '"tender_fee":null,"tender_fee_mode":null,'
        '"submission_last_date":null,"opening_date":null,'
        '"pre_bid_meeting_date":null,"pre_bid_meeting_venue":null,'
        '"submission_mode":null,"tender_document_link":null,'
        '"bid_validity":null,"completion_period":null,'
        '"payment_terms":null,"eligibility_criteria":null,'
        '"gazette_no":null,"gazette_type":null,"publication_date":null,'
        '"gazette_link":null,"gazette_content":null,'
        '"notification_no":null,"land_location":null,"affected_area":null,'
        '"plot_numbers":null,"khasra_no":null,"thana_no":null,'
        '"district":null,"tehsil":null,"village":null,'
        '"notification_type":null,"effective_date":null,"order_link":null,'
        '"compensation_details":null,"objections_last_date":null,'
        '"objections_address":null,"land_type":null,'
        '"issuing_department":null,"release_date":null,'
        '"release_link":null,"full_content":null,'
        '"announcement_type":null,"target_audience":null,'
        '"action_required":null,"action_deadline":null,'
        '"publication_name":null,"publication_type":null,"publisher":null,'
        '"download_link":null,"author":null,"pages":null,'
        '"language":null,"edition":null,"isbn":null,"price":null,'
        '"subject":null,"notice_type":null,"applicable_to":null,"supersedes":null,'
        '"extra_details":[],"extra_details_present":false'
        '}]}\n\n'
        + json.dumps(prompt_items, ensure_ascii=False)
    )


def _normalize_label(label):
    return re.sub(r"[^\w\s]", "", (label or "").lower()).strip()


def _clean_extra_details(raw):
    if not isinstance(raw, list):
        return []
    out = []
    seen_labels = set()
    skip_labels = {
        "qualification", "age", "age limit", "age_limit",
        "no of post", "no of posts", "number of post", "total post",
        "total posts", "honorarium", "salary", "pay scale", "pay_scale",
        "application fee", "application_fee", "last date", "last_date",
        "start date", "end date", "publish date", "published date",
    }
    for item in raw[:15]:
        if not isinstance(item, dict):
            continue
        label = clean_text(str(item.get("label", "")), 100)
        value = clean_text(str(item.get("value", "")), 300)
        if not label or not value:
            continue
        if _normalize_label(label) in skip_labels:
            continue
        key = _normalize_label(label)
        if key in seen_labels:
            continue
        seen_labels.add(key)
        out.append({"label": label, "value": value})
    return out


def _parse_gemini_response(text, item_count):
    text = re.sub(r"^```(?:json)?\s*", "", text, flags=re.I)
    text = re.sub(r"\s*```$", "", text).strip()
    parsed = json.loads(text)
    rows = []
    if isinstance(parsed, dict) and isinstance(parsed.get("items"), list):
        rows = parsed["items"]
    elif isinstance(parsed, list):
        rows = parsed

    def _str(row, key, limit=300):
        v = row.get(key)
        if v is None:
            return None
        s = clean_text(str(v), limit)
        return s or None

    result = {}
    for row in rows:
        if not isinstance(row, dict):
            continue
        idx = str(row.get("id", ""))
        if not (idx.isdigit() and 0 <= int(idx) < item_count):
            continue
        post_details = row.get("post_details")
        if not isinstance(post_details, list):
            post_details = []
        clean_posts = []
        for pd in post_details[:15]:
            if not isinstance(pd, dict):
                continue
            clean_posts.append({
                "post_name": clean_text(str(pd.get("post_name", "")), 120),
                "category": clean_text(str(pd.get("category", "")), 40),
                "vacancies": pd.get("vacancies"),
            })
        result[idx] = {
            "important": bool(row.get("important", False)),
            "category": clean_text(str(row.get("category", "notice")), 40) or "notice",
            "summary": clean_text(str(row.get("summary", "")), 200),
            "title_hi": _str(row, "title_hi", 200),
            "reference_number": _str(row, "reference_number", 100),
            "issuing_authority": _str(row, "issuing_authority", 200),
            "issuing_date": _str(row, "issuing_date", 80),
            "contact_person": _str(row, "contact_person", 120),
            "contact_number": _str(row, "contact_number", 100),
            "email": _str(row, "email", 150),
            "helpline_number": _str(row, "helpline_number", 100),
            "official_address": _str(row, "official_address", 300),
            "important_instructions": _str(row, "important_instructions", 400),
            "total_posts": row.get("total_posts"),
            "post_details": clean_posts,
            "qualification": _str(row, "qualification", 250),
            "age_limit": _str(row, "age_limit", 100),
            "age_relaxation": _str(row, "age_relaxation", 150),
            "pay_scale": _str(row, "pay_scale", 200),
            "salary_type": _str(row, "salary_type", 80),
            "application_fee": _str(row, "application_fee", 250),
            "application_start_date": _str(row, "application_start_date", 80),
            "last_date": _str(row, "last_date", 80),
            "apply_link": _str(row, "apply_link", 500),
            "advertisement_no": _str(row, "advertisement_no", 100),
            "how_to_apply": _str(row, "how_to_apply", 200),
            "documents_required": _str(row, "documents_required", 400),
            "selection_process": _str(row, "selection_process", 300),
            "experience_required": _str(row, "experience_required", 200),
            "posting_location": _str(row, "posting_location", 200),
            "reservation_details": _str(row, "reservation_details", 250),
            "bond_details": _str(row, "bond_details", 200),
            "interview_date": _str(row, "interview_date", 80),
            "interview_time": _str(row, "interview_time", 60),
            "venue": _str(row, "venue", 250),
            "reporting_time": _str(row, "reporting_time", 60),
            "engagement_type": _str(row, "engagement_type", 100),
            "result_for": _str(row, "result_for", 200),
            "exam_name": _str(row, "exam_name", 200),
            "session": _str(row, "session", 80),
            "semester": _str(row, "semester", 60),
            "result_date": _str(row, "result_date", 80),
            "result_link": _str(row, "result_link", 500),
            "result_type": _str(row, "result_type", 80),
            "merit_list_link": _str(row, "merit_list_link", 500),
            "cutoff_marks": _str(row, "cutoff_marks", 150),
            "total_selected": _str(row, "total_selected", 60),
            "next_stage": _str(row, "next_stage", 200),
            "next_stage_date": _str(row, "next_stage_date", 80),
            "roll_no_required": row.get("roll_no_required"),
            "rechecking_last_date": _str(row, "rechecking_last_date", 80),
            "rechecking_link": _str(row, "rechecking_link", 500),
            "rechecking_fee": _str(row, "rechecking_fee", 100),
            "rechecking_mode": _str(row, "rechecking_mode", 80),
            "exam_date": _str(row, "exam_date", 80),
            "exam_time": _str(row, "exam_time", 60),
            "exam_duration": _str(row, "exam_duration", 60),
            "exam_pattern": _str(row, "exam_pattern", 200),
            "exam_center": _str(row, "exam_center", 250),
            "download_start_date": _str(row, "download_start_date", 80),
            "download_last_date": _str(row, "download_last_date", 80),
            "admit_card_link": _str(row, "admit_card_link", 500),
            "instructions": _str(row, "instructions", 400),
            "download_mode": _str(row, "download_mode", 80),
            "total_questions": _str(row, "total_questions", 60),
            "answer_key_link": _str(row, "answer_key_link", 500),
            "objection_start_date": _str(row, "objection_start_date", 80),
            "objection_last_date": _str(row, "objection_last_date", 80),
            "objection_fee": _str(row, "objection_fee", 100),
            "per_question_fee": _str(row, "per_question_fee", 100),
            "objection_mode": _str(row, "objection_mode", 80),
            "objection_address": _str(row, "objection_address", 250),
            "payment_mode": _str(row, "payment_mode", 100),
            "answer_key_type": _str(row, "answer_key_type", 80),
            "course_name": _str(row, "course_name", 200),
            "course_duration": _str(row, "course_duration", 80),
            "university_name": _str(row, "university_name", 200),
            "eligibility": _str(row, "eligibility", 250),
            "eligibility_marks": _str(row, "eligibility_marks", 100),
            "age_criteria": _str(row, "age_criteria", 100),
            "fee_structure": _str(row, "fee_structure", 200),
            "apply_start_date": _str(row, "apply_start_date", 80),
            "counselling_date": _str(row, "counselling_date", 80),
            "admission_mode": _str(row, "admission_mode", 100),
            "total_seats": _str(row, "total_seats", 60),
            "entrance_exam_name": _str(row, "entrance_exam_name", 200),
            "hostel_available": _str(row, "hostel_available", 60),
            "prospectus_link": _str(row, "prospectus_link", 500),
            "round": _str(row, "round", 60),
            "counselling_time": _str(row, "counselling_time", 60),
            "seat_matrix": _str(row, "seat_matrix", 200),
            "registration_fee": _str(row, "registration_fee", 100),
            "choice_filling_dates": _str(row, "choice_filling_dates", 100),
            "required_documents": _str(row, "required_documents", 400),
            "counselling_mode": _str(row, "counselling_mode", 80),
            "next_round_date": _str(row, "next_round_date", 80),
            "scheme_name": _str(row, "scheme_name", 200),
            "scholarship_amount": _str(row, "scholarship_amount", 150),
            "scholarship_duration": _str(row, "scholarship_duration", 100),
            "applicable_category": _str(row, "applicable_category", 150),
            "income_limit": _str(row, "income_limit", 100),
            "apply_mode": _str(row, "apply_mode", 100),
            "portal_name": _str(row, "portal_name", 150),
            "disbursement_mode": _str(row, "disbursement_mode", 100),
            "renewal_criteria": _str(row, "renewal_criteria", 250),
            "income_certificate_required": _str(row, "income_certificate_required", 40),
            "caste_certificate_required": _str(row, "caste_certificate_required", 40),
            "selection_criteria": _str(row, "selection_criteria", 250),
            "helpline": _str(row, "helpline", 100),
            "exam_start_date": _str(row, "exam_start_date", 80),
            "exam_end_date": _str(row, "exam_end_date", 80),
            "timetable_link": _str(row, "timetable_link", 500),
            "subject_list": _str(row, "subject_list", 400),
            "paper_code": _str(row, "paper_code", 200),
            "practical_dates": _str(row, "practical_dates", 150),
            "viva_dates": _str(row, "viva_dates", 150),
            "tender_no": _str(row, "tender_no", 100),
            "tender_type": _str(row, "tender_type", 100),
            "work_description": _str(row, "work_description", 300),
            "estimated_cost": _str(row, "estimated_cost", 100),
            "emd_amount": _str(row, "emd_amount", 100),
            "emd_mode": _str(row, "emd_mode", 100),
            "tender_fee": _str(row, "tender_fee", 100),
            "tender_fee_mode": _str(row, "tender_fee_mode", 100),
            "submission_last_date": _str(row, "submission_last_date", 80),
            "opening_date": _str(row, "opening_date", 80),
            "pre_bid_meeting_date": _str(row, "pre_bid_meeting_date", 80),
            "pre_bid_meeting_venue": _str(row, "pre_bid_meeting_venue", 200),
            "submission_mode": _str(row, "submission_mode", 80),
            "tender_document_link": _str(row, "tender_document_link", 500),
            "bid_validity": _str(row, "bid_validity", 80),
            "completion_period": _str(row, "completion_period", 100),
            "payment_terms": _str(row, "payment_terms", 250),
            "eligibility_criteria": _str(row, "eligibility_criteria", 300),
            "gazette_no": _str(row, "gazette_no", 100),
            "gazette_type": _str(row, "gazette_type", 100),
            "publication_date": _str(row, "publication_date", 80),
            "gazette_link": _str(row, "gazette_link", 500),
            "gazette_content": _str(row, "gazette_content", 400),
            "notification_no": _str(row, "notification_no", 100),
            "land_location": _str(row, "land_location", 250),
            "affected_area": _str(row, "affected_area", 100),
            "plot_numbers": _str(row, "plot_numbers", 200),
            "khasra_no": _str(row, "khasra_no", 100),
            "thana_no": _str(row, "thana_no", 80),
            "district": _str(row, "district", 100),
            "tehsil": _str(row, "tehsil", 100),
            "village": _str(row, "village", 150),
            "notification_type": _str(row, "notification_type", 100),
            "effective_date": _str(row, "effective_date", 80),
            "order_link": _str(row, "order_link", 500),
            "compensation_details": _str(row, "compensation_details", 250),
            "objections_last_date": _str(row, "objections_last_date", 80),
            "objections_address": _str(row, "objections_address", 250),
            "land_type": _str(row, "land_type", 100),
            "issuing_department": _str(row, "issuing_department", 200),
            "release_date": _str(row, "release_date", 80),
            "release_link": _str(row, "release_link", 500),
            "full_content": _str(row, "full_content", 500),
            "announcement_type": _str(row, "announcement_type", 100),
            "target_audience": _str(row, "target_audience", 200),
            "action_required": _str(row, "action_required", 250),
            "action_deadline": _str(row, "action_deadline", 80),
            "publication_name": _str(row, "publication_name", 200),
            "publication_type": _str(row, "publication_type", 100),
            "publisher": _str(row, "publisher", 200),
            "download_link": _str(row, "download_link", 500),
            "author": _str(row, "author", 150),
            "pages": _str(row, "pages", 40),
            "language": _str(row, "language", 60),
            "edition": _str(row, "edition", 60),
            "isbn": _str(row, "isbn", 60),
            "price": _str(row, "price", 60),
            "subject": _str(row, "subject", 200),
            "notice_type": _str(row, "notice_type", 100),
            "applicable_to": _str(row, "applicable_to", 200),
            "supersedes": _str(row, "supersedes", 200),
            "extra_details": _clean_extra_details(row.get("extra_details")),
            "extra_details_present": bool(row.get("extra_details_present", False)),
        }
    if not result:
        raise RuntimeError("Gemini returned no usable classifications")
    return result


def _extract_gemini_text(data):
    candidates = None
    if isinstance(data, dict):
        candidates = data.get("candidates")
    elif isinstance(data, list):
        candidates = data
    if not isinstance(candidates, list) or not candidates:
        raise RuntimeError("Gemini returned no candidates")
    first = candidates[0]
    part_lists = []
    if isinstance(first, dict):
        content = first.get("content")
        if isinstance(content, dict):
            raw_parts = content.get("parts")
            if isinstance(raw_parts, list):
                part_lists.append(raw_parts)
        elif isinstance(content, list):
            part_lists.append(content)
    elif isinstance(first, list):
        part_lists.append(first)
    texts = []
    for parts in part_lists:
        for part in parts:
            if isinstance(part, dict):
                t = part.get("text")
                if isinstance(t, str) and t.strip():
                    texts.append(t)
    return "".join(texts).strip()


def gemini_classify(items, api_key, model, timeout):
    if not items:
        return {}
    prompt_items = [
        {
            "id": str(i),
            "title": item["title"],
            "url": item["url"],
            "context": item.get("context", "")[:500],
            "pdf_text": item.get("pdf_text", "")[:3000],
        }
        for i, item in enumerate(items)
    ]
    prompt = _build_prompt(prompt_items)
    endpoint = f"https://generativelanguage.googleapis.com/v1beta/models/{model}:generateContent"
    payload = {
        "contents": [{"parts": [{"text": prompt}]}],
        "generationConfig": {
            "responseMimeType": "application/json",
            "maxOutputTokens": GEMINI_MAX_OUTPUT_TOKENS,
            "temperature": 0.1,
        },
    }
    last_error = "Gemini classification failed"
    for attempt in range(3):
        try:
            response, key_used, reason = _gemini_post_with_rotation(endpoint, payload, timeout=timeout)
            if response is None:
                if reason == "all_keys_quota_exhausted":
                    raise RuntimeError("All Gemini keys quota-exhausted")
                raise RuntimeError(f"Gemini keys unavailable: {reason}")
            if response.status_code in (500, 502, 503, 504):
                last_error = f"Gemini HTTP {response.status_code}"
                if attempt < 2:
                    time.sleep(min(10, 2 ** attempt))
                    continue
                raise RuntimeError(last_error)
            if response.status_code == 404:
                _DEAD_MODELS.add(model)
                raise RuntimeError(f"Gemini model unavailable: {model}")
            if response.status_code >= 400:
                raise RuntimeError(f"Gemini HTTP {response.status_code}: {clean_text(response.text, 500)}")
            data = response.json()
            response_text = _extract_gemini_text(data)
            if not response_text:
                raise RuntimeError("Gemini returned empty response")
            return _parse_gemini_response(response_text, len(items))
        except (requests.RequestException, ValueError, KeyError, TypeError, RuntimeError) as exc:
            last_error = str(exc)
            if attempt < 2:
                time.sleep(min(10, 2 ** attempt))
    raise RuntimeError(last_error)


def gemini_classify_with_fallback(items, api_key, timeout):
    global _GEMINI_QUOTA_EXHAUSTED, _GEMINI_KEY_INDEX
    if _GEMINI_QUOTA_EXHAUSTED or not _has_live_gemini_keys():
        print("[GEMINI] No usable Gemini keys; using keyword fallback.", file=sys.stderr)
        return keyword_fallback(items)
    seen = []
    for model in _DYNAMIC_MODELS:
        if model in seen or model in _DEAD_MODELS:
            continue
        seen.append(model)
        try:
            result = gemini_classify(items, api_key, model, timeout)
            if result:
                print(f"[INFO] Gemini classify success: {model}")
                return result
        except Exception as exc:
            err_str = str(exc)
            if "all gemini keys quota-exhausted" in err_str.lower():
                _GEMINI_QUOTA_EXHAUSTED = True
                print("[QUOTA] All Gemini keys quota-exhausted; using keyword fallback.", file=sys.stderr)
                break
            print(f"[WARN] Classify {model} failed: {clean_text(err_str, 200)}", file=sys.stderr)
            continue
    print("[WARN] Gemini classification unavailable. Using keyword fallback.", file=sys.stderr)
    return keyword_fallback(items)


# ---------------------------------------------------------------------------
# Telegram
# ---------------------------------------------------------------------------

def telegram_request(method, token, payload, timeout=20):
    return requests.post(f"https://api.telegram.org/bot{token}/{method}", json=payload, timeout=timeout)


def validate_telegram_token(token):
    response = telegram_request("getMe", token, {}, timeout=15)
    if not response.ok:
        raise RuntimeError(f"Telegram bot token invalid: HTTP {response.status_code}: {clean_text(response.text, 300)}")


def send_telegram(token, chat_id, text):
    for attempt in range(3):
        try:
            response = telegram_request("sendMessage", token, {
                "chat_id": chat_id, "text": text,
                "parse_mode": "HTML", "disable_web_page_preview": False,
            })
            if response.ok:
                return (True, False, "sent")
            try:
                data = response.json()
                description = clean_text(str(data.get("description", response.text)), 400)
                retry_after = int((data.get("parameters") or {}).get("retry_after", 0) or 0)
            except Exception:
                description = clean_text(response.text, 400)
                retry_after = 0
            if response.status_code in (400, 401, 403, 404):
                return (False, True, f"Telegram HTTP {response.status_code}: {description}")
            if response.status_code == 429 and attempt < 2:
                time.sleep(min(max(retry_after + 1, 2), 60))
                continue
            if response.status_code >= 500 and attempt < 2:
                time.sleep(min(10, 2 ** attempt))
                continue
            return (False, False, f"Telegram HTTP {response.status_code}: {description}")
        except requests.RequestException as exc:
            if attempt < 2:
                time.sleep(min(10, 2 ** attempt))
                continue
            return (False, False, f"Telegram network error: {exc}")
    return (False, False, "Telegram send failed")


def send_telegram_document(token, chat_id, pdf_bytes, filename, caption=""):
    for attempt in range(3):
        try:
            files = {"document": (filename, pdf_bytes, "application/pdf")}
            data = {
                "chat_id": chat_id,
                "caption": caption[:TELEGRAM_CAPTION_LIMIT],
                "parse_mode": "HTML",
            }
            response = requests.post(
                f"https://api.telegram.org/bot{token}/sendDocument",
                data=data, files=files, timeout=60,
            )
            if response.ok:
                return (True, False, "sent")
            try:
                rdata = response.json()
                description = clean_text(str(rdata.get("description", response.text)), 400)
                retry_after = int((rdata.get("parameters") or {}).get("retry_after", 0) or 0)
            except Exception:
                description = clean_text(response.text, 400)
                retry_after = 0
            if response.status_code in (400, 401, 403, 404):
                return (False, True, f"Telegram HTTP {response.status_code}: {description}")
            if response.status_code == 429 and attempt < 2:
                time.sleep(min(max(retry_after + 1, 2), 60))
                continue
            if response.status_code >= 500 and attempt < 2:
                time.sleep(min(10, 2 ** attempt))
                continue
            return (False, False, f"Telegram HTTP {response.status_code}: {description}")
        except requests.RequestException as exc:
            if attempt < 2:
                time.sleep(min(10, 2 ** attempt))
                continue
            return (False, False, f"Telegram network error: {exc}")
    return (False, False, "Telegram send document failed")


def _safe_filename(url, default="notice.pdf"):
    try:
        parsed = urlparse(url)
        name = parsed.path.rsplit("/", 1)[-1]
        if name and name.lower().endswith(".pdf"):
            cleaned = unquote(name)
            cleaned = re.sub(r"[^\w\u0900-\u097F\-.]", "_", cleaned)
            return cleaned[:100]
        path = unquote(parsed.path or "").rstrip("/")
        slug = path.rsplit("/", 1)[-1]
        slug = re.sub(r"^(notice|document|page|post)[-_/]", "", slug, flags=re.I)
        slug = re.sub(r"[^\w\u0900-\u097F\-]", "_", slug)
        slug = re.sub(r"_+", "_", slug).strip("_")
        if slug and len(slug) >= 5:
            return f"{slug[:80]}.pdf"
    except Exception:
        pass
    return default


def _build_pdf_caption(full_message, classification):
    if not classification:
        return full_message[:TELEGRAM_CAPTION_LIMIT]
    priority_keys = [
        ("last_date", "Last Date"),
        ("submission_last_date", "Submission Last"),
        ("application_start_date", "App Starts"),
        ("apply_start_date", "App Starts"),
        ("exam_date", "Exam Date"),
        ("result_date", "Result Date"),
        ("total_posts", "Total Posts"),
        ("application_fee", "Fee"),
        ("pay_scale", "Pay"),
    ]
    parts = []
    for k, label in priority_keys:
        v = classification.get(k)
        if v:
            parts.append(f"• {label}: {v}")
    priority_block = ""
    if parts:
        priority_block = "\n\n━━━\n" + "\n".join(parts[:6])
    available = TELEGRAM_CAPTION_LIMIT - len(priority_block)
    if available > 200:
        caption = full_message[:available]
        last_nl = caption.rfind("\n")
        if last_nl > available * 0.7:
            caption = caption[:last_nl]
        return caption.rstrip() + priority_block
    return full_message[:TELEGRAM_CAPTION_LIMIT]


def send_notification_with_pdf(token, chat_id, record, full_message):
    pdf_url = record.get("url", "")
    filename = _safe_filename(pdf_url)
    pdf_bytes = _RUNTIME_PDF_CACHE.get(pdf_url)
    if pdf_bytes is None:
        try:
            session = make_session()
            content, actual_url, method = _download_with_pdf_resolution(session, pdf_url, 30)
            if content and len(content) <= MAX_PDF_SEND_BYTES:
                pdf_bytes = content
                _cache_put(pdf_url, content)
                if actual_url and actual_url != pdf_url:
                    _cache_put(actual_url, content)
                    new_name = _safe_filename(actual_url)
                    if new_name and new_name != "notice.pdf":
                        filename = new_name
        except Exception as exc:
            print(f"[WARN] PDF download for send failed: {exc}", file=sys.stderr)
    if not pdf_bytes:
        return send_telegram(token, chat_id, truncate_telegram(full_message))
    caption = _build_pdf_caption(full_message, record.get("classification"))
    if len(caption) > TELEGRAM_CAPTION_LIMIT:
        caption = caption[:TELEGRAM_CAPTION_LIMIT]
        last_nl = caption.rfind("\n")
        if last_nl > TELEGRAM_CAPTION_LIMIT * 0.7:
            caption = caption[:last_nl]
        caption = caption.rstrip()
    return send_telegram_document(token, chat_id, pdf_bytes, filename, caption=caption)


# ---------------------------------------------------------------------------
# Message formatting
# ---------------------------------------------------------------------------

CATEGORY_EMOJI = {
    "vacancy": "💼", "result": "📊", "admit_card": "🎫",
    "answer_key": "🔑", "admission": "🎓", "counselling": "🎯",
    "scholarship": "🎓", "exam_schedule": "📅", "tender": "📑",
    "gazette": "📰", "land_revenue": "🏞️", "press_release": "📢",
    "announcement": "📣", "publication": "📚", "notice": "📌", "other": "📎",
}


def _safe_str(value, limit=300):
    if value is None:
        return None
    text = clean_text(str(value), limit)
    return text or None


def _is_devanagari(s):
    if not s:
        return False
    dev_count = sum(1 for c in s if "\u0900" <= c <= "\u097F")
    return dev_count > len(s) * 0.3


_LABELS_HI = {
    "reference_number": "संदर्भ संख्या", "issuing_authority": "जारीकर्ता विभाग",
    "issuing_date": "जारी तारीख़", "contact_person": "संपर्क व्यक्ति",
    "contact_number": "संपर्क नंबर", "email": "ईमेल",
    "helpline_number": "हेल्पलाइन नंबर", "official_address": "कार्यालय पता",
    "important_instructions": "ज़रूरी निर्देश",
    "total_posts": "कुल पद", "post_breakdown": "पद की जानकारी",
    "qualification": "योग्यता", "age_limit": "उम्र सीमा",
    "age_relaxation": "उम्र में छूट", "pay_scale": "वेतन",
    "salary_type": "वेतन प्रकार", "application_fee": "फ़ीस / चार्जेस",
    "application_start_date": "आवेदन शुरू",
    "last_date": "आख़िरी तारीख़", "apply_online": "ऑनलाइन अप्लाई करें",
    "advertisement_no": "विज्ञापन संख्या", "how_to_apply": "कैसे अप्लाई करें",
    "documents_required": "ज़रूरी दस्तावेज़",
    "selection_process": "चयन प्रक्रिया",
    "experience_required": "अनुभव ज़रूरी",
    "posting_location": "पोस्टिंग स्थान",
    "reservation_details": "आरक्षण विवरण",
    "bond_details": "बॉन्ड विवरण",
    "interview_date": "इंटरव्यू की तारीख़", "interview_time": "इंटरव्यू का समय",
    "venue": "स्थान", "reporting_time": "रिपोर्टिंग समय",
    "engagement_type": "नियुक्ति प्रकार",
    "result_for": "रिजल्ट किसका है", "declared_on": "रिजल्ट की तारीख़",
    "check_result": "रिजल्ट देखें", "session": "सत्र",
    "semester": "सेमेस्टर", "result_type": "रिजल्ट प्रकार",
    "merit_list_link": "मेरिट लिस्ट देखें", "cutoff_marks": "कटऑफ़ मार्क्स",
    "total_selected": "कुल चयनित", "next_stage": "अगला स्टेज",
    "next_stage_date": "अगले स्टेज की तारीख़",
    "rechecking_last_date": "रीचेकिंग आख़िरी", "rechecking_link": "रीचेकिंग लिंक",
    "rechecking_fee": "रीचेकिंग शुल्क", "rechecking_mode": "रीचेकिंग मोड",
    "exam": "एग्ज़ाम", "exam_date": "एग्ज़ाम की तारीख़",
    "exam_time": "एग्ज़ाम का समय", "exam_duration": "एग्ज़ाम की अवधि",
    "exam_pattern": "एग्ज़ाम पैटर्न", "exam_center": "एग्ज़ाम सेंटर",
    "download_admit_card": "एडमिट कार्ड डाउनलोड करें",
    "download_start_date": "डाउनलोड शुरू", "download_last_date": "डाउनलोड आख़िरी",
    "instructions": "निर्देश", "download_mode": "डाउनलोड मोड",
    "view_answer_key": "आंसर की देखें", "total_questions": "कुल प्रश्न",
    "objection_start_date": "आपत्ति शुरू", "objection_last_date": "आपत्ति आख़िरी",
    "objection_fee": "आपत्ति शुल्क", "per_question_fee": "प्रति प्रश्न शुल्क",
    "objection_mode": "आपत्ति मोड", "objection_link": "आपत्ति दर्ज करें",
    "objection_address": "आपत्ति पता", "payment_mode": "भुगतान मोड",
    "answer_key_type": "आंसर की प्रकार",
    "course": "कोर्स", "course_duration": "कोर्स अवधि",
    "university_name": "यूनिवर्सिटी", "eligibility_marks": "योग्यता मार्क्स",
    "age_criteria": "उम्र मानदंड", "fee_structure": "फ़ीस संरचना",
    "apply_start_date": "आवेदन शुरू", "admission_mode": "एडमिशन मोड",
    "total_seats": "कुल सीटें", "entrance_exam_name": "एंट्रेंस एग्ज़ाम",
    "hostel_available": "हॉस्टल उपलब्ध", "prospectus_link": "प्रॉस्पेक्टस देखें",
    "counselling_date": "काउंसलिंग तारीख़", "counselling_time": "समय",
    "round": "राउंड", "seat_matrix": "सीट मैट्रिक्स",
    "registration_fee": "रजिस्ट्रेशन शुल्क",
    "choice_filling_dates": "चॉइस फिलिंग तारीख़ें",
    "required_documents": "ज़रूरी दस्तावेज़",
    "counselling_mode": "काउंसलिंग मोड", "next_round_date": "अगला राउंड",
    "scheme_name": "स्कीम", "amount": "अमाउंट / रकम",
    "scholarship_duration": "अवधि",
    "applicable_category": "किस श्रेणी के लिए", "income_limit": "आय सीमा",
    "apply_mode": "आवेदन मोड", "portal_name": "पोर्टल",
    "disbursement_mode": "भुगतान मोड", "renewal_criteria": "नवीनीकरण मानदंड",
    "income_certificate_required": "आय प्रमाण पत्र ज़रूरी",
    "caste_certificate_required": "जाति प्रमाण पत्र ज़रूरी",
    "selection_criteria": "चयन मानदंड", "helpline": "हेल्पलाइन",
    "exam_start_date": "एग्ज़ाम शुरू", "exam_end_date": "एग्ज़ाम ख़त्म",
    "timetable_link": "टाइम टेबल देखें", "subject_list": "विषय सूची",
    "paper_code": "पेपर कोड", "practical_dates": "प्रैक्टिकल तारीख़ें",
    "viva_dates": "वाइवा तारीख़ें",
    "tender_no": "निविदा संख्या", "tender_type": "निविदा प्रकार",
    "work_description": "कार्य विवरण", "estimated_cost": "अनुमानित लागत",
    "emd_amount": "EMD / बयाना राशि", "emd_mode": "EMD मोड",
    "tender_fee": "निविदा शुल्क", "tender_fee_mode": "निविदा शुल्क मोड",
    "submission_last_date": "जमा आख़िरी", "opening_date": "खोलने की तारीख़",
    "pre_bid_meeting_date": "प्री-बिड मीटिंग तारीख़",
    "pre_bid_meeting_venue": "प्री-बिड मीटिंग स्थान",
    "submission_mode": "जमा तरीक़ा", "download_tender": "निविदा डाउनलोड करें",
    "tender_document_link": "निविदा दस्तावेज़",
    "bid_validity": "बिड वैधता", "completion_period": "पूर्णता अवधि",
    "payment_terms": "भुगतान शर्तें", "eligibility_criteria": "पात्रता मानदंड",
    "gazette_no": "गजट संख्या", "gazette_type": "गजट प्रकार",
    "publication_date": "प्रकाशन तारीख़", "gazette_link": "गजट देखें",
    "gazette_content": "गजट विवरण",
    "notification_no": "अधिसूचना संख्या", "land_location": "भूमि स्थान",
    "affected_area": "प्रभावित क्षेत्र", "plot_numbers": "प्लॉट संख्या",
    "khasra_no": "खसरा संख्या", "thana_no": "थाना संख्या",
    "district": "ज़िला", "tehsil": "तहसील", "village": "गाँव",
    "notification_type": "अधिसूचना प्रकार", "effective_date": "प्रभावी तारीख़",
    "order_link": "आदेश देखें", "compensation_details": "मुआवज़ा विवरण",
    "objections_last_date": "आपत्ति आख़िरी",
    "objections_address": "आपत्ति पता", "land_type": "भूमि प्रकार",
    "issuing_department": "विभाग", "release_date": "जारी तारीख़",
    "release_link": "प्रेस रिलीज़ देखें", "full_content": "पूरा विवरण",
    "announcement_type": "घोषणा प्रकार",
    "target_audience": "किसके लिए", "action_required": "क्या करना है",
    "action_deadline": "करने की आख़िरी तारीख़",
    "publication_name": "प्रकाशन", "publication_type": "प्रकार",
    "publisher": "प्रकाशक", "download_link": "डाउनलोड करें",
    "author": "लेखक", "pages": "पृष्ठ", "language": "भाषा",
    "edition": "संस्करण", "isbn": "ISBN", "price": "क़ीमत",
    "subject": "विषय", "notice_type": "सूचना प्रकार",
    "applicable_to": "किस पर लागू", "supersedes": "किसे रद्द करता है",
    "other_details": "अन्य जानकारी",
    "read_full": "पूरी नोटिफिकेशन देखें",
}

_LABELS_EN = {
    "reference_number": "Reference No", "issuing_authority": "Issuing Authority",
    "issuing_date": "Issuing Date", "contact_person": "Contact Person",
    "contact_number": "Contact Number", "email": "Email",
    "helpline_number": "Helpline", "official_address": "Official Address",
    "important_instructions": "Important Instructions",
    "total_posts": "Total Posts", "post_breakdown": "Post-wise Breakdown",
    "qualification": "Qualification", "age_limit": "Age Limit",
    "age_relaxation": "Age Relaxation", "pay_scale": "Pay Scale",
    "salary_type": "Salary Type", "application_fee": "Application Fee",
    "application_start_date": "Application Starts",
    "last_date": "Last Date", "apply_online": "Apply Online",
    "advertisement_no": "Advertisement No", "how_to_apply": "How to Apply",
    "documents_required": "Documents Required",
    "selection_process": "Selection Process",
    "experience_required": "Experience Required",
    "posting_location": "Posting Location",
    "reservation_details": "Reservation Details",
    "bond_details": "Bond Details",
    "interview_date": "Interview Date", "interview_time": "Interview Time",
    "venue": "Venue", "reporting_time": "Reporting Time",
    "engagement_type": "Engagement Type",
    "result_for": "Result For", "declared_on": "Declared",
    "check_result": "Check Result", "session": "Session",
    "semester": "Semester", "result_type": "Result Type",
    "merit_list_link": "Merit List", "cutoff_marks": "Cutoff Marks",
    "total_selected": "Total Selected", "next_stage": "Next Stage",
    "next_stage_date": "Next Stage Date",
    "rechecking_last_date": "Rechecking Last Date", "rechecking_link": "Rechecking Link",
    "rechecking_fee": "Rechecking Fee", "rechecking_mode": "Rechecking Mode",
    "exam": "Exam", "exam_date": "Exam Date",
    "exam_time": "Exam Time", "exam_duration": "Exam Duration",
    "exam_pattern": "Exam Pattern", "exam_center": "Exam Center",
    "download_admit_card": "Download Admit Card",
    "download_start_date": "Download Starts", "download_last_date": "Download Last Date",
    "instructions": "Instructions", "download_mode": "Download Mode",
    "view_answer_key": "View Answer Key", "total_questions": "Total Questions",
    "objection_start_date": "Objection Starts", "objection_last_date": "Objection Last Date",
    "objection_fee": "Objection Fee", "per_question_fee": "Per Question Fee",
    "objection_mode": "Objection Mode", "objection_link": "File Objection",
    "objection_address": "Objection Address", "payment_mode": "Payment Mode",
    "answer_key_type": "Answer Key Type",
    "course": "Course", "course_duration": "Course Duration",
    "university_name": "University", "eligibility_marks": "Eligibility Marks",
    "age_criteria": "Age Criteria", "fee_structure": "Fee Structure",
    "apply_start_date": "Application Starts", "admission_mode": "Admission Mode",
    "total_seats": "Total Seats", "entrance_exam_name": "Entrance Exam",
    "hostel_available": "Hostel Available", "prospectus_link": "Prospectus",
    "counselling_date": "Counselling Date", "counselling_time": "Time",
    "round": "Round", "seat_matrix": "Seat Matrix",
    "registration_fee": "Registration Fee",
    "choice_filling_dates": "Choice Filling Dates",
    "required_documents": "Documents Required",
    "counselling_mode": "Counselling Mode", "next_round_date": "Next Round",
    "scheme_name": "Scheme", "amount": "Amount",
    "scholarship_duration": "Duration",
    "applicable_category": "Applicable Category", "income_limit": "Income Limit",
    "apply_mode": "Application Mode", "portal_name": "Portal",
    "disbursement_mode": "Disbursement Mode", "renewal_criteria": "Renewal Criteria",
    "income_certificate_required": "Income Certificate Required",
    "caste_certificate_required": "Caste Certificate Required",
    "selection_criteria": "Selection Criteria", "helpline": "Helpline",
    "exam_start_date": "Exam Starts", "exam_end_date": "Exam Ends",
    "timetable_link": "Timetable", "subject_list": "Subjects",
    "paper_code": "Paper Code", "practical_dates": "Practical Dates",
    "viva_dates": "Viva Dates",
    "tender_no": "Tender No", "tender_type": "Tender Type",
    "work_description": "Work Description", "estimated_cost": "Estimated Cost",
    "emd_amount": "EMD", "emd_mode": "EMD Mode",
    "tender_fee": "Tender Fee", "tender_fee_mode": "Fee Mode",
    "submission_last_date": "Submission Last Date", "opening_date": "Opening Date",
    "pre_bid_meeting_date": "Pre-Bid Meeting Date",
    "pre_bid_meeting_venue": "Pre-Bid Meeting Venue",
    "submission_mode": "Submission Mode", "download_tender": "Download Tender",
    "tender_document_link": "Tender Document",
    "bid_validity": "Bid Validity", "completion_period": "Completion Period",
    "payment_terms": "Payment Terms", "eligibility_criteria": "Eligibility",
    "gazette_no": "Gazette No", "gazette_type": "Gazette Type",
    "publication_date": "Publication Date", "gazette_link": "View Gazette",
    "gazette_content": "Gazette Content",
    "notification_no": "Notification No", "land_location": "Land Location",
    "affected_area": "Affected Area", "plot_numbers": "Plot Numbers",
    "khasra_no": "Khasra No", "thana_no": "Thana No",
    "district": "District", "tehsil": "Tehsil", "village": "Village",
    "notification_type": "Notification Type", "effective_date": "Effective Date",
    "order_link": "View Order", "compensation_details": "Compensation Details",
    "objections_last_date": "Objections Last Date",
    "objections_address": "Objections Address", "land_type": "Land Type",
    "issuing_department": "Department", "release_date": "Release Date",
    "release_link": "View Press Release", "full_content": "Full Content",
    "announcement_type": "Announcement Type",
    "target_audience": "Target Audience", "action_required": "Action Required",
    "action_deadline": "Action Deadline",
    "publication_name": "Publication", "publication_type": "Type",
    "publisher": "Publisher", "download_link": "Download",
    "author": "Author", "pages": "Pages", "language": "Language",
    "edition": "Edition", "isbn": "ISBN", "price": "Price",
    "subject": "Subject", "notice_type": "Notice Type",
    "applicable_to": "Applicable To", "supersedes": "Supersedes",
    "other_details": "Other Details",
    "read_full": "View Full Notice",
}

_CATEGORY_NAMES_HI = {
    "vacancy": "भर्ती", "result": "रिजल्ट", "admit_card": "एडमिट कार्ड",
    "answer_key": "आंसर की", "admission": "एडमिशन", "counselling": "काउंसलिंग",
    "scholarship": "स्कॉलरशिप", "exam_schedule": "एग्ज़ाम शेड्यूल",
    "tender": "टेंडर", "gazette": "गजट", "land_revenue": "भू-अर्जन / राजस्व",
    "press_release": "प्रेस रिलीज़", "announcement": "घोषणा",
    "publication": "प्रकाशन", "notice": "सूचना", "other": "अन्य",
}

_CATEGORY_NAMES_EN = {
    "vacancy": "Vacancy", "result": "Result", "admit_card": "Admit Card",
    "answer_key": "Answer Key", "admission": "Admission", "counselling": "Counselling",
    "scholarship": "Scholarship", "exam_schedule": "Exam Schedule",
    "tender": "Tender", "gazette": "Gazette", "land_revenue": "Land / Revenue",
    "press_release": "Press Release", "announcement": "Announcement",
    "publication": "Publication", "notice": "Notice", "other": "Other",
}

_DISCLAIMER_HI = "⚠️ एक बार ऑफिशियल नोटिफिकेशन ज़रूर पढ़ें — सभी डिटेल्स खुद कन्फर्म कर लें।"
_DISCLAIMER_EN = "⚠️ Please read the official notification once to confirm all details."


def _labels(key):
    if NOTIFY_LANGUAGE == "hi":
        return _LABELS_HI.get(key, _LABELS_EN.get(key, key))
    if NOTIFY_LANGUAGE == "en":
        return _LABELS_EN.get(key, key)
    hi = _LABELS_HI.get(key, key)
    en = _LABELS_EN.get(key, key)
    if hi == en:
        return hi
    return f"{hi} / {en}"


def _category_name(category):
    if NOTIFY_LANGUAGE == "hi":
        return _CATEGORY_NAMES_HI.get(category, category)
    if NOTIFY_LANGUAGE == "en":
        return _CATEGORY_NAMES_EN.get(category, category)
    hi = _CATEGORY_NAMES_HI.get(category, category)
    en = _CATEGORY_NAMES_EN.get(category, category)
    if hi == en:
        return hi
    return f"{hi} / {en}"


def _disclaimer_block():
    lines = ["", "━━━━━━━━━━━━━━━"]
    if NOTIFY_LANGUAGE in ("hi", "both"):
        lines.append(f"<i>{html.escape(_DISCLAIMER_HI)}</i>")
    if NOTIFY_LANGUAGE in ("en", "both"):
        lines.append(f"<i>{html.escape(_DISCLAIMER_EN)}</i>")
    return lines


def _line(lines, emoji, label, value):
    if value:
        lines.append(f"{emoji} <b>{_labels(label)}:</b> {html.escape(str(value))}")


def _link_line(lines, emoji, label, url):
    if url:
        lines.append(f'{emoji} <a href="{html.escape(url, quote=True)}">{html.escape(_labels(label))}</a>')


def _format_extra_details(lines, c):
    details = c.get("extra_details") or []
    if not details:
        return
    lines.append("")
    lines.append(f"📋 <b>{_labels('other_details')}:</b>")
    for d in details[:10]:
        label = _safe_str(d.get("label"), 100)
        value = _safe_str(d.get("value"), 300)
        if label and value:
            lines.append(f"   • <b>{html.escape(label)}:</b> {html.escape(value)}")


def _format_vacancy(lines, c):
    total = c.get("total_posts")
    if total:
        lines.append(f"📊 <b>{_labels('total_posts')}:</b> {html.escape(str(total))}")
    pd_list = c.get("post_details") or []
    if pd_list:
        lines.append(f"📋 <b>{_labels('post_breakdown')}:</b>")
        for pd in pd_list[:10]:
            pname = html.escape(_safe_str(pd.get("post_name"), 120) or "Post")
            cat = html.escape(_safe_str(pd.get("category"), 40) or "-")
            vac = pd.get("vacancies")
            vac_str = f" — {vac}" if vac is not None else ""
            lines.append(f"   • {pname} ({cat}){vac_str}")
    _line(lines, "📋", "advertisement_no", _safe_str(c.get("advertisement_no")))
    _line(lines, "🏢", "issuing_authority", _safe_str(c.get("issuing_authority")))
    _line(lines, "🎓", "qualification", _safe_str(c.get("qualification")))
    _line(lines, "🎂", "age_limit", _safe_str(c.get("age_limit")))
    _line(lines, "🎂", "age_relaxation", _safe_str(c.get("age_relaxation")))
    _line(lines, "📋", "engagement_type", _safe_str(c.get("engagement_type")))
    _line(lines, "📋", "salary_type", _safe_str(c.get("salary_type")))
    _line(lines, "💰", "pay_scale", _safe_str(c.get("pay_scale")))
    _line(lines, "📋", "experience_required", _safe_str(c.get("experience_required")))
    _line(lines, "📋", "posting_location", _safe_str(c.get("posting_location")))
    _line(lines, "📋", "reservation_details", _safe_str(c.get("reservation_details")))
    _line(lines, "💳", "application_fee", _safe_str(c.get("application_fee")))
    _line(lines, "📋", "how_to_apply", _safe_str(c.get("how_to_apply")))
    _line(lines, "📋", "selection_process", _safe_str(c.get("selection_process")))
    _line(lines, "📋", "documents_required", _safe_str(c.get("documents_required")))
    _line(lines, "📅", "application_start_date", _safe_str(c.get("application_start_date")))
    _line(lines, "📅", "last_date", _safe_str(c.get("last_date")))
    _line(lines, "📅", "interview_date", _safe_str(c.get("interview_date")))
    _line(lines, "⏰", "interview_time", _safe_str(c.get("interview_time")))
    _line(lines, "⏰", "reporting_time", _safe_str(c.get("reporting_time")))
    _line(lines, "📍", "venue", _safe_str(c.get("venue")))
    _line(lines, "📋", "bond_details", _safe_str(c.get("bond_details")))
    _line(lines, "📞", "contact_number", _safe_str(c.get("contact_number")))
    _line(lines, "📧", "email", _safe_str(c.get("email")))
    _link_line(lines, "🌐", "apply_online", _safe_str(c.get("apply_link"), 500))
    _format_extra_details(lines, c)


def _format_result(lines, c):
    _line(lines, "📝", "result_for", _safe_str(c.get("result_for")))
    _line(lines, "📝", "exam", _safe_str(c.get("exam_name")))
    _line(lines, "📅", "session", _safe_str(c.get("session")))
    _line(lines, "📚", "semester", _safe_str(c.get("semester")))
    _line(lines, "📋", "result_type", _safe_str(c.get("result_type")))
    _line(lines, "📅", "declared_on", _safe_str(c.get("result_date")))
    _line(lines, "📊", "total_selected", _safe_str(c.get("total_selected")))
    _line(lines, "📋", "cutoff_marks", _safe_str(c.get("cutoff_marks")))
    _link_line(lines, "📄", "check_result", _safe_str(c.get("result_link"), 500))
    _link_line(lines, "📄", "merit_list_link", _safe_str(c.get("merit_list_link"), 500))
    _line(lines, "📋", "next_stage", _safe_str(c.get("next_stage")))
    _line(lines, "📅", "next_stage_date", _safe_str(c.get("next_stage_date")))
    _line(lines, "🔄", "rechecking_last_date", _safe_str(c.get("rechecking_last_date")))
    _line(lines, "💳", "rechecking_fee", _safe_str(c.get("rechecking_fee")))
    _link_line(lines, "🔗", "rechecking_link", _safe_str(c.get("rechecking_link"), 500))
    _line(lines, "📞", "helpline_number", _safe_str(c.get("helpline_number")))
    _format_extra_details(lines, c)


def _format_admit_card(lines, c):
    _line(lines, "📝", "exam", _safe_str(c.get("exam_name")))
    _line(lines, "📅", "session", _safe_str(c.get("session")))
    _line(lines, "📚", "semester", _safe_str(c.get("semester")))
    _line(lines, "📅", "exam_date", _safe_str(c.get("exam_date")))
    _line(lines, "⏰", "exam_time", _safe_str(c.get("exam_time")))
    _line(lines, "⏱️", "exam_duration", _safe_str(c.get("exam_duration")))
    _line(lines, "📋", "exam_pattern", _safe_str(c.get("exam_pattern")))
    _line(lines, "📍", "exam_center", _safe_str(c.get("exam_center")))
    _line(lines, "⏰", "reporting_time", _safe_str(c.get("reporting_time")))
    _line(lines, "⬇️", "download_start_date", _safe_str(c.get("download_start_date")))
    _line(lines, "📅", "download_last_date", _safe_str(c.get("download_last_date")))
    _line(lines, "📋", "instructions", _safe_str(c.get("instructions")))
    _line(lines, "📞", "helpline_number", _safe_str(c.get("helpline_number")))
    _link_line(lines, "🎫", "download_admit_card", _safe_str(c.get("admit_card_link"), 500))
    _format_extra_details(lines, c)


def _format_answer_key(lines, c):
    _line(lines, "📝", "exam", _safe_str(c.get("exam_name")))
    _line(lines, "📅", "session", _safe_str(c.get("session")))
    _line(lines, "📅", "exam_date", _safe_str(c.get("exam_date")))
    _line(lines, "📋", "total_questions", _safe_str(c.get("total_questions")))
    _line(lines, "📋", "answer_key_type", _safe_str(c.get("answer_key_type")))
    _link_line(lines, "🔑", "view_answer_key", _safe_str(c.get("answer_key_link"), 500))
    _line(lines, "📅", "objection_start_date", _safe_str(c.get("objection_start_date")))
    _line(lines, "📅", "objection_last_date", _safe_str(c.get("objection_last_date")))
    _line(lines, "💳", "objection_fee", _safe_str(c.get("objection_fee")))
    _line(lines, "💳", "per_question_fee", _safe_str(c.get("per_question_fee")))
    _line(lines, "📋", "objection_mode", _safe_str(c.get("objection_mode")))
    _line(lines, "💳", "payment_mode", _safe_str(c.get("payment_mode")))
    _line(lines, "📍", "objection_address", _safe_str(c.get("objection_address")))
    _link_line(lines, "🔗", "objection_link", _safe_str(c.get("objection_link"), 500))
    _format_extra_details(lines, c)


def _format_admission(lines, c):
    _line(lines, "🎓", "course", _safe_str(c.get("course_name")))
    _line(lines, "📅", "course_duration", _safe_str(c.get("course_duration")))
    _line(lines, "🏛️", "university_name", _safe_str(c.get("university_name")))
    _line(lines, "📅", "session", _safe_str(c.get("session")))
    _line(lines, "📋", "admission_mode", _safe_str(c.get("admission_mode")))
    _line(lines, "📋", "entrance_exam_name", _safe_str(c.get("entrance_exam_name")))
    _line(lines, "📊", "total_seats", _safe_str(c.get("total_seats")))
    _line(lines, "✅", "eligibility", _safe_str(c.get("eligibility")))
    _line(lines, "📋", "eligibility_marks", _safe_str(c.get("eligibility_marks")))
    _line(lines, "🎂", "age_criteria", _safe_str(c.get("age_criteria")))
    _line(lines, "💳", "application_fee", _safe_str(c.get("application_fee")))
    _line(lines, "💰", "fee_structure", _safe_str(c.get("fee_structure")))
    _line(lines, "📋", "hostel_available", _safe_str(c.get("hostel_available")))
    _line(lines, "📋", "documents_required", _safe_str(c.get("documents_required")))
    _line(lines, "📅", "apply_start_date", _safe_str(c.get("apply_start_date")))
    _line(lines, "📅", "last_date", _safe_str(c.get("last_date")))
    _line(lines, "🎯", "counselling_date", _safe_str(c.get("counselling_date")))
    _link_line(lines, "📄", "prospectus_link", _safe_str(c.get("prospectus_link"), 500))
    _link_line(lines, "🌐", "apply_online", _safe_str(c.get("apply_link"), 500))
    _format_extra_details(lines, c)


def _format_counselling(lines, c):
    _line(lines, "🎓", "course", _safe_str(c.get("course_name")))
    _line(lines, "🔢", "round", _safe_str(c.get("round")))
    _line(lines, "📅", "counselling_date", _safe_str(c.get("counselling_date")))
    _line(lines, "⏰", "counselling_time", _safe_str(c.get("counselling_time")))
    _line(lines, "📍", "venue", _safe_str(c.get("venue")))
    _line(lines, "💳", "registration_fee", _safe_str(c.get("registration_fee")))
    _line(lines, "📋", "seat_matrix", _safe_str(c.get("seat_matrix")))
    _line(lines, "📅", "choice_filling_dates", _safe_str(c.get("choice_filling_dates")))
    _line(lines, "📋", "required_documents", _safe_str(c.get("required_documents")))
    _line(lines, "📋", "counselling_mode", _safe_str(c.get("counselling_mode")))
    _line(lines, "📅", "next_round_date", _safe_str(c.get("next_round_date")))
    _link_line(lines, "🌐", "apply_online", _safe_str(c.get("apply_link"), 500))
    _format_extra_details(lines, c)


def _format_scholarship(lines, c):
    _line(lines, "🎯", "scheme_name", _safe_str(c.get("scheme_name")))
    _line(lines, "💰", "amount", _safe_str(c.get("scholarship_amount")))
    _line(lines, "📅", "scholarship_duration", _safe_str(c.get("scholarship_duration")))
    _line(lines, "👥", "applicable_category", _safe_str(c.get("applicable_category")))
    _line(lines, "💵", "income_limit", _safe_str(c.get("income_limit")))
    _line(lines, "🎓", "eligibility", _safe_str(c.get("eligibility")))
    _line(lines, "📋", "renewal_criteria", _safe_str(c.get("renewal_criteria")))
    _line(lines, "📋", "selection_criteria", _safe_str(c.get("selection_criteria")))
    _line(lines, "📋", "income_certificate_required", _safe_str(c.get("income_certificate_required")))
    _line(lines, "📋", "caste_certificate_required", _safe_str(c.get("caste_certificate_required")))
    _line(lines, "📋", "apply_mode", _safe_str(c.get("apply_mode")))
    _line(lines, "📋", "portal_name", _safe_str(c.get("portal_name")))
    _line(lines, "💳", "disbursement_mode", _safe_str(c.get("disbursement_mode")))
    _line(lines, "📅", "last_date", _safe_str(c.get("last_date")))
    _line(lines, "📞", "helpline", _safe_str(c.get("helpline")))
    _link_line(lines, "🌐", "apply_online", _safe_str(c.get("apply_link"), 500))
    _format_extra_details(lines, c)


def _format_exam_schedule(lines, c):
    _line(lines, "📝", "exam", _safe_str(c.get("exam_name")))
    _line(lines, "📅", "session", _safe_str(c.get("session")))
    _line(lines, "📚", "semester", _safe_str(c.get("semester")))
    _line(lines, "🎓", "course", _safe_str(c.get("course_name")))
    _line(lines, "📅", "exam_start_date", _safe_str(c.get("exam_start_date")))
    _line(lines, "📅", "exam_end_date", _safe_str(c.get("exam_end_date")))
    _line(lines, "⏰", "exam_time", _safe_str(c.get("exam_time")))
    _line(lines, "📍", "exam_center", _safe_str(c.get("exam_center")))
    _line(lines, "📋", "subject_list", _safe_str(c.get("subject_list")))
    _line(lines, "📋", "paper_code", _safe_str(c.get("paper_code")))
    _line(lines, "📅", "practical_dates", _safe_str(c.get("practical_dates")))
    _line(lines, "📅", "viva_dates", _safe_str(c.get("viva_dates")))
    _line(lines, "⏰", "reporting_time", _safe_str(c.get("reporting_time")))
    _link_line(lines, "📄", "timetable_link", _safe_str(c.get("timetable_link"), 500))
    _format_extra_details(lines, c)


def _format_tender(lines, c):
    _line(lines, "📋", "tender_no", _safe_str(c.get("tender_no")))
    _line(lines, "📋", "tender_type", _safe_str(c.get("tender_type")))
    _line(lines, "📝", "work_description", _safe_str(c.get("work_description")))
    _line(lines, "🏢", "issuing_authority", _safe_str(c.get("issuing_authority")))
    _line(lines, "💰", "estimated_cost", _safe_str(c.get("estimated_cost")))
    _line(lines, "💳", "emd_amount", _safe_str(c.get("emd_amount")))
    _line(lines, "💳", "emd_mode", _safe_str(c.get("emd_mode")))
    _line(lines, "📄", "tender_fee", _safe_str(c.get("tender_fee")))
    _line(lines, "💳", "tender_fee_mode", _safe_str(c.get("tender_fee_mode")))
    _line(lines, "📅", "pre_bid_meeting_date", _safe_str(c.get("pre_bid_meeting_date")))
    _line(lines, "📍", "pre_bid_meeting_venue", _safe_str(c.get("pre_bid_meeting_venue")))
    _line(lines, "📅", "submission_last_date", _safe_str(c.get("submission_last_date")))
    _line(lines, "📅", "opening_date", _safe_str(c.get("opening_date")))
    _line(lines, "📅", "bid_validity", _safe_str(c.get("bid_validity")))
    _line(lines, "📅", "completion_period", _safe_str(c.get("completion_period")))
    _line(lines, "🌐", "submission_mode", _safe_str(c.get("submission_mode")))
    _line(lines, "📋", "eligibility_criteria", _safe_str(c.get("eligibility_criteria")))
    _line(lines, "💳", "payment_terms", _safe_str(c.get("payment_terms")))
    _link_line(lines, "📄", "tender_document_link", _safe_str(c.get("tender_document_link"), 500))
    _link_line(lines, "🔗", "download_tender", _safe_str(c.get("apply_link"), 500))
    _format_extra_details(lines, c)


def _format_gazette(lines, c):
    _line(lines, "📋", "gazette_no", _safe_str(c.get("gazette_no")))
    _line(lines, "📰", "gazette_type", _safe_str(c.get("gazette_type")))
    _line(lines, "📝", "subject", _safe_str(c.get("subject")))
    _line(lines, "🏢", "issuing_authority", _safe_str(c.get("issuing_authority")))
    _line(lines, "📅", "publication_date", _safe_str(c.get("publication_date")))
    _line(lines, "📅", "effective_date", _safe_str(c.get("effective_date")))
    _line(lines, "📋", "gazette_content", _safe_str(c.get("gazette_content")))
    _link_line(lines, "🔗", "gazette_link", _safe_str(c.get("gazette_link"), 500))
    _format_extra_details(lines, c)


def _format_land_revenue(lines, c):
    _line(lines, "📋", "notification_no", _safe_str(c.get("notification_no")))
    _line(lines, "📝", "subject", _safe_str(c.get("subject")))
    _line(lines, "🔖", "notification_type", _safe_str(c.get("notification_type")))
    _line(lines, "🏞️", "land_location", _safe_str(c.get("land_location")))
    _line(lines, "📍", "village", _safe_str(c.get("village")))
    _line(lines, "📍", "tehsil", _safe_str(c.get("tehsil")))
    _line(lines, "📍", "district", _safe_str(c.get("district")))
    _line(lines, "📐", "plot_numbers", _safe_str(c.get("plot_numbers")))
    _line(lines, "📐", "khasra_no", _safe_str(c.get("khasra_no")))
    _line(lines, "📐", "thana_no", _safe_str(c.get("thana_no")))
    _line(lines, "📐", "affected_area", _safe_str(c.get("affected_area")))
    _line(lines, "📋", "land_type", _safe_str(c.get("land_type")))
    _line(lines, "💰", "compensation_details", _safe_str(c.get("compensation_details")))
    _line(lines, "🏢", "issuing_authority", _safe_str(c.get("issuing_authority")))
    _line(lines, "📅", "effective_date", _safe_str(c.get("effective_date")))
    _line(lines, "📅", "objections_last_date", _safe_str(c.get("objections_last_date")))
    _line(lines, "📍", "objections_address", _safe_str(c.get("objections_address")))
    _link_line(lines, "🔗", "order_link", _safe_str(c.get("order_link"), 500))
    _format_extra_details(lines, c)


def _format_press_release(lines, c):
    _line(lines, "📝", "subject", _safe_str(c.get("subject")))
    _line(lines, "🏢", "issuing_department", _safe_str(c.get("issuing_department")))
    _line(lines, "📅", "release_date", _safe_str(c.get("release_date")))
    _line(lines, "🔖", "reference_no", _safe_str(c.get("reference_number")))
    _line(lines, "📋", "full_content", _safe_str(c.get("full_content")))
    _link_line(lines, "🔗", "release_link", _safe_str(c.get("release_link"), 500))
    _format_extra_details(lines, c)


def _format_announcement(lines, c):
    _line(lines, "📝", "subject", _safe_str(c.get("subject")))
    _line(lines, "🏢", "issuing_authority", _safe_str(c.get("issuing_authority")))
    _line(lines, "🔖", "reference_no", _safe_str(c.get("reference_number")))
    _line(lines, "📋", "announcement_type", _safe_str(c.get("announcement_type")))
    _line(lines, "👥", "target_audience", _safe_str(c.get("target_audience")))
    _line(lines, "📋", "action_required", _safe_str(c.get("action_required")))
    _line(lines, "📅", "action_deadline", _safe_str(c.get("action_deadline")))
    _line(lines, "📅", "effective_date", _safe_str(c.get("effective_date")))
    _link_line(lines, "🌐", "apply_online", _safe_str(c.get("apply_link"), 500))
    _format_extra_details(lines, c)


def _format_publication(lines, c):
    _line(lines, "📚", "publication_name", _safe_str(c.get("publication_name")))
    _line(lines, "🔖", "publication_type", _safe_str(c.get("publication_type")))
    _line(lines, "✍️", "author", _safe_str(c.get("author")))
    _line(lines, "🏢", "publisher", _safe_str(c.get("publisher")))
    _line(lines, "📅", "publication_date", _safe_str(c.get("publication_date")))
    _line(lines, "📋", "language", _safe_str(c.get("language")))
    _line(lines, "📋", "edition", _safe_str(c.get("edition")))
    _line(lines, "📋", "pages", _safe_str(c.get("pages")))
    _line(lines, "📋", "isbn", _safe_str(c.get("isbn")))
    _line(lines, "💰", "price", _safe_str(c.get("price")))
    _link_line(lines, "🔗", "download_link", _safe_str(c.get("download_link"), 500))
    _format_extra_details(lines, c)


def _format_notice(lines, c):
    _line(lines, "📝", "subject", _safe_str(c.get("subject")))
    _line(lines, "📋", "notice_type", _safe_str(c.get("notice_type")))
    _line(lines, "🔖", "reference_no", _safe_str(c.get("reference_number")))
    _line(lines, "🏢", "issuing_authority", _safe_str(c.get("issuing_authority")))
    _line(lines, "👥", "applicable_to", _safe_str(c.get("applicable_to")))
    _line(lines, "📋", "action_required", _safe_str(c.get("action_required")))
    _line(lines, "📅", "action_deadline", _safe_str(c.get("action_deadline")))
    _line(lines, "📋", "supersedes", _safe_str(c.get("supersedes")))
    _line(lines, "📅", "effective_date", _safe_str(c.get("effective_date")))
    _line(lines, "📋", "important_instructions", _safe_str(c.get("important_instructions")))
    _link_line(lines, "🔗", "order_link", _safe_str(c.get("order_link"), 500))
    _format_extra_details(lines, c)


_FORMATTERS = {
    "vacancy": _format_vacancy, "result": _format_result,
    "admit_card": _format_admit_card, "answer_key": _format_answer_key,
    "admission": _format_admission, "counselling": _format_counselling,
    "scholarship": _format_scholarship, "exam_schedule": _format_exam_schedule,
    "tender": _format_tender, "gazette": _format_gazette,
    "land_revenue": _format_land_revenue, "press_release": _format_press_release,
    "announcement": _format_announcement, "publication": _format_publication,
    "notice": _format_notice,
}


def format_message(site, item, classification=None):
    classification = classification or {}
    raw_title = clean_text(item.get("title", "Notification"), 300)
    if _is_language_selector(raw_title):
        raw_title = (
            clean_text(item.get("context", ""), 200)
            or _title_from_url(item.get("url", ""))
            or "Notification"
        )
    title_hi = _safe_str(classification.get("title_hi"), 200)
    title_is_hindi = _is_devanagari(raw_title)
    site_name = html.escape(site["name"])
    url = html.escape(item["url"], quote=True)
    summary = html.escape(_safe_str(classification.get("summary")) or "")
    category = (classification.get("category") or "notice").lower()
    emoji = CATEGORY_EMOJI.get(category, "📌")
    ocr_method = item.get("pdf_method", "")
    if ocr_method == "gemini":
        ocr_marker = " 🔍G"
    elif ocr_method == "rapidocr":
        ocr_marker = " 🔍R"
    else:
        ocr_marker = ""
    pdf_marker = " 📄" if item.get("is_pdf") else ""
    lines = [f"🔔 <b>{site_name}</b>{pdf_marker}", ""]
    lines.append(f"<b>{html.escape(raw_title)}</b>{ocr_marker}")
    if not title_is_hindi and title_hi and title_hi.strip().lower() != raw_title.strip().lower():
        if NOTIFY_LANGUAGE in ("both", "hi"):
            lines.append(f"<i>{html.escape(title_hi)}</i>")
    lines.append("")
    if summary:
        lines.append(summary)
        lines.append("")
    try:
        formatter = _FORMATTERS.get(category)
        if formatter:
            formatter(lines, classification)
    except Exception as exc:
        print(f"[WARN] Message formatting error: {exc}", file=sys.stderr)
    lines.append("")
    lines.append(f"{emoji} <b>{html.escape(_category_name(category))}</b>")
    lines.append(f'🔗 <a href="{url}">{html.escape(_labels("read_full"))}</a>')
    lines.extend(_disclaimer_block())
    return "\n".join(lines)


def truncate_telegram(text, limit=TELEGRAM_SAFE_LIMIT):
    if len(text) <= limit:
        return text
    truncated = text[:limit]
    last_nl = truncated.rfind("\n")
    if last_nl > limit * 0.7:
        truncated = truncated[:last_nl]
    return truncated.rstrip() + "\n\n<i>…(truncated)</i>"


# ---------------------------------------------------------------------------
# Prune / stats
# ---------------------------------------------------------------------------

def prune_state(state, retention_days, max_items=3000, max_pending_attempts=72, max_bytes=3000000):
    now = datetime.now(timezone.utc)
    cutoff = now - timedelta(days=retention_days)
    items = state.setdefault("items", {})
    remove = []
    terminal = {"sent", "ignored", "permanent_error", "baseline"}

    for key, record in list(items.items()):
        if not isinstance(record, dict):
            remove.append(key)
            continue

        status = record.get("status", "baseline")
        loaded_status = record.pop("_loaded_status", None)
        if status == "pending" and int(record.get("attempts", 0) or 0) >= max_pending_attempts:
            record["status"] = "permanent_error"
            record["last_error"] = clean_text(
                "Retry limit reached; last error: " + str(record.get("last_error") or "unknown"), 500
            )
            status = "permanent_error"
        telegram_attempts = int(record.get("telegram_attempts", 0) or 0)
        telegram_first_failed = _parse_utc_timestamp(record.get("telegram_first_failed_at"))
        telegram_window_expired = bool(
            telegram_first_failed
            and (now - telegram_first_failed).total_seconds() > TELEGRAM_RETRY_WINDOW_HOURS * 3600
        )
        if status == "ready" and (
            telegram_attempts >= TELEGRAM_MAX_ATTEMPTS or telegram_window_expired
        ):
            print(
                f"[ERROR] Telegram retry exhausted for {record.get('url', key)[:100]} "
                f"after {telegram_attempts} attempt(s); manual review required.",
                file=sys.stderr,
            )
            record["status"] = "permanent_error"
            record["last_error"] = clean_text(
                "Telegram retry window/attempt limit reached; last error: "
                + str(record.get("last_error") or "unknown"), 500
            )
            status = "permanent_error"

        if status in terminal:
            status_days = {"sent": 90, "ignored": 30, "baseline": 60, "permanent_error": retention_days}.get(status, retention_days)
            status_cutoff = now - timedelta(days=status_days)
            if not record.get("terminal_at"):
                if loaded_status and loaded_status not in terminal:
                    record["terminal_at"] = now.isoformat()
                else:
                    record["terminal_at"] = record.get("first_seen") or record.get("last_seen") or now.isoformat()
            record.pop("pdf_text", None)
            record.pop("classification", None)
            record.pop("summary", None)
            record.pop("pdf_extracted", None)
            record.pop("pdf_method", None)
            record.pop("ocr_used", None)
            if record.get("context"):
                record["context"] = clean_text(record.get("context"), 300)
            stamp = record.get("terminal_at")
            try:
                dt = datetime.fromisoformat(str(stamp).replace("Z", "+00:00"))
                if dt.tzinfo is None:
                    dt = dt.replace(tzinfo=timezone.utc)
            except Exception:
                dt = now
            if dt < status_cutoff:
                remove.append(key)
        else:
            record.pop("terminal_at", None)

    for key in remove:
        items.pop(key, None)

    review = state.setdefault("review_queue", {})
    review_cutoff = now - timedelta(days=90)
    for key, entry in list(review.items()):
        stamp = _parse_utc_timestamp(entry.get("updated_at") or entry.get("first_seen")) if isinstance(entry, dict) else None
        if not isinstance(entry, dict) or (stamp and stamp < review_cutoff and entry.get("status") != "open"):
            review.pop(key, None)
    if len(review) > 500:
        ordered = sorted(review.items(), key=lambda kv: str((kv[1] or {}).get("updated_at", "")))
        for key, _ in ordered[:len(review) - 500]:
            if review.get(key, {}).get("status") != "open":
                review.pop(key, None)

    if len(items) > max_items:
        terminal_rows = []
        active_rows = []
        for key, record in items.items():
            stamp = record.get("terminal_at") or record.get("last_seen") or record.get("first_seen") or ""
            row = (str(stamp), key)
            if record.get("status") in terminal:
                terminal_rows.append(row)
            else:
                active_rows.append(row)
        terminal_rows.sort()
        while len(items) > max_items and terminal_rows:
            _, key = terminal_rows.pop(0)
            items.pop(key, None)
        if len(items) > max_items:
            active_rows.sort(reverse=True)
            keep = {key for _, key in active_rows[:max_items - len(items) + len(active_rows)]}
            for _, key in active_rows:
                if len(items) <= max_items:
                    break
                if key in items and key not in keep:
                    items.pop(key, None)
            if len(items) > max_items:
                for _, key in sorted(active_rows):
                    if len(items) <= max_items:
                        break
                    items.pop(key, None)
            print("[WARN] State hard cap reached; oldest excess records were evicted.", file=sys.stderr)

    def serialized_size():
        try:
            payload = json.dumps(state, ensure_ascii=False, indent=2, separators=(",", ": ")) + "\n"
            return len(payload.encode("utf-8"))
        except (TypeError, ValueError):
            return max_bytes + 1

    for record in items.values():
        if not isinstance(record, dict):
            continue
        for field, limit in (("title", 300), ("context", 700), ("summary", 500), ("last_error", 500), ("pdf_text", MAX_PDF_TEXT_CHARS)):
            value = record.get(field)
            if isinstance(value, str) and len(value) > limit:
                record[field] = clean_text(value, limit)
        classification = record.get("classification")
        if isinstance(classification, dict):
            compact = {}
            for key, value in classification.items():
                if value is None or value == "" or value == []:
                    continue
                if key == "post_details" and isinstance(value, list):
                    compact[key] = value[:8]
                elif key == "extra_details" and isinstance(value, list):
                    compact[key] = value[:8]
                elif isinstance(value, str):
                    compact[key] = clean_text(value, 500)
                else:
                    compact[key] = value
            compact.setdefault("important", bool(classification.get("important", False)))
            compact.setdefault("category", classification.get("category", "notice"))
            record["classification"] = compact

    if serialized_size() > max_bytes:
        terminal_rows = []
        for key, record in items.items():
            if isinstance(record, dict) and record.get("status") in terminal:
                stamp = record.get("terminal_at") or record.get("first_seen") or record.get("last_seen") or ""
                terminal_rows.append((str(stamp), key))
        terminal_rows.sort()
        removed_terminal = 0
        for _, key in terminal_rows:
            items.pop(key, None)
            removed_terminal += 1
            if removed_terminal % 20 == 0 and serialized_size() <= max_bytes:
                break

    if serialized_size() > max_bytes:
        for record in items.values():
            if not isinstance(record, dict):
                continue
            status = record.get("status")
            if status == "ready" and record.get("classification"):
                record.pop("pdf_text", None)
            elif status == "pending" and isinstance(record.get("pdf_text"), str):
                record["pdf_text"] = clean_text(record["pdf_text"], 1800)
            if isinstance(record.get("context"), str):
                record["context"] = clean_text(record["context"], 350)
        if serialized_size() > max_bytes:
            active = []
            for key, record in items.items():
                if not isinstance(record, dict):
                    active.append(("", 2, key))
                    continue
                status = record.get("status", "baseline")
                priority = 2 if status == "ready" else 1 if status == "pending" else 0
                stamp = str(record.get("first_seen") or record.get("last_seen") or "")
                active.append((priority, stamp, key))
            active.sort(key=lambda row: (row[0], row[1]))
            evicted = 0
            for _, _, key in active:
                items.pop(key, None)
                evicted += 1
                if evicted % 20 == 0 and serialized_size() <= max_bytes:
                    break
            if evicted:
                print(f"[WARN] State byte cap reached; evicted {evicted} oldest active record(s).", file=sys.stderr)

    final_size = serialized_size()
    if final_size > max_bytes:
        raise RuntimeError(f"State exceeds configured byte cap: {final_size} > {max_bytes}")
    print(f"[STATE] bounded state size={final_size} bytes (limit={max_bytes})")


def refresh_stats(state):
    counts = {"sent": 0, "ignored": 0, "pending": 0}
    for record in state.get("items", {}).values():
        status = record.get("status")
        if status in counts:
            counts[status] += 1
    state["stats"]["pending"] = counts["pending"]
    state["stats"]["ignored"] = counts["ignored"]
    state["stats"]["sent"] = counts["sent"]


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def _should_fetch_pdf(record):
    if record.get("pdf_extracted") or record.get("pdf_text"):
        return False
    if int(record.get("pdf_attempts", 0)) >= MAX_PDF_ATTEMPTS:
        return False
    url = record.get("url", "")
    url_lower = url.lower()
    if any(pat in url_lower for pat in (
        "/past-notices", "/past_notices",
        "/whats-new", "/whats_new",
        "/notice_category", "/notice-category",
        "/document-category", "/document_category",
        "/archive", "/search",
    )):
        return False
    try:
        parsed = urlparse(url)
        if parsed.path in ("", "/"):
            return False
    except Exception:
        pass
    return True


def _fetch_pdfs_for_batch(batch, scan):
    targets = [
        (iid, record)
        for iid, record in batch
        if _should_fetch_pdf(record)
    ]
    if not targets:
        return
    timeout = scan["request_timeout_seconds"]

    def _fetch_one(record):
        try:
            return download_pdf_content(record["url"], timeout)
        except Exception as exc:
            print(f"[WARN] PDF fetch error: {exc}", file=sys.stderr)
            return None, "", False, "error"

    workers = max(1, min(OCR_MAX_WORKERS, len(targets)))
    with ThreadPoolExecutor(max_workers=workers) as ex:
        futures = {ex.submit(_fetch_one, record): (iid, record) for iid, record in targets}
        for fut in as_completed(futures):
            iid, record = futures[fut]
            try:
                content, text, ocr_used, method = fut.result()
            except Exception:
                content, text, ocr_used, method = None, "", False, "error"
            record["pdf_attempts"] = int(record.get("pdf_attempts", 0)) + 1
            record["pdf_method"] = method
            if content:
                try:
                    new_hash = _pdf_content_fingerprint(content)
                    new_kind = new_hash.split(":", 1)[0]
                    old_hash = record.get("pdf_hash")
                    old_kind = record.get("pdf_hash_kind")
                    if old_hash and old_kind == new_kind and old_hash != new_hash:
                        print(f"[PDF-CHANGED] PDF rendered content changed: {record.get('url', '')[:100]}", file=sys.stderr)
                        record["classification"] = None
                        record["summary"] = ""
                    record["pdf_hash"] = new_hash
                    record["pdf_hash_kind"] = new_kind
                except Exception as exc:
                    print(f"[WARN] PDF hash failed: {exc}", file=sys.stderr)
            if text:
                record["pdf_text"] = text[:MAX_PDF_TEXT_CHARS]
                record["pdf_extracted"] = True
                record["ocr_used"] = bool(ocr_used)
                if _is_stale_notice(
                    record.get("title", ""), record.get("context", ""), record.get("url", ""),
                    upload_date=_parse_upload_date(record.get("upload_date")), pdf_text=text,
                ):
                    record["status"] = "baseline"
                    record["classification"] = None
                    record["summary"] = ""
                    record["last_error"] = f"PDF content stale (limit={STALE_NOTICE_DAYS}d or old year)"
                    print(f"[STALE-PDF] Suppressed old PDF notice: {record.get('url','')[:80]}", file=sys.stderr)
                    continue


def _parse_upload_date(raw):
    if not raw:
        return None
    try:
        dt = datetime.fromisoformat(str(raw).replace("Z", "+00:00"))
        if dt.tzinfo is None:
            dt = dt.replace(tzinfo=timezone.utc)
        return dt
    except Exception:
        return None


def suppress_stale_pending_and_ready(state):
    changed = 0
    for record in state.get("items", {}).values():
        if not isinstance(record, dict) or record.get("status") not in {"pending", "ready"}:
            continue
        if _is_stale_notice(
            record.get("title", ""), record.get("context", ""), record.get("url", ""),
            upload_date=_parse_upload_date(record.get("upload_date")),
            pdf_text=record.get("pdf_text", ""),
        ):
            record["status"] = "baseline"
            record["classification"] = None
            record["summary"] = ""
            record["last_error"] = f"Stale persisted item suppressed (limit={STALE_NOTICE_DAYS}d or old year)"
            changed += 1
    if changed:
        print(f"[STALE-SKIP] Suppressed {changed} stale persisted item(s)", file=sys.stderr)
    return changed


def enqueue_persisted_pending(state, pending, max_pending_attempts, configured_site_ids):
    by_id = {iid: record for iid, record in pending}
    for iid, record in state.get("items", {}).items():
        if not isinstance(record, dict) or record.get("status") != "pending":
            continue
        sid = record.get("site_id")
        if sid not in configured_site_ids:
            continue
        if not site_state(state, sid).get("baseline_complete", False):
            continue
        if int(record.get("attempts", 0) or 0) >= max_pending_attempts:
            continue
        by_id[iid] = record
    return list(by_id.items())


def main():
    global STALE_NOTICE_DAYS, _RUNTIME_PDF_CACHE, _GEMINI_API_KEY, _GEMINI_QUOTA_EXHAUSTED
    global _GEMINI_KEYS_POOL, _GEMINI_KEY_INDEX, _GEMINI_DEAD_KEYS, _MODELS_DISCOVERED, _DYNAMIC_MODELS

    _RUNTIME_PDF_CACHE = {}
    _DEAD_MODELS.clear()
    _GEMINI_QUOTA_EXHAUSTED = False
    _GEMINI_KEYS_POOL = _load_gemini_keys()
    _GEMINI_KEY_INDEX = 0
    _GEMINI_DEAD_KEYS = set()
    _MODELS_DISCOVERED = False
    _DYNAMIC_MODELS = []

    import time as _time
    _START_TIME = _time.monotonic()
    _MAX_RUN_SECONDS = 20 * 60

    def _time_exceeded():
        return (_time.monotonic() - _START_TIME) > _MAX_RUN_SECONDS

    try:
        cfg = get_config()
        state = load_state()
    except Exception as exc:
        print(f"[FATAL] Configuration/state error: {exc}", file=sys.stderr)
        return 2

    token = os.getenv("TELEGRAM_BOT_TOKEN", "").strip()
    chat_id = os.getenv("TELEGRAM_CHAT_ID", "").strip()
    gemini_key = os.getenv("GEMINI_API_KEY", "").strip()

    _GEMINI_API_KEY = gemini_key or (_GEMINI_KEYS_POOL[0] if _GEMINI_KEYS_POOL else "")

    if not token or not chat_id:
        print("[FATAL] TELEGRAM_BOT_TOKEN and TELEGRAM_CHAT_ID are required.", file=sys.stderr)
        return 2
    if not _GEMINI_KEYS_POOL:
        print("[FATAL] No Gemini API keys configured. Set GEMINI_API_KEYS or GEMINI_API_KEY.", file=sys.stderr)
        return 2
    print(f"[INFO] Loaded {len(_GEMINI_KEYS_POOL)} unique Gemini API key(s).", file=sys.stderr)
    if not cfg["websites"]:
        print("[FATAL] No enabled websites configured.", file=sys.stderr)
        return 2
    try:
        validate_telegram_token(token)
    except Exception as exc:
        print(f"[FATAL] Telegram validation failed: {exc}", file=sys.stderr)
        return 2

    _discover_models()

    scan = cfg["scan"]
    STALE_NOTICE_DAYS = scan.get("stale_notice_days", STALE_NOTICE_DAYS)

    state["stats"]["runs"] = int(state["stats"].get("runs", 0)) + 1
    state["last_run"] = utc_now()
    run_errors = 0
    results = {}

    workers = min(scan["max_workers"], len(cfg["websites"]))
    with ThreadPoolExecutor(max_workers=max(1, workers)) as executor:
        futures = {executor.submit(scan_site, site, scan): site for site in cfg["websites"]}
        for future in as_completed(futures):
            site = futures[future]
            try:
                sid, candidates, errors, success = future.result()
                results[sid] = {"candidates": candidates, "errors": errors, "success": success}
                if success:
                    mark_site_success(state, sid, len(candidates))
                    state["metrics"]["site_scan_success"][sid] = state["metrics"]["site_scan_success"].get(sid, 0) + 1
                    if errors:
                        state["metrics"]["parse_errors"] = int(state["metrics"].get("parse_errors", 0)) + len(errors)
                    print(f"[OK] {site['name']}: {len(candidates)} candidate(s), {len(errors)} partial error(s)")
                else:
                    run_errors += 1
                    state["metrics"]["site_scan_failure"][sid] = state["metrics"]["site_scan_failure"].get(sid, 0) + 1
                    mark_site_failure(state, sid, "; ".join(errors) or "No page could be fetched")
                    print(f"[ERROR] {site['name']}: no page could be fetched", file=sys.stderr)
            except Exception as exc:
                run_errors += 1
                state["metrics"]["site_scan_failure"][site["id"]] = state["metrics"]["site_scan_failure"].get(site["id"], 0) + 1
                results[site["id"]] = {"candidates": [], "errors": [str(exc)], "success": False}
                mark_site_failure(state, site["id"], str(exc))
                print(f"[ERROR] {site['name']}: {exc}", file=sys.stderr)

    try:
        threshold = scan.get("site_alert_threshold", 3)
        cooldown = scan.get("site_alert_cooldown_hours", 6)
        _check_and_send_site_alerts(state, cfg, token, chat_id, threshold, cooldown)
    except Exception as exc:
        print(f"[WARN] Site alert check failed: {exc}", file=sys.stderr)

    site_index = build_site_index(state)
    pending = []

    for site in cfg["websites"]:
        sid = site["id"]
        ss = site_state(state, sid)
        result = results.get(sid, {"candidates": [], "success": False})
        candidates = result["candidates"]
        current_scan_success = bool(result["success"])

        baseline_scan_complete = baseline_can_complete(current_scan_success, result.get("errors", []))
        if not ss["baseline_complete"] and baseline_scan_complete:
            for candidate in candidates:
                iid = item_id(sid, candidate["url"], candidate["title"], candidate.get("context", ""))
                state["items"].setdefault(iid, {
                    "site_id": sid, "site_name": site["name"],
                    "url": candidate["url"], "title": candidate["title"],
                    "context": candidate.get("context", "")[:700],
                    "is_pdf": bool(candidate.get("is_pdf")),
                    "first_seen": utc_now(), "last_seen": utc_now(),
                    "status": "baseline", "attempts": 0, "summary": "",
                    "classification": None, "pdf_extracted": False,
                    "pdf_text": "", "pdf_attempts": 0, "ocr_used": False,
                    "pdf_method": "", "telegram_attempts": 0, "pdf_sent": False,
                    "upload_date": candidate.get("upload_date"),
                    "last_error": None,
                    "etag": None, "last_modified": None, "pdf_hash": None, "pdf_hash_kind": None, "last_content_check_at": None,
                })
            ss["baseline_complete"] = True
            ss["baseline_completed_at"] = utc_now()
            ss.pop("baseline_pending_reason", None)
            print(f"[BASELINE] {site['name']} initialized with {len(candidates)} item(s)")
            continue
        elif not ss["baseline_complete"]:
            ss["baseline_pending_reason"] = "scan failed or partial errors; baseline withheld to prevent archive spam"
            print(f"[BASELINE-PENDING] {site['name']}: waiting for a complete scan", file=sys.stderr)
            continue

        site_items_list = site_index.get(sid, [])

        for candidate in candidates:
            iid = item_id(sid, candidate["url"], candidate["title"], candidate.get("context", ""))
            record = state["items"].get(iid)
            upload_dt = _parse_upload_date(candidate.get("upload_date"))

            if _is_stale_notice(
                candidate.get("title", ""), candidate.get("context", ""),
                candidate.get("url", ""), upload_date=upload_dt,
            ):
                matched_iid = iid if record is not None else find_url_match(site_items_list, candidate["url"])
                if not matched_iid and record is None:
                    matched_iid = find_fuzzy_match(site_items_list, candidate.get("title", ""), candidate.get("url", ""))
                if matched_iid and matched_iid in state["items"]:
                    stale_record = state["items"][matched_iid]
                    stale_record["last_seen"] = utc_now()
                    if stale_record.get("status") not in {"sent", "ignored", "permanent_error"}:
                        stale_record["status"] = "baseline"
                        stale_record["classification"] = None
                        stale_record["summary"] = ""
                        stale_record["last_error"] = f"Stale notice (limit={STALE_NOTICE_DAYS}d or old year)"
                else:
                    state["items"][iid] = {
                        "site_id": sid, "site_name": site["name"],
                        "url": candidate["url"], "title": candidate.get("title", ""),
                        "context": candidate.get("context", "")[:700],
                        "is_pdf": bool(candidate.get("is_pdf")),
                        "first_seen": utc_now(), "last_seen": utc_now(),
                        "status": "baseline", "attempts": 0, "summary": "",
                        "classification": None, "pdf_extracted": False,
                        "pdf_text": "", "pdf_attempts": 0, "ocr_used": False,
                        "pdf_method": "", "telegram_attempts": 0, "pdf_sent": False,
                        "upload_date": candidate.get("upload_date"),
                        "last_error": f"Stale notice (limit={STALE_NOTICE_DAYS}d or old year)",
                        "etag": None, "last_modified": None, "pdf_hash": None,
                        "pdf_hash_kind": None, "last_content_check_at": None,
                    }
                    site_items_list.append((iid, candidate.get("title", ""), candidate.get("url", "")))
                print(f"[STALE-SKIP] {candidate.get('title', '')[:80]}", file=sys.stderr)
                continue

            url_lower = candidate["url"].lower()
            is_pdf_or_notice = (
                bool(candidate.get("is_pdf"))
                or _looks_like_pdf_url(candidate["url"])
                or "/notice/" in url_lower
                or "/document" in url_lower
            )

            if record is None:
                matched_iid = find_url_match(site_items_list, candidate["url"])
                if not matched_iid:
                    matched_iid = find_fuzzy_match(site_items_list, candidate["title"], candidate["url"])
                if matched_iid and matched_iid in state["items"]:
                    state["metrics"]["duplicate_rejects"] = int(state["metrics"].get("duplicate_rejects", 0)) + 1
                    iid = matched_iid
                    record = state["items"][matched_iid]
                    old_title = clean_text(record.get("title", ""), 300)
                    old_context = clean_text(record.get("context", ""), 700)
                    new_title = clean_text(candidate.get("title", ""), 300)
                    new_context = clean_text(candidate.get("context", ""), 700)
                    metadata_changed = _meaningful_metadata_change(
                        old_title, new_title, old_context, new_context
                    )
                    record["last_seen"] = utc_now()
                    if metadata_changed and record.get("status") in {"sent", "ignored", "baseline"}:
                        record["status"] = "pending"
                        record.pop("terminal_at", None)
                        record["attempts"] = 0
                        record["last_error"] = None
                        record["classification"] = None
                        record["summary"] = ""
                        record["pdf_extracted"] = False
                        record["pdf_text"] = ""
                        record["pdf_attempts"] = 0
                        record["ocr_used"] = False
                        record["pdf_method"] = ""
                        print(f"[RE-PROCESS] Existing notice metadata changed: {candidate['url'][:100]}")
                    if new_title:
                        record["title"] = new_title
                    if new_context:
                        record["context"] = new_context
                    if candidate.get("upload_date"):
                        record["upload_date"] = candidate["upload_date"]
                    record["is_pdf"] = bool(record.get("is_pdf") or is_pdf_or_notice)
                    if record.get("status") == "pending" and int(record.get("attempts", 0)) < scan["max_pending_attempts"]:
                        pending.append((iid, record))
                    continue

                upload_dt = _parse_upload_date(candidate.get("upload_date"))
                if _is_stale_notice(
                    candidate["title"], candidate.get("context", ""),
                    candidate["url"], upload_date=upload_dt,
                ):
                    state["items"][iid] = {
                        "site_id": sid, "site_name": site["name"],
                        "url": candidate["url"], "title": candidate["title"],
                        "context": candidate.get("context", "")[:700],
                        "is_pdf": is_pdf_or_notice,
                        "first_seen": utc_now(), "last_seen": utc_now(),
                        "status": "baseline", "attempts": 0, "summary": "",
                        "classification": None, "pdf_extracted": False,
                        "pdf_text": "", "pdf_attempts": 0, "ocr_used": False,
                        "pdf_method": "", "telegram_attempts": 0, "pdf_sent": False,
                        "upload_date": candidate.get("upload_date"),
                        "last_error": f"Stale (limit={STALE_NOTICE_DAYS}d)",
                        "etag": None, "last_modified": None, "pdf_hash": None, "pdf_hash_kind": None, "last_content_check_at": None,
                    }
                    site_items_list.append((iid, candidate["title"], candidate["url"]))
                    continue

                record = {
                    "site_id": sid, "site_name": site["name"],
                    "url": candidate["url"], "title": candidate["title"],
                    "context": candidate.get("context", "")[:700],
                    "is_pdf": is_pdf_or_notice,
                    "first_seen": utc_now(), "last_seen": utc_now(),
                    "status": "pending", "attempts": 0, "summary": "",
                    "classification": None, "pdf_extracted": False,
                    "pdf_text": "", "pdf_attempts": 0, "ocr_used": False,
                    "pdf_method": "", "telegram_attempts": 0, "pdf_sent": False,
                    "upload_date": candidate.get("upload_date"),
                    "last_error": None,
                    "etag": None, "last_modified": None, "pdf_hash": None, "pdf_hash_kind": None, "last_content_check_at": None,
                }
                state["items"][iid] = record
                site_items_list.append((iid, record["title"], record["url"]))
            else:
                record["last_seen"] = utc_now()

                if record.get("status") in ("sent", "ignored"):
                    should_check = True
                    try:
                        checked_at = record.get("last_content_check_at")
                        if checked_at:
                            checked_dt = datetime.fromisoformat(checked_at.replace("Z", "+00:00"))
                            if checked_dt.tzinfo is None:
                                checked_dt = checked_dt.replace(tzinfo=timezone.utc)
                            age_days = (datetime.now(timezone.utc) - checked_dt).total_seconds() / 86400
                            should_check = age_days >= ETAG_CHECK_MAX_AGE_DAYS
                    except Exception:
                        should_check = True

                    if should_check:
                        try:
                            session = make_session()
                            changed, new_etag, new_lm = _check_url_changed(
                                session, candidate["url"], record
                            )
                            if changed:
                                print(f"[UPDATE] Content changed: {candidate['url'][:80]}", file=sys.stderr)
                                record["status"] = "pending"
                                record.pop("terminal_at", None)
                                record["attempts"] = 0
                                record["last_error"] = None
                                record["pdf_extracted"] = False
                                record["pdf_text"] = ""
                                record["pdf_attempts"] = 0
                                record["classification"] = None
                                record["summary"] = ""
                            if new_etag:
                                record["etag"] = new_etag
                            if new_lm:
                                record["last_modified"] = new_lm
                            record["last_content_check_at"] = utc_now()
                        except Exception as exc:
                            print(f"[WARN] ETag check failed: {exc}", file=sys.stderr)

                if record.get("status") == "baseline":
                    old_title = (record.get("title") or "").strip()
                    new_title = (candidate.get("title") or "").strip()
                    old_context = record.get("context", "")
                    new_context = candidate.get("context", "")
                    if _meaningful_metadata_change(old_title, new_title, old_context, new_context):
                        record["status"] = "pending"
                        record["attempts"] = 0
                        record["last_error"] = None
                        record["pdf_extracted"] = False
                        record["pdf_text"] = ""
                        record["pdf_attempts"] = 0
                        print(f"[RE-PROCESS] Substantive baseline metadata change: {new_title[:80]}")

                if candidate["title"]:
                    record["title"] = candidate["title"]
                if candidate.get("context"):
                    record["context"] = candidate["context"][:700]
                if candidate.get("upload_date"):
                    record["upload_date"] = candidate["upload_date"]
                record["is_pdf"] = bool(
                    candidate.get("is_pdf", record.get("is_pdf", False))
                ) or is_pdf_or_notice

            if (
                ss["baseline_complete"]
                and record.get("status") == "pending"
                and int(record.get("attempts", 0)) < scan["max_pending_attempts"]
            ):
                pending.append((iid, record))

    suppress_stale_pending_and_ready(state)
    pending = [(iid, record) for iid, record in pending if record.get("status") == "pending"]

    pending = enqueue_persisted_pending(
        state,
        pending,
        scan["max_pending_attempts"],
        {site["id"] for site in cfg["websites"]},
    )

    state["initialized"] = all(
        site_state(state, site["id"])["baseline_complete"] for site in cfg["websites"]
    )

    pending = list({iid: record for iid, record in pending}.items())
    pending.sort(
        key=lambda pair: pending_priority(pair[1], scan["keywords"]),
        reverse=True,
    )
    max_items_this_run = min(
        scan["gemini_batch_size"] * scan["gemini_max_calls_per_run"],
        40,
    )
    pending = pending[:max_items_this_run]

    batch_size = scan["gemini_batch_size"]
    for start in range(0, len(pending), batch_size):
        if _time_exceeded():
            print("[TIME_LIMIT] Exceeded 20 min — stopping Gemini batches early", file=sys.stderr)
            break

        batch = pending[start : start + batch_size]
        try:
            _fetch_pdfs_for_batch(batch, scan)
        except Exception as exc:
            print(f"[WARN] PDF batch fetch failed: {exc}", file=sys.stderr)
        try:
            result = gemini_classify_with_fallback(
                [record for _, record in batch], gemini_key, scan["request_timeout_seconds"],
            )
            for index, (_, record) in enumerate(batch):
                if record.get("status") == "baseline" and str(record.get("last_error", "")).startswith("PDF content stale"):
                    continue
                record["attempts"] = int(record.get("attempts", 0)) + 1
                classification = result.get(str(index))
                if classification is None:
                    record["status"] = "pending"
                    record["last_error"] = "Gemini returned no classification"
                    add_review_item(state, record, "classification_missing")
                    continue
                if classification.get("ambiguous") is True or classification.get("needs_review") is True:
                    add_review_item(state, record, "Gemini marked notice ambiguous", classification)
                record["last_error"] = None
                record["classification"] = classification
                record["summary"] = classification.get("summary", "")
                record["status"] = "ready" if classification.get("important") else "ignored"
        except Exception as exc:
            error = clean_text(str(exc), 500)
            for _, record in batch:
                record["attempts"] = int(record.get("attempts", 0)) + 1
                record["status"] = "pending"
                record["last_error"] = error
            run_errors += 1
            print(f"[ERROR] Gemini classification failed: {error}", file=sys.stderr)
            break

    ready = [
        (iid, record)
        for iid, record in state["items"].items()
        if record.get("status") == "ready"
        and int(record.get("telegram_attempts", 0) or 0) < TELEGRAM_MAX_ATTEMPTS
        and _telegram_retry_due(record)
    ]
    ready.sort(key=lambda pair: pair[1].get("first_seen", ""), reverse=True)

    sent_count = 0
    for iid, record in ready[: scan["max_new_items_per_run"]]:
        if _time_exceeded():
            print("[TIME_LIMIT] Exceeded — stopping Telegram sends early", file=sys.stderr)
            break

        site = next((s for s in cfg["websites"] if s["id"] == record.get("site_id")), None)
        if site is None:
            record["status"] = "permanent_error"
            record["last_error"] = "Configured site no longer exists"
            continue

        full_message = format_message(site, record, record.get("classification"))
        full_message = truncate_telegram(full_message)

        is_pdf_flag = record.get("is_pdf", False)
        if SEND_PDF_ENABLED and is_pdf_flag:
            ok, permanent, detail = send_notification_with_pdf(
                token, chat_id, record, full_message
            )
        else:
            ok, permanent, detail = send_telegram(token, chat_id, full_message)

        record["telegram_attempts"] = int(record.get("telegram_attempts", 0)) + 1
        if ok:
            state["metrics"]["sent_notifications"] = int(state["metrics"].get("sent_notifications", 0)) + 1
            record["status"] = "sent"
            record["last_error"] = None
            record.pop("telegram_next_attempt_at", None)
            record.pop("telegram_first_failed_at", None)
            sent_count += 1
        elif permanent:
            state["metrics"]["failed_notifications"] = int(state["metrics"].get("failed_notifications", 0)) + 1
            record["status"] = "permanent_error"
            record["last_error"] = detail
            record.pop("telegram_next_attempt_at", None)
            run_errors += 1
            print(f"[ERROR] Permanent Telegram error: {detail}", file=sys.stderr)
        else:
            state["metrics"]["failed_notifications"] = int(state["metrics"].get("failed_notifications", 0)) + 1
            record["status"] = "ready"
            record["last_error"] = detail
            _schedule_telegram_retry(record)
            run_errors += 1
            print(
                f"[WARN] Telegram delivery failed; retry scheduled at "
                f"{record.get('telegram_next_attempt_at')}: {detail}", file=sys.stderr
            )

    try:
        should_alert = run_errors > 0
        last_health_alert = state.get("last_health_alert_at")
        if last_health_alert:
            health_dt = _parse_utc_timestamp(last_health_alert)
            if health_dt and (datetime.now(timezone.utc) - health_dt).total_seconds() < 24 * 3600:
                should_alert = False
        if should_alert:
            alert_msg = (
                f"⚠️ <b>Monitor Health Alert</b>\n\n"
                f"Is run me {run_errors} error(s) record hue.\n"
                f"Delivered notices in this run: {sent_count}.\n"
                f"Run time: {state.get('last_run', 'unknown')}"
            )
            ok, _permanent, detail = send_telegram(token, chat_id, alert_msg)
            if ok:
                state["last_health_alert_at"] = utc_now()
                print(f"[ALERT] Run completed with {run_errors} error(s)", file=sys.stderr)
            else:
                print(f"[WARN] Health alert not delivered: {detail}", file=sys.stderr)
        if sent_count > 0:
            state["last_successful_notify_at"] = utc_now()
    except Exception as exc:
        print(f"[WARN] Health alert check failed: {exc}", file=sys.stderr)

    _RUNTIME_PDF_CACHE.clear()

    try:
        state["stats"]["errors"] = int(state["stats"].get("errors", 0)) + run_errors
        prune_state(
            state,
            scan["retention_days"],
            scan["max_state_items"],
            scan["max_pending_attempts"],
            scan["max_state_bytes"],
        )
        refresh_stats(state)
        atomic_save_json(STATE_FILE, state, max_bytes=scan["max_state_bytes"])
        try:
            print(f"[STATE] records={len(state.get('items', {}))} bytes={STATE_FILE.stat().st_size}")
        except OSError:
            pass
    except Exception as exc:
        state.setdefault("metrics", {})["state_save_failures"] = int(state.get("metrics", {}).get("state_save_failures", 0)) + 1
        print(f"[FATAL] State save failed: {exc}", file=sys.stderr)
        return 1

    elapsed = _time.monotonic() - _START_TIME
    print(
        f"[DONE] initialized={state['initialized']} "
        f"sites={len(cfg['websites'])} "
        f"sent_this_run={sent_count} "
        f"pending={state['stats']['pending']} "
        f"errors_this_run={run_errors} "
        f"review_open={sum(1 for x in state.get('review_queue', {}).values() if x.get('status') == 'open')} "
        f"duplicate_rejects={state.get('metrics', {}).get('duplicate_rejects', 0)} "
        f"elapsed={elapsed:.1f}s"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
