import base64
import hashlib
import html
import io
import json
import os
import re
import sys
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime, timezone, timedelta
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple
from urllib.parse import urljoin, urlparse, urlunparse, unquote

import pdfplumber
import pytesseract
import requests
from bs4 import BeautifulSoup
from pdf2image import convert_from_bytes
from rapidfuzz import fuzz
from requests.adapters import HTTPAdapter
from urllib3.util.retry import Retry


BASE = Path(__file__).resolve().parent
CONFIG_FILE = BASE / "websites.json"
STATE_FILE = BASE / "state.json"

FALLBACK_MODELS = [
    "gemini-3.5-flash-lite",
    "gemini-2.5-flash-lite",
    "gemini-2.0-flash-lite",
]

FUZZY_DUPLICATE_THRESHOLD = 97

MAX_PDF_BYTES = 5 * 1024 * 1024
MAX_PDF_SEND_BYTES = 45 * 1024 * 1024
MAX_PDF_PAGES = 8
MAX_PDF_TEXT_CHARS = 4000
MAX_PDF_ATTEMPTS = 3
TELEGRAM_SAFE_LIMIT = 4000
TELEGRAM_CAPTION_LIMIT = 1024

GEMINI_MAX_OUTPUT_TOKENS = int(os.getenv("GEMINI_MAX_OUTPUT_TOKENS", "16384"))

OCR_ENABLED = os.getenv("OCR_ENABLED", "true").strip().lower() == "true"
OCR_DPI = int(os.getenv("OCR_DPI", "200"))
OCR_LANG = os.getenv("OCR_LANG", "eng+hin")
OCR_MIN_TEXT_CHARS = int(os.getenv("OCR_MIN_TEXT_CHARS", "200"))
OCR_MAX_WORKERS = int(os.getenv("OCR_MAX_WORKERS", "1"))

GEMINI_PDF_OCR_ENABLED = os.getenv("GEMINI_PDF_OCR_ENABLED", "true").strip().lower() == "true"

SEND_PDF_ENABLED = os.getenv("SEND_PDF_ENABLED", "true").strip().lower() == "true"

NOTIFY_LANGUAGE = os.getenv("NOTIFY_LANGUAGE", "both").strip().lower()
if NOTIFY_LANGUAGE not in {"both", "hi", "en"}:
    NOTIFY_LANGUAGE = "both"

STALE_NOTICE_DAYS = int(os.getenv("STALE_NOTICE_DAYS", "30"))

USER_AGENT = os.getenv(
    "MONITOR_USER_AGENT",
    "Mozilla/5.0 (compatible; JharkhandNoticeMonitor/6.4)"
)

STRONG_KEYWORDS = [
    "recruitment", "vacancy", "post", "job", "result",
    "admit card", "answer key", "merit", "selection",
    "scholarship", "admission", "counselling",
    "notification", "notice", "tender", "appointment",
    "भर्ती", "परिणाम", "नियुक्ति", "प्रवेश", "छात्रवृत्ति",
    "सूचना", "नोटिस", "निविदा"
]

# Runtime PDF cache
_RUNTIME_PDF_CACHE: Dict[str, bytes] = {}

# Gemini API key (set in main)
_GEMINI_API_KEY = ""


# ---------------------------------------------------------------------------
# Navigation filters
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
    # FIX #5: language-prefixed archive/listing paths (e.g. /hi/past-notices/..., /en/whats-new)
    re.compile(r"/(hi|en|hn|ur|bn|ta|te|mr|gu|kn|ml|pa|or|as)(/|$).*(past[-_]?notices|whats[-_]?new|archive|category|notice[-_]?category|document[-_]?category|search)", re.I),
    re.compile(r"/(hi|en|hn|ur|bn|ta|te|mr|gu|kn|ml|pa|or|as)/?$", re.I),
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
    """
    FIX #3: Extract a human-readable title from URL path when anchor text
    is unusable (e.g. language selectors like 'हिन्दी').
    """
    try:
        path = unquote(urlparse(url).path or "")
    except Exception:
        return ""
    slug = path.rstrip("/").rsplit("/", 1)[-1]
    if not slug or slug.lower().endswith(".pdf"):
        # For PDFs, keep filename but strip .pdf
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
                if not (2000 <= y <= 2100):
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
                    return ds[0]
        text = search_root.get_text(" ", strip=True)
        for pat in _UPLOAD_DATE_TEXT_PATTERNS:
            m = pat.search(text)
            if m:
                ds = _extract_full_dates(m.group(1))
                if ds:
                    return ds[0]
    except Exception:
        pass
    return None


def _is_stale_notice(title, context, url, upload_date=None):
    now = datetime.now(timezone.utc)
    cutoff = now - timedelta(days=STALE_NOTICE_DAYS)
    if upload_date is not None:
        if upload_date.tzinfo is None:
            upload_date = upload_date.replace(tzinfo=timezone.utc)
        if upload_date > now:
            return False
        return upload_date < cutoff
    haystack = f"{title} {context}".strip()
    all_dates = _extract_full_dates(haystack)
    if all_dates:
        latest = max(all_dates)
        if latest > now:
            return False
        return latest < cutoff
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


def atomic_save_json(path, data):
    tmp = path.with_suffix(path.suffix + ".tmp")
    with tmp.open("w", encoding="utf-8") as f:
        json.dump(data, f, ensure_ascii=False, indent=2)
        f.write("\n")
        f.flush()
        os.fsync(f.fileno())
    os.replace(tmp, path)


def canonical_url(raw):
    raw = (raw or "").strip()
    p = urlparse(raw)
    if not p.scheme or not p.netloc:
        return raw
    return urlunparse((p.scheme.lower(), p.netloc.lower(), p.path or "/", "", p.query, ""))


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
        "max_discovery_pages_per_site": 5,
        "max_new_items_per_run": 25,
        "gemini_batch_size": 3,
        "gemini_max_calls_per_run": 15,
        "retention_days": 90,
        "max_pending_attempts": 12,
        "stale_notice_days": 30,
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
    scan["max_new_items_per_run"] = max(1, int(scan["max_new_items_per_run"]))
    scan["gemini_batch_size"] = max(1, min(20, int(scan["gemini_batch_size"])))
    scan["gemini_max_calls_per_run"] = max(1, int(scan["gemini_max_calls_per_run"]))
    scan["retention_days"] = max(7, int(scan["retention_days"]))
    scan["max_pending_attempts"] = max(1, int(scan["max_pending_attempts"]))
    scan["stale_notice_days"] = max(1, int(scan["stale_notice_days"]))
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
        "version": 19,
        "initialized": False,
        "last_run": None,
        "items": {},
        "sites": {},
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
    state["version"] = 19
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


# ---------------------------------------------------------------------------
# Scoring / IDs / Dedup
# ---------------------------------------------------------------------------

def local_score(title, url, context, keywords):
    text = f"{title} {url} {context}".lower()
    return sum(1 for kw in keywords if kw and kw in text)


def item_id(site_id, url, title, context=""):
    fingerprint = hashlib.sha256(
        clean_text(f"{title}|{context}", 900).lower().encode()
    ).hexdigest()[:12]
    raw = f"{site_id}|{canonical_url(url)}|{fingerprint}"
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
    for iid, record in state.get("items", {}).items():
        if not isinstance(record, dict):
            continue
        if record.get("status") in ("ignored", "permanent_error"):
            continue
        sid = record.get("site_id")
        if not sid:
            continue
        index.setdefault(sid, []).append((iid, record.get("title", ""), record.get("url", "")))
    return index


def find_fuzzy_match(site_items, title, url):
    if not site_items or not title:
        return None
    new_title = _normalize_title(title)
    new_segs = _url_path_segments(url)
    if not new_title:
        return None
    best = None
    best_score = 0
    for iid, existing_title, existing_url in site_items:
        existing_norm = _normalize_title(existing_title)
        if not existing_norm:
            continue
        existing_segs = _url_path_segments(existing_url)
        if new_segs and existing_segs and not (new_segs & existing_segs):
            continue
        score = fuzz.token_sort_ratio(new_title, existing_norm)
        if score >= FUZZY_DUPLICATE_THRESHOLD and score > best_score:
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
                # FIX #3: URL-based title fallback for language-selector anchors
                url_title = _title_from_url(href, min_len=8)
                if url_title:
                    title = url_title
                else:
                    continue

        score = local_score(title, href, context, keywords)
        pdf_bonus = 1 if is_pdf(href) else 0
        if score <= 0 and pdf_bonus == 0:
            continue
        if href in seen:
            continue
        seen.add(href)
        upload_dt = _extract_upload_date(a)
        out.append({
            "url": href,
            "title": title or clean_text(context, 180) or href.rsplit("/", 1)[-1],
            "context": context,
            "source_page": page_url,
            "is_pdf": is_pdf(href),
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


def discover_site(session, site, scan):
    base_url = site["url"]
    timeout = scan["request_timeout_seconds"]
    max_pages = scan["max_discovery_pages_per_site"]
    discovery_keywords = list(dict.fromkeys(
        scan["discovery_keywords"] + site.get("discovery_keywords", []) + scan["keywords"]
    ))
    queue = [base_url]
    queue.extend(discover_from_sitemap(session, base_url, scan))
    visited = set()
    candidates = {}
    errors = []
    successful_pages = 0
    while queue and len(visited) < max_pages:
        page = canonical_url(queue.pop(0))
        if page in visited or not same_host(base_url, page):
            continue
        visited.add(page)

        # FIX #1: Page-level navigation check — never fetch archive/listing pages
        # even if they were queued via discovery keywords.
        if _is_navigation_url(page):
            continue

        try:
            response = session.get(page, timeout=timeout, allow_redirects=True)
            if response.status_code >= 400:
                raise RuntimeError(f"HTTP {response.status_code}")
            final_url = canonical_url(response.url)

            # FIX #2: After redirects, if we landed on a navigation/archive URL, skip.
            if _is_navigation_url(final_url):
                successful_pages += 1
                continue

            content_type = response.headers.get("content-type", "").lower()
            if is_pdf(final_url) or "application/pdf" in content_type:
                filename = final_url.rsplit("/", 1)[-1] or "PDF Notice"
                candidates[final_url] = {
                    "url": final_url, "title": clean_text(filename, 300),
                    "context": "Direct PDF notice", "source_page": page,
                    "is_pdf": True, "score": 2, "upload_date": None,
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
                if _is_navigation_url(href):
                    continue
                anchor = clean_text(a.get_text(" ", strip=True), 220).lower()
                path = urlparse(href).path.lower()
                haystack = f"{anchor} {path}"
                if any(kw in haystack for kw in discovery_keywords if kw):
                    queue.append(href)
                    if len(queue) >= max_pages * 2:
                        break
        except Exception as exc:
            errors.append(f"{page}: {clean_text(str(exc), 250)}")
    values = list(candidates.values())
    values.sort(key=lambda x: (-x["score"], x["title"].lower()))
    return (site["id"], values[: scan["max_items_per_site"]], errors, successful_pages > 0)


def scan_site(site, scan):
    return discover_site(make_session(), site, scan)


# ---------------------------------------------------------------------------
# PDF extraction (text + tables + OCR)
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


def _extract_pdf_text_ocr(content):
    """Tesseract OCR fallback."""
    parts = []
    try:
        images = convert_from_bytes(
            content,
            first_page=1,
            last_page=MAX_PDF_PAGES,
            dpi=OCR_DPI,
        )
        for idx, img in enumerate(images):
            try:
                txt = pytesseract.image_to_string(img, lang=OCR_LANG) or ""
                if txt.strip():
                    parts.append(txt)
            except Exception as exc:
                print(f"[WARN] Tesseract page {idx+1} failed: {exc}", file=sys.stderr)
    except Exception as exc:
        print(f"[WARN] Tesseract conversion failed: {exc}", file=sys.stderr)
    return "\n".join(parts)


def _extract_with_gemini_pdf(pdf_bytes):
    """
    Send PDF directly to Gemini (native PDF support).
    Tries all 3 fallback models. Returns text or empty string.
    """
    if not GEMINI_PDF_OCR_ENABLED or not _GEMINI_API_KEY:
        return ""

    try:
        pdf_b64 = base64.b64encode(pdf_bytes).decode("utf-8")

        prompt = (
            "Extract ALL text from this government notice PDF. "
            "May be in Hindi, English, or both. May contain tables. "
            "Return extracted text verbatim, preserving structure. "
            "Do NOT summarize. Do NOT invent. Just extract the text."
        )

        payload = {
            "contents": [{
                "parts": [
                    {"text": prompt},
                    {
                        "inline_data": {
                            "mime_type": "application/pdf",
                            "data": pdf_b64,
                        }
                    }
                ]
            }],
            "generationConfig": {
                "temperature": 0.0,
                "maxOutputTokens": 8192,
            },
        }

        headers = {
            "x-goog-api-key": _GEMINI_API_KEY,
            "Content-Type": "application/json",
        }

        for model in FALLBACK_MODELS:
            endpoint = (
                "https://generativelanguage.googleapis.com/"
                f"v1beta/models/{model}:generateContent"
            )
            try:
                response = requests.post(
                    endpoint, headers=headers,
                    json=payload, timeout=60,
                )
                if response.status_code == 429:
                    print(f"[WARN] Gemini PDF OCR rate limited ({model})", file=sys.stderr)
                    continue
                if response.status_code >= 400:
                    continue
                data = response.json()
                text = _extract_gemini_text(data)
                if text and len(text.strip()) > 50:
                    print(f"[INFO] Gemini PDF OCR succeeded ({model})", file=sys.stderr)
                    return text
            except Exception as exc:
                print(f"[WARN] Gemini PDF failed ({model}): {exc}", file=sys.stderr)
                continue
    except Exception as exc:
        print(f"[WARN] Gemini PDF OCR failed: {exc}", file=sys.stderr)

    return ""


def _text_looks_thin(text):
    stripped = (text or "").strip()
    if len(stripped) < OCR_MIN_TEXT_CHARS:
        return True
    if not re.search(r"\d", stripped):
        return True
    if stripped.count("\n") < 3:
        return True
    return False


def download_pdf_content(pdf_url, timeout=30):
    """
    Download PDF once. Returns (content_bytes, text, ocr_used, method).
    OCR chain: pdfplumber → Gemini PDF → Tesseract.
    Uses runtime cache to avoid re-download.
    """
    global _RUNTIME_PDF_CACHE

    if pdf_url in _RUNTIME_PDF_CACHE:
        content = _RUNTIME_PDF_CACHE[pdf_url]
    else:
        try:
            session = make_session()
            try:
                head = session.head(pdf_url, timeout=10, allow_redirects=True)
                cl = head.headers.get("content-length")
                if cl:
                    try:
                        if int(cl) > MAX_PDF_SEND_BYTES:
                            return None, "", False, "size_limit"
                    except (TypeError, ValueError):
                        pass
            except Exception:
                pass

            response = session.get(pdf_url, timeout=timeout)
            if response.status_code >= 400:
                return None, "", False, "http_error"
            content = response.content
            if not content or len(content) > MAX_PDF_SEND_BYTES:
                return None, "", False, "size_limit"
            _RUNTIME_PDF_CACHE[pdf_url] = content
        except Exception as exc:
            print(f"[WARN] PDF download failed for {pdf_url}: {exc}", file=sys.stderr)
            return None, "", False, "download_error"

    text = _extract_pdf_text_plumber(content)
    method = "plumber"

    if _text_looks_thin(text):
        print(f"[INFO] PDF thin ({len(text)} chars). Trying Gemini PDF OCR...", file=sys.stderr)
        gemini_text = _extract_with_gemini_pdf(content)

        if gemini_text and len(gemini_text.strip()) > len(text.strip()):
            text = (
                f"{text}\n\n--- GEMINI OCR ---\n\n{gemini_text}"
                if text.strip() else gemini_text
            )
            method = "gemini"
            print(f"[INFO] Gemini OCR succeeded ({len(gemini_text)} chars)", file=sys.stderr)
        else:
            print("[INFO] Gemini failed. Trying Tesseract...", file=sys.stderr)
            tess_text = _extract_pdf_text_ocr(content)
            if tess_text and len(tess_text.strip()) > len(text.strip()):
                text = (
                    f"{text}\n\n--- TESSERACT OCR ---\n\n{tess_text}"
                    if text.strip() else tess_text
                )
                method = "tesseract"
                print(f"[INFO] Tesseract OCR succeeded ({len(tess_text)} chars)", file=sys.stderr)
            else:
                print("[WARN] All OCR methods failed", file=sys.stderr)

    return (
        content,
        clean_text(text, MAX_PDF_TEXT_CHARS),
        method != "plumber",
        method,
    )


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
        "3. summary — 1-line summary (<= 150 chars)\n\n"

        "IMPORTANT: If 'pdf_text' is provided, treat it as PRIMARY source. "
        "The text may come from OCR (scanned PDF) and could have minor errors. "
        "Extract only what you are confident about. "
        "If a value is unclear, set it to null instead of guessing.\n\n"

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
        '"id":"0","important":true,"category":"vacancy","summary":"...",'
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
    headers = {"x-goog-api-key": api_key, "Content-Type": "application/json"}
    last_error = "Gemini classification failed"
    for attempt in range(3):
        try:
            response = requests.post(endpoint, headers=headers, json=payload, timeout=timeout)
            if response.status_code in (429, 500, 502, 503, 504):
                last_error = f"Gemini HTTP {response.status_code}"
                if attempt < 2:
                    time.sleep(min(10, 2 ** attempt))
                    continue
                raise RuntimeError(last_error)
            if response.status_code >= 400:
                raise RuntimeError(f"Gemini HTTP {response.status_code}: {clean_text(response.text, 500)}")
            data = response.json()
            text = _extract_gemini_text(data)
            if not text:
                raise RuntimeError("Gemini returned empty response")
            return _parse_gemini_response(text, len(items))
        except (requests.RequestException, ValueError, KeyError, TypeError, RuntimeError) as exc:
            last_error = str(exc)
            if attempt < 2:
                time.sleep(min(10, 2 ** attempt))
    raise RuntimeError(last_error)


def gemini_classify_with_fallback(items, api_key, timeout):
    seen = []
    for model in FALLBACK_MODELS:
        if model in seen:
            continue
        seen.append(model)
        try:
            result = gemini_classify(items, api_key, model, timeout)
            if result:
                print(f"[INFO] Gemini success with model: {model}")
                return result
        except Exception as exc:
            print(f"[WARN] Model {model} failed: {clean_text(str(exc), 200)}", file=sys.stderr)
            continue
    print("[WARN] All Gemini models failed. Using keyword fallback.", file=sys.stderr)
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
                data=data,
                files=files,
                timeout=60,
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
        name = url.rsplit("/", 1)[-1].split("?")[0]
        if name and name.lower().endswith(".pdf"):
            return name[:100]
    except Exception:
        pass
    return default


def send_notification_with_pdf(token, chat_id, record, full_message):
    """
    Send PDF document with caption. SINGLE MESSAGE ONLY.
    Uses runtime cache to avoid re-download.
    """
    pdf_url = record.get("url", "")
    filename = _safe_filename(pdf_url)

    pdf_bytes = _RUNTIME_PDF_CACHE.get(pdf_url)

    if pdf_bytes is None:
        try:
            session = make_session()
            try:
                head = session.head(pdf_url, timeout=10, allow_redirects=True)
                cl = head.headers.get("content-length")
                if cl:
                    try:
                        if int(cl) > MAX_PDF_SEND_BYTES:
                            return send_telegram(token, chat_id, truncate_telegram(full_message))
                    except (TypeError, ValueError):
                        pass
            except Exception:
                pass

            response = session.get(pdf_url, timeout=30)
            if response.status_code == 200:
                content = response.content
                content_type = response.headers.get("content-type", "").lower()
                if (is_pdf(pdf_url) or "application/pdf" in content_type) and len(content) <= MAX_PDF_SEND_BYTES:
                    pdf_bytes = content
                    _RUNTIME_PDF_CACHE[pdf_url] = content
        except Exception as exc:
            print(f"[WARN] PDF download for send failed: {exc}", file=sys.stderr)

    if not pdf_bytes:
        return send_telegram(token, chat_id, truncate_telegram(full_message))

    caption = full_message
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
        raw_title = clean_text(item.get("context", ""), 200) or "Notification"
    title = html.escape(raw_title)
    site_name = html.escape(site["name"])
    url = html.escape(item["url"], quote=True)
    summary = html.escape(_safe_str(classification.get("summary")) or "")
    category = (classification.get("category") or "notice").lower()
    emoji = CATEGORY_EMOJI.get(category, "📌")

    # OCR method marker
    ocr_method = item.get("pdf_method", "")
    if ocr_method == "gemini":
        ocr_marker = " 🔍G"
    elif ocr_method == "tesseract":
        ocr_marker = " 🔍T"
    else:
        ocr_marker = ""

    pdf_marker = " 📄" if item.get("is_pdf") else ""

    lines = [f"🔔 <b>{site_name}</b>{pdf_marker}", "", f"<b>{title}</b>{ocr_marker}", ""]
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

def prune_state(state, retention_days):
    cutoff = datetime.now(timezone.utc) - timedelta(days=retention_days)
    remove = []
    for key, record in state.get("items", {}).items():
        if not isinstance(record, dict):
            remove.append(key)
            continue
        stamp = record.get("last_seen") or record.get("first_seen")
        try:
            dt = datetime.fromisoformat(stamp.replace("Z", "+00:00"))
        except Exception:
            dt = datetime.now(timezone.utc)
        if dt < cutoff and record.get("status") in {"sent", "ignored", "permanent_error", "baseline"}:
            remove.append(key)
    for key in remove:
        state["items"].pop(key, None)


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

def _fetch_pdfs_for_batch(batch, scan):
    targets = [
        (iid, record)
        for iid, record in batch
        if record.get("is_pdf")
        and not record.get("pdf_extracted")
        and not record.get("pdf_text")
        and int(record.get("pdf_attempts", 0)) < MAX_PDF_ATTEMPTS
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
            if text:
                record["pdf_text"] = text[:MAX_PDF_TEXT_CHARS]
                record["pdf_extracted"] = True
                record["ocr_used"] = bool(ocr_used)


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


def main():
    global STALE_NOTICE_DAYS, _RUNTIME_PDF_CACHE, _GEMINI_API_KEY

    _RUNTIME_PDF_CACHE = {}

    try:
        cfg = get_config()
        state = load_state()
    except Exception as exc:
        print(f"[FATAL] Configuration/state error: {exc}", file=sys.stderr)
        return 2

    token = os.getenv("TELEGRAM_BOT_TOKEN", "").strip()
    chat_id = os.getenv("TELEGRAM_CHAT_ID", "").strip()
    gemini_key = os.getenv("GEMINI_API_KEY", "").strip()

    # Set global for OCR functions
    _GEMINI_API_KEY = gemini_key

    if not token or not chat_id or not gemini_key:
        print("[FATAL] TELEGRAM_BOT_TOKEN, TELEGRAM_CHAT_ID and GEMINI_API_KEY are required.", file=sys.stderr)
        return 2
    if not cfg["websites"]:
        print("[FATAL] No enabled websites configured.", file=sys.stderr)
        return 2
    try:
        validate_telegram_token(token)
    except Exception as exc:
        print(f"[FATAL] Telegram validation failed: {exc}", file=sys.stderr)
        return 2

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
                    print(f"[OK] {site['name']}: {len(candidates)} candidate(s), {len(errors)} partial error(s)")
                else:
                    run_errors += 1
                    mark_site_failure(state, sid, "; ".join(errors) or "No page could be fetched")
                    print(f"[ERROR] {site['name']}: no page could be fetched", file=sys.stderr)
            except Exception as exc:
                run_errors += 1
                results[site["id"]] = {"candidates": [], "errors": [str(exc)], "success": False}
                mark_site_failure(state, site["id"], str(exc))
                print(f"[ERROR] {site['name']}: {exc}", file=sys.stderr)

    site_index = build_site_index(state)
    pending = []

    for site in cfg["websites"]:
        sid = site["id"]
        ss = site_state(state, sid)
        result = results.get(sid, {"candidates": [], "success": False})
        candidates = result["candidates"]
        current_scan_success = bool(result["success"])

        if not ss["baseline_complete"] and current_scan_success:
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
                })
            ss["baseline_complete"] = True
            print(f"[BASELINE] {site['name']} initialized with {len(candidates)} item(s)")
            continue

        site_items_list = site_index.get(sid, [])

        for candidate in candidates:
            iid = item_id(sid, candidate["url"], candidate["title"], candidate.get("context", ""))
            record = state["items"].get(iid)

            if record is None:
                fuzzy_iid = find_fuzzy_match(site_items_list, candidate["title"], candidate["url"])
                if fuzzy_iid and fuzzy_iid in state["items"]:
                    state["items"][fuzzy_iid]["last_seen"] = utc_now()
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
                        "is_pdf": bool(candidate.get("is_pdf")),
                        "first_seen": utc_now(), "last_seen": utc_now(),
                        "status": "baseline", "attempts": 0, "summary": "",
                        "classification": None, "pdf_extracted": False,
                        "pdf_text": "", "pdf_attempts": 0, "ocr_used": False,
                        "pdf_method": "", "telegram_attempts": 0, "pdf_sent": False,
                        "upload_date": candidate.get("upload_date"),
                        "last_error": f"Stale (limit={STALE_NOTICE_DAYS}d)",
                    }
                    site_items_list.append((iid, candidate["title"], candidate["url"]))
                    continue

                record = {
                    "site_id": sid, "site_name": site["name"],
                    "url": candidate["url"], "title": candidate["title"],
                    "context": candidate.get("context", "")[:700],
                    "is_pdf": bool(candidate.get("is_pdf")),
                    "first_seen": utc_now(), "last_seen": utc_now(),
                    "status": "pending", "attempts": 0, "summary": "",
                    "classification": None, "pdf_extracted": False,
                    "pdf_text": "", "pdf_attempts": 0, "ocr_used": False,
                    "pdf_method": "", "telegram_attempts": 0, "pdf_sent": False,
                    "upload_date": candidate.get("upload_date"),
                    "last_error": None,
                }
                state["items"][iid] = record
                site_items_list.append((iid, record["title"], record["url"]))
            else:
                record["last_seen"] = utc_now()
                if candidate["title"]:
                    record["title"] = candidate["title"]
                if candidate.get("context"):
                    record["context"] = candidate["context"][:700]
                if candidate.get("upload_date"):
                    record["upload_date"] = candidate["upload_date"]
                record["is_pdf"] = bool(candidate.get("is_pdf", record.get("is_pdf", False)))

            if (
                ss["baseline_complete"]
                and record.get("status") == "pending"
                and int(record.get("attempts", 0)) < scan["max_pending_attempts"]
            ):
                pending.append((iid, record))

    state["initialized"] = all(
        site_state(state, site["id"])["baseline_complete"] for site in cfg["websites"]
    )

    pending.sort(key=lambda pair: pair[1].get("first_seen", ""), reverse=True)
    pending.sort(key=lambda pair: -local_score(
        pair[1]["title"], pair[1]["url"], pair[1].get("context", ""), scan["keywords"],
    ))
    pending = pending[: scan["gemini_batch_size"] * scan["gemini_max_calls_per_run"]]

    batch_size = scan["gemini_batch_size"]
    for start in range(0, len(pending), batch_size):
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
                record["attempts"] = int(record.get("attempts", 0)) + 1
                classification = result.get(str(index))
                if classification is None:
                    record["status"] = "pending"
                    record["last_error"] = "Gemini returned no classification"
                    continue
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
        and int(record.get("telegram_attempts", 0)) < 10
    ]
    ready.sort(key=lambda pair: pair[1].get("first_seen", ""), reverse=True)

    sent_count = 0
    for iid, record in ready[: scan["max_new_items_per_run"]]:
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
            record["status"] = "sent"
            record["last_error"] = None
            sent_count += 1
        elif permanent:
            record["status"] = "permanent_error"
            record["last_error"] = detail
            run_errors += 1
            print(f"[ERROR] Permanent Telegram error: {detail}", file=sys.stderr)
        else:
            record["status"] = "ready"
            record["last_error"] = detail
            run_errors += 1
            print(f"[WARN] Telegram delivery failed; will retry: {detail}", file=sys.stderr)

    _RUNTIME_PDF_CACHE.clear()

    state["stats"]["errors"] = int(state["stats"].get("errors", 0)) + run_errors
    refresh_stats(state)
    prune_state(state, scan["retention_days"])
    atomic_save_json(STATE_FILE, state)

    print(
        f"[DONE] initialized={state['initialized']} "
        f"sites={len(cfg['websites'])} "
        f"sent_this_run={sent_count} "
        f"pending={state['stats']['pending']} "
        f"errors_this_run={run_errors}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
