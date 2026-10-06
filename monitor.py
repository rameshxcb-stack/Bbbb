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
from urllib.parse import urljoin, urlparse, urlunparse

import pdfplumber
import requests
from bs4 import BeautifulSoup
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

# FIX 4: 95 → 97 (avoid skipping "Recruitment 01/2026" vs "Recruitment 02/2026")
FUZZY_DUPLICATE_THRESHOLD = 97

MAX_PDF_BYTES = 5 * 1024 * 1024
MAX_PDF_PAGES = 3
MAX_PDF_TEXT_CHARS = 2500
MAX_PDF_ATTEMPTS = 3
TELEGRAM_SAFE_LIMIT = 4000

NOTIFY_LANGUAGE = os.getenv("NOTIFY_LANGUAGE", "both").strip().lower()
if NOTIFY_LANGUAGE not in {"both", "hi", "en"}:
    NOTIFY_LANGUAGE = "both"

STALE_NOTICE_DAYS = int(os.getenv("STALE_NOTICE_DAYS", "30"))

USER_AGENT = os.getenv(
    "MONITOR_USER_AGENT",
    "Mozilla/5.0 (compatible; JharkhandNoticeMonitor/5.6)"
)

STRONG_KEYWORDS = [
    "recruitment", "vacancy", "post", "job", "result",
    "admit card", "answer key", "merit", "selection",
    "scholarship", "admission", "counselling",
    "notification", "notice", "tender", "appointment",
    "भर्ती", "परिणाम", "नियुक्ति", "प्रवेश", "छात्रवृत्ति",
    "सूचना", "नोटिस", "निविदा"
]


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

# FIX 1: Hindi months added to regex
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
        "max_new_items_per_run": 30,
        "gemini_batch_size": 3,
        "gemini_max_calls_per_run": 25,
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
        "version": 14,
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
        record.setdefault("telegram_attempts", 0)
        record.setdefault("upload_date", None)
        record.setdefault("first_seen", utc_now())
        record.setdefault("last_seen", record["first_seen"])
    state["version"] = 14
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

        # FIX 2: Prefer <tr> so date (in sibling <td>) is included in context
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
        try:
            response = session.get(page, timeout=timeout, allow_redirects=True)
            if response.status_code >= 400:
                raise RuntimeError(f"HTTP {response.status_code}")
            final_url = canonical_url(response.url)
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
# PDF
# ---------------------------------------------------------------------------

def download_pdf_text(session, pdf_url, timeout=30):
    try:
        response = session.get(pdf_url, timeout=timeout)
        if response.status_code >= 400:
            return ""
        content_length = response.headers.get("content-length")
        if content_length:
            try:
                if int(content_length) > MAX_PDF_BYTES:
                    return ""
            except (TypeError, ValueError):
                pass
        content = response.content
        if not content or len(content) > MAX_PDF_BYTES:
            return ""
        text_parts = []
        with pdfplumber.open(io.BytesIO(content)) as pdf:
            for page in pdf.pages[:MAX_PDF_PAGES]:
                try:
                    page_text = page.extract_text() or ""
                except Exception:
                    page_text = ""
                if page_text:
                    text_parts.append(page_text)
        return clean_text("\n".join(text_parts), MAX_PDF_TEXT_CHARS)
    except Exception as exc:
        print(f"[WARN] PDF extract failed for {pdf_url}: {exc}", file=sys.stderr)
        return ""


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
        "IMPORTANT: If 'pdf_text' is provided, treat it as PRIMARY source.\n\n"

        "── CATEGORY-SPECIFIC EXTRACTION ──\n\n"

        "VACANCY: total_posts (int), post_details (array of "
        "{post_name, category (UR/OBC/SC/ST/EWS), vacancies}), qualification, "
        "age_limit, pay_scale, application_fee, last_date, apply_link\n\n"

        "RESULT: result_for, exam_name, session, semester, result_date, "
        "result_link, rechecking_last_date, rechecking_link\n\n"

        "ADMIT_CARD: exam_name, session, semester, exam_date, "
        "download_start_date, download_last_date, roll_no_required, admit_card_link\n\n"

        "ANSWER_KEY: exam_name, session, objection_start_date, "
        "objection_last_date, objection_fee, answer_key_link, objection_link\n\n"

        "ADMISSION: course_name, session, university_name, eligibility, "
        "application_fee, last_date, counselling_date, apply_link\n\n"

        "COUNSELLING: course_name, round, counselling_date, "
        "counselling_time, venue, apply_link\n\n"

        "SCHOLARSHIP: scheme_name, scholarship_amount, eligibility, "
        "applicable_category, income_limit, last_date, apply_link\n\n"

        "EXAM_SCHEDULE: exam_name, session, semester, course, "
        "exam_start_date, exam_end_date, exam_time, timetable_link\n\n"

        "TENDER: tender_no, work_description, issuing_authority, "
        "estimated_cost, emd_amount, tender_fee, submission_last_date, "
        "opening_date, submission_mode, apply_link\n\n"

        "GAZETTE: gazette_no, gazette_type (E-Gazette/Gazetteer/Official), "
        "subject, issuing_authority, publication_date, gazette_link\n\n"

        "LAND_REVENUE: notification_no, subject, "
        "land_location (village/plot), affected_area, "
        "notification_type (Acquisition/Revenue/Transfer), "
        "issuing_authority, effective_date, order_link\n\n"

        "PRESS_RELEASE: subject, issuing_department, release_date, "
        "reference_no, release_link\n\n"

        "ANNOUNCEMENT: subject, issuing_authority, reference_no, "
        "effective_date, apply_link\n\n"

        "PUBLICATION: publication_name, publication_type, "
        "publisher, publication_date, download_link\n\n"

        "NOTICE: subject, reference_no, issuing_authority, "
        "effective_date, order_link\n\n"

        "Do NOT invent facts. Use null when unsure.\n\n"

        "Schema:\n"
        '{"items":[{'
        '"id":"0","important":true,"category":"vacancy","summary":"...",'
        '"total_posts":null,"post_details":[],"qualification":null,'
        '"age_limit":null,"pay_scale":null,"application_fee":null,'
        '"last_date":null,"apply_link":null,'
        '"result_for":null,"exam_name":null,"session":null,"semester":null,'
        '"result_date":null,"result_link":null,'
        '"rechecking_last_date":null,"rechecking_link":null,'
        '"exam_date":null,"download_start_date":null,"download_last_date":null,'
        '"roll_no_required":null,"admit_card_link":null,'
        '"objection_start_date":null,"objection_last_date":null,'
        '"objection_fee":null,"answer_key_link":null,"objection_link":null,'
        '"course_name":null,"university_name":null,'
        '"counselling_date":null,"counselling_time":null,"venue":null,'
        '"round":null,'
        '"scheme_name":null,"scholarship_amount":null,"eligibility":null,'
        '"applicable_category":null,"income_limit":null,'
        '"exam_start_date":null,"exam_end_date":null,"exam_time":null,'
        '"timetable_link":null,'
        '"tender_no":null,"work_description":null,"issuing_authority":null,'
        '"estimated_cost":null,"emd_amount":null,"tender_fee":null,'
        '"submission_last_date":null,"opening_date":null,"submission_mode":null,'
        '"gazette_no":null,"gazette_type":null,"publication_date":null,'
        '"gazette_link":null,'
        '"notification_no":null,"land_location":null,"affected_area":null,'
        '"notification_type":null,"effective_date":null,"order_link":null,'
        '"issuing_department":null,"release_date":null,"reference_no":null,'
        '"release_link":null,'
        '"publication_name":null,"publication_type":null,"publisher":null,'
        '"download_link":null,'
        '"subject":null'
        '}]}\n\n'
        + json.dumps(prompt_items, ensure_ascii=False)
    )


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
            "total_posts": row.get("total_posts"),
            "post_details": clean_posts,
            "qualification": _str(row, "qualification", 200),
            "age_limit": _str(row, "age_limit", 100),
            "pay_scale": _str(row, "pay_scale", 150),
            "application_fee": _str(row, "application_fee", 200),
            "last_date": _str(row, "last_date", 80),
            "apply_link": _str(row, "apply_link", 500),
            "result_for": _str(row, "result_for", 200),
            "exam_name": _str(row, "exam_name", 200),
            "session": _str(row, "session", 80),
            "semester": _str(row, "semester", 60),
            "result_date": _str(row, "result_date", 80),
            "result_link": _str(row, "result_link", 500),
            "rechecking_last_date": _str(row, "rechecking_last_date", 80),
            "rechecking_link": _str(row, "rechecking_link", 500),
            "exam_date": _str(row, "exam_date", 80),
            "download_start_date": _str(row, "download_start_date", 80),
            "download_last_date": _str(row, "download_last_date", 80),
            "roll_no_required": row.get("roll_no_required"),
            "admit_card_link": _str(row, "admit_card_link", 500),
            "objection_start_date": _str(row, "objection_start_date", 80),
            "objection_last_date": _str(row, "objection_last_date", 80),
            "objection_fee": _str(row, "objection_fee", 100),
            "answer_key_link": _str(row, "answer_key_link", 500),
            "objection_link": _str(row, "objection_link", 500),
            "course_name": _str(row, "course_name", 200),
            "university_name": _str(row, "university_name", 200),
            "counselling_date": _str(row, "counselling_date", 80),
            "counselling_time": _str(row, "counselling_time", 60),
            "venue": _str(row, "venue", 200),
            "round": _str(row, "round", 60),
            "scheme_name": _str(row, "scheme_name", 200),
            "scholarship_amount": _str(row, "scholarship_amount", 100),
            "eligibility": _str(row, "eligibility", 250),
            "applicable_category": _str(row, "applicable_category", 100),
            "income_limit": _str(row, "income_limit", 100),
            "exam_start_date": _str(row, "exam_start_date", 80),
            "exam_end_date": _str(row, "exam_end_date", 80),
            "exam_time": _str(row, "exam_time", 60),
            "timetable_link": _str(row, "timetable_link", 500),
            "tender_no": _str(row, "tender_no", 100),
            "work_description": _str(row, "work_description", 300),
            "issuing_authority": _str(row, "issuing_authority", 200),
            "estimated_cost": _str(row, "estimated_cost", 100),
            "emd_amount": _str(row, "emd_amount", 100),
            "tender_fee": _str(row, "tender_fee", 100),
            "submission_last_date": _str(row, "submission_last_date", 80),
            "opening_date": _str(row, "opening_date", 80),
            "submission_mode": _str(row, "submission_mode", 60),
            "gazette_no": _str(row, "gazette_no", 100),
            "gazette_type": _str(row, "gazette_type", 100),
            "publication_date": _str(row, "publication_date", 80),
            "gazette_link": _str(row, "gazette_link", 500),
            "notification_no": _str(row, "notification_no", 100),
            "land_location": _str(row, "land_location", 250),
            "affected_area": _str(row, "affected_area", 100),
            "notification_type": _str(row, "notification_type", 100),
            "effective_date": _str(row, "effective_date", 80),
            "order_link": _str(row, "order_link", 500),
            "issuing_department": _str(row, "issuing_department", 200),
            "release_date": _str(row, "release_date", 80),
            "reference_no": _str(row, "reference_no", 100),
            "release_link": _str(row, "release_link", 500),
            "publication_name": _str(row, "publication_name", 200),
            "publication_type": _str(row, "publication_type", 100),
            "publisher": _str(row, "publisher", 200),
            "download_link": _str(row, "download_link", 500),
            "subject": _str(row, "subject", 200),
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
            "pdf_text": item.get("pdf_text", "")[:2000],
        }
        for i, item in enumerate(items)
    ]
    prompt = _build_prompt(prompt_items)
    endpoint = f"https://generativelanguage.googleapis.com/v1beta/models/{model}:generateContent"
    payload = {
        "contents": [{"parts": [{"text": prompt}]}],
        "generationConfig": {
            "responseMimeType": "application/json",
            "maxOutputTokens": 8192,
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


# ---------------------------------------------------------------------------
# Message formatting
# ---------------------------------------------------------------------------

CATEGORY_EMOJI = {
    "vacancy": "💼",
    "result": "📊",
    "admit_card": "🎫",
    "answer_key": "🔑",
    "admission": "🎓",
    "counselling": "🎯",
    "scholarship": "🎓",
    "exam_schedule": "📅",
    "tender": "📑",
    "gazette": "📰",
    "land_revenue": "🏞️",
    "press_release": "📢",
    "announcement": "📣",
    "publication": "📚",
    "notice": "📌",
    "other": "📎",
}


def _safe_str(value, limit=300):
    if value is None:
        return None
    text = clean_text(str(value), limit)
    return text or None


_LABELS_HI = {
    "total_posts": "कुल पद", "post_breakdown": "पद की जानकारी",
    "qualification": "योग्यता", "age_limit": "उम्र सीमा",
    "pay_scale": "वेतन", "application_fee": "फ़ीस / चार्जेस",
    "last_date": "आख़िरी तारीख़", "apply_online": "ऑनलाइन अप्लाई करें",
    "result_for": "रिजल्ट किसका है", "declared_on": "रिजल्ट की तारीख़",
    "check_result": "रिजल्ट देखें", "session": "सत्र",
    "semester": "सेमेस्टर",
    "rechecking_last_date": "रीचेकिंग आख़िरी तारीख़", "rechecking_link": "रीचेकिंग लिंक",
    "exam": "एग्ज़ाम", "exam_date": "एग्ज़ाम की तारीख़",
    "download_admit_card": "एडमिट कार्ड डाउनलोड करें",
    "download_start_date": "डाउनलोड शुरू", "download_last_date": "डाउनलोड आख़िरी",
    "view_answer_key": "आंसर की देखें",
    "objection_start_date": "आपत्ति शुरू", "objection_last_date": "आपत्ति आख़िरी",
    "objection_fee": "आपत्ति शुल्क", "objection_link": "आपत्ति दर्ज करें",
    "course": "कोर्स", "university_name": "यूनिवर्सिटी",
    "counselling_date": "काउंसलिंग तारीख़", "counselling_time": "समय",
    "venue": "स्थान",
    "scheme_name": "स्कीम", "amount": "अमाउंट / रकम",
    "eligibility": "कौन अप्लाई कर सकता है", "applicable_category": "किस श्रेणी के लिए",
    "income_limit": "आय सीमा",
    "exam_start_date": "एग्ज़ाम शुरू", "exam_end_date": "एग्ज़ाम ख़त्म",
    "exam_time": "एग्ज़ाम का समय", "timetable_link": "टाइम टेबल देखें",
    "round": "राउंड",
    "tender_no": "निविदा संख्या", "work_description": "कार्य विवरण",
    "issuing_authority": "जारीकर्ता विभाग", "estimated_cost": "अनुमानित लागत",
    "emd_amount": "EMD / बयाना राशि", "tender_fee": "निविदा शुल्क",
    "submission_last_date": "जमा आख़िरी", "opening_date": "खोलने की तारीख़",
    "submission_mode": "जमा तरीक़ा", "download_tender": "निविदा डाउनलोड करें",
    "gazette_no": "गजट संख्या", "gazette_type": "गजट प्रकार",
    "publication_date": "प्रकाशन तारीख़", "gazette_link": "गजट देखें",
    "notification_no": "अधिसूचना संख्या", "land_location": "भूमि स्थान",
    "affected_area": "प्रभावित क्षेत्र", "notification_type": "अधिसूचना प्रकार",
    "effective_date": "प्रभावी तारीख़", "order_link": "आदेश देखें",
    "issuing_department": "विभाग", "release_date": "जारी तारीख़",
    "reference_no": "संदर्भ संख्या", "release_link": "प्रेस रिलीज़ देखें",
    "publication_name": "प्रकाशन", "publication_type": "प्रकार",
    "publisher": "प्रकाशक", "download_link": "डाउनलोड करें",
    "subject": "विषय",
    "read_full": "पूरी नोटिफिकेशन देखें",
}

_LABELS_EN = {
    "total_posts": "Total Posts", "post_breakdown": "Post-wise Breakdown",
    "qualification": "Qualification", "age_limit": "Age Limit",
    "pay_scale": "Pay Scale", "application_fee": "Application Fee",
    "last_date": "Last Date", "apply_online": "Apply Online",
    "result_for": "Result For", "declared_on": "Declared",
    "check_result": "Check Result", "session": "Session",
    "semester": "Semester",
    "rechecking_last_date": "Rechecking Last Date", "rechecking_link": "Rechecking Link",
    "exam": "Exam", "exam_date": "Exam Date",
    "download_admit_card": "Download Admit Card",
    "download_start_date": "Download Starts", "download_last_date": "Download Last Date",
    "view_answer_key": "View Answer Key",
    "objection_start_date": "Objection Starts", "objection_last_date": "Objection Last Date",
    "objection_fee": "Objection Fee", "objection_link": "File Objection",
    "course": "Course", "university_name": "University",
    "counselling_date": "Counselling Date", "counselling_time": "Time",
    "venue": "Venue",
    "scheme_name": "Scheme", "amount": "Amount",
    "eligibility": "Eligibility", "applicable_category": "Applicable Category",
    "income_limit": "Income Limit",
    "exam_start_date": "Exam Starts", "exam_end_date": "Exam Ends",
    "exam_time": "Exam Time", "timetable_link": "View Timetable",
    "round": "Round",
    "tender_no": "Tender No", "work_description": "Work Description",
    "issuing_authority": "Issuing Authority", "estimated_cost": "Estimated Cost",
    "emd_amount": "EMD", "tender_fee": "Tender Fee",
    "submission_last_date": "Submission Last Date", "opening_date": "Opening Date",
    "submission_mode": "Submission Mode", "download_tender": "Download Tender",
    "gazette_no": "Gazette No", "gazette_type": "Gazette Type",
    "publication_date": "Publication Date", "gazette_link": "View Gazette",
    "notification_no": "Notification No", "land_location": "Land Location",
    "affected_area": "Affected Area", "notification_type": "Notification Type",
    "effective_date": "Effective Date", "order_link": "View Order",
    "issuing_department": "Department", "release_date": "Release Date",
    "reference_no": "Reference No", "release_link": "View Press Release",
    "publication_name": "Publication", "publication_type": "Type",
    "publisher": "Publisher", "download_link": "Download",
    "subject": "Subject",
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
    _line(lines, "🎓", "qualification", _safe_str(c.get("qualification")))
    _line(lines, "🎂", "age_limit", _safe_str(c.get("age_limit")))
    _line(lines, "💰", "pay_scale", _safe_str(c.get("pay_scale")))
    _line(lines, "💳", "application_fee", _safe_str(c.get("application_fee")))
    _line(lines, "📅", "last_date", _safe_str(c.get("last_date")))
    _link_line(lines, "🌐", "apply_online", _safe_str(c.get("apply_link"), 500))


def _format_result(lines, c):
    _line(lines, "📝", "result_for", _safe_str(c.get("result_for")))
    _line(lines, "📝", "exam", _safe_str(c.get("exam_name")))
    _line(lines, "📅", "session", _safe_str(c.get("session")))
    _line(lines, "📚", "semester", _safe_str(c.get("semester")))
    _line(lines, "📅", "declared_on", _safe_str(c.get("result_date")))
    _link_line(lines, "📄", "check_result", _safe_str(c.get("result_link"), 500))
    _line(lines, "🔄", "rechecking_last_date", _safe_str(c.get("rechecking_last_date")))
    _link_line(lines, "🔗", "rechecking_link", _safe_str(c.get("rechecking_link"), 500))


def _format_admit_card(lines, c):
    _line(lines, "📝", "exam", _safe_str(c.get("exam_name")))
    _line(lines, "📅", "session", _safe_str(c.get("session")))
    _line(lines, "📚", "semester", _safe_str(c.get("semester")))
    _line(lines, "📅", "exam_date", _safe_str(c.get("exam_date")))
    _line(lines, "⬇️", "download_start_date", _safe_str(c.get("download_start_date")))
    _line(lines, "📅", "download_last_date", _safe_str(c.get("download_last_date")))
    _link_line(lines, "🎫", "download_admit_card", _safe_str(c.get("admit_card_link"), 500))


def _format_answer_key(lines, c):
    _line(lines, "📝", "exam", _safe_str(c.get("exam_name")))
    _line(lines, "📅", "session", _safe_str(c.get("session")))
    _link_line(lines, "🔑", "view_answer_key", _safe_str(c.get("answer_key_link"), 500))
    _line(lines, "📅", "objection_start_date", _safe_str(c.get("objection_start_date")))
    _line(lines, "📅", "objection_last_date", _safe_str(c.get("objection_last_date")))
    _line(lines, "💳", "objection_fee", _safe_str(c.get("objection_fee")))
    _link_line(lines, "🔗", "objection_link", _safe_str(c.get("objection_link"), 500))


def _format_admission(lines, c):
    _line(lines, "🎓", "course", _safe_str(c.get("course_name")))
    _line(lines, "🏛️", "university_name", _safe_str(c.get("university_name")))
    _line(lines, "📅", "session", _safe_str(c.get("session")))
    _line(lines, "✅", "eligibility", _safe_str(c.get("eligibility")))
    _line(lines, "💳", "application_fee", _safe_str(c.get("application_fee")))
    _line(lines, "📅", "last_date", _safe_str(c.get("last_date")))
    _line(lines, "🎯", "counselling_date", _safe_str(c.get("counselling_date")))
    _link_line(lines, "🌐", "apply_online", _safe_str(c.get("apply_link"), 500))


def _format_counselling(lines, c):
    _line(lines, "🎓", "course", _safe_str(c.get("course_name")))
    _line(lines, "🔢", "round", _safe_str(c.get("round")))
    _line(lines, "📅", "counselling_date", _safe_str(c.get("counselling_date")))
    _line(lines, "⏰", "counselling_time", _safe_str(c.get("counselling_time")))
    _line(lines, "📍", "venue", _safe_str(c.get("venue")))
    _link_line(lines, "🌐", "apply_online", _safe_str(c.get("apply_link"), 500))


def _format_scholarship(lines, c):
    _line(lines, "🎯", "scheme_name", _safe_str(c.get("scheme_name")))
    _line(lines, "💰", "amount", _safe_str(c.get("scholarship_amount")))
    _line(lines, "👥", "applicable_category", _safe_str(c.get("applicable_category")))
    _line(lines, "💵", "income_limit", _safe_str(c.get("income_limit")))
    _line(lines, "🎓", "eligibility", _safe_str(c.get("eligibility")))
    _line(lines, "📅", "last_date", _safe_str(c.get("last_date")))
    _link_line(lines, "🌐", "apply_online", _safe_str(c.get("apply_link"), 500))


def _format_exam_schedule(lines, c):
    _line(lines, "📝", "exam", _safe_str(c.get("exam_name")))
    _line(lines, "📅", "session", _safe_str(c.get("session")))
    _line(lines, "📚", "semester", _safe_str(c.get("semester")))
    _line(lines, "🎓", "course", _safe_str(c.get("course_name")))
    _line(lines, "📅", "exam_start_date", _safe_str(c.get("exam_start_date")))
    _line(lines, "📅", "exam_end_date", _safe_str(c.get("exam_end_date")))
    _line(lines, "⏰", "exam_time", _safe_str(c.get("exam_time")))
    _link_line(lines, "📄", "timetable_link", _safe_str(c.get("timetable_link"), 500))


def _format_tender(lines, c):
    _line(lines, "📋", "tender_no", _safe_str(c.get("tender_no")))
    _line(lines, "📝", "work_description", _safe_str(c.get("work_description")))
    _line(lines, "🏢", "issuing_authority", _safe_str(c.get("issuing_authority")))
    _line(lines, "💰", "estimated_cost", _safe_str(c.get("estimated_cost")))
    _line(lines, "💳", "emd_amount", _safe_str(c.get("emd_amount")))
    _line(lines, "📄", "tender_fee", _safe_str(c.get("tender_fee")))
    _line(lines, "📅", "submission_last_date", _safe_str(c.get("submission_last_date")))
    _line(lines, "📅", "opening_date", _safe_str(c.get("opening_date")))
    _line(lines, "🌐", "submission_mode", _safe_str(c.get("submission_mode")))
    _link_line(lines, "🔗", "download_tender", _safe_str(c.get("apply_link"), 500))


def _format_gazette(lines, c):
    _line(lines, "📋", "gazette_no", _safe_str(c.get("gazette_no")))
    _line(lines, "📰", "gazette_type", _safe_str(c.get("gazette_type")))
    _line(lines, "📝", "subject", _safe_str(c.get("subject")))
    _line(lines, "🏢", "issuing_authority", _safe_str(c.get("issuing_authority")))
    _line(lines, "📅", "publication_date", _safe_str(c.get("publication_date")))
    _link_line(lines, "🔗", "gazette_link", _safe_str(c.get("gazette_link"), 500))


def _format_land_revenue(lines, c):
    _line(lines, "📋", "notification_no", _safe_str(c.get("notification_no")))
    _line(lines, "📝", "subject", _safe_str(c.get("subject")))
    _line(lines, "🏞️", "land_location", _safe_str(c.get("land_location")))
    _line(lines, "📐", "affected_area", _safe_str(c.get("affected_area")))
    _line(lines, "🔖", "notification_type", _safe_str(c.get("notification_type")))
    _line(lines, "🏢", "issuing_authority", _safe_str(c.get("issuing_authority")))
    _line(lines, "📅", "effective_date", _safe_str(c.get("effective_date")))
    _link_line(lines, "🔗", "order_link", _safe_str(c.get("order_link"), 500))


def _format_press_release(lines, c):
    _line(lines, "📝", "subject", _safe_str(c.get("subject")))
    _line(lines, "🏢", "issuing_department", _safe_str(c.get("issuing_department")))
    _line(lines, "📅", "release_date", _safe_str(c.get("release_date")))
    _line(lines, "🔖", "reference_no", _safe_str(c.get("reference_no")))
    _link_line(lines, "🔗", "release_link", _safe_str(c.get("release_link"), 500))


def _format_announcement(lines, c):
    _line(lines, "📝", "subject", _safe_str(c.get("subject")))
    _line(lines, "🏢", "issuing_authority", _safe_str(c.get("issuing_authority")))
    _line(lines, "🔖", "reference_no", _safe_str(c.get("reference_no")))
    _line(lines, "📅", "effective_date", _safe_str(c.get("effective_date")))
    _link_line(lines, "🌐", "apply_online", _safe_str(c.get("apply_link"), 500))


def _format_publication(lines, c):
    _line(lines, "📚", "publication_name", _safe_str(c.get("publication_name")))
    _line(lines, "🔖", "publication_type", _safe_str(c.get("publication_type")))
    _line(lines, "🏢", "publisher", _safe_str(c.get("publisher")))
    _line(lines, "📅", "publication_date", _safe_str(c.get("publication_date")))
    _link_line(lines, "🔗", "download_link", _safe_str(c.get("download_link"), 500))


def _format_notice(lines, c):
    _line(lines, "📝", "subject", _safe_str(c.get("subject")))
    _line(lines, "🔖", "reference_no", _safe_str(c.get("reference_no")))
    _line(lines, "🏢", "issuing_authority", _safe_str(c.get("issuing_authority")))
    _line(lines, "📅", "effective_date", _safe_str(c.get("effective_date")))
    _link_line(lines, "🔗", "order_link", _safe_str(c.get("order_link"), 500))


_FORMATTERS = {
    "vacancy": _format_vacancy,
    "result": _format_result,
    "admit_card": _format_admit_card,
    "answer_key": _format_answer_key,
    "admission": _format_admission,
    "counselling": _format_counselling,
    "scholarship": _format_scholarship,
    "exam_schedule": _format_exam_schedule,
    "tender": _format_tender,
    "gazette": _format_gazette,
    "land_revenue": _format_land_revenue,
    "press_release": _format_press_release,
    "announcement": _format_announcement,
    "publication": _format_publication,
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

    lines = [f"🔔 <b>{site_name}</b>", "", f"<b>{title}</b>", ""]
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
            return download_pdf_text(make_session(), record["url"], timeout)
        except Exception as exc:
            print(f"[WARN] PDF fetch error: {exc}", file=sys.stderr)
            return ""

    with ThreadPoolExecutor(max_workers=3) as ex:
        futures = {ex.submit(_fetch_one, record): (iid, record) for iid, record in targets}
        for fut in as_completed(futures):
            iid, record = futures[fut]
            try:
                text = fut.result()
            except Exception:
                text = ""
            record["pdf_attempts"] = int(record.get("pdf_attempts", 0)) + 1
            if text:
                record["pdf_text"] = text[:MAX_PDF_TEXT_CHARS]
                record["pdf_extracted"] = True


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
    global STALE_NOTICE_DAYS
    try:
        cfg = get_config()
        state = load_state()
    except Exception as exc:
        print(f"[FATAL] Configuration/state error: {exc}", file=sys.stderr)
        return 2

    token = os.getenv("TELEGRAM_BOT_TOKEN", "").strip()
    chat_id = os.getenv("TELEGRAM_CHAT_ID", "").strip()
    gemini_key = os.getenv("GEMINI_API_KEY", "").strip()
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
                    "pdf_text": "", "pdf_attempts": 0, "telegram_attempts": 0,
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
                        "pdf_text": "", "pdf_attempts": 0, "telegram_attempts": 0,
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
                    "pdf_text": "", "pdf_attempts": 0, "telegram_attempts": 0,
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
        message = truncate_telegram(format_message(site, record, record.get("classification")))
        ok, permanent, detail = send_telegram(token, chat_id, message)
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
