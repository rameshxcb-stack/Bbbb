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

FUZZY_DUPLICATE_THRESHOLD = 95

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
    "Mozilla/5.0 (compatible; JharkhandNoticeMonitor/5.3)"
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
# Navigation / listing page filters
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


def _is_navigation_url(url: str) -> bool:
    try:
        parsed = urlparse(url)
        target = (parsed.path or "") + ("?" + parsed.query if parsed.query else "")
    except Exception:
        return False
    for pat in _NON_NOTICE_URL_PATTERNS:
        if pat.search(target):
            return True
    return False


def _is_generic_title(title: str) -> bool:
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


def _is_language_selector(title: str) -> bool:
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


def _is_empty_page_text(html_text: str) -> bool:
    if not html_text:
        return False
    sample = html_text[:8000].lower()
    return any(phrase in sample for phrase in _EMPTY_PAGE_PHRASES)


# ---------------------------------------------------------------------------
# Full-date extraction (with Hindi month support)
# ---------------------------------------------------------------------------

_MONTH_NAMES = {
    # English
    "january": 1, "jan": 1, "february": 2, "feb": 2,
    "march": 3, "mar": 3, "april": 4, "apr": 4,
    "may": 5, "june": 6, "jun": 6, "july": 7, "jul": 7,
    "august": 8, "aug": 8, "september": 9, "sep": 9, "sept": 9,
    "october": 10, "oct": 10, "november": 11, "nov": 11,
    "december": 12, "dec": 12,
    # Hindi (Devanagari)
    "जनवरी": 1, "फरवरी": 2, "मार्च": 3, "अप्रैल": 4,
    "मई": 5, "जून": 6, "जुलाई": 7, "अगस्त": 8,
    "सितंबर": 9, "सितम्बर": 9, "अक्टूबर": 10, "अक्तूबर": 10,
    "नवंबर": 11, "नवम्बर": 11, "दिसंबर": 12, "दिसम्बर": 12,
}

# English month names for regex (Hindi months rarely appear in full-date pattern)
_MONTH_REGEX = (
    r"jan|feb|mar|apr|may|jun|jul|aug|sep|sept|oct|nov|dec|"
    r"january|february|march|april|june|july|august|"
    r"september|october|november|december"
)

_FULL_DATE_PATTERNS = [
    re.compile(r"\b(\d{1,2})[/\-.](\d{1,2})[/\-.](\d{4})\b"),
    re.compile(r"\b(\d{4})-(\d{1,2})-(\d{1,2})\b"),
    re.compile(
        r"\b(\d{1,2})(?:st|nd|rd|th)?[\s\-]+"
        r"(" + _MONTH_REGEX + r")"
        r"[\s\-,]+(\d{4})\b",
        re.I,
    ),
    re.compile(
        r"\b(" + _MONTH_REGEX + r")"
        r"[\s\-]+(\d{1,2})(?:st|nd|rd|th)?[\s\-,]+(\d{4})\b",
        re.I,
    ),
]


def _extract_full_dates(text: str) -> List[datetime]:
    if not text:
        return []
    dates: List[datetime] = []
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
                    d = int(a)
                    mo = _MONTH_NAMES.get(b.lower(), 0)
                    y = int(c)
                elif a and not a.isdigit():
                    mo = _MONTH_NAMES.get(a.lower(), 0)
                    d = int(b)
                    y = int(c)
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


# ---------------------------------------------------------------------------
# Upload date extraction (authoritative source)
# ---------------------------------------------------------------------------

_UPLOAD_DATE_TEXT_PATTERNS = [
    re.compile(
        r"(?:published|posted|uploaded|issued|dated)"
        r"\s*(?:on|at|:|\-)?\s*"
        r"(\d{1,2}[/\-.]\d{1,2}[/\-.]\d{4})",
        re.I,
    ),
    re.compile(
        r"(?:published|posted|uploaded|issued|dated)"
        r"\s*(?:on|at|:|\-)?\s*"
        r"(\d{1,2}(?:st|nd|rd|th)?\s+"
        r"(?:" + _MONTH_REGEX + r")"
        r"\s+\d{4})",
        re.I,
    ),
    re.compile(
        r"(?:दिनांक|प्रकाशित|जारी|अपलोड|अद्यतन)"
        r"\s*[:\-]?\s*"
        r"(\d{1,2}[/\-.]\d{1,2}[/\-.]\d{4})",
        re.I,
    ),
]


def _extract_upload_date(anchor_tag) -> Optional[datetime]:
    """
    Extract publication/upload date near a link.

    Priority for search_root:
      1. <tr>        (NIC table sites — date in sibling <td>)  ← CRITICAL
      2. <li>        (list-based sites)
      3. <article>   (WordPress-style sites)
      4. <div>/<section>  (fallback — riskier)
      5. anchor's parent (last resort)

    Returns timezone-aware datetime or None.
    """
    try:
        # Prefer <tr> first — critical for NIC table-based sites
        search_root = (
            anchor_tag.find_parent("tr")
            or anchor_tag.find_parent("li")
            or anchor_tag.find_parent("article")
            or anchor_tag.find_parent(["div", "section"])
            or anchor_tag.parent
        )

        if not search_root:
            return None

        # 1. <time datetime="...">
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

        # 2. Text patterns ("Published:", "दिनांक:", etc.)
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


def _is_stale_notice(
    title: str,
    context: str,
    url: str,
    upload_date: Optional[datetime] = None,
) -> bool:
    """
    Decide if a notice is too old to alert.

    Priority:
      0. Upload date (authoritative) — if available, use it.
      1. Full date in content ("21 March 2021", "05/11/2026").
      2. Year-only mentions → IGNORE (weak signal, allow).

    Returns True only when we have STRONG evidence of old age.
    """
    now = datetime.now(timezone.utc)
    cutoff = now - timedelta(days=STALE_NOTICE_DAYS)

    # ---- Level 0: authoritative upload date ---------------------------
    if upload_date is not None:
        if upload_date.tzinfo is None:
            upload_date = upload_date.replace(tzinfo=timezone.utc)
        if upload_date > now:
            return False   # Future date → allow
        return upload_date < cutoff

    # ---- Level 1: full date in content --------------------------------
    haystack = f"{title} {context}".strip()
    all_dates = _extract_full_dates(haystack)
    if all_dates:
        latest = max(all_dates)
        if latest > now:
            return False
        return latest < cutoff

    # ---- Level 2: no signal → allow -----------------------------------
    return False


# ---------------------------------------------------------------------------
# Utilities
# ---------------------------------------------------------------------------

def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat()


def clean_text(value: str, limit: int = 500) -> str:
    value = re.sub(r"\s+", " ", value or "").strip()
    return value[:limit]


def load_json(path: Path, default: Any) -> Any:
    try:
        with path.open("r", encoding="utf-8") as f:
            return json.load(f)
    except FileNotFoundError:
        return default
    except json.JSONDecodeError as exc:
        raise RuntimeError(f"Invalid JSON in {path.name}: {exc}") from exc


def atomic_save_json(path: Path, data: Any) -> None:
    tmp = path.with_suffix(path.suffix + ".tmp")
    with tmp.open("w", encoding="utf-8") as f:
        json.dump(data, f, ensure_ascii=False, indent=2)
        f.write("\n")
        f.flush()
        os.fsync(f.fileno())
    os.replace(tmp, path)


def canonical_url(raw: str) -> str:
    raw = (raw or "").strip()
    p = urlparse(raw)
    if not p.scheme or not p.netloc:
        return raw
    return urlunparse((p.scheme.lower(), p.netloc.lower(), p.path or "/", "", p.query, ""))


def same_host(a: str, b: str) -> bool:
    return urlparse(a).netloc.lower() == urlparse(b).netloc.lower()


def is_http_url(url: str) -> bool:
    return urlparse(url).scheme in {"http", "https"}


def is_pdf(url: str) -> bool:
    return urlparse(url).path.lower().endswith(".pdf")


def make_session() -> requests.Session:
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

def get_config() -> Dict[str, Any]:
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
        "gemini_batch_size": 4,
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

def default_state() -> Dict[str, Any]:
    return {
        "version": 11,
        "initialized": False,
        "last_run": None,
        "items": {},
        "sites": {},
        "stats": {"runs": 0, "sent": 0, "ignored": 0, "pending": 0, "errors": 0},
    }


def load_state() -> Dict[str, Any]:
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

    state["version"] = 11
    return state


def site_state(state: Dict[str, Any], site_id: str) -> Dict[str, Any]:
    s = state.setdefault("sites", {}).setdefault(site_id, {})
    s.setdefault("baseline_complete", False)
    s.setdefault("consecutive_failures", 0)
    s.setdefault("total_failures", 0)
    s.setdefault("last_success", None)
    s.setdefault("last_error", None)
    s.setdefault("last_error_at", None)
    s.setdefault("last_item_count", 0)
    return s


def mark_site_success(state: Dict[str, Any], site_id: str, count: int) -> None:
    s = site_state(state, site_id)
    s["consecutive_failures"] = 0
    s["last_success"] = utc_now()
    s["last_error"] = None
    s["last_error_at"] = None
    s["last_item_count"] = count


def mark_site_failure(state: Dict[str, Any], site_id: str, error: str) -> None:
    s = site_state(state, site_id)
    s["consecutive_failures"] += 1
    s["total_failures"] += 1
    s["last_error"] = clean_text(error, 500)
    s["last_error_at"] = utc_now()


# ---------------------------------------------------------------------------
# Scoring / IDs
# ---------------------------------------------------------------------------

def local_score(title: str, url: str, context: str, keywords: List[str]) -> int:
    text = f"{title} {url} {context}".lower()
    return sum(1 for kw in keywords if kw and kw in text)


def item_id(site_id: str, url: str, title: str, context: str = "") -> str:
    fingerprint = hashlib.sha256(
        clean_text(f"{title}|{context}", 900).lower().encode()
    ).hexdigest()[:12]
    raw = f"{site_id}|{canonical_url(url)}|{fingerprint}"
    return hashlib.sha256(raw.encode("utf-8")).hexdigest()[:32]


# ---------------------------------------------------------------------------
# Fuzzy dedup
# ---------------------------------------------------------------------------

def _normalize_title(title: str) -> str:
    return re.sub(r"[^\w\s]", " ", (title or "").lower()).strip()


def _url_path_segments(url: str) -> set:
    try:
        path = urlparse(url).path.strip("/").lower()
        return {seg for seg in path.split("/") if seg and len(seg) > 2}
    except Exception:
        return set()


def build_site_index(state: Dict[str, Any]) -> Dict[str, List[Tuple[str, str, str]]]:
    index: Dict[str, List[Tuple[str, str, str]]] = {}
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

        parent = a.find_parent(["li", "td", "article", "section", "div"])
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

        # Extract upload date (authoritative if present)
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
# PDF extraction
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
# Gemini classification
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
        result[str(index)] = {
            "important": important, "category": category,
            "summary": clean_text(item.get("title", ""), 180),
        }
    return result


def _build_prompt(prompt_items):
    return (
        "You classify and extract details from links on official "
        "Indian government/district websites. "
        "Return JSON only using the exact schema below.\n\n"
        "CRITICAL — set important=false for ALL of these:\n"
        "- Language selector links (titles like 'हिन्दी', 'English', 'संताली')\n"
        "- Category listing pages (e.g. 'Announcement/Advertisement', 'Notices')\n"
        "- Archive / past-notices pages\n"
        "- Pagination pages (URLs containing '/page/2/', '?page=', etc.)\n"
        "- Navigation pages (Home, Contact, About, Gallery, Departments)\n"
        "- Pages with titles like: 'Archive', 'More', '»', 'Next', 'Previous', "
        "  just numbers, or empty titles\n"
        "- Pages that say 'Sorry, no notice matched this category' or "
        "  'no records found' or 'no data found'\n"
        "- Generic description like 'listing page', 'category page', "
        "  'announcements and advertisements listing page'\n\n"
        "Set important=true ONLY for genuine, specific notices such as:\n"
        "- A specific recruitment/vacancy notice (with post details)\n"
        "- A specific result / admit card / answer key\n"
        "- A specific scholarship / admission notice\n"
        "- A specific tender notice\n"
        "- A specific appointment/order notification\n\n"
        "For EACH item, determine:\n"
        "1. important (true/false)\n"
        "2. category — one of: 'vacancy', 'result', 'admit_card', "
        "'answer_key', 'scholarship', 'admission', 'tender', 'notice', 'other'\n"
        "3. summary — 1-line summary (<= 150 chars).\n\n"
        "IMPORTANT: If 'pdf_text' is provided, treat it as PRIMARY source "
        "for extracting details. 'context' is secondary.\n\n"
        "If category is 'vacancy', ALSO extract (use null if not available):\n"
        "- total_posts (integer)\n"
        "- post_details: array of {post_name, category (UR/OBC/SC/ST/EWS/Other), vacancies}\n"
        "- qualification (string)\n- age_limit (string)\n"
        "- pay_scale (string)\n- application_fee (string)\n"
        "- last_date (string)\n- apply_link (string URL)\n\n"
        "If category is 'result': result_for, result_date, result_link\n"
        "If category is 'admit_card': exam_name, exam_date, admit_card_link\n"
        "If category is 'answer_key': exam_name, answer_key_link\n"
        "If category is 'scholarship': scholarship_amount, eligibility, last_date\n"
        "If category is 'admission': course_name, last_date, apply_link\n\n"
        "Do NOT invent facts. Use null when unsure.\n\n"
        "Schema:\n"
        '{"items":[{'
        '"id":"0","important":true,"category":"vacancy","summary":"...",'
        '"total_posts":10,'
        '"post_details":[{"post_name":"...","category":"UR","vacancies":5}],'
        '"qualification":"...","age_limit":"...","pay_scale":"...",'
        '"application_fee":"...","last_date":"...","apply_link":"...",'
        '"result_for":null,"result_date":null,"result_link":null,'
        '"exam_name":null,"exam_date":null,"admit_card_link":null,'
        '"answer_key_link":null,"scholarship_amount":null,"eligibility":null,'
        '"course_name":null'
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
            "qualification": clean_text(str(row.get("qualification") or ""), 200) or None,
            "age_limit": clean_text(str(row.get("age_limit") or ""), 100) or None,
            "pay_scale": clean_text(str(row.get("pay_scale") or ""), 150) or None,
            "application_fee": clean_text(str(row.get("application_fee") or ""), 200) or None,
            "last_date": clean_text(str(row.get("last_date") or ""), 80) or None,
            "apply_link": clean_text(str(row.get("apply_link") or ""), 500) or None,
            "result_for": clean_text(str(row.get("result_for") or ""), 200) or None,
            "result_date": clean_text(str(row.get("result_date") or ""), 80) or None,
            "result_link": clean_text(str(row.get("result_link") or ""), 500) or None,
            "exam_name": clean_text(str(row.get("exam_name") or ""), 200) or None,
            "exam_date": clean_text(str(row.get("exam_date") or ""), 80) or None,
            "admit_card_link": clean_text(str(row.get("admit_card_link") or ""), 500) or None,
            "answer_key_link": clean_text(str(row.get("answer_key_link") or ""), 500) or None,
            "scholarship_amount": clean_text(str(row.get("scholarship_amount") or ""), 100) or None,
            "eligibility": clean_text(str(row.get("eligibility") or ""), 250) or None,
            "course_name": clean_text(str(row.get("course_name") or ""), 200) or None,
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
    "vacancy": "💼", "result": "📊", "admit_card": "🎫",
    "answer_key": "🔑", "scholarship": "🎓", "admission": "🎓",
    "tender": "📑", "notice": "📌", "other": "📎",
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
    "check_result": "रिजल्ट देखें", "exam": "एग्ज़ाम",
    "exam_date": "एग्ज़ाम की तारीख़", "download_admit_card": "एडमिट कार्ड डाउनलोड करें",
    "view_answer_key": "आंसर की देखें", "amount": "अमाउंट / रकम",
    "eligibility": "कौन अप्लाई कर सकता है", "course": "कोर्स",
    "read_full": "पूरी नोटिफिकेशन देखें",
}

_LABELS_EN = {
    "total_posts": "Total Posts", "post_breakdown": "Post-wise Breakdown",
    "qualification": "Qualification", "age_limit": "Age Limit",
    "pay_scale": "Pay Scale", "application_fee": "Application Fee",
    "last_date": "Last Date", "apply_online": "Apply Online",
    "result_for": "Result For", "declared_on": "Declared",
    "check_result": "Check Result", "exam": "Exam",
    "exam_date": "Exam Date", "download_admit_card": "Download Admit Card",
    "view_answer_key": "View Answer Key", "amount": "Amount",
    "eligibility": "Eligibility", "course": "Course",
    "read_full": "View Full Notice",
}

_CATEGORY_NAMES_HI = {
    "vacancy": "भर्ती", "result": "रिजल्ट", "admit_card": "एडमिट कार्ड",
    "answer_key": "आंसर की", "scholarship": "स्कॉलरशिप",
    "admission": "एडमिशन", "tender": "टेंडर", "notice": "सूचना", "other": "अन्य",
}

_CATEGORY_NAMES_EN = {
    "vacancy": "Vacancy", "result": "Result", "admit_card": "Admit Card",
    "answer_key": "Answer Key", "scholarship": "Scholarship",
    "admission": "Admission", "tender": "Tender", "notice": "Notice", "other": "Other",
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
    if v := _safe_str(c.get("qualification")):
        lines.append(f"🎓 <b>{_labels('qualification')}:</b> {html.escape(v)}")
    if v := _safe_str(c.get("age_limit")):
        lines.append(f"🎂 <b>{_labels('age_limit')}:</b> {html.escape(v)}")
    if v := _safe_str(c.get("pay_scale")):
        lines.append(f"💰 <b>{_labels('pay_scale')}:</b> {html.escape(v)}")
    if v := _safe_str(c.get("application_fee")):
        lines.append(f"💳 <b>{_labels('application_fee')}:</b> {html.escape(v)}")
    if v := _safe_str(c.get("last_date")):
        lines.append(f"📅 <b>{_labels('last_date')}:</b> {html.escape(v)}")
    link = _safe_str(c.get("apply_link"), 500)
    if link:
        lines.append(f'🌐 <a href="{html.escape(link, quote=True)}">{html.escape(_labels("apply_online"))}</a>')


def _format_result(lines, c):
    if v := _safe_str(c.get("result_for")):
        lines.append(f"📝 <b>{_labels('result_for')}:</b> {html.escape(v)}")
    if v := _safe_str(c.get("result_date")):
        lines.append(f"📅 <b>{_labels('declared_on')}:</b> {html.escape(v)}")
    link = _safe_str(c.get("result_link"), 500)
    if link:
        lines.append(f'📄 <a href="{html.escape(link, quote=True)}">{html.escape(_labels("check_result"))}</a>')


def _format_admit_card(lines, c):
    if v := _safe_str(c.get("exam_name")):
        lines.append(f"📝 <b>{_labels('exam')}:</b> {html.escape(v)}")
    if v := _safe_str(c.get("exam_date")):
        lines.append(f"📅 <b>{_labels('exam_date')}:</b> {html.escape(v)}")
    link = _safe_str(c.get("admit_card_link"), 500)
    if link:
        lines.append(f'🎫 <a href="{html.escape(link, quote=True)}">{html.escape(_labels("download_admit_card"))}</a>')


def _format_answer_key(lines, c):
    if v := _safe_str(c.get("exam_name")):
        lines.append(f"📝 <b>{_labels('exam')}:</b> {html.escape(v)}")
    link = _safe_str(c.get("answer_key_link"), 500)
    if link:
        lines.append(f'🔑 <a href="{html.escape(link, quote=True)}">{html.escape(_labels("view_answer_key"))}</a>')


def _format_scholarship(lines, c):
    if v := _safe_str(c.get("scholarship_amount")):
        lines.append(f"💰 <b>{_labels('amount')}:</b> {html.escape(v)}")
    if v := _safe_str(c.get("eligibility")):
        lines.append(f"🎓 <b>{_labels('eligibility')}:</b> {html.escape(v)}")
    if v := _safe_str(c.get("last_date")):
        lines.append(f"📅 <b>{_labels('last_date')}:</b> {html.escape(v)}")


def _format_admission(lines, c):
    if v := _safe_str(c.get("course_name")):
        lines.append(f"🎓 <b>{_labels('course')}:</b> {html.escape(v)}")
    if v := _safe_str(c.get("last_date")):
        lines.append(f"📅 <b>{_labels('last_date')}:</b> {html.escape(v)}")
    link = _safe_str(c.get("apply_link"), 500)
    if link:
        lines.append(f'🌐 <a href="{html.escape(link, quote=True)}">{html.escape(_labels("apply_online"))}</a>')


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
        if category == "vacancy": _format_vacancy(lines, classification)
        elif category == "result": _format_result(lines, classification)
        elif category == "admit_card": _format_admit_card(lines, classification)
        elif category == "answer_key": _format_answer_key(lines, classification)
        elif category == "scholarship": _format_scholarship(lines, classification)
        elif category == "admission": _format_admission(lines, classification)
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
# State pruning / stats
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


def _parse_upload_date(raw) -> Optional[datetime]:
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

                # Use upload_date (authoritative) for staleness check
                upload_dt = _parse_upload_date(candidate.get("upload_date"))
                if _is_stale_notice(
                    candidate["title"],
                    candidate.get("context", ""),
                    candidate["url"],
                    upload_date=upload_dt,
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
                        "last_error": (
                            f"Stale notice "
                            f"(upload={candidate.get('upload_date')}, "
                            f"limit={STALE_NOTICE_DAYS}d)"
                        ),
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
