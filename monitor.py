# -*- coding: utf-8 -*-
import base64
import hashlib
import html
import importlib
import io
import json
import os
import re
import sys
import time
import threading
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


def _try_import(*names):
    for name in names:
        try:
            return importlib.import_module(name)
        except ImportError:
            continue
    return None


fitz = _try_import("pymupdf", "fitz")

_rapidocr_mod = _try_import("rapidocr_onnxruntime", "rapidocr")
RapidOCR = getattr(_rapidocr_mod, "RapidOCR", None) if _rapidocr_mod is not None else None
_RAPIDOCR_AVAILABLE = RapidOCR is not None

pytesseract = _try_import("pytesseract")
_PIL_Image = _try_import("PIL.Image")
_TESSERACT_AVAILABLE = pytesseract is not None and _PIL_Image is not None

try:
    from playwright.sync_api import sync_playwright, Error as PlaywrightError
    _PLAYWRIGHT_AVAILABLE = True
except ImportError:
    sync_playwright = None
    PlaywrightError = Exception
    _PLAYWRIGHT_AVAILABLE = False


BASE = Path(__file__).resolve().parent
CONFIG_FILE = BASE / "websites.json"
STATE_FILE = BASE / "state.json"

FALLBACK_MODELS = ["gemini-3.5-flash-lite", "gemini-3.1-flash-lite"]

FUZZY_DUPLICATE_THRESHOLD = 94
FUZZY_CROSS_PATH_THRESHOLD = 96
TELEGRAM_MAX_ATTEMPTS = 100
TELEGRAM_RETRY_WINDOW_HOURS = 168
TELEGRAM_RETRY_BASE_MINUTES = 20
TELEGRAM_RETRY_MAX_MINUTES = 360

MAX_PDF_SEND_BYTES = 45 * 1024 * 1024
MAX_GEMINI_PDF_BYTES = 18 * 1024 * 1024
MAX_PDF_PAGES = int(os.getenv("MAX_PDF_PAGES", "8"))
MAX_PDF_TEXT_CHARS = 4000
MAX_PDF_RAW_TEXT_CHARS = 8000
MAX_PDF_ATTEMPTS = 3
TELEGRAM_SAFE_LIMIT = 4000
TELEGRAM_CAPTION_LIMIT = 1024

_RUNTIME_PDF_CACHE_MAX_ITEMS = 20

GEMINI_MAX_OUTPUT_TOKENS = int(os.getenv("GEMINI_MAX_OUTPUT_TOKENS", "16384"))

OCR_ENABLED = os.getenv("OCR_ENABLED", "true").strip().lower() == "true"
OCR_DPI = int(os.getenv("OCR_DPI", "150"))
OCR_MIN_TEXT_CHARS = int(os.getenv("OCR_MIN_TEXT_CHARS", "200"))
OCR_MAX_WORKERS = int(os.getenv("OCR_MAX_WORKERS", "2"))
_OCR_MAX_PAGES = int(os.getenv("OCR_MAX_PAGES", "4"))

TESSERACT_ENABLED = os.getenv("TESSERACT_ENABLED", "true").strip().lower() == "true"
TESSERACT_LANG = os.getenv("TESSERACT_LANG", "hin+eng").strip() or "hin+eng"
TESSERACT_PSM = os.getenv("TESSERACT_PSM", "6").strip()

GEMINI_PDF_OCR_ENABLED = os.getenv("GEMINI_PDF_OCR_ENABLED", "true").strip().lower() == "true"
SEND_PDF_ENABLED = os.getenv("SEND_PDF_ENABLED", "true").strip().lower() == "true"

JS_RENDER_ENABLED = os.getenv("JS_RENDER_ENABLED", "true").strip().lower() == "true"
JS_RENDER_TIMEOUT_MS = int(os.getenv("JS_RENDER_TIMEOUT_MS", "25000"))
JS_WAIT_UNTIL = os.getenv("JS_WAIT_UNTIL", "domcontentloaded").strip() or "domcontentloaded"
JS_THIN_TEXT_THRESHOLD = int(os.getenv("JS_THIN_TEXT_THRESHOLD", "200"))
JS_MAX_RENDER_PER_SITE = int(os.getenv("JS_MAX_RENDER_PER_SITE", "40"))
JS_WAIT_AFTER_MS = max(0, min(30000, int(os.getenv("JS_WAIT_AFTER_MS", "2500"))))
JS_SCROLL_TO_BOTTOM = os.getenv("JS_SCROLL_TO_BOTTOM", "false").strip().lower() == "true"
JS_WAIT_FOR_SELECTOR_DEFAULT = os.getenv("JS_WAIT_FOR_SELECTOR_DEFAULT", "").strip()


NOTIFY_LANGUAGE = os.getenv("NOTIFY_LANGUAGE", "both").strip().lower()
if NOTIFY_LANGUAGE not in {"both", "hi", "en"}:
    NOTIFY_LANGUAGE = "both"

STALE_NOTICE_DAYS = int(os.getenv("STALE_NOTICE_DAYS", "10"))
OLD_YEAR_HINT_YEARS_BACK = int(os.getenv("OLD_YEAR_HINT_YEARS_BACK", "2"))
ETAG_CHECK_MAX_AGE_DAYS = int(os.getenv("ETAG_CHECK_MAX_AGE_DAYS", "14"))

USER_AGENT = os.getenv(
    "MONITOR_USER_AGENT",
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
    "(KHTML, like Gecko) Chrome/122.0.0.0 Safari/537.36"
)

JS_RENDER_USER_AGENT = os.getenv(
    "JS_RENDER_USER_AGENT",
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
    "(KHTML, like Gecko) Chrome/122.0.0.0 Safari/537.36"
)

STRONG_KEYWORDS = [
    "admission", "result", "admit card", "answer key", "examination",
    "exam", "semester", "revaluation", "migration", "certificate",
    "scholarship", "fee", "syllabus", "timetable", "counselling",
    "recruitment", "vacancy", "tender", "notice", "notification",
    "placement", "hostel", "convocation", "registration", "enrollment",
    "merit", "marksheet", "transcript", "bonafide", "grading", "cgpa", "gpa",
    "phd", "ph.d", "research", "internship", "challan", "demand draft",
    "eligibility", "qualification", "provisional", "backlog", "reappear",
    "supplementary", "marks", "score",
    "प्रवेश", "परिणाम", "प्रवेश पत्र", "उत्तर कुंजी", "परीक्षा",
    "सेमेस्टर", "पुनर्मूल्यांकन", "माइग्रेशन", "प्रमाण पत्र",
    "छात्रवृत्ति", "शुल्क", "पाठ्यक्रम", "समय सारिणी", "काउंसलिंग",
    "भर्ती", "निविदा", "सूचना", "अधिसूचना", "प्लेसमेंट", "छात्रावास",
    "दीक्षांत समारोह", "पंजीकरण", "नामांकन",
    "मेरिट", "अंकतालिका", "अनुसंधान"
]

_DEVA_DIGIT_TRANS = str.maketrans("०१२३४५६७८९", "0123456789")

_RUNTIME_PDF_CACHE: Dict[str, bytes] = {}
_GEMINI_API_KEY = ""
_GEMINI_KEYS_POOL: List[str] = []
_GEMINI_KEY_INDEX: int = 0
_GEMINI_DEAD_KEYS: set = set()
_GEMINI_KEY_LOCK = threading.Lock()

_MODELS_DISCOVERED: bool = False
_DYNAMIC_MODELS: List[str] = []
_DEAD_MODELS: set = set()
_GEMINI_QUOTA_EXHAUSTED: bool = False

_RAPIDOCR_INSTANCE = None
_ROBOTS_CACHE = {}

_TESSERACT_WARNED: bool = False

_JS_RENDER_COUNT = 0
_JS_RENDER_COUNT_LOCK = threading.Lock()


_NAV_SIGNALS: Tuple[str, ...] = (
    "home", "homepage", "about us", "about", "contact us", "contact",
    "feedback", "site map", "sitemap", "skip to content",
    "accessibility", "screen reader",
    "whats new", "what's new", "whatsnew", "latest news", "latest update",
    "latest updates", "photo gallery", "video gallery", "gallery",
    "facebook", "twitter", "instagram", "youtube", "whatsapp", "linkedin",
    "social media", "follow us", "share",
    "login", "sign in", "sign up", "register", "logout",
    "main menu", "menu", "navigation",
    "मुख्य पृष्ठ", "होम", "हमारे बारे में", "संपर्क करें", "संपर्क",
    "फीडबैक", "साइट मैप", "स्क्रीन रीडर", "महत्वपूर्ण लिंक", "त्वरित लिंक",
    "नई खबरें", "ताज़ा खबर", "अंतिम अपडेट", "गैलरी", "फोटो गैलरी",
)

_NOTICE_SIGNALS: Tuple[str, ...] = (
    "admission", "result", "admit card", "answer key", "examination",
    "exam", "revaluation", "migration", "scholarship", "fee", "syllabus",
    "timetable", "counselling", "recruitment", "vacancy", "tender",
    "notice", "notification", "placement", "convocation", "registration",
    "प्रवेश", "परिणाम", "प्रवेश पत्र", "उत्तर कुंजी", "परीक्षा",
    "पुनर्मूल्यांकन", "छात्रवृत्ति", "शुल्क", "भर्ती", "निविदा", "सूचना",
)

_EXPLICIT_DUMP_SIGNALS: Tuple[str, ...] = (
    "skip to content", "site map", "sitemap",
    "मुख्य पृष्ठ", "महत्वपूर्ण लिंक", "त्वरित लिंक",
)

_STRICT_EARLY_NAV_SIGNALS: Tuple[str, ...] = (
    "home", "homepage", "whats new", "what's new", "whatsnew",
    "facebook", "twitter", "instagram", "youtube", "whatsapp",
    "linkedin", "skip to content", "sitemap", "site map",
    "मुख्य पृष्ठ", "होम", "साइट मैप",
)

_DEVANAGARI_DELIMS = r"[\s\|•\-–—,:;()\[\]{}/\\?!\"'`]"
_LATIN_LEFT_BOUNDARY = r"(?<![A-Za-z0-9_])"
_LATIN_RIGHT_BOUNDARY = r"(?![A-Za-z0-9_])"

_TITLE_STRIP_SIGNALS: Tuple[str, ...] = tuple(
    sorted(_STRICT_EARLY_NAV_SIGNALS, key=len, reverse=True)
)


_JS_REQUIRED_MARKERS = (
    '<div id="root"', '<div id="app"', '<div id="__next"', '<div id="__nuxt"',
    'ng-app', 'ng-version', 'data-reactroot', 'data-v-app',
    'please enable javascript', 'javascript is disabled',
    'you need to enable javascript', 'enable javascript and cookies',
    'enable javascript to run', 'loading...', 'loading…',
    'जावास्क्रिप्ट सक्षम',
    'ng-cloak', 'ng-controller', 'ng-repeat', 'ng-bind', 'ng-view',
    'ng-include', 'ng-scope', 'ng-binding', 'angular.js', 'angular.min.js',
    'angular-route', 'react.production', 'react-dom.production',
    'vue.min.js', 'vue.runtime', 'data-v-', '__next_data__', '_next/static',
    '__nuxt__', '_nuxt/',
)

_JS_PDF_VIEWER_MARKERS = (
    "pdfjs", "pdf.js", "pdfobject", "viewer.html",
    "docs.google.com/viewer", "drive.google.com/file",
    "googleusercontent.com/viewer", "pdfjs-viewer", "web/viewer.html",
)


def _page_requires_js(html_text):
    if not html_text:
        return True
    lower = html_text.lower()
    for marker in _JS_REQUIRED_MARKERS:
        if marker in lower:
            return True
    try:
        soup = BeautifulSoup(html_text, "html.parser")
        for tag in soup(["script", "style", "noscript", "template", "svg"]):
            tag.decompose()
        body = soup.body or soup
        text = body.get_text(" ", strip=True)
        if len(text) < JS_THIN_TEXT_THRESHOLD:
            return True
        anchors = soup.find_all("a", href=True)
        if len(anchors) < 3 and len(text) < 400:
            return True
    except Exception:
        return True
    return False


def _has_unrendered_angular_templates(html_text):
    return bool(re.search(r"\{\{[^}]{1,200}\}\}", html_text or ""))


def _should_render_js(site, html_text, page_url):
    mode = str((site or {}).get("js_render", "auto")).strip().lower()
    if mode == "never":
        return False
    if mode == "always":
        return True
    fragment = (urlparse(page_url).fragment or "").strip()
    if fragment.startswith("/") or fragment.startswith("!/"):
        return True
    return _page_requires_js(html_text)


def _html_looks_like_js_pdf_viewer(html_text):
    if not html_text:
        return False
    lower = html_text.lower()
    return any(m in lower for m in _JS_PDF_VIEWER_MARKERS)


def _render_with_playwright(
    url, timeout_ms=None, wait_until=None, wait_for_selector=None,
    wait_after_ms=None, scroll_bottom=False, selector_timeout_ms=None,
):
    if not _PLAYWRIGHT_AVAILABLE or not JS_RENDER_ENABLED:
        return None, url, "playwright_disabled"

    timeout_ms = max(1000, int(timeout_ms or JS_RENDER_TIMEOUT_MS))
    wait_until = wait_until or JS_WAIT_UNTIL
    if wait_until == "networkidle":
        wait_until = "domcontentloaded"
    wait_after_ms = JS_WAIT_AFTER_MS if wait_after_ms is None else wait_after_ms
    try:
        wait_after_ms = max(0, min(30000, int(wait_after_ms)))
    except (TypeError, ValueError):
        wait_after_ms = JS_WAIT_AFTER_MS
    selector = str(wait_for_selector or JS_WAIT_FOR_SELECTOR_DEFAULT or "").strip()
    try:
        selector_timeout_ms = max(1000, min(60000, int(selector_timeout_ms or 10000)))
    except (TypeError, ValueError, OverflowError):
        selector_timeout_ms = 10000

    try:
        with sync_playwright() as pw:
            browser = pw.chromium.launch(
                headless=True,
                args=[
                    "--no-sandbox", "--disable-dev-shm-usage", "--disable-gpu",
                    "--disable-blink-features=AutomationControlled",
                ],
            )
            try:
                context = browser.new_context(
                    user_agent=JS_RENDER_USER_AGENT,
                    locale="en-IN",
                    viewport={"width": 1366, "height": 900},
                    java_script_enabled=True,
                    ignore_https_errors=True,
                    extra_http_headers={"Accept-Language": "en-IN,en;q=0.9,hi;q=0.8"},
                )
                context.route(
                    "**/*",
                    lambda route: route.abort()
                    if route.request.resource_type in {"image", "media", "font"}
                    else route.continue_(),
                )
                page = context.new_page()
                page.set_default_timeout(timeout_ms)
                try:
                    page.goto(url, wait_until=wait_until, timeout=timeout_ms)
                except Exception:
                    try:
                        page.goto(url, wait_until="domcontentloaded", timeout=timeout_ms)
                    except Exception as exc:
                        return None, url, f"playwright_nav_error:{type(exc).__name__}"

                try:
                    page.wait_for_load_state("networkidle", timeout=min(8000, timeout_ms))
                except Exception:
                    pass

                if selector:
                    try:
                        page.wait_for_selector(
                            selector, state="attached", timeout=min(selector_timeout_ms, timeout_ms)
                        )
                    except Exception:
                        pass
                if wait_after_ms:
                    try:
                        page.wait_for_timeout(wait_after_ms)
                    except Exception:
                        pass

                if scroll_bottom:
                    try:
                        previous_height = -1
                        for _ in range(4):
                            height = page.evaluate(
                                "() => Math.max(document.body.scrollHeight, document.documentElement.scrollHeight)"
                            )
                            page.evaluate("() => window.scrollTo(0, document.body.scrollHeight)")
                            page.wait_for_timeout(600)
                            if height == previous_height:
                                break
                            previous_height = height
                        page.evaluate("() => window.scrollTo(0, 0)")
                    except Exception:
                        pass

                try:
                    html_content = page.content()
                    if _has_unrendered_angular_templates(html_content):
                        page.wait_for_timeout(min(2000, max(500, wait_after_ms)))
                        html_content = page.content()
                except Exception as exc:
                    return None, url, f"playwright_content_error:{type(exc).__name__}"

                if html_content:
                    global _JS_RENDER_COUNT
                    with _JS_RENDER_COUNT_LOCK:
                        _JS_RENDER_COUNT += 1
                return html_content, (page.url or url), "playwright_ok"
            finally:
                try:
                    browser.close()
                except Exception:
                    pass
    except Exception as exc:
        print(
            f"[WARN] Playwright render failed for {url[:80]}: "
            f"{type(exc).__name__}: {exc}", file=sys.stderr,
        )
        return None, url, f"playwright_error:{type(exc).__name__}"


def _is_devanagari_str(text: str) -> bool:
    return any("\u0900" <= c <= "\u097F" for c in (text or ""))


def _match_signal(text: str, signal: str) -> bool:
    if not text or not signal:
        return False
    sig = signal.strip().lower()
    if not sig:
        return False
    lower = text.lower()
    if _is_devanagari_str(sig):
        pattern = (r"(?:^|" + _DEVANAGARI_DELIMS + r")" + re.escape(sig)
                   + r"(?:$|" + _DEVANAGARI_DELIMS + r")")
    else:
        pattern = _LATIN_LEFT_BOUNDARY + re.escape(sig) + _LATIN_RIGHT_BOUNDARY
    return bool(re.search(pattern, lower))


def _count_nav_signals(text: str) -> int:
    if not text:
        return 0
    remaining = text.lower()
    matched = 0
    for sig in sorted(_NAV_SIGNALS, key=len, reverse=True):
        sig_lower = sig.strip().lower()
        if not sig_lower:
            continue
        if _is_devanagari_str(sig_lower):
            pattern = (r"(?:^|" + _DEVANAGARI_DELIMS + r")" + re.escape(sig_lower)
                       + r"(?:$|" + _DEVANAGARI_DELIMS + r")")
        else:
            pattern = _LATIN_LEFT_BOUNDARY + re.escape(sig_lower) + _LATIN_RIGHT_BOUNDARY
        new_remaining, n = re.subn(pattern, " ", remaining)
        if n > 0:
            matched += 1
            remaining = new_remaining
    return matched


_NOTICE_DOC_URL_HINTS = (
    "/writereaddata/", "/uploadfile/", "/uploads/",
    "/downloadfile", "/download_file", "/getfile",
    "/showfile", "/viewfile", "/filedownload",
    "/attachment", "/documents/", "/docs/",
    "/notice/", "/notice_", "/download/",
)


def _is_notice_document_url(url):
    if not url:
        return False
    u = url.lower()
    if u.endswith(".pdf") or ".pdf?" in u:
        return True
    if _looks_like_pdf_url(url):
        return True
    try:
        path = (urlparse(url).path or "").lower()
    except Exception:
        return False
    return any(hint in path for hint in _NOTICE_DOC_URL_HINTS)


def _looks_like_menu_dump(title):
    if not title:
        return False
    words = title.split()
    if len(words) < 4:
        return False
    first_words = " ".join(words[:8]).lower()
    count = sum(1 for sig in _STRICT_EARLY_NAV_SIGNALS if _match_signal(first_words, sig))
    return count >= 2


def _is_garbage_title(title):
    if not title:
        return True
    t = title.strip()
    if not t:
        return True
    if re.search(r"\{\{[^}]{0,200}\}\}", t):
        return True
    if (
        re.match(r"^\[(?:ng|data-ng|x-ng)[\w-]*\]", t, re.I)
        or re.match(r"^\((?:click|change|input|submit|keyup|keydown|mouseover|mouseout)\)", t, re.I)
        or re.match(r"^\*ng[A-Z][\w-]*", t)
        or re.match(r"^(?:ng-|data-ng-|x-ng-)[\w-]+", t, re.I)
    ):
        return True
    if t.casefold() in {"undefined", "null", "nan", "{}", "[]", "{{}}"}:
        return True
    stripped = re.sub(r"^[\s\|•\-–—,:;.]+|[\s\|•\-–—,:;.]+$", "", t)
    if not stripped or len(stripped) < 4:
        return True
    if re.match(r"^[\d\s/\-.:()\[\]|,]+$", stripped):
        return True
    if _is_generic_title(stripped):
        return True
    if _is_language_selector(stripped):
        return True
    return False


def _filename_to_title(url):
    try:
        path = unquote(urlparse(url).path or "")
        name = path.rstrip("/").rsplit("/", 1)[-1]
        if not name:
            return ""
        if "." in name:
            name = name.rsplit(".", 1)[0]
        name = re.sub(r"[_\-]+", " ", name)
        name = re.sub(r"^(pdf|doc|docx|file|download|notice|document|scan|img|image)\s+", "", name, flags=re.I)
        name = re.sub(r"\s+", " ", name).strip()
        if len(name) < 10 or _is_generic_title(name):
            return ""
        if re.match(r"^[\d\s/\-.:()\[\]]+$", name):
            return ""
        return clean_text(name, 300)
    except Exception:
        return ""


def _strip_nav_prefix(title):
    if not title:
        return title
    scan_region = title[:400]
    last_end = 0
    for sig in _TITLE_STRIP_SIGNALS:
        sig_lower = sig.lower()
        if _is_devanagari_str(sig_lower):
            pattern = re.compile(r"(?:^|" + _DEVANAGARI_DELIMS + r")" + re.escape(sig_lower)
                                 + r"(?:$|" + _DEVANAGARI_DELIMS + r")")
        else:
            pattern = re.compile(_LATIN_LEFT_BOUNDARY + re.escape(sig_lower) + _LATIN_RIGHT_BOUNDARY)
        for m in pattern.finditer(scan_region.lower()):
            if m.end() > last_end:
                last_end = m.end()
    if last_end <= 0:
        return title
    rest = title[last_end:].lstrip(" \t:-–—|•,;")
    rest = re.sub(r"^\d{1,2}[./\-]\d{1,2}[./\-]\d{4}[\s:;\-–—]+", "", rest)
    for marker in (
        r"\bPublished\s+on\s*:", r"\bPosted\s+on\s*:", r"\bUploaded\s+on\s*:",
        r"\bDate\s+of\s+Publication\s*:", r"\bप्रकाशित\s*:",
    ):
        m = re.search(marker, rest, re.I)
        if m and m.start() >= 15:
            rest = rest[:m.start()].rstrip(" .;,-")
    rest = rest.strip()
    return rest if len(rest) >= 15 else title


def _cleanup_menu_dump_title(title, url="", explicit=""):
    if explicit and not _is_generic_title(explicit) \
            and not _is_language_selector(explicit) \
            and not _looks_like_menu_dump(explicit) \
            and not _is_garbage_title(explicit):
        return clean_text(explicit, 300)
    if url and _is_notice_document_url(url):
        name = _filename_to_title(url)
        if name:
            return name
    if title:
        stripped = _strip_nav_prefix(title)
        if stripped and stripped != title and len(stripped) >= 15:
            return clean_text(stripped, 300)
    if url:
        slug = _title_from_url(url, min_len=8)
        if slug:
            return slug
    return title


def _resolve_title(item):
    explicit = clean_text(item.get("explicit_title") or "", 300)
    anchor = clean_text(item.get("title") or "", 300)
    context = clean_text(item.get("context") or "", 200)
    url = item.get("url", "")

    def _ok(v):
        return (v and not _is_generic_title(v) and not _is_language_selector(v)
                and not _looks_like_menu_dump(v) and not _is_garbage_title(v))

    if _ok(explicit):
        return explicit
    if _ok(anchor):
        return anchor

    for candidate in (explicit, anchor):
        if candidate and (_looks_like_menu_dump(candidate) or _is_garbage_title(candidate)):
            cleaned = _cleanup_menu_dump_title(candidate, url=url, explicit="")
            if cleaned and cleaned != candidate and _ok(cleaned):
                return cleaned

    if context and not _is_generic_title(context) \
            and not _is_language_selector(context) \
            and not _looks_like_menu_dump(context):
        return context[:200]

    slug = _title_from_url(url, min_len=5)
    if slug:
        return slug

    return "Notice"


def _get_rapidocr():
    global _RAPIDOCR_INSTANCE
    if _RAPIDOCR_INSTANCE is None and _RAPIDOCR_AVAILABLE:
        try:
            _RAPIDOCR_INSTANCE = RapidOCR(params={"Rec.lang_type": "devanagari"})
            print("[INFO] RapidOCR initialized with Devanagari model.", file=sys.stderr)
        except Exception as exc:
            print(f"[WARN] RapidOCR Devanagari init failed: {exc}", file=sys.stderr)
            try:
                _RAPIDOCR_INSTANCE = RapidOCR()
                print("[WARN] Falling back to default RapidOCR.", file=sys.stderr)
            except Exception as exc2:
                print(f"[WARN] RapidOCR default init failed: {exc2}", file=sys.stderr)
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
        for part in (raw or "").split(","):
            key = part.strip()
            if key and key not in seen:
                seen.add(key)
                keys.append(key)

    add(os.getenv("GEMINI_API_KEYS", ""))
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
    print(f"[GEMINI] Key #{index} skipped ({reason}); {remaining} remain.", file=sys.stderr)


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
            print(f"[WARN] Gemini network error: {type(exc).__name__}", file=sys.stderr)
            continue
        if response.status_code == 429:
            try:
                err = response.json().get("error", {})
                msg = str(err.get("message", "")).lower()
                status = str(err.get("status", "")).upper()
            except Exception:
                msg, status = response.text.lower(), ""
            quota = status == "RESOURCE_EXHAUSTED" or any(
                term in msg for term in ("quota", "daily limit", "per day", "limit: 0")
            )
            if quota:
                _mark_gemini_key_dead(key, "quota exhausted")
                last_reason = "quota_exhausted"
                continue
            last_reason = "rate_limited"
            continue
        if response.status_code in (401, 403):
            _mark_gemini_key_dead(key, f"HTTP {response.status_code}")
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
                    _mark_gemini_key_dead(key, "model-discovery quota")
                    continue
                if response.status_code in (401, 403):
                    _mark_gemini_key_dead(key, f"model-discovery {response.status_code}")
                    continue
                response.raise_for_status()
                data = response.json()
                break
            except Exception:
                continue
        if data is None:
            raise RuntimeError("No configured Gemini key succeeded")
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
        if not _DYNAMIC_MODELS:
            _DYNAMIC_MODELS = list(FALLBACK_MODELS)
        print(f"[INFO] Discovered {len(_DYNAMIC_MODELS)} models.", file=sys.stderr)
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
                    pix = page.get_pixmap(matrix=fitz.Matrix(0.75, 0.75), colorspace=fitz.csGRAY, alpha=False)
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
    except Exception:
        pass
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


MEANINGFUL_FIELDS = {
    "admission_last_date": [
        r"(?:last date|last date to apply|apply(?:ing)? till|closing date|admission last date|अंतिम तिथि|आवेदन की अंतिम तिथि)\s*[:：-]?\s*([^\n,;]{1,50})"
    ],
    "exam_date": [r"(?:exam(?:ination)? date|परीक्षा तिथि|परीक्षा दिनांक)\s*[:：-]?\s*([^\n,;]{1,50})"],
    "result_date": [r"(?:result date|परिणाम तिथि|रिजल्ट जारी)\s*[:：-]?\s*([^\n,;]{1,50})"],
    "revaluation_last_date": [r"(?:revaluation last date|revaluation deadline|पुनर्मूल्यांकन अंतिम तिथि)\s*[:：-]?\s*([^\n,;]{1,50})"],
    "fee_last_date": [r"(?:fee submission last date|last date to pay fee|शुल्क जमा अंतिम तिथि)\s*[:：-]?\s*([^\n,;]{1,50})"],
    "vacancy_count": [r"(?:total vacancies?|no\. of vacancies?|vacancies|पदों की संख्या|कुल पद|रिक्त पद)\s*[:：-]?\s*([\d,]+)"],
    "admit_card_date": [r"(?:admit card download|admit card available|प्रवेश पत्र डाउनलोड)\s*[:：-]?\s*([^\n,;]{1,50})"],
    "counselling_date": [r"(?:counselling date|काउंसलिंग तिथि)\s*[:：-]?\s*([^\n,;]{1,50})"],
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


def _meaningful_metadata_change(old_title, new_title, old_context, new_context):
    old_title_norm = re.sub(r"\s+", " ", (old_title or "").casefold()).strip()
    new_title_norm = re.sub(r"\s+", " ", (new_title or "").casefold()).strip()
    if old_title_norm and old_title_norm == new_title_norm:
        old_fields = extract_meaningful_fields("\n".join([old_title or "", old_context or ""]))
        new_fields = extract_meaningful_fields("\n".join([new_title or "", new_context or ""]))
        return any(old_fields.get(k) != new_fields.get(k)
                   for k in set(old_fields) | set(new_fields))

    details = meaningful_change_details(
        "\n".join([old_title or "", old_context or ""]),
        "\n".join([new_title or "", new_context or ""])
    )
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


def baseline_can_complete(scan_success, errors, max_errors=3):
    if isinstance(errors, str):
        error_count = 1 if errors.strip() else 0
    else:
        try:
            error_count = len(errors or [])
        except TypeError:
            error_count = 1 if errors else 0
    try:
        limit = max(0, min(50, int(max_errors)))
    except (TypeError, ValueError, OverflowError):
        limit = 3
    return bool(scan_success) and error_count <= limit


def add_review_item(state, record, reason, details=None):
    queue = state.setdefault("review_queue", {})
    key = hashlib.sha256(
        (record.get("site_id", "") + "|" + record.get("url", "")).encode("utf-8")
    ).hexdigest()
    previous = queue.get(key, {})
    queue[key] = {
        "site_id": record.get("site_id"), "site_name": record.get("site_name"),
        "url": record.get("url"), "title": record.get("title"),
        "reason": clean_text(str(reason), 500),
        "detected_dates": extract_meaningful_fields(
            "\n".join([record.get("title", ""), record.get("context", ""), record.get("pdf_text", "")])
        ),
        "gemini_output": record.get("classification"),
        "diff_summary": details or record.get("meaningful_diff", {}),
        "status": "open",
        "retry_count": int(previous.get("retry_count", 0)) + (1 if previous else 0),
        "first_seen": previous.get("first_seen", utc_now()),
        "updated_at": utc_now(),
    }


def _check_url_changed(session, url, record, verify_ssl=True):
    try:
        head = session.head(url, timeout=8, allow_redirects=True, verify=verify_ssl)
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
                with session.get(url, timeout=20, allow_redirects=True, stream=True, verify=verify_ssl) as response:
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
    re.compile(r"/directory/?$", re.I),
    re.compile(r"/about-district/?$", re.I),
    re.compile(r"/department/?$", re.I),
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
    "view all", "show more", "see more", "load more", "learn more",
    "continue reading", "read more chevron_right", "view all chevron_right",
    "chevron_right", "chevron_left", "arrow_forward", "arrow_back",
    "click here", "here", "link",
    "department name", "name of department", "department", "dept",
    "designation", "post name", "post", "employee name", "father name",
    "address", "email", "phone", "mobile", "date of birth", "dob",
    "gender", "category", "serial number", "sr no", "sr. no", "s.no",
    "sl no", "sl. no", "roll number", "roll no", "registration no",
    "registration number", "enrollment no", "enrollment number",
    "qualification", "status", "remarks", "pincode", "pin code",
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
    "sorry, no notice matched", "no notice matched this category",
    "no records found", "no data found", "no notices found", "no results found",
]


_TITLE_LABEL_RE = re.compile(
    r"^\s*(?:document\s+title|title|subject|शीर्षक|विषय|दस्तावेज़\s*शीर्षक)\s*[:：–—-]\s*$",
    re.IGNORECASE,
)
_TITLE_INLINE_RE = re.compile(
    r"^\s*(?:document\s+title|title|subject|शीर्षक|विषय|दस्तावेज़\s*शीर्षक)\s*[:：–—-]\s*(.+?)\s*$",
    re.IGNORECASE,
)
_TITLE_LABEL_STRICT_RE = re.compile(
    r"^\s*(?:document\s+title|title|subject|शीर्षक|विषय|दस्तावेज़\s*शीर्षक)"
    r"\s*[:：–—-]?\s*$",
    re.IGNORECASE,
)


def _extract_explicit_title(soup):
    def clean_value(value):
        value = clean_text(value or "", 500)
        if len(value) < 15 or _is_generic_title(value) or _is_language_selector(value):
            return ""
        if _TITLE_LABEL_RE.match(value):
            return ""
        if _looks_like_menu_dump(value):
            return ""
        return value

    for tr in soup.find_all("tr"):
        cells = tr.find_all(["th", "td"], recursive=False)
        if len(cells) >= 2:
            label = clean_text(cells[0].get_text(" ", strip=True), 100)
            if _TITLE_LABEL_STRICT_RE.match(label):
                value = clean_value(cells[1].get_text(" ", strip=True))
                if value:
                    return value

    for dt in soup.find_all("dt"):
        label = clean_text(dt.get_text(" ", strip=True), 100)
        if _TITLE_LABEL_STRICT_RE.match(label):
            dd = dt.find_next_sibling("dd")
            if dd:
                value = clean_value(dd.get_text(" ", strip=True))
                if value:
                    return value

    for label_node in soup.find_all(["b", "strong", "label"]):
        label = clean_text(label_node.get_text(" ", strip=True), 100)
        if not _TITLE_LABEL_STRICT_RE.match(label):
            continue
        sibling = label_node.find_next_sibling()
        if sibling:
            value = clean_value(sibling.get_text(" ", strip=True))
            if value:
                return value
        parent = label_node.parent
        if parent:
            combined = clean_text(parent.get_text(" ", strip=True), 700)
            m = _TITLE_INLINE_RE.match(combined)
            if m:
                value = clean_value(m.group(1))
                if value:
                    return value

    for node in soup.find_all(["td", "th", "dd", "p", "div", "li", "span"]):
        raw = node.get_text(" ", strip=True)
        if len(raw) > 700:
            continue
        text_value = clean_text(raw, 700)
        m = _TITLE_INLINE_RE.match(text_value)
        if m:
            value = clean_value(m.group(1))
            if value:
                return value

    return ""


def _is_navigation_url(url):
    try:
        parsed = urlparse(url)
        fragment = (parsed.fragment or "").strip()
        if (fragment.startswith("/") or fragment.startswith("!/")) and len(fragment) > 2:
            return False
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
    t = re.sub(r"\s+", " ", (title or "").strip().casefold())
    if not t:
        return True
    if t in _GENERIC_TITLES:
        return True
    if len(t.split()) <= 3 and re.fullmatch(
        r"(?:[\w.-]+\s+)?(?:name|no|no\.|number|id|code|address|email|"
        r"phone|mobile|dob|status|remarks|qualification|designation|"
        r"department|dept|category|gender|pincode|serial|roll|registration|enrollment)",
        t, flags=re.UNICODE,
    ):
        return True
    if len(t) > 50 and re.match(r"^(?:national|indian)\s+institute\s+of\s+", t):
        return True
    if len(t) > 40 and re.match(
        r"^(?:address|campus address|contact address|postal address|administrative office address)\b", t
    ) and re.search(r"(?:pincode|pin\s*code|\b(?:81|82|83|84|85)\d{4}\b)", t):
        return True
    ui_only = re.sub(
        r"\s+(?:chevron_(?:right|left|up|down)|arrow_(?:forward|back|right|left)|"
        r"keyboard_arrow_(?:right|left|up|down)|east|west|north|south)+$", "", t
    ).strip()
    if ui_only in _GENERIC_TITLES:
        return True
    if re.match(
        r"^(?:read|view|show|see|load|continue|learn)\s+(?:more|all|less|next)"
        r"(?:\s+(?:chevron_\w+|arrow_\w+|east|west|north|south))*$", t
    ):
        return True
    compact = re.sub(r"[^\w]+", "", t, flags=re.UNICODE)
    if not compact or len(compact) <= 2:
        return True
    if t.isdigit() and len(t) <= 3:
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
            str(img.get("src") or ""), str(img.get("alt") or ""),
            " ".join(img.get("class") or []), str(img.get("title") or ""),
        ]).lower()
        if any(kw in img_attrs for kw in ("pdf", "document", "file", "download", "attachment", "doc")):
            _add(href, 65)

    _FILE_LABEL_RE = re.compile(
        r"^(file|फ़ाइल|फाइल|attachment|संलग्नक|file\s*name|फ़ाइल\s*नाम)\s*[:\-]?\s*$", re.I,
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
        _add(a.get("href", ""), 30)

    ranked = sorted(candidates.items(), key=lambda x: -x[1])
    return ranked[:max_candidates]


def _find_pdf_link_in_html(html_text, base_url):
    ranked = _collect_all_pdf_candidates(html_text, base_url, max_candidates=1)
    return ranked[0][0] if ranked else None


def _download_with_pdf_resolution(session, url, timeout, depth=0, _visited=None, verify_ssl=True):
    if _visited is None:
        _visited = set()
    canon = canonical_url(url)
    if canon in _visited:
        return None, url, "already_visited"
    _visited.add(canon)
    if depth > 3:
        return None, url, "max_depth_exceeded"
    try:
        head = session.head(url, timeout=min(10, timeout), allow_redirects=True, verify=verify_ssl)
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
        response = session.get(url, timeout=timeout, allow_redirects=True, verify=verify_ssl)
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
        if not candidates and _html_looks_like_js_pdf_viewer(html_text) and depth == 0:
            print(f"[JS-PDF] Detected JS PDF viewer at {final_url[:80]}, rendering...", file=sys.stderr)
            rendered_html, rendered_url, _ = _render_with_playwright(
                final_url, wait_after_ms=3000, scroll_bottom=False
            )
            if rendered_html:
                candidates = _collect_all_pdf_candidates(
                    rendered_html, rendered_url or final_url, max_candidates=10
                )
        for cand_url, priority in candidates:
            sub_content, sub_url, sub_method = _download_with_pdf_resolution(
                session, cand_url, timeout, depth + 1, _visited, verify_ssl
            )
            if sub_content:
                return sub_content, sub_url, f"html_wrap(p{priority})->{sub_method}"
        return None, url, "html_no_pdf_found"
    if content[:4] == b"%PDF":
        return content, final_url, "magic_bytes"
    return None, url, f"unsupported:{content_type[:40]}"


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
    text = str(text).translate(_DEVA_DIGIT_TRANS)
    dates = []
    for pattern in _UPLOAD_DATE_TEXT_PATTERNS:
        for match in pattern.finditer(text):
            dates.extend(_extract_full_dates(match.group(1)))
    return sorted(set(dates))


def _extract_upload_date(anchor_tag):
    try:
        search_root = (
            anchor_tag.find_parent("tr") or anchor_tag.find_parent("li")
            or anchor_tag.find_parent("article")
            or anchor_tag.find_parent(["div", "section"]) or anchor_tag.parent
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
    normalized_title = title_text.translate(_DEVA_DIGIT_TRANS)
    normalized_context = context_text.translate(_DEVA_DIGIT_TRANS)
    normalized_full = full_text.translate(_DEVA_DIGIT_TRANS)

    title_words = normalized_title.split()
    if len(title_words) >= 5:
        first_words = " ".join(title_words[:6]).lower()
        early_nav_count = sum(1 for sig in _STRICT_EARLY_NAV_SIGNALS if _match_signal(first_words, sig))
        if early_nav_count >= 2:
            if not _is_notice_document_url(url):
                return True
        short_words = [w for w in title_words if len(w.strip("|•-–—,:;")) <= 6]
        title_lower = normalized_title.lower()
        nav_count = _count_nav_signals(title_lower)
        has_notice_signal = any(_match_signal(title_lower, sig) for sig in _NOTICE_SIGNALS)
        mostly_short = len(short_words) >= len(title_words) * 0.6
        explicit_nav_dump = any(_match_signal(title_lower, sig) for sig in _EXPLICIT_DUMP_SIGNALS)
        compact_social_dump = (len(title_words) <= 8 and nav_count >= 3 and not has_notice_signal)
        if not has_notice_signal and not _is_notice_document_url(url):
            if (mostly_short and (nav_count >= 2 or explicit_nav_dump)) or compact_social_dump:
                return True

    title_years = [int(year) for year in re.findall(r"(?<!\d)(?:19|20)\d{2}(?!\d)", normalized_title)]
    current_year = now.year
    current_academic_start = current_year if now.month >= 7 else current_year - 1
    current_year_update = bool(re.search(
        rf"(?:revised|revision|corrigendum|addendum|amended|modified|संशोधित|शुद्धिपत्र).{{0,50}}{current_year}|"
        rf"{current_year}.{{0,50}}(?:revised|revision|corrigendum|addendum|amended|modified|संशोधित|शुद्धिपत्र)",
        f"{normalized_title} {normalized_context}", re.I
    ))
    session_pattern = re.compile(
        r"(?<!\d)((?:19|20)\d{2})\s*[-/–—]\s*((?:19|20)\d{2}|\d{2})(?!\d)"
    )
    admission_session_signal = bool(re.search(
        r"\b(?:admission|admissions|provisional|application|counselling|counseling|"
        r"selection\s+list|merit\s+list|ph\.?d\.?|enrollment|enrolment|प्रवेश|आवेदन|"
        r"चयन\s+सूची|मेरिट\s+सूची)\b", normalized_title, re.I
    ))
    if admission_session_signal and not current_year_update:
        for match in session_pattern.finditer(normalized_title):
            session_start = int(match.group(1))
            end_token = match.group(2)
            session_end = int(end_token) if len(end_token) == 4 else (session_start // 100) * 100 + int(end_token)
            if session_end < session_start:
                session_end += 100
            if session_start < current_academic_start:
                return True

    title_has_old_range = len(title_years) >= 2 and max(title_years) < current_year
    title_has_very_old_year = bool(title_years) and max(title_years) < current_year - 1
    if (title_has_old_range or title_has_very_old_year) and not current_year_update:
        return True

    issue_dates = _extract_explicit_issue_dates(normalized_full)
    past_issue_dates = [date for date in issue_dates if date <= now]
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

    years = [int(year) for year in re.findall(r"(?<!\d)(?:19|20)\d{2}(?!\d)", normalized_full)]
    if years and max(years) < current_year and not current_year_update:
        return True
    return False


def _classify_stale_reason(title, context, url, upload_date=None, pdf_text=None):
    if not _is_stale_notice(title, context, url, upload_date=upload_date, pdf_text=pdf_text):
        return None
    title_lower = str(title or "").lower()
    nav_count = _count_nav_signals(title_lower)
    has_notice_signal = any(_match_signal(title_lower, sig) for sig in _NOTICE_SIGNALS)
    if nav_count >= 2 and not has_notice_signal:
        return f"MENU-DUMP(nav={nav_count})"
    return "STALE"


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


def _canonical_spa_url(raw):
    raw = (raw or "").strip()
    p = urlparse(raw)
    if not p.scheme or not p.netloc:
        return raw
    fragment = (p.fragment or "").strip()
    keep_fragment = fragment.startswith("/") or fragment.startswith("!/")
    return urlunparse((
        p.scheme.lower(), p.netloc.lower(), p.path or "/", "", p.query,
        fragment if keep_fragment else "",
    ))


def canonical_identity_url(raw):
    normalized = _canonical_spa_url(raw)
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
    return urlunparse((p.scheme.lower(), p.netloc.lower(), p.path or "/", "", urlencode(pairs, doseq=True), p.fragment))


def same_host(a, b):
    return urlparse(a).netloc.lower() == urlparse(b).netloc.lower()


def is_http_url(url):
    return urlparse(url).scheme in {"http", "https"}


def is_pdf(url):
    return urlparse(url).path.lower().endswith(".pdf")


def make_session():
    session = requests.Session()
    retry = Retry(
        total=2, connect=2, read=2, status=2,
        backoff_factor=0.5,
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


_SITE_VERIFY_SSL_BY_ID = {}
_SITE_TIMEOUT_BY_ID = {}


def get_config():
    cfg = load_json(CONFIG_FILE, {})
    if not isinstance(cfg, dict):
        raise RuntimeError("websites.json root must be an object")
    scan = cfg.get("scan") or {}
    defaults = {
        "request_timeout_seconds": 45,
        "max_workers": 6,
        "max_items_per_site": 100,
        "max_discovery_pages_per_site": 15,
        "max_archive_pages_per_site": 20,
        "max_pagination_per_archive": 4,
        "max_new_items_per_run": 30,
        "gemini_batch_size": 3,
        "gemini_max_calls_per_run": 20,
        "retention_days": 90,
        "sent_retention_days": 90,
        "ignored_retention_days": 30,
        "baseline_retention_days": 60,
        "domain_delay_seconds": 0.4,
        "max_state_items": 3000,
        "max_state_bytes": 8000000,
        "max_pending_attempts": 500,
        "stale_notice_days": 15,
        "baseline_max_errors": 3,
        "exclude_title_signals": list(_DEFAULT_EXCLUDED_TITLE_SIGNALS),
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
    scan["max_state_bytes"] = max(500000, min(10000000, int(scan["max_state_bytes"])))
    scan["max_pending_attempts"] = max(500, int(scan["max_pending_attempts"]))
    scan["stale_notice_days"] = max(1, int(scan["stale_notice_days"]))
    scan["baseline_max_errors"] = max(0, min(50, int(scan.get("baseline_max_errors", 3))))
    raw_exclusions = scan.get("exclude_title_signals", list(_DEFAULT_EXCLUDED_TITLE_SIGNALS))
    if not isinstance(raw_exclusions, list):
        raw_exclusions = list(_DEFAULT_EXCLUDED_TITLE_SIGNALS)
    scan["exclude_title_signals"] = list(dict.fromkeys(
        clean_text(str(x), 100).casefold() for x in raw_exclusions if str(x).strip()
    ))
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
        js_mode = str(site.get("js_render", "auto")).strip().lower()
        if js_mode not in ("auto", "always", "never"):
            js_mode = "auto"
        site["js_render"] = js_mode
        try:
            site["request_timeout_seconds"] = max(
                5, min(180, int(site.get("request_timeout_seconds", scan["request_timeout_seconds"])))
            )
        except (TypeError, ValueError, OverflowError):
            site["request_timeout_seconds"] = scan["request_timeout_seconds"]
        try:
            site["baseline_max_errors"] = max(
                0, min(50, int(site.get("baseline_max_errors", scan["baseline_max_errors"])))
            )
        except (TypeError, ValueError, OverflowError):
            site["baseline_max_errors"] = scan["baseline_max_errors"]
        raw_verify_ssl = site.get("verify_ssl", True)
        if isinstance(raw_verify_ssl, str):
            site["verify_ssl"] = raw_verify_ssl.strip().casefold() not in {"0", "false", "no", "off"}
        else:
            site["verify_ssl"] = bool(raw_verify_ssl)

        try:
            site["js_wait_after_ms"] = max(
                0, min(30000, int(site.get("js_wait_after_ms", JS_WAIT_AFTER_MS)))
            )
        except (TypeError, ValueError, OverflowError):
            site["js_wait_after_ms"] = JS_WAIT_AFTER_MS

        raw_scroll = site.get("js_scroll_bottom", JS_SCROLL_TO_BOTTOM)
        if isinstance(raw_scroll, str):
            site["js_scroll_bottom"] = raw_scroll.strip().lower() in {"1", "true", "yes", "on"}
        else:
            site["js_scroll_bottom"] = bool(raw_scroll)

        raw_selector = site.get("js_wait_for_selector", JS_WAIT_FOR_SELECTOR_DEFAULT)
        site["js_wait_for_selector"] = clean_text(str(raw_selector or ""), 200) or None
        try:
            site["js_selector_timeout_ms"] = max(1000, min(60000, int(site.get("js_selector_timeout_ms", 10000))))
        except (TypeError, ValueError, OverflowError):
            site["js_selector_timeout_ms"] = 10000
        enabled.append(site)
    cfg["websites"] = enabled
    global _SITE_VERIFY_SSL_BY_ID, _SITE_TIMEOUT_BY_ID
    _SITE_VERIFY_SSL_BY_ID = {site["id"]: site["verify_ssl"] for site in enabled}
    _SITE_TIMEOUT_BY_ID = {site["id"]: site["request_timeout_seconds"] for site in enabled}
    return cfg


def default_state():
    return {
        "version": 31,
        "initialized": False,
        "last_run": None,
        "items": {},
        "sites": {},
        "review_queue": {},
        "metrics": {"site_scan_success": {}, "site_scan_failure": {}, "parse_errors": 0,
                     "sent_notifications": 0, "failed_notifications": 0,
                     "duplicate_rejects": 0, "state_save_failures": 0,
                     "js_renders": 0},
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
    state["metrics"].setdefault("js_renders", 0)
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
        record.setdefault("explicit_title", "")
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
    state["version"] = 31
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
            print(f"[WARN] Site failure alert not delivered: {detail}", file=sys.stderr)

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
            print(f"[WARN] Site recovery alert not delivered: {detail}", file=sys.stderr)


def local_score(title, url, context, keywords):
    text = f"{title} {url} {context}".lower()
    return sum(1 for kw in keywords if kw and kw in text)


def pending_priority(record, keywords, now=None):
    now = now or datetime.now(timezone.utc)
    first_seen = _parse_utc_timestamp(record.get("first_seen"))
    age_days = max(0.0, (now - first_seen).total_seconds() / 86400) if first_seen else 0.0
    title = " ".join((record.get("explicit_title") or "", record.get("title") or "", record.get("context") or "")).casefold()
    if any(x in title for x in ("admit card", "exam date", "प्रवेश पत्र", "परीक्षा तिथि", "परीक्षा कार्यक्रम")):
        urgency = 100
    elif any(x in title for x in ("result", "रिजल्ट", "परिणाम", "answer key", "उत्तर कुंजी", "merit list", "मेरिट सूची")):
        urgency = 50
    else:
        urgency = 0
    score = local_score(
        record.get("title", ""), record.get("url", ""), record.get("context", ""), keywords
    )
    age_bonus = min(age_days, 30.0)
    return urgency + score + age_bonus, age_days


_PRECLASS_STRONG = (
    "admission", "result", "admit card", "answer key", "examination",
    "exam", "revaluation", "migration", "scholarship", "fee", "syllabus",
    "timetable", "counselling", "recruitment", "vacancy", "tender",
    "notice", "notification", "placement", "convocation", "registration",
    "result", "notice", "notification", "examination",
    "exam form", "exam schedule", "exam programme",
    "marksheet", "merit", "advertisement",
    "प्रवेश", "परिणाम", "प्रवेश पत्र", "उत्तर कुंजी", "परीक्षा",
    "पुनर्मूल्यांकन", "छात्रवृत्ति", "शुल्क", "भर्ती", "निविदा", "सूचना",
    "अधिसूचना", "परीक्षा कार्यक्रम", "परीक्षा केंद्र", "परीक्षा फॉर्म",
)
_PRECLASS_NAV_ONLY = (
    "photo gallery", "video gallery", "site map", "web policies",
    "screen reader", "feedback", "anti-ragging", "grievance cell",
)

_DEFAULT_EXCLUDED_TITLE_SIGNALS = (
    "gst return", "income tax", "annual report", "balance sheet",
    "minutes of meeting", "right to information", "rti application",
)


def _matched_excluded_title_signal(title, signals=None):
    text = re.sub(r"\s+", " ", str(title or "").casefold()).strip()
    for raw in (signals if signals is not None else _DEFAULT_EXCLUDED_TITLE_SIGNALS):
        signal = re.sub(r"\s+", " ", str(raw or "").casefold()).strip()
        if not signal:
            continue
        pattern = r"(?<!\w)" + r"\s+".join(re.escape(part) for part in signal.split()) + r"(?!\w)"
        if re.search(pattern, text, flags=re.UNICODE):
            return signal
    return ""


def _keyword_pre_classify(record, excluded_signals=None):
    if _is_stale_notice(
        record.get("explicit_title") or record.get("title", ""),
        record.get("context", ""), record.get("url", ""),
        upload_date=_parse_upload_date(record.get("upload_date")),
        pdf_text=record.get("pdf_text", ""),
    ):
        return False
    title = " ".join((record.get("explicit_title") or "", record.get("title") or "")).casefold()
    if _is_generic_title(title):
        return False
    if _matched_excluded_title_signal(title, excluded_signals):
        return False
    if any(sig in title for sig in _PRECLASS_STRONG):
        return True
    url = (record.get("url") or "").casefold()
    title_is_nav = any(sig in title for sig in _PRECLASS_NAV_ONLY)
    has_notice_signal = any(sig in title for sig in _PRECLASS_STRONG) or any(
        sig in title for sig in ("notice", "notification", "सूचना", "आवेदन", "advertisement")
    )
    if title_is_nav and not has_notice_signal and not _is_notice_document_url(url):
        return False
    return None


def item_id(site_id, url, title="", context=""):
    raw = f"{site_id}|{canonical_identity_url(url)}"
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


def _duplicate_alias_slug(url):
    try:
        path = unquote(urlparse(url).path or "").rstrip("/")
        slug = path.rsplit("/", 1)[-1].casefold()
        slug = re.sub(r"\.(?:pdf|html?|aspx?|php)$", "", slug)
        slug = re.sub(r"(?:[-_ ](?:copy|duplicate|duplicated|download|downloaded|final-copy))+$", "", slug)
        return re.sub(r"[^a-z0-9]+", "", slug)
    except Exception:
        return ""


def find_fuzzy_match(site_items, title, url):
    if not site_items or not title:
        return None
    new_title = _normalize_title(title)
    new_slug = _duplicate_alias_slug(url)
    if len(new_title) < 12 or len(new_slug) < 8:
        return None
    for iid, existing_title, existing_url in site_items:
        old_slug = _duplicate_alias_slug(existing_url)
        if not old_slug or old_slug != new_slug:
            continue
        old_title = _normalize_title(existing_title)
        if len(old_title) >= 12 and fuzz.token_sort_ratio(new_title, old_title) >= FUZZY_CROSS_PATH_THRESHOLD:
            return iid
    return None


def _is_duplicate_by_pdf_hash(state, record, exclude_iid=None):
    new_hash = record.get("pdf_hash")
    new_kind = record.get("pdf_hash_kind")
    new_site = record.get("site_id")
    if not new_hash or not new_kind or not new_site:
        return None
    for other_iid, other in state.get("items", {}).items():
        if other_iid == exclude_iid or not isinstance(other, dict):
            continue
        if other.get("status") != "sent":
            continue
        if other.get("site_id") != new_site:
            continue
        if other.get("pdf_hash_kind") != new_kind:
            continue
        if other.get("pdf_hash") == new_hash:
            return other.get("title") or other_iid
    return None


def extract_candidates(html_text, page_url, site, scan):
    soup = BeautifulSoup(html_text, "html.parser")
    for tag in soup(["script", "style", "noscript", "svg", "template"]):
        tag.decompose()
    keywords = list(dict.fromkeys(scan["keywords"] + site.get("keywords", [])))
    out = []
    seen = set()
    for a in soup.find_all("a", href=True):
        href = _canonical_spa_url(urljoin(page_url, a.get("href", "")))
        if not is_http_url(href) or not same_host(page_url, href):
            continue
        if _is_navigation_url(href):
            continue

        title = clean_text(a.get_text(" ", strip=True), 300)
        parent = a.find_parent("tr")
        if parent is None:
            parent = a.find_parent(["li", "article", "section"])
        if parent is None:
            parent = a.find_parent(["div", "td"])
        context = clean_text(parent.get_text(" ", strip=True) if parent else "", 700)

        if _is_generic_title(title) or _is_language_selector(title):
            context_parts = re.split(r"[|\n\r\t]+", context)
            context_title = ""
            for part in context_parts:
                part = clean_text(part, 200)
                if len(part) >= 8 and not _is_generic_title(part) and not _is_language_selector(part):
                    context_title = part
                    break
            title = context_title or _title_from_url(href, min_len=5) or ""
            if not title or _is_generic_title(title):
                continue

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

        if len(title) < 20 and context:
            parts = re.split(r"[|\-–—:]", context)
            for p in parts:
                p = clean_text(p.strip(), 200)
                if len(p) >= 20 and not _is_generic_title(p) and not _is_language_selector(p):
                    title = p
                    break

        score = local_score(title, href, context, keywords)
        href_lower = href.lower()
        is_pdf_link = bool(is_pdf(href) or _looks_like_pdf_url(href))
        if is_pdf_link:
            pdf_bonus = 2
        elif any(kw in href_lower for kw in (
            "/notice/", "/notices/", "/document", "/writereaddata/", "/uploadfile/", "/uploads/",
            "/upload/", "/downloadfile/", "/download_file/", "/getfile/",
            "/showfile/", "/viewfile/", "/filedownload/", "/files/", "/media/",
            "/file/", "/attachment/", "/attachments/", "/docs/",
            "/download/", "/downloads/",
        )):
            pdf_bonus = 1
        else:
            pdf_bonus = 0

        if score <= 0 and pdf_bonus == 0:
            continue
        if href in seen:
            continue
        seen.add(href)
        upload_dt = _extract_upload_date(a)

        final_title = clean_text(title, 300)
        if not final_title or _is_generic_title(final_title):
            final_title = clean_text(context, 180)
        if not final_title or _is_generic_title(final_title):
            final_title = _title_from_url(href, min_len=5)
        if not final_title:
            final_title = "Notice"

        out.append({
            "url": href, "title": final_title, "context": context,
            "source_page": page_url, "is_pdf": is_pdf_link,
            "score": score + pdf_bonus,
            "upload_date": upload_dt.isoformat() if upload_dt else None,
        })

    out.sort(key=lambda x: (-x["score"], x["title"].lower()))
    out = out[: scan["max_items_per_site"]]

    page_explicit_title = _extract_explicit_title(soup)
    if page_explicit_title:
        for row in out:
            if _is_notice_document_url(row["url"]):
                row["explicit_title"] = page_explicit_title

    for row in out:
        if _is_notice_document_url(row["url"]) and _looks_like_menu_dump(row.get("title", "")):
            cleaned = _cleanup_menu_dump_title(
                row["title"], url=row["url"], explicit=row.get("explicit_title", ""),
            )
            if cleaned and cleaned != row["title"]:
                print(f"[TITLE-CLEANUP] {row['title'][:60]!r} → {cleaned[:60]!r}", file=sys.stderr)
                row["title"] = cleaned

    return out


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
    timeout = int(site.get("request_timeout_seconds", scan["request_timeout_seconds"]))
    effective_scan = dict(scan)
    effective_scan["request_timeout_seconds"] = timeout
    max_pages = scan["max_discovery_pages_per_site"]
    max_archive_pages = scan.get("max_archive_pages_per_site", 5)
    max_pagination_per_archive = scan.get("max_pagination_per_archive", 3)

    discovery_keywords = list(dict.fromkeys(
        scan["discovery_keywords"] + site.get("discovery_keywords", []) + scan["keywords"]
    ))

    queue = [base_url]
    queue.extend(discover_from_sitemap(session, base_url, effective_scan))
    visited = set()
    archive_visited_count = 0
    pagination_tracker = {}
    candidates = {}
    errors = []
    successful_pages = 0
    total_budget = max_pages + max_archive_pages
    normal_visited_count = 0
    js_render_count = 0

    while queue and len(visited) < total_budget:
        page = _canonical_spa_url(queue.pop(0))
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
            verify_ssl = bool(site.get("verify_ssl", True))
            if not verify_ssl:
                print(f"[WARN] TLS certificate verification disabled for configured site: {page}", file=sys.stderr)

            response = None
            response_text = None
            rendered_from_waf = False
            final_url = page
            content_type = ""
            try:
                response = session.get(
                    page, timeout=timeout, allow_redirects=True, verify=verify_ssl
                )
                final_url = canonical_url(response.url)
                content_type = response.headers.get("content-type", "").lower()
            except requests.RequestException as request_exc:
                can_browser_retry = (
                    site.get("js_render", "auto") != "never"
                    and JS_RENDER_ENABLED and _PLAYWRIGHT_AVAILABLE
                    and js_render_count < JS_MAX_RENDER_PER_SITE
                )
                if can_browser_retry:
                    print(
                        f"[NETWORK-RETRY] {type(request_exc).__name__}; trying Playwright: {page}",
                        file=sys.stderr,
                    )
                    rendered_html, rendered_url, js_method = _render_with_playwright(
                        page,
                        timeout_ms=timeout * 1000,
                        wait_for_selector=site.get("js_wait_for_selector"),
                        wait_after_ms=site.get("js_wait_after_ms"),
                        scroll_bottom=site.get("js_scroll_bottom", JS_SCROLL_TO_BOTTOM),
                        selector_timeout_ms=site.get("js_selector_timeout_ms"),
                    )
                    js_render_count += 1
                    if rendered_html:
                        response_text = rendered_html
                        final_url = _canonical_spa_url(rendered_url or page)
                        content_type = "text/html"
                        rendered_from_waf = True
                        print(
                            f"[NETWORK-RETRY-OK] {page[:80]} ({js_method}, {len(rendered_html)} chars)",
                            file=sys.stderr,
                        )
                    else:
                        print(
                            f"[NETWORK-RETRY-FAIL] {page[:80]}: {type(request_exc).__name__}; {js_method}",
                            file=sys.stderr,
                        )
                if response_text is None:
                    raise request_exc

            if response is not None and response.status_code in (403, 503):
                if JS_RENDER_ENABLED and _PLAYWRIGHT_AVAILABLE and js_render_count < JS_MAX_RENDER_PER_SITE:
                    print(f"[WAF-RETRY] HTTP {response.status_code}; trying Playwright: {page}", file=sys.stderr)
                    rendered_html, rendered_url, js_method = _render_with_playwright(
                        page,
                        timeout_ms=timeout * 1000,
                        wait_for_selector=site.get("js_wait_for_selector"),
                        wait_after_ms=site.get("js_wait_after_ms"),
                        scroll_bottom=site.get("js_scroll_bottom", JS_SCROLL_TO_BOTTOM),
                        selector_timeout_ms=site.get("js_selector_timeout_ms"),
                    )
                    js_render_count += 1
                    if rendered_html:
                        response_text = rendered_html
                        final_url = _canonical_spa_url(rendered_url)
                        content_type = "text/html"
                        rendered_from_waf = True
                        print(f"[WAF-RETRY-OK] {page[:80]} ({js_method}, {len(rendered_html)} chars)", file=sys.stderr)
                    else:
                        print(f"[WAF-RETRY-FAIL] {page[:80]}: {js_method}", file=sys.stderr)
                if response_text is None:
                    raise RuntimeError(f"HTTP {response.status_code}; Playwright fallback unavailable or failed")
            elif response is not None and response.status_code >= 400:
                raise RuntimeError(f"HTTP {response.status_code}")

            if response is not None and not rendered_from_waf and _looks_like_pdf_response(response.content, content_type, final_url):
                filename = final_url.rsplit("/", 1)[-1] or "PDF Notice"
                candidates[final_url] = {
                    "url": final_url, "title": clean_text(filename, 300),
                    "context": "Direct PDF notice", "source_page": page,
                    "is_pdf": True, "score": 3, "upload_date": None,
                }
                successful_pages += 1
                continue

            if response is not None and not rendered_from_waf and content_type and "html" not in content_type and "xhtml" not in content_type:
                print(f"[SKIP] Non-HTML content-type={content_type[:60]!r} at {page}", file=sys.stderr)
                continue

            js_mode = site.get("js_render", "auto")
            source_html = response.text if response is not None else (response_text or "")
            should_render_js = False if rendered_from_waf else _should_render_js(site, source_html, page)

            if (should_render_js and JS_RENDER_ENABLED and _PLAYWRIGHT_AVAILABLE
                    and js_render_count < JS_MAX_RENDER_PER_SITE):
                print(f"[JS-RENDER] {page} (mode={js_mode})", file=sys.stderr)
                rendered_html, rendered_url, js_method = _render_with_playwright(
                    page,
                    timeout_ms=timeout * 1000,
                    wait_for_selector=site.get("js_wait_for_selector"),
                    wait_after_ms=site.get("js_wait_after_ms"),
                    scroll_bottom=site.get("js_scroll_bottom", JS_SCROLL_TO_BOTTOM),
                    selector_timeout_ms=site.get("js_selector_timeout_ms"),
                )
                js_render_count += 1
                if rendered_html:
                    response_text = rendered_html
                    final_url = _canonical_spa_url(rendered_url)
                    print(f"[JS-OK] {page[:80]} -> {len(rendered_html)} chars ({js_method})", file=sys.stderr)
                else:
                    response_text = response.text
                    print(f"[JS-FAIL] {page[:80]}: {js_method}", file=sys.stderr)
            elif response_text is None:
                response_text = response.text if response is not None else ""

            if _is_empty_page_text(response_text):
                successful_pages += 1
                continue

            found = extract_candidates(response_text, final_url, site, effective_scan)
            for row in found:
                old = candidates.get(row["url"])
                if old is None or row["score"] > old["score"]:
                    candidates[row["url"]] = row
            successful_pages += 1

            soup = BeautifulSoup(response_text, "html.parser")
            for a in soup.find_all("a", href=True):
                href = _canonical_spa_url(urljoin(final_url, a.get("href", "")))
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
                parsed_href = urlparse(href)
                path = parsed_href.path.lower()
                route = (parsed_href.fragment or "").replace("!", " ").replace("/", " ")
                haystack = f"{anchor} {path} {route}"
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
                        try:
                            if callable(getattr(table, "extract", None)):
                                rows = table.extract() or []
                            elif getattr(table, "rows", None) is not None and not isinstance(table, (list, tuple)):
                                rows = table.rows
                            else:
                                rows = table or []
                        except Exception as table_exc:
                            print(f"[WARN] Table normalization failed on page {idx+1}: {table_exc}", file=sys.stderr)
                            continue
                        for row in rows:
                            if hasattr(row, "cells"):
                                row = row.cells
                            if not isinstance(row, (list, tuple)):
                                continue
                            cells = [str(c).strip() for c in row if c is not None and str(c).strip()]
                            if cells:
                                parts.append(" | ".join(cells))
                except Exception as exc:
                    print(f"[WARN] Page {idx+1} table extract failed: {exc}", file=sys.stderr)
    except Exception as exc:
        print(f"[WARN] pdfplumber open failed: {exc}", file=sys.stderr)
    return "\n\n".join(parts)


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
    result_text = "\n\n".join(parts)
    if result_text and _text_looks_garbage(result_text):
        return ""
    return result_text


def _extract_pdf_text_tesseract(content):
    global _TESSERACT_WARNED
    if not TESSERACT_ENABLED or not _TESSERACT_AVAILABLE:
        if TESSERACT_ENABLED and not _TESSERACT_AVAILABLE and not _TESSERACT_WARNED:
            print("[INFO] Tesseract not installed; skipping Hindi fallback.", file=sys.stderr)
            _TESSERACT_WARNED = True
        return ""
    if fitz is None or _PIL_Image is None:
        return ""
    parts = []
    try:
        doc = fitz.open(stream=content, filetype="pdf")
        pages_to_process = min(len(doc), MAX_PDF_PAGES, _OCR_MAX_PAGES)
        config = f"--psm {TESSERACT_PSM}" if TESSERACT_PSM else ""
        for page_num in range(pages_to_process):
            try:
                page = doc.load_page(page_num)
                pix = page.get_pixmap(dpi=OCR_DPI)
                img = _PIL_Image.open(io.BytesIO(pix.tobytes("png")))
                text = pytesseract.image_to_string(img, lang=TESSERACT_LANG, config=config)
                if text.strip():
                    parts.append(text)
            except Exception as exc:
                if not _TESSERACT_WARNED:
                    print(f"[WARN] Tesseract page {page_num+1} failed: {exc}", file=sys.stderr)
                    _TESSERACT_WARNED = True
                break
        doc.close()
    except Exception as exc:
        print(f"[WARN] Tesseract PDF processing failed: {exc}", file=sys.stderr)
    result_text = "\n\n".join(parts)
    if result_text and _text_looks_garbage(result_text):
        return ""
    return result_text


def _extract_with_gemini_pdf(pdf_bytes):
    global _GEMINI_QUOTA_EXHAUSTED
    if not GEMINI_PDF_OCR_ENABLED or not _GEMINI_KEYS_POOL:
        return ""
    if _GEMINI_QUOTA_EXHAUSTED:
        return ""
    if len(pdf_bytes) > MAX_GEMINI_PDF_BYTES:
        return ""
    try:
        pdf_b64 = base64.b64encode(pdf_bytes).decode("utf-8")
        prompt = (
            "Extract ALL text from this university notice/exam document. "
            "May be in Hindi, English, or both. May contain tables. "
            "Return extracted text verbatim, preserving structure. "
            "Do NOT summarize. Do NOT invent. Just extract the text."
        )
        payload = {
            "contents": [{"parts": [
                {"text": prompt},
                {"inline_data": {"mime_type": "application/pdf", "data": pdf_b64}}
            ]}],
            "generationConfig": {"temperature": 0.0, "maxOutputTokens": 16384}
        }
        for model in _DYNAMIC_MODELS:
            if model in _DEAD_MODELS:
                continue
            endpoint = f"https://generativelanguage.googleapis.com/v1beta/models/{model}:generateContent"
            for attempt in range(2):
                response, key_used, reason = _gemini_post_with_rotation(endpoint, payload, timeout=90)
                if response is None:
                    if reason == "all_keys_quota_exhausted":
                        _GEMINI_QUOTA_EXHAUSTED = True
                    return ""
                if response.status_code == 404:
                    _DEAD_MODELS.add(model)
                    break
                if response.status_code >= 500:
                    if attempt == 0:
                        time.sleep(1.5)
                        continue
                    break
                if response.status_code >= 400:
                    break
                try:
                    data = response.json()
                    extracted = _extract_gemini_text(data)
                    if extracted and len(extracted.strip()) > 50:
                        return extracted
                    break
                except Exception:
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


def _text_looks_garbage(text):
    if not text:
        return True
    stripped = text.strip()
    if len(stripped) < 20:
        return True
    valid = 0
    weird = 0
    for c in stripped:
        if c.isalnum() or c.isspace():
            valid += 1
        elif "\u0900" <= c <= "\u097F":
            valid += 1
        elif c in ".,:;/-()[]{}\"'!?%&@#*+=<>|":
            valid += 1
        else:
            weird += 1
    if weird > len(stripped) * 0.05:
        return True
    words = re.findall(r"\w+", stripped, re.UNICODE)
    if len(words) < 5:
        return True
    avg_len = sum(len(w) for w in words) / len(words)
    if avg_len > 20:
        return True
    if re.search(r"[bcdfghjklmnpqrstvwxz]{5,}", stripped, re.I):
        return True
    return False


_TITLE_KEYWORDS = (
    "admission", "result", "admit card", "answer key", "examination",
    "exam", "revaluation", "migration", "scholarship", "fee", "syllabus",
    "timetable", "counselling", "recruitment", "vacancy", "tender",
    "notice", "notification", "placement", "convocation", "registration",
    "प्रवेश", "परिणाम", "प्रवेश पत्र", "उत्तर कुंजी", "परीक्षा",
    "पुनर्मूल्यांकन", "छात्रवृत्ति", "शुल्क", "भर्ती", "निविदा", "सूचना",
)

_BOILERPLATE_HINTS = (
    "पता:", "address:", "फोन", "phone", "email", "e-mail",
    "website", "वेबसाइट", "दूरभाष", "fax", "फैक्स",
)


def _score_pdf_title_line(line, index):
    if not line:
        return -1
    ln = line.strip()
    if len(ln) < 15:
        return -1
    if re.match(r"^[\d\s/\-:.()|]+$", ln):
        return -1
    if _is_generic_title(ln) or _is_language_selector(ln):
        return -1
    low = ln.lower()
    score = min(len(ln), 120)
    for kw in _TITLE_KEYWORDS:
        if kw in low:
            score += 60
            break
    if re.search(r"(?:संख्या|no\.?|number)[\s:/\-]*[\w/\-]{2,}", low):
        score += 40
    if any(bad in low for bad in _BOILERPLATE_HINTS):
        score -= 60
    score += max(0, 10 - index)
    return score


def _extract_pdf_title_and_summary(raw_pdf_text, fallback_title=""):
    if not raw_pdf_text:
        return fallback_title, ""
    current_clean = clean_text(fallback_title or "", 300)
    current_lower = current_clean.lower()
    lines = [ln.strip() for ln in raw_pdf_text.splitlines() if ln.strip()][:30]
    scored = []
    for idx, ln in enumerate(lines):
        sc = _score_pdf_title_line(ln, idx)
        if sc > 0:
            scored.append((sc, idx, ln))
    scored.sort(key=lambda row: (-row[0], row[1]))
    better_title = current_clean
    for _sc, _idx, ln in scored:
        ln_low = ln.lower()
        if ln_low == current_lower:
            continue
        if len(ln) > len(current_clean) + 5:
            better_title = clean_text(ln, 300)
            break
    summary = ""
    for _sc, _idx, ln in scored:
        if ln.lower() == better_title.lower():
            continue
        if re.search(r"\d", ln):
            summary = clean_text(ln, 200)
            break
    if not summary:
        for _sc, _idx, ln in scored:
            if ln.lower() != better_title.lower():
                summary = clean_text(ln, 200)
                break
    return better_title, summary


def download_pdf_content(pdf_url, timeout=30, verify_ssl=True):
    global _RUNTIME_PDF_CACHE
    if pdf_url in _RUNTIME_PDF_CACHE:
        content = _RUNTIME_PDF_CACHE[pdf_url]
    else:
        try:
            session = make_session()
            content, actual_url, method = _download_with_pdf_resolution(session, pdf_url, timeout, verify_ssl=verify_ssl)
            if not content:
                return None, "", False, method, ""
            if len(content) > MAX_PDF_SEND_BYTES:
                return None, "", False, "size_limit", ""
            _cache_put(pdf_url, content)
            if actual_url and actual_url != pdf_url:
                _cache_put(actual_url, content)
        except Exception as exc:
            print(f"[WARN] PDF download failed for {pdf_url}: {exc}", file=sys.stderr)
            return None, "", False, "download_error", ""

    raw_text = _extract_pdf_text_plumber(content)
    extraction_method = "plumber"

    if _text_looks_thin(raw_text):
        gemini_text = _extract_with_gemini_pdf(content)
        if gemini_text and len(gemini_text.strip()) > len(raw_text.strip()):
            raw_text = f"{raw_text}\n\n--- GEMINI OCR ---\n\n{gemini_text}" if raw_text.strip() else gemini_text
            extraction_method = "gemini"
        else:
            if OCR_ENABLED and _RAPIDOCR_AVAILABLE:
                rocr_text = _extract_pdf_text_rapidocr(content)
                if rocr_text and len(rocr_text.strip()) > len(raw_text.strip()):
                    raw_text = f"{raw_text}\n\n--- RAPIDOCR ---\n\n{rocr_text}" if raw_text.strip() else rocr_text
                    extraction_method = "rapidocr"
            if extraction_method == "plumber" and TESSERACT_ENABLED and _TESSERACT_AVAILABLE:
                tess_text = _extract_pdf_text_tesseract(content)
                if tess_text and len(tess_text.strip()) > len(raw_text.strip()):
                    raw_text = f"{raw_text}\n\n--- TESSERACT OCR ---\n\n{tess_text}" if raw_text.strip() else tess_text
                    extraction_method = "tesseract"

    cleaned = clean_text(raw_text, MAX_PDF_TEXT_CHARS)
    raw_for_title = raw_text[:MAX_PDF_RAW_TEXT_CHARS]
    return (content, cleaned, extraction_method != "plumber", extraction_method, raw_for_title)


def keyword_fallback(items):
    """
    FIX: keyword_fallback must NEVER set important=False. If Gemini is
    unavailable (quota exhausted / auth failure) and a real notice title
    does not contain a STRONG_KEYWORD, silently marking it "ignored"
    permanently loses the notice. Instead we mark it important=True and
    tag it with "unverified" so downstream UI/debug can tell the difference,
    but real notices are never silently dropped.
    """
    result = {}
    for index, item in enumerate(items):
        text = (f"{item.get('title', '')} {item.get('url', '')} "
                f"{item.get('context', '')} {item.get('pdf_text', '')}").lower()
        keyword_match = any(kw in text for kw in STRONG_KEYWORDS if kw)
        category = "notice"
        if any(k in text for k in ("admission", "प्रवेश")):
            category = "admission"
        elif any(k in text for k in ("result", "परिणाम", "रिजल्ट")):
            category = "result"
        elif any(k in text for k in ("admit card", "प्रवेश पत्र")):
            category = "admit_card"
        elif any(k in text for k in ("answer key", "उत्तर कुंजी")):
            category = "answer_key"
        elif any(k in text for k in ("revaluation", "पुनर्मूल्यांकन")):
            category = "revaluation"
        elif any(k in text for k in ("migration", "माइग्रेशन", "provisional certificate", "duplicate marksheet")):
            category = "migration_certificate"
        elif any(k in text for k in ("fee", "शुल्क")):
            category = "fee_structure"
        elif any(k in text for k in ("academic calendar", "शैक्षणिक कैलेंडर")):
            category = "academic_calendar"
        elif any(k in text for k in ("syllabus", "पाठ्यक्रम")):
            category = "syllabus"
        elif any(k in text for k in ("timetable", "time table", "समय सारिणी")):
            category = "timetable"
        elif any(k in text for k in ("scholarship", "छात्रवृत्ति")):
            category = "scholarship"
        elif any(k in text for k in ("placement", "प्लेसमेंट")):
            category = "placement"
        elif any(k in text for k in ("tender", "निविदा")):
            category = "tender"
        elif any(k in text for k in ("recruitment", "vacancy", "भर्ती")):
            category = "vacancy"
        elif any(k in text for k in ("exam schedule", "examination programme", "परीक्षा कार्यक्रम")):
            category = "exam_schedule"

        title_text = (item.get("title") or "").strip()
        pdf_hint = (item.get("pdf_summary_hint") or "").strip()
        ctx = (item.get("context") or "").strip()

        summary = ""
        if pdf_hint and pdf_hint.lower() != title_text.lower():
            summary = pdf_hint
        elif ctx and ctx.lower() != title_text.lower() and len(ctx) >= 20:
            summary = ctx

        result[str(index)] = {
            "important": True,
            "category": category,
            "summary": clean_text(summary, 180),
            "title_hi": None,
            "unverified": not keyword_match,
            "confidence": "high" if keyword_match else "low",
            "pre_classified": False,
        }
    return result


def _build_prompt(prompt_items):
    return (
        "You classify and extract details from links on official "
        "Jharkhand university websites (nic.in and .ac.in). "
        "Return JSON only using the exact schema below.\n\n"
        "CRITICAL — set important=false for ALL of these:\n"
        "- Language selector links (titles like 'हिन्दी', 'English')\n"
        "- Category listing pages, archive pages, pagination pages\n"
        "- Navigation pages (Home, Contact, About, Gallery, Anti-Ragging, Grievance)\n"
        "- Pages with titles like 'Archive', 'More', '»', numbers, empty\n"
        "- 'Sorry, no notice matched', 'no records found', 'no data found'\n"
        "- Generic descriptions like 'listing page', 'category page'\n\n"
        "Set important=true ONLY for genuine, specific notices — "
        "admission, result, admit card, answer key, exam schedule, revaluation, "
        "migration/certificate, fee structure, academic calendar, syllabus, "
        "timetable, scholarship, placement, recruitment, tender, etc.\n\n"
        "For EACH item determine:\n"
        "1. important (true/false)\n"
        "2. category — one of: 'admission', 'result', 'admit_card', 'answer_key', "
        "'exam_schedule', 'revaluation', 'migration_certificate', 'fee_structure', "
        "'academic_calendar', 'syllabus', 'timetable', 'scholarship', 'placement', "
        "'tender', 'vacancy', 'notice', 'other'\n"
        "3. summary — 1-line summary (<= 150 chars)\n"
        "4. title_hi — Hindi (Devanagari) translation of the title.\n\n"
        "IMPORTANT: If 'pdf_text' is provided, treat it as PRIMARY source.\n"
        "Do NOT invent facts. Use null when unsure.\n\n"
        "Schema:\n"
        '{"items":[{'
        '"id":"0","important":true,"category":"admission","summary":"...","title_hi":"...",'
        '"reference_number":null,"issuing_authority":null,"issuing_date":null,'
        '"contact_person":null,"contact_number":null,"email":null,'
        '"helpline_number":null,"official_address":null,"important_instructions":null,'
        '"course_name":null,"course_level":null,"session":null,"admission_mode":null,'
        '"entrance_exam_name":null,"eligibility":null,"eligibility_marks":null,'
        '"age_criteria":null,"application_fee":null,"fee_structure":null,'
        '"total_seats":null,"reservation_details":null,"apply_start_date":null,'
        '"last_date":null,"counselling_date":null,"apply_link":null,'
        '"prospectus_link":null,"documents_required":null,"hostel_available":null,'
        '"result_for":null,"exam_name":null,"semester":null,"result_date":null,'
        '"result_link":null,"result_type":null,"merit_list_link":null,'
        '"cutoff_marks":null,"total_selected":null,"next_stage":null,'
        '"next_stage_date":null,"rechecking_last_date":null,"rechecking_link":null,'
        '"rechecking_fee":null,'
        '"exam_date":null,"exam_time":null,"exam_duration":null,"exam_center":null,'
        '"reporting_time":null,"download_start_date":null,"download_last_date":null,'
        '"admit_card_link":null,"instructions":null,'
        '"total_questions":null,"answer_key_link":null,"objection_start_date":null,'
        '"objection_last_date":null,"objection_fee":null,"per_question_fee":null,'
        '"objection_mode":null,"objection_address":null,"payment_mode":null,'
        '"exam_start_date":null,"exam_end_date":null,"timetable_link":null,'
        '"subject_list":null,"paper_code":null,"practical_dates":null,"viva_dates":null,'
        '"revaluation_start_date":null,"revaluation_last_date":null,'
        '"revaluation_fee":null,"revaluation_mode":null,'
        '"certificate_type":null,"processing_time":null,'
        '"fee_type":null,"amount":null,"late_fee":null,"payment_link":null,'
        '"event_type":null,"event_date":null,"event_description":null,'
        '"calendar_link":null,'
        '"syllabus_link":null,"effective_from":null,'
        '"scheme_name":null,"scholarship_amount":null,"applicable_category":null,'
        '"income_limit":null,"apply_mode":null,"portal_name":null,'
        '"company_name":null,"job_role":null,"package":null,"location":null,'
        '"drive_date":null,'
        '"tender_no":null,"tender_type":null,"work_description":null,'
        '"estimated_cost":null,"emd_amount":null,"tender_fee":null,'
        '"submission_last_date":null,"opening_date":null,"tender_document_link":null,'
        '"eligibility_criteria":null,'
        '"post_name":null,"total_posts":null,"post_details":[],"qualification":null,'
        '"age_limit":null,"pay_scale":null,"advertisement_no":null,'
        '"selection_process":null,"experience_required":null,"posting_location":null,'
        '"interview_date":null,"venue":null,'
        '"subject":null,"notice_type":null,"applicable_to":null,"action_required":null,'
        '"action_deadline":null,"effective_date":null,"supersedes":null,"order_link":null,'
        '"full_content":null,'
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
            "course_name": _str(row, "course_name", 200),
            "course_level": _str(row, "course_level", 60),
            "session": _str(row, "session", 80),
            "admission_mode": _str(row, "admission_mode", 100),
            "entrance_exam_name": _str(row, "entrance_exam_name", 200),
            "eligibility": _str(row, "eligibility", 250),
            "eligibility_marks": _str(row, "eligibility_marks", 100),
            "age_criteria": _str(row, "age_criteria", 100),
            "application_fee": _str(row, "application_fee", 250),
            "fee_structure": _str(row, "fee_structure", 200),
            "total_seats": _str(row, "total_seats", 60),
            "reservation_details": _str(row, "reservation_details", 250),
            "apply_start_date": _str(row, "apply_start_date", 80),
            "last_date": _str(row, "last_date", 80),
            "counselling_date": _str(row, "counselling_date", 80),
            "apply_link": _str(row, "apply_link", 500),
            "prospectus_link": _str(row, "prospectus_link", 500),
            "documents_required": _str(row, "documents_required", 400),
            "hostel_available": _str(row, "hostel_available", 60),
            "result_for": _str(row, "result_for", 200),
            "exam_name": _str(row, "exam_name", 200),
            "semester": _str(row, "semester", 60),
            "result_date": _str(row, "result_date", 80),
            "result_link": _str(row, "result_link", 500),
            "result_type": _str(row, "result_type", 80),
            "merit_list_link": _str(row, "merit_list_link", 500),
            "cutoff_marks": _str(row, "cutoff_marks", 150),
            "total_selected": _str(row, "total_selected", 60),
            "next_stage": _str(row, "next_stage", 200),
            "next_stage_date": _str(row, "next_stage_date", 80),
            "rechecking_last_date": _str(row, "rechecking_last_date", 80),
            "rechecking_link": _str(row, "rechecking_link", 500),
            "rechecking_fee": _str(row, "rechecking_fee", 100),
            "exam_date": _str(row, "exam_date", 80),
            "exam_time": _str(row, "exam_time", 60),
            "exam_duration": _str(row, "exam_duration", 60),
            "exam_center": _str(row, "exam_center", 250),
            "reporting_time": _str(row, "reporting_time", 60),
            "download_start_date": _str(row, "download_start_date", 80),
            "download_last_date": _str(row, "download_last_date", 80),
            "admit_card_link": _str(row, "admit_card_link", 500),
            "instructions": _str(row, "instructions", 400),
            "total_questions": _str(row, "total_questions", 60),
            "answer_key_link": _str(row, "answer_key_link", 500),
            "objection_start_date": _str(row, "objection_start_date", 80),
            "objection_last_date": _str(row, "objection_last_date", 80),
            "objection_fee": _str(row, "objection_fee", 100),
            "per_question_fee": _str(row, "per_question_fee", 100),
            "objection_mode": _str(row, "objection_mode", 80),
            "objection_address": _str(row, "objection_address", 250),
            "payment_mode": _str(row, "payment_mode", 100),
            "exam_start_date": _str(row, "exam_start_date", 80),
            "exam_end_date": _str(row, "exam_end_date", 80),
            "timetable_link": _str(row, "timetable_link", 500),
            "subject_list": _str(row, "subject_list", 400),
            "paper_code": _str(row, "paper_code", 200),
            "practical_dates": _str(row, "practical_dates", 150),
            "viva_dates": _str(row, "viva_dates", 150),
            "revaluation_start_date": _str(row, "revaluation_start_date", 80),
            "revaluation_last_date": _str(row, "revaluation_last_date", 80),
            "revaluation_fee": _str(row, "revaluation_fee", 100),
            "revaluation_mode": _str(row, "revaluation_mode", 80),
            "certificate_type": _str(row, "certificate_type", 120),
            "processing_time": _str(row, "processing_time", 80),
            "fee_type": _str(row, "fee_type", 100),
            "amount": _str(row, "amount", 100),
            "late_fee": _str(row, "late_fee", 100),
            "payment_link": _str(row, "payment_link", 500),
            "event_type": _str(row, "event_type", 100),
            "event_date": _str(row, "event_date", 80),
            "event_description": _str(row, "event_description", 250),
            "calendar_link": _str(row, "calendar_link", 500),
            "syllabus_link": _str(row, "syllabus_link", 500),
            "effective_from": _str(row, "effective_from", 80),
            "scheme_name": _str(row, "scheme_name", 200),
            "scholarship_amount": _str(row, "scholarship_amount", 150),
            "applicable_category": _str(row, "applicable_category", 150),
            "income_limit": _str(row, "income_limit", 100),
            "apply_mode": _str(row, "apply_mode", 100),
            "portal_name": _str(row, "portal_name", 150),
            "company_name": _str(row, "company_name", 200),
            "job_role": _str(row, "job_role", 200),
            "package": _str(row, "package", 100),
            "location": _str(row, "location", 200),
            "drive_date": _str(row, "drive_date", 80),
            "tender_no": _str(row, "tender_no", 100),
            "tender_type": _str(row, "tender_type", 100),
            "work_description": _str(row, "work_description", 300),
            "estimated_cost": _str(row, "estimated_cost", 100),
            "emd_amount": _str(row, "emd_amount", 100),
            "tender_fee": _str(row, "tender_fee", 100),
            "submission_last_date": _str(row, "submission_last_date", 80),
            "opening_date": _str(row, "opening_date", 80),
            "tender_document_link": _str(row, "tender_document_link", 500),
            "eligibility_criteria": _str(row, "eligibility_criteria", 300),
            "post_name": _str(row, "post_name", 200),
            "total_posts": row.get("total_posts"),
            "post_details": clean_posts,
            "qualification": _str(row, "qualification", 250),
            "age_limit": _str(row, "age_limit", 100),
            "pay_scale": _str(row, "pay_scale", 200),
            "advertisement_no": _str(row, "advertisement_no", 100),
            "selection_process": _str(row, "selection_process", 300),
            "experience_required": _str(row, "experience_required", 200),
            "posting_location": _str(row, "posting_location", 200),
            "interview_date": _str(row, "interview_date", 80),
            "venue": _str(row, "venue", 250),
            "subject": _str(row, "subject", 200),
            "notice_type": _str(row, "notice_type", 100),
            "applicable_to": _str(row, "applicable_to", 200),
            "action_required": _str(row, "action_required", 250),
            "action_deadline": _str(row, "action_deadline", 80),
            "effective_date": _str(row, "effective_date", 80),
            "supersedes": _str(row, "supersedes", 200),
            "order_link": _str(row, "order_link", 500),
            "full_content": _str(row, "full_content", 500),
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
            "id": str(i), "title": item["title"], "url": item["url"],
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
    global _GEMINI_QUOTA_EXHAUSTED
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
        ("last_date", "Last Date"), ("submission_last_date", "Submission Last"),
        ("application_start_date", "App Starts"), ("apply_start_date", "App Starts"),
        ("exam_date", "Exam Date"), ("result_date", "Result Date"),
        ("total_posts", "Total Posts"), ("application_fee", "Fee"),
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
            content, actual_url, method = _download_with_pdf_resolution(
                session, pdf_url, 30,
                verify_ssl=_SITE_VERIFY_SSL_BY_ID.get(record.get("site_id"), True),
            )
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


CATEGORY_EMOJI = {
    "admission": "🎓", "result": "📊", "admit_card": "🎫",
    "answer_key": "🔑", "exam_schedule": "📅", "revaluation": "🔄",
    "migration_certificate": "📜", "fee_structure": "💳",
    "academic_calendar": "🗓️", "syllabus": "📚", "timetable": "⏰",
    "scholarship": "🎯", "placement": "💼", "tender": "📑",
    "vacancy": "💼", "notice": "📌", "other": "📎",
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
    "reference_number": "संदर्भ संख्या", "issuing_authority": "जारीकर्ता प्राधिकरण",
    "issuing_date": "जारी तारीख़", "contact_person": "संपर्क व्यक्ति",
    "contact_number": "संपर्क नंबर", "email": "ईमेल",
    "helpline_number": "हेल्पलाइन नंबर", "official_address": "कार्यालय पता",
    "important_instructions": "ज़रूरी निर्देश",
    "course_name": "कोर्स", "course_level": "कोर्स स्तर", "session": "सत्र",
    "admission_mode": "प्रवेश मोड", "entrance_exam_name": "प्रवेश परीक्षा",
    "eligibility": "योग्यता", "eligibility_marks": "योग्यता मार्क्स",
    "age_criteria": "उम्र मानदंड", "application_fee": "आवेदन शुल्क",
    "fee_structure": "शुल्क संरचना", "total_seats": "कुल सीटें",
    "reservation_details": "आरक्षण विवरण", "apply_start_date": "आवेदन शुरू",
    "last_date": "अंतिम तिथि", "counselling_date": "काउंसलिंग तिथि",
    "apply_link": "ऑनलाइन आवेदन", "prospectus_link": "प्रॉस्पेक्टस",
    "documents_required": "आवश्यक दस्तावेज़", "hostel_available": "हॉस्टल उपलब्ध",
    "result_for": "परिणाम किसका", "exam_name": "परीक्षा", "semester": "सेमेस्टर",
    "result_date": "परिणाम तिथि", "result_link": "परिणाम देखें",
    "result_type": "परिणाम प्रकार", "merit_list_link": "मेरिट लिस्ट",
    "cutoff_marks": "कटऑफ़ मार्क्स", "total_selected": "कुल चयनित",
    "next_stage": "अगला चरण", "next_stage_date": "अगले चरण की तिथि",
    "rechecking_last_date": "रीचेकिंग अंतिम तिथि", "rechecking_link": "रीचेकिंग लिंक",
    "rechecking_fee": "रीचेकिंग शुल्क",
    "exam_date": "परीक्षा तिथि", "exam_time": "परीक्षा समय",
    "exam_duration": "परीक्षा अवधि", "exam_center": "परीक्षा केंद्र",
    "reporting_time": "रिपोर्टिंग समय", "download_start_date": "डाउनलोड शुरू",
    "download_last_date": "डाउनलोड अंतिम", "admit_card_link": "एडमिट कार्ड डाउनलोड",
    "instructions": "निर्देश",
    "total_questions": "कुल प्रश्न", "answer_key_link": "उत्तर कुंजी देखें",
    "objection_start_date": "आपत्ति शुरू", "objection_last_date": "आपत्ति अंतिम",
    "objection_fee": "आपत्ति शुल्क", "per_question_fee": "प्रति प्रश्न शुल्क",
    "objection_mode": "आपत्ति मोड", "objection_address": "आपत्ति पता",
    "payment_mode": "भुगतान मोड",
    "exam_start_date": "परीक्षा शुरू", "exam_end_date": "परीक्षा समाप्त",
    "timetable_link": "टाइम टेबल देखें", "subject_list": "विषय सूची",
    "paper_code": "पेपर कोड", "practical_dates": "प्रैक्टिकल तिथियाँ",
    "viva_dates": "वाइवा तिथियाँ",
    "revaluation_start_date": "पुनर्मूल्यांकन शुरू", "revaluation_last_date": "पुनर्मूल्यांकन अंतिम",
    "revaluation_fee": "पुनर्मूल्यांकन शुल्क", "revaluation_mode": "पुनर्मूल्यांकन मोड",
    "certificate_type": "प्रमाण पत्र प्रकार", "processing_time": "प्रोसेसिंग समय",
    "fee_type": "शुल्क प्रकार", "amount": "राशि", "late_fee": "विलंब शुल्क",
    "payment_link": "भुगतान लिंक",
    "event_type": "कार्यक्रम प्रकार", "event_date": "कार्यक्रम तिथि",
    "event_description": "विवरण", "calendar_link": "कैलेंडर देखें",
    "syllabus_link": "पाठ्यक्रम देखें", "effective_from": "प्रभावी तिथि से",
    "scheme_name": "योजना", "scholarship_amount": "छात्रवृत्ति राशि",
    "applicable_category": "किस श्रेणी के लिए", "income_limit": "आय सीमा",
    "apply_mode": "आवेदन मोड", "portal_name": "पोर्टल",
    "company_name": "कंपनी", "job_role": "जॉब रोल", "package": "पैकेज",
    "location": "स्थान", "drive_date": "ड्राइव तिथि",
    "tender_no": "निविदा संख्या", "tender_type": "निविदा प्रकार",
    "work_description": "कार्य विवरण", "estimated_cost": "अनुमानित लागत",
    "emd_amount": "EMD राशि", "tender_fee": "निविदा शुल्क",
    "submission_last_date": "जमा अंतिम तिथि", "opening_date": "खोलने की तिथि",
    "tender_document_link": "निविदा दस्तावेज़", "eligibility_criteria": "पात्रता मानदंड",
    "post_name": "पद का नाम", "total_posts": "कुल पद", "post_breakdown": "पद विवरण",
    "qualification": "योग्यता", "age_limit": "उम्र सीमा", "pay_scale": "वेतन",
    "advertisement_no": "विज्ञापन संख्या", "selection_process": "चयन प्रक्रिया",
    "experience_required": "अनुभव आवश्यक", "posting_location": "पोस्टिंग स्थान",
    "interview_date": "इंटरव्यू तिथि", "venue": "स्थान",
    "subject": "विषय", "notice_type": "सूचना प्रकार", "applicable_to": "किस पर लागू",
    "action_required": "क्या करना है", "action_deadline": "अंतिम तिथि",
    "effective_date": "प्रभावी तिथि", "supersedes": "किसे रद्द करता है",
    "order_link": "आदेश देखें", "full_content": "पूरा विवरण",
    "other_details": "अन्य जानकारी", "read_full": "पूरी सूचना देखें",
}

_LABELS_EN = {
    "reference_number": "Reference No", "issuing_authority": "Issuing Authority",
    "issuing_date": "Issuing Date", "contact_person": "Contact Person",
    "contact_number": "Contact Number", "email": "Email",
    "helpline_number": "Helpline", "official_address": "Official Address",
    "important_instructions": "Important Instructions",
    "course_name": "Course", "course_level": "Course Level", "session": "Session",
    "admission_mode": "Admission Mode", "entrance_exam_name": "Entrance Exam",
    "eligibility": "Eligibility", "eligibility_marks": "Eligibility Marks",
    "age_criteria": "Age Criteria", "application_fee": "Application Fee",
    "fee_structure": "Fee Structure", "total_seats": "Total Seats",
    "reservation_details": "Reservation Details", "apply_start_date": "Application Starts",
    "last_date": "Last Date", "counselling_date": "Counselling Date",
    "apply_link": "Apply Online", "prospectus_link": "Prospectus",
    "documents_required": "Documents Required", "hostel_available": "Hostel Available",
    "result_for": "Result For", "exam_name": "Exam", "semester": "Semester",
    "result_date": "Result Date", "result_link": "Check Result",
    "result_type": "Result Type", "merit_list_link": "Merit List",
    "cutoff_marks": "Cutoff Marks", "total_selected": "Total Selected",
    "next_stage": "Next Stage", "next_stage_date": "Next Stage Date",
    "rechecking_last_date": "Rechecking Last Date", "rechecking_link": "Rechecking Link",
    "rechecking_fee": "Rechecking Fee",
    "exam_date": "Exam Date", "exam_time": "Exam Time",
    "exam_duration": "Exam Duration", "exam_center": "Exam Center",
    "reporting_time": "Reporting Time", "download_start_date": "Download Starts",
    "download_last_date": "Download Last Date", "admit_card_link": "Download Admit Card",
    "instructions": "Instructions",
    "total_questions": "Total Questions", "answer_key_link": "View Answer Key",
    "objection_start_date": "Objection Starts", "objection_last_date": "Objection Last Date",
    "objection_fee": "Objection Fee", "per_question_fee": "Per Question Fee",
    "objection_mode": "Objection Mode", "objection_address": "Objection Address",
    "payment_mode": "Payment Mode",
    "exam_start_date": "Exam Starts", "exam_end_date": "Exam Ends",
    "timetable_link": "Timetable", "subject_list": "Subjects",
    "paper_code": "Paper Code", "practical_dates": "Practical Dates",
    "viva_dates": "Viva Dates",
    "revaluation_start_date": "Revaluation Starts", "revaluation_last_date": "Revaluation Last Date",
    "revaluation_fee": "Revaluation Fee", "revaluation_mode": "Revaluation Mode",
    "certificate_type": "Certificate Type", "processing_time": "Processing Time",
    "fee_type": "Fee Type", "amount": "Amount", "late_fee": "Late Fee",
    "payment_link": "Payment Link",
    "event_type": "Event Type", "event_date": "Event Date",
    "event_description": "Description", "calendar_link": "View Calendar",
    "syllabus_link": "View Syllabus", "effective_from": "Effective From",
    "scheme_name": "Scheme", "scholarship_amount": "Scholarship Amount",
    "applicable_category": "Applicable Category", "income_limit": "Income Limit",
    "apply_mode": "Application Mode", "portal_name": "Portal",
    "company_name": "Company", "job_role": "Job Role", "package": "Package",
    "location": "Location", "drive_date": "Drive Date",
    "tender_no": "Tender No", "tender_type": "Tender Type",
    "work_description": "Work Description", "estimated_cost": "Estimated Cost",
    "emd_amount": "EMD", "tender_fee": "Tender Fee",
    "submission_last_date": "Submission Last Date", "opening_date": "Opening Date",
    "tender_document_link": "Tender Document", "eligibility_criteria": "Eligibility",
    "post_name": "Post Name", "total_posts": "Total Posts", "post_breakdown": "Post-wise Breakdown",
    "qualification": "Qualification", "age_limit": "Age Limit", "pay_scale": "Pay Scale",
    "advertisement_no": "Advertisement No", "selection_process": "Selection Process",
    "experience_required": "Experience Required", "posting_location": "Posting Location",
    "interview_date": "Interview Date", "venue": "Venue",
    "subject": "Subject", "notice_type": "Notice Type", "applicable_to": "Applicable To",
    "action_required": "Action Required", "action_deadline": "Action Deadline",
    "effective_date": "Effective Date", "supersedes": "Supersedes",
    "order_link": "View Order", "full_content": "Full Content",
    "other_details": "Other Details", "read_full": "View Full Notice",
}

_CATEGORY_NAMES_HI = {
    "admission": "प्रवेश", "result": "परिणाम", "admit_card": "प्रवेश पत्र",
    "answer_key": "उत्तर कुंजी", "exam_schedule": "परीक्षा कार्यक्रम",
    "revaluation": "पुनर्मूल्यांकन", "migration_certificate": "माइग्रेशन / प्रमाण पत्र",
    "fee_structure": "शुल्क संरचना", "academic_calendar": "शैक्षणिक कैलेंडर",
    "syllabus": "पाठ्यक्रम", "timetable": "समय सारिणी",
    "scholarship": "छात्रवृत्ति", "placement": "प्लेसमेंट",
    "tender": "निविदा", "vacancy": "भर्ती", "notice": "सूचना", "other": "अन्य",
}

_CATEGORY_NAMES_EN = {
    "admission": "Admission", "result": "Result", "admit_card": "Admit Card",
    "answer_key": "Answer Key", "exam_schedule": "Exam Schedule",
    "revaluation": "Revaluation", "migration_certificate": "Migration / Certificate",
    "fee_structure": "Fee Structure", "academic_calendar": "Academic Calendar",
    "syllabus": "Syllabus", "timetable": "Timetable",
    "scholarship": "Scholarship", "placement": "Placement",
    "tender": "Tender", "vacancy": "Vacancy", "notice": "Notice", "other": "Other",
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


def _format_admission(lines, c):
    _line(lines, "🎓", "course_name", _safe_str(c.get("course_name")))
    _line(lines, "📊", "course_level", _safe_str(c.get("course_level")))
    _line(lines, "📅", "session", _safe_str(c.get("session")))
    _line(lines, "📋", "admission_mode", _safe_str(c.get("admission_mode")))
    _line(lines, "📝", "entrance_exam_name", _safe_str(c.get("entrance_exam_name")))
    _line(lines, "📊", "total_seats", _safe_str(c.get("total_seats")))
    _line(lines, "✅", "eligibility", _safe_str(c.get("eligibility")))
    _line(lines, "📋", "eligibility_marks", _safe_str(c.get("eligibility_marks")))
    _line(lines, "🎂", "age_criteria", _safe_str(c.get("age_criteria")))
    _line(lines, "💳", "application_fee", _safe_str(c.get("application_fee")))
    _line(lines, "💰", "fee_structure", _safe_str(c.get("fee_structure")))
    _line(lines, "📋", "reservation_details", _safe_str(c.get("reservation_details")))
    _line(lines, "📋", "hostel_available", _safe_str(c.get("hostel_available")))
    _line(lines, "📋", "documents_required", _safe_str(c.get("documents_required")))
    _line(lines, "📅", "apply_start_date", _safe_str(c.get("apply_start_date")))
    _line(lines, "📅", "last_date", _safe_str(c.get("last_date")))
    _line(lines, "🎯", "counselling_date", _safe_str(c.get("counselling_date")))
    _link_line(lines, "📄", "prospectus_link", _safe_str(c.get("prospectus_link"), 500))
    _link_line(lines, "🌐", "apply_link", _safe_str(c.get("apply_link"), 500))
    _format_extra_details(lines, c)


def _format_result(lines, c):
    _line(lines, "📝", "result_for", _safe_str(c.get("result_for")))
    _line(lines, "📝", "exam_name", _safe_str(c.get("exam_name")))
    _line(lines, "📅", "session", _safe_str(c.get("session")))
    _line(lines, "📚", "semester", _safe_str(c.get("semester")))
    _line(lines, "📋", "result_type", _safe_str(c.get("result_type")))
    _line(lines, "📅", "result_date", _safe_str(c.get("result_date")))
    _line(lines, "📊", "total_selected", _safe_str(c.get("total_selected")))
    _line(lines, "📋", "cutoff_marks", _safe_str(c.get("cutoff_marks")))
    _link_line(lines, "📄", "result_link", _safe_str(c.get("result_link"), 500))
    _link_line(lines, "📄", "merit_list_link", _safe_str(c.get("merit_list_link"), 500))
    _line(lines, "📋", "next_stage", _safe_str(c.get("next_stage")))
    _line(lines, "📅", "next_stage_date", _safe_str(c.get("next_stage_date")))
    _line(lines, "🔄", "rechecking_last_date", _safe_str(c.get("rechecking_last_date")))
    _line(lines, "💳", "rechecking_fee", _safe_str(c.get("rechecking_fee")))
    _link_line(lines, "🔗", "rechecking_link", _safe_str(c.get("rechecking_link"), 500))
    _format_extra_details(lines, c)


def _format_admit_card(lines, c):
    _line(lines, "📝", "exam_name", _safe_str(c.get("exam_name")))
    _line(lines, "📅", "session", _safe_str(c.get("session")))
    _line(lines, "📚", "semester", _safe_str(c.get("semester")))
    _line(lines, "📅", "exam_date", _safe_str(c.get("exam_date")))
    _line(lines, "⏰", "exam_time", _safe_str(c.get("exam_time")))
    _line(lines, "⏱️", "exam_duration", _safe_str(c.get("exam_duration")))
    _line(lines, "📍", "exam_center", _safe_str(c.get("exam_center")))
    _line(lines, "⏰", "reporting_time", _safe_str(c.get("reporting_time")))
    _line(lines, "⬇️", "download_start_date", _safe_str(c.get("download_start_date")))
    _line(lines, "📅", "download_last_date", _safe_str(c.get("download_last_date")))
    _line(lines, "📋", "instructions", _safe_str(c.get("instructions")))
    _line(lines, "📞", "helpline_number", _safe_str(c.get("helpline_number")))
    _link_line(lines, "🎫", "admit_card_link", _safe_str(c.get("admit_card_link"), 500))
    _format_extra_details(lines, c)


def _format_answer_key(lines, c):
    _line(lines, "📝", "exam_name", _safe_str(c.get("exam_name")))
    _line(lines, "📅", "session", _safe_str(c.get("session")))
    _line(lines, "📅", "exam_date", _safe_str(c.get("exam_date")))
    _line(lines, "📋", "total_questions", _safe_str(c.get("total_questions")))
    _link_line(lines, "🔑", "answer_key_link", _safe_str(c.get("answer_key_link"), 500))
    _line(lines, "📅", "objection_start_date", _safe_str(c.get("objection_start_date")))
    _line(lines, "📅", "objection_last_date", _safe_str(c.get("objection_last_date")))
    _line(lines, "💳", "objection_fee", _safe_str(c.get("objection_fee")))
    _line(lines, "💳", "per_question_fee", _safe_str(c.get("per_question_fee")))
    _line(lines, "📋", "objection_mode", _safe_str(c.get("objection_mode")))
    _line(lines, "💳", "payment_mode", _safe_str(c.get("payment_mode")))
    _line(lines, "📍", "objection_address", _safe_str(c.get("objection_address")))
    _format_extra_details(lines, c)


def _format_exam_schedule(lines, c):
    _line(lines, "📝", "exam_name", _safe_str(c.get("exam_name")))
    _line(lines, "📅", "session", _safe_str(c.get("session")))
    _line(lines, "📚", "semester", _safe_str(c.get("semester")))
    _line(lines, "🎓", "course_name", _safe_str(c.get("course_name")))
    _line(lines, "📅", "exam_start_date", _safe_str(c.get("exam_start_date")))
    _line(lines, "📅", "exam_end_date", _safe_str(c.get("exam_end_date")))
    _line(lines, "⏰", "exam_time", _safe_str(c.get("exam_time")))
    _line(lines, "📍", "exam_center", _safe_str(c.get("exam_center")))
    _line(lines, "📋", "subject_list", _safe_str(c.get("subject_list")))
    _line(lines, "📋", "paper_code", _safe_str(c.get("paper_code")))
    _line(lines, "📅", "practical_dates", _safe_str(c.get("practical_dates")))
    _line(lines, "📅", "viva_dates", _safe_str(c.get("viva_dates")))
    _link_line(lines, "📄", "timetable_link", _safe_str(c.get("timetable_link"), 500))
    _format_extra_details(lines, c)


def _format_revaluation(lines, c):
    _line(lines, "📝", "exam_name", _safe_str(c.get("exam_name")))
    _line(lines, "📅", "session", _safe_str(c.get("session")))
    _line(lines, "📚", "semester", _safe_str(c.get("semester")))
    _line(lines, "🎓", "course_name", _safe_str(c.get("course_name")))
    _line(lines, "📅", "revaluation_start_date", _safe_str(c.get("revaluation_start_date")))
    _line(lines, "📅", "revaluation_last_date", _safe_str(c.get("revaluation_last_date")))
    _line(lines, "💳", "revaluation_fee", _safe_str(c.get("revaluation_fee")))
    _line(lines, "📋", "revaluation_mode", _safe_str(c.get("revaluation_mode")))
    _line(lines, "📋", "instructions", _safe_str(c.get("instructions")))
    _link_line(lines, "🌐", "apply_link", _safe_str(c.get("apply_link"), 500))
    _format_extra_details(lines, c)


def _format_migration_certificate(lines, c):
    _line(lines, "📜", "certificate_type", _safe_str(c.get("certificate_type")))
    _line(lines, "📋", "applicable_to", _safe_str(c.get("applicable_to")))
    _line(lines, "💳", "application_fee", _safe_str(c.get("application_fee")))
    _line(lines, "⏱️", "processing_time", _safe_str(c.get("processing_time")))
    _line(lines, "📋", "documents_required", _safe_str(c.get("documents_required")))
    _line(lines, "📋", "instructions", _safe_str(c.get("instructions")))
    _line(lines, "📞", "contact_number", _safe_str(c.get("contact_number")))
    _link_line(lines, "🌐", "apply_link", _safe_str(c.get("apply_link"), 500))
    _format_extra_details(lines, c)


def _format_fee_structure(lines, c):
    _line(lines, "🎓", "course_name", _safe_str(c.get("course_name")))
    _line(lines, "📊", "course_level", _safe_str(c.get("course_level")))
    _line(lines, "📅", "session", _safe_str(c.get("session")))
    _line(lines, "💳", "fee_type", _safe_str(c.get("fee_type")))
    _line(lines, "💰", "amount", _safe_str(c.get("amount")))
    _line(lines, "💳", "late_fee", _safe_str(c.get("late_fee")))
    _line(lines, "📅", "last_date", _safe_str(c.get("last_date")))
    _line(lines, "📋", "payment_mode", _safe_str(c.get("payment_mode")))
    _line(lines, "📋", "instructions", _safe_str(c.get("instructions")))
    _link_line(lines, "🌐", "payment_link", _safe_str(c.get("payment_link"), 500))
    _format_extra_details(lines, c)


def _format_academic_calendar(lines, c):
    _line(lines, "📅", "session", _safe_str(c.get("session")))
    _line(lines, "📋", "event_type", _safe_str(c.get("event_type")))
    _line(lines, "📅", "event_date", _safe_str(c.get("event_date")))
    _line(lines, "📝", "event_description", _safe_str(c.get("event_description")))
    _line(lines, "👥", "applicable_to", _safe_str(c.get("applicable_to")))
    _link_line(lines, "📄", "calendar_link", _safe_str(c.get("calendar_link"), 500))
    _format_extra_details(lines, c)


def _format_syllabus(lines, c):
    _line(lines, "🎓", "course_name", _safe_str(c.get("course_name")))
    _line(lines, "📊", "course_level", _safe_str(c.get("course_level")))
    _line(lines, "📚", "semester", _safe_str(c.get("semester")))
    _line(lines, "📅", "session", _safe_str(c.get("session")))
    _line(lines, "📅", "effective_from", _safe_str(c.get("effective_from")))
    _line(lines, "📋", "subject_list", _safe_str(c.get("subject_list")))
    _link_line(lines, "📄", "syllabus_link", _safe_str(c.get("syllabus_link"), 500))
    _format_extra_details(lines, c)


def _format_timetable(lines, c):
    _line(lines, "📝", "exam_name", _safe_str(c.get("exam_name")))
    _line(lines, "📅", "session", _safe_str(c.get("session")))
    _line(lines, "📚", "semester", _safe_str(c.get("semester")))
    _line(lines, "🎓", "course_name", _safe_str(c.get("course_name")))
    _line(lines, "📅", "exam_start_date", _safe_str(c.get("exam_start_date")))
    _line(lines, "📅", "exam_end_date", _safe_str(c.get("exam_end_date")))
    _line(lines, "📋", "subject_list", _safe_str(c.get("subject_list")))
    _link_line(lines, "📄", "timetable_link", _safe_str(c.get("timetable_link"), 500))
    _format_extra_details(lines, c)


def _format_scholarship(lines, c):
    _line(lines, "🎯", "scheme_name", _safe_str(c.get("scheme_name")))
    _line(lines, "💰", "scholarship_amount", _safe_str(c.get("scholarship_amount")))
    _line(lines, "👥", "applicable_category", _safe_str(c.get("applicable_category")))
    _line(lines, "💵", "income_limit", _safe_str(c.get("income_limit")))
    _line(lines, "🎓", "eligibility", _safe_str(c.get("eligibility")))
    _line(lines, "📋", "documents_required", _safe_str(c.get("documents_required")))
    _line(lines, "📋", "apply_mode", _safe_str(c.get("apply_mode")))
    _line(lines, "📋", "portal_name", _safe_str(c.get("portal_name")))
    _line(lines, "📅", "last_date", _safe_str(c.get("last_date")))
    _line(lines, "📞", "helpline_number", _safe_str(c.get("helpline_number")))
    _link_line(lines, "🌐", "apply_link", _safe_str(c.get("apply_link"), 500))
    _format_extra_details(lines, c)


def _format_placement(lines, c):
    _line(lines, "🏢", "company_name", _safe_str(c.get("company_name")))
    _line(lines, "💼", "job_role", _safe_str(c.get("job_role")))
    _line(lines, "💰", "package", _safe_str(c.get("package")))
    _line(lines, "📍", "location", _safe_str(c.get("location")))
    _line(lines, "📅", "drive_date", _safe_str(c.get("drive_date")))
    _line(lines, "🎓", "eligibility", _safe_str(c.get("eligibility")))
    _line(lines, "📋", "documents_required", _safe_str(c.get("documents_required")))
    _line(lines, "📅", "last_date", _safe_str(c.get("last_date")))
    _link_line(lines, "🌐", "apply_link", _safe_str(c.get("apply_link"), 500))
    _format_extra_details(lines, c)


def _format_tender(lines, c):
    _line(lines, "📋", "tender_no", _safe_str(c.get("tender_no")))
    _line(lines, "📋", "tender_type", _safe_str(c.get("tender_type")))
    _line(lines, "📝", "work_description", _safe_str(c.get("work_description")))
    _line(lines, "🏢", "issuing_authority", _safe_str(c.get("issuing_authority")))
    _line(lines, "💰", "estimated_cost", _safe_str(c.get("estimated_cost")))
    _line(lines, "💳", "emd_amount", _safe_str(c.get("emd_amount")))
    _line(lines, "📄", "tender_fee", _safe_str(c.get("tender_fee")))
    _line(lines, "📅", "submission_last_date", _safe_str(c.get("submission_last_date")))
    _line(lines, "📅", "opening_date", _safe_str(c.get("opening_date")))
    _line(lines, "📋", "eligibility_criteria", _safe_str(c.get("eligibility_criteria")))
    _link_line(lines, "📄", "tender_document_link", _safe_str(c.get("tender_document_link"), 500))
    _format_extra_details(lines, c)


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
    _line(lines, "💰", "pay_scale", _safe_str(c.get("pay_scale")))
    _line(lines, "📋", "experience_required", _safe_str(c.get("experience_required")))
    _line(lines, "📋", "posting_location", _safe_str(c.get("posting_location")))
    _line(lines, "📋", "selection_process", _safe_str(c.get("selection_process")))
    _line(lines, "📅", "last_date", _safe_str(c.get("last_date")))
    _line(lines, "📅", "interview_date", _safe_str(c.get("interview_date")))
    _line(lines, "📍", "venue", _safe_str(c.get("venue")))
    _line(lines, "📞", "contact_number", _safe_str(c.get("contact_number")))
    _link_line(lines, "🌐", "apply_link", _safe_str(c.get("apply_link"), 500))
    _format_extra_details(lines, c)


def _format_notice(lines, c):
    _line(lines, "📝", "subject", _safe_str(c.get("subject")))
    _line(lines, "📋", "notice_type", _safe_str(c.get("notice_type")))
    _line(lines, "🔖", "reference_number", _safe_str(c.get("reference_number")))
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
    "admission": _format_admission,
    "result": _format_result,
    "admit_card": _format_admit_card,
    "answer_key": _format_answer_key,
    "exam_schedule": _format_exam_schedule,
    "revaluation": _format_revaluation,
    "migration_certificate": _format_migration_certificate,
    "fee_structure": _format_fee_structure,
    "academic_calendar": _format_academic_calendar,
    "syllabus": _format_syllabus,
    "timetable": _format_timetable,
    "scholarship": _format_scholarship,
    "placement": _format_placement,
    "tender": _format_tender,
    "vacancy": _format_vacancy,
    "notice": _format_notice,
}


def format_message(site, item, classification=None):
    classification = classification or {}
    raw_title = _resolve_title(item)
    title_hi = _safe_str(classification.get("title_hi"), 200)
    title_is_hindi = _is_devanagari(raw_title)
    site_name = html.escape(site["name"])
    url = html.escape(item["url"], quote=True)
    summary_raw = _safe_str(classification.get("summary")) or ""
    if summary_raw.strip().lower() == raw_title.strip().lower():
        summary_raw = ""
    summary = html.escape(summary_raw)
    category = (classification.get("category") or "notice").lower()
    emoji = CATEGORY_EMOJI.get(category, "📌")
    ocr_method = item.get("pdf_method", "")
    if ocr_method == "gemini":
        ocr_marker = " 🔍G"
    elif ocr_method == "rapidocr":
        ocr_marker = " 🔍R"
    elif ocr_method == "tesseract":
        ocr_marker = " 🔍T"
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


def prune_state(
    state, retention_days, max_items=3000, max_pending_attempts=72, max_bytes=3000000,
    sent_retention_days=90, ignored_retention_days=30, baseline_retention_days=60,
):
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
        if status == "ready" and (telegram_attempts >= TELEGRAM_MAX_ATTEMPTS or telegram_window_expired):
            record["status"] = "permanent_error"
            record["last_error"] = clean_text(
                "Telegram retry window/attempt limit reached; last error: "
                + str(record.get("last_error") or "unknown"), 500
            )
            status = "permanent_error"

        if status in terminal:
            status_days = {
                "sent": max(7, int(sent_retention_days)),
                "ignored": max(7, int(ignored_retention_days)),
                "baseline": max(7, int(baseline_retention_days)),
                "permanent_error": retention_days,
            }.get(status, retention_days)
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
            record.pop("pdf_summary_hint", None)
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

    def serialized_size():
        try:
            payload = json.dumps(state, ensure_ascii=False, indent=2, separators=(",", ": ")) + "\n"
            return len(payload.encode("utf-8"))
        except (TypeError, ValueError):
            return max_bytes + 1

    for record in items.values():
        if not isinstance(record, dict):
            continue
        for field, limit in (("title", 300), ("context", 700), ("summary", 500), ("last_error", 500), ("pdf_text", MAX_PDF_TEXT_CHARS), ("explicit_title", 300)):
            value = record.get(field)
            if isinstance(value, str) and len(value) > limit:
                record[field] = clean_text(value, limit)
        if record.get("status") in {"pending", "ready"} and isinstance(record.get("pdf_text"), str):
            if len(record["pdf_text"]) > 2000:
                record["pdf_text"] = clean_text(record["pdf_text"], 2000)
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
        for _, key in terminal_rows:
            items.pop(key, None)
            if serialized_size() <= max_bytes:
                break

    if serialized_size() > max_bytes:
        for record in items.values():
            if not isinstance(record, dict):
                continue
            status = record.get("status")
            if status == "ready" and record.get("classification"):
                record.pop("pdf_text", None)
            elif status in {"pending", "ready"} and isinstance(record.get("pdf_text"), str):
                record["pdf_text"] = clean_text(record["pdf_text"], 2000)
            if isinstance(record.get("context"), str):
                record["context"] = clean_text(record.get("context"), 350)

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


_SELF_TEST_STALE_CASES: List[Tuple[str, str, str, bool, str]] = [
    ("संपर्क करें: नई भर्ती 2026", "", "", False, "Hindi recruitment title that contains 'संपर्क' word"),
    ("Facebook WhatsApp Integration Notice", "", "", False, "Facebook-related integration notice (has 'notice' signal)"),
    ("जिला प्रशासन द्वारा नई नियुक्ति सूचना", "", "", False, "Hindi appointment notice"),
    ("Tender Notice: Contact Office for Details", "", "", False, "Tender with 'contact' nav word but also 'tender'/'notice' signals"),
    ("19.09.2026: Very Short Term Tender Notice from Education Department, Giridih.", "", "", False, "Dated tender notice from district site"),
    ("भर्ती विज्ञापन संख्या 03/2026 - जिला प्रशासन गिरिडीह", "", "", False, "Hindi vacancy with reference number"),
    ("Home Whats New Facebook Latest News", "", "https://x.nic.in/about/", True, "Classic English menu dump on non-document URL"),
    ("Home Whats New Facebook X Whats New 08.10.2026", "", "https://x.nic.in/contact/", True, "Long menu dump with repeated nav signals"),
    ("Home Whats New Facebook X Whats New 08.10.2026: Important Apprenticeship "
     "Notice From Employment Exchange, Giridih. Published on: 08/10/2026 "
     "Prime Minister National Apprenticeship Mela – 12-10-2026 Sha", "", "", True, "Real Giridih production case with empty URL (no document hint)"),
    ("मुख्य पृष्ठ महत्वपूर्ण लिंक त्वरित लिंक", "", "", True, "Hindi menu dump"),
    ("About Us Contact Us Feedback Site Map", "", "https://x.nic.in/about/", True, "Classic English about/contact nav dump"),
    ("Home Facebook Twitter Instagram YouTube", "", "https://x.nic.in/", True, "Social links nav dump"),
    ("Home Whats New Facebook X Whats New 08.10.2026: Important Apprenticeship "
     "Notice From Employment Exchange, Giridih.",
     "", "https://giridih.nic.in/writereaddata/Apprenticeship.pdf", False, "Giridih production case: document URL with menu-dump title must be kept"),
    ("Home Whats New Facebook X Whats New: Latest Update",
     "", "https://giridih.nic.in/downloadfile/notice_2026.pdf", False, "Document URL with menu-dump title must be kept"),
]


def _run_stale_notice_self_tests():
    failures = 0
    total = len(_SELF_TEST_STALE_CASES)
    print(f"[TEST] Running {total} stale-notice cases...", file=sys.stderr)
    for title, context, url, expected, desc in _SELF_TEST_STALE_CASES:
        try:
            got = _is_stale_notice(title, context, url)
        except Exception as exc:
            print(f"[TEST-ERROR] {desc}: {type(exc).__name__}: {exc}", file=sys.stderr)
            failures += 1
            continue
        if got == expected:
            print(f"[TEST-PASS ] {desc}", file=sys.stderr)
        else:
            print(f"[TEST-FAIL ] {desc}: got={got} expected={expected} title='{title[:70]}'", file=sys.stderr)
            failures += 1
    print(f"[TEST] Done: {total - failures}/{total} passed, {failures} failed.", file=sys.stderr)
    return failures


def _run_spa_self_tests():
    failures = 0
    cases = [
        ("https://vbu.ac.in/#/notices", "https://vbu.ac.in/#/notices"),
        ("https://vbu.ac.in/#!/home", "https://vbu.ac.in/#!/home"),
        ("https://vbu.ac.in/#section", "https://vbu.ac.in/"),
    ]
    for raw, expected in cases:
        got = _canonical_spa_url(raw)
        if got == expected:
            print(f"[TEST-PASS ] SPA URL canonicalization: {raw}", file=sys.stderr)
        else:
            print(f"[TEST-FAIL ] SPA URL canonicalization: got={got!r}, expected={expected!r}", file=sys.stderr)
            failures += 1
    identity_cases = [
        ("https://vbu.ac.in/#/notice/12345", "https://vbu.ac.in/#/notice/12345"),
        ("https://vbu.ac.in/#!/home", "https://vbu.ac.in/#!/home"),
        ("https://vbu.ac.in/#team", "https://vbu.ac.in/"),
        ("https://vbu.ac.in/?utm_source=test#/notice/12345", "https://vbu.ac.in/#/notice/12345"),
    ]
    for raw, expected in identity_cases:
        got = canonical_identity_url(raw)
        if got == expected:
            print(f"[TEST-PASS ] SPA identity canonicalization: {raw}", file=sys.stderr)
        else:
            print(f"[TEST-FAIL ] SPA identity canonicalization: got={got!r}, expected={expected!r}", file=sys.stderr)
            failures += 1

    try:
        test_html = '<a href="#/notice/12345">UG Semester Result Notice 2026</a>'
        test_scan = {"keywords": ["notice", "result", "semester"], "discovery_keywords": [], "max_items_per_site": 100}
        test_site = {"id": "vbu-test", "name": "VBU test", "keywords": [], "discovery_keywords": []}
        extracted = extract_candidates(test_html, "https://vbu.ac.in/", test_site, test_scan)
        if any(row.get("url") == "https://vbu.ac.in/#/notice/12345" for row in extracted):
            print("[TEST-PASS ] SPA candidate extraction preserves hash route", file=sys.stderr)
        else:
            print(f"[TEST-FAIL ] SPA candidate extraction lost hash route: {[row.get('url') for row in extracted]!r}", file=sys.stderr)
            failures += 1
    except Exception as exc:
        print(f"[TEST-FAIL ] SPA candidate extraction raised {type(exc).__name__}: {exc}", file=sys.stderr)
        failures += 1

    template_cases = [
        ("<div>{{ notice.title }}</div>", True),
        ("<div>Ordinary notice title</div>", False),
    ]
    for html_text, expected in template_cases:
        got = _has_unrendered_angular_templates(html_text)
        if got == expected:
            print(f"[TEST-PASS ] Angular template detection: expected={expected}", file=sys.stderr)
        else:
            print(f"[TEST-FAIL ] Angular template detection: got={got}, expected={expected}", file=sys.stderr)
            failures += 1

    js_decision_cases = [
        ({"js_render": "auto"}, "<html><body>Normal HTML with enough text and several links</body></html>", "https://vbu.ac.in/#/notice/123", True),
        ({"js_render": "never"}, "<html><body>ng-app</body></html>", "https://vbu.ac.in/#/notice/123", False),
        ({"js_render": "always"}, "<html><body>Static</body></html>", "https://vbu.ac.in/", True),
    ]
    for site, html_text, page_url, expected in js_decision_cases:
        got = _should_render_js(site, html_text, page_url)
        if got == expected:
            print(f"[TEST-PASS ] JS render decision: mode={site['js_render']}, url={page_url}", file=sys.stderr)
        else:
            print(f"[TEST-FAIL ] JS render decision: got={got}, expected={expected}, url={page_url}", file=sys.stderr)
            failures += 1

    title_cases = [
        ("{{ notice.title }}", True), ("undefined", True),
        ("[ngClass] notice", True),
        ("UG Semester Examination Form Fill-up Notice 2026", False),
    ]
    for title, expected in title_cases:
        got = _is_garbage_title(title)
        if got == expected:
            print(f"[TEST-PASS ] SPA title filtering: {title[:50]!r}", file=sys.stderr)
        else:
            print(f"[TEST-FAIL ] SPA title filtering: {title[:50]!r}: got={got}, expected={expected}", file=sys.stderr)
            failures += 1
    route_cases = [
        ("https://vbu.ac.in/#/notices", False),
        ("https://vbu.ac.in/#!/home", False),
        ("https://vbu.ac.in/archive/", True),
    ]
    for url, expected in route_cases:
        got = _is_navigation_url(url)
        if got == expected:
            print(f"[TEST-PASS ] SPA navigation filter: {url}", file=sys.stderr)
        else:
            print(f"[TEST-FAIL ] SPA navigation filter: {url}: got={got}, expected={expected}", file=sys.stderr)
            failures += 1
    total = len(cases) + len(identity_cases) + 1 + len(template_cases) + len(js_decision_cases) + len(title_cases) + len(route_cases)
    print(f"[TEST] SPA: {total - failures}/{total} passed, {failures} failed.", file=sys.stderr)
    return failures


def _run_config_self_tests():
    failures = 0
    try:
        cfg = get_config()
        sites = {site.get("id"): site for site in cfg.get("websites", [])}
        if len(sites) >= 1:
            print(f"[TEST-PASS ] Config loaded {len(sites)} enabled sites", file=sys.stderr)
        else:
            print("[TEST-FAIL ] Config has no enabled sites", file=sys.stderr)
            failures += 1

        scan = cfg.get("scan", {})
        scan_checks = [
            ("request_timeout_seconds", 45),
            ("domain_delay_seconds", 0.5),
        ]
        for key, expected in scan_checks:
            got = scan.get(key)
            if got == expected:
                print(f"[TEST-PASS ] Scan config {key}", file=sys.stderr)
            else:
                print(f"[TEST-FAIL ] Scan config {key}: got={got!r}, expected={expected!r}", file=sys.stderr)
                failures += 1

        broad_discovery = {"pdf", "download"}.intersection(set(scan.get("discovery_keywords", [])))
        if not broad_discovery:
            print("[TEST-PASS ] Broad discovery keywords excluded", file=sys.stderr)
        else:
            print(f"[TEST-FAIL ] Broad discovery keywords still present: {sorted(broad_discovery)}", file=sys.stderr)
            failures += 1

        if "iimranchi" not in sites and "iiimranchi" in sites:
            print("[TEST-PASS ] Legacy IIM site ID preserved for state compatibility", file=sys.stderr)
        elif "iimranchi" in sites:
            print("[TEST-PASS ] IIM site ID uses canonical spelling", file=sys.stderr)
        else:
            print("[TEST-FAIL ] IIM Ranchi site ID missing", file=sys.stderr)
            failures += 1

        expected_urls = {
            "kolhan-university": "https://www.kolhanuniversity.ac.in/",
            "bau-ranchi": "https://bauranchi.org/",
        }
        for site_id, expected_url in expected_urls.items():
            got_url = sites.get(site_id, {}).get("url")
            if got_url == expected_url:
                print(f"[TEST-PASS ] Official base URL {site_id}", file=sys.stderr)
            else:
                print(f"[TEST-FAIL ] Base URL {site_id}: got={got_url!r}, expected={expected_url!r}", file=sys.stderr)
                failures += 1

        advanced_checks = [
            ("rims-ranchi", "baseline_max_errors", 10),
            ("aisect-university", "js_render", "always"),
            ("aisect-university", "js_wait_after_ms", 10000),
            ("aisect-university", "js_selector_timeout_ms", 45000),
            ("aisect-university", "request_timeout_seconds", 120),
        ]
        for site_id, key, expected in advanced_checks:
            site = sites.get(site_id)
            got = site.get(key) if site else None
            if got == expected:
                print(f"[TEST-PASS ] Advanced config {site_id}.{key}", file=sys.stderr)
            else:
                print(f"[TEST-FAIL ] Advanced config {site_id}.{key}: got={got!r}, expected={expected!r}", file=sys.stderr)
                failures += 1

        if "annual report" in scan.get("exclude_title_signals", []):
            print("[TEST-PASS ] Configurable low-relevance title exclusion loaded", file=sys.stderr)
        else:
            print("[TEST-FAIL ] Configurable title exclusion missing", file=sys.stderr)
            failures += 1

        if scan.get("max_state_bytes") == 8000000:
            print("[TEST-PASS ] State size cap supports configured 8 MB", file=sys.stderr)
        else:
            print(f"[TEST-FAIL ] State size cap mismatch: {scan.get('max_state_bytes')!r}", file=sys.stderr)
            failures += 1

        checks = [
            ("vbu-hazaribagh", "js_render", "always"),
            ("vbu-hazaribagh", "js_wait_after_ms", 4500),
            ("vbu-hazaribagh", "js_scroll_bottom", True),
            ("vbu-hazaribagh", "js_wait_for_selector", "table, .notice, .notice-list, .news-list, ng-view, .ng-scope, mat-table, .mat-table"),
            ("bbmku-dhanbad", "js_wait_after_ms", 3500),
        ]
        for site_id, key, expected in checks:
            site = sites.get(site_id)
            got = site.get(key) if site else None
            if got == expected:
                print(f"[TEST-PASS ] Per-site config {site_id}.{key}", file=sys.stderr)
            else:
                print(f"[TEST-FAIL ] Per-site config {site_id}.{key}: got={got!r}, expected={expected!r}", file=sys.stderr)
                failures += 1
    except Exception as exc:
        print(f"[TEST-FAIL ] Config self-test raised {type(exc).__name__}: {exc}", file=sys.stderr)
        failures += 1
    total_checks = 19
    print(f"[TEST] Config: {total_checks - failures}/{total_checks} passed, {failures} failed.", file=sys.stderr)
    return failures


def _run_dedup_self_tests():
    failures = 0
    total = 0
    cases = [
        ([('old', 'Recruitment Notice 01/2026 For Clerk Post', 'https://x.nic.in/writereaddata/notice01.pdf')],
         'Recruitment Notice 02/2026 For Clerk Post', 'https://x.nic.in/writereaddata/notice02.pdf', None,
         'sequential numbered notices remain distinct'),
        ([('old', 'Recruitment Notice 01/2026 For Clerk Post', 'https://x.nic.in/writereaddata/notice01.pdf')],
         'Recruitment Notice 01/2026 For Clerk Post', 'https://x.nic.in/archive/notice01-copy.pdf', 'old',
         'obvious same-basename copy alias remains deduplicable'),
        ([('old', 'Events Session: 2026-2027 Meta-Analysis for Randomised Control Trials', 'https://x.ac.in/events/meta-analysis-1')],
         'Events Session: 2026-2027 Meta-Analysis for Randomised Control Trials', 'https://x.ac.in/events/meta-analysis-13', None,
         'different event URLs with identical titles remain distinct'),
    ]
    for site_items, title, url, expected, label in cases:
        total += 1
        got = find_fuzzy_match(site_items, title, url)
        if got == expected:
            print(f"[TEST-PASS ] {label}", file=sys.stderr)
        else:
            print(f"[TEST-FAIL ] {label}: got={got!r}, expected={expected!r}", file=sys.stderr)
            failures += 1
    total += 1
    same_url_id_a = item_id("site-a", "https://x.ac.in/notice?id=1", "Old title", "Old dynamic counter")
    same_url_id_b = item_id("site-a", "https://x.ac.in/notice?id=1", "Updated title", "New dynamic counter")
    if same_url_id_a == same_url_id_b:
        print("[TEST-PASS ] Same canonical URL keeps stable identity when metadata changes", file=sys.stderr)
    else:
        print("[TEST-FAIL ] Item identity changed with mutable title/context", file=sys.stderr)
        failures += 1
    state = {"items": {
        "sent1": {"site_id": "district-a", "status": "sent", "title": "Notice A", "pdf_hash": "visual-v1:abc", "pdf_hash_kind": "visual-v1"},
        "ready1": {"site_id": "district-a", "status": "ready", "title": "Notice B", "pdf_hash": "visual-v1:ready", "pdf_hash_kind": "visual-v1"},
        "sent_other_site": {"site_id": "district-b", "status": "sent", "title": "Notice C", "pdf_hash": "visual-v1:abc", "pdf_hash_kind": "visual-v1"},
    }}
    hash_cases = [
        ({"site_id": "district-a", "pdf_hash": "visual-v1:abc", "pdf_hash_kind": "visual-v1"}, "Notice A", "same-site sent PDF fingerprint detected"),
        ({"site_id": "district-a", "pdf_hash": "visual-v1:ready", "pdf_hash_kind": "visual-v1"}, None, "ready-only fingerprint does not block sending"),
        ({"site_id": "district-c", "pdf_hash": "visual-v1:abc", "pdf_hash_kind": "visual-v1"}, None, "cross-district fingerprint does not block sending"),
        ({"site_id": "district-a", "pdf_hash": "visual-v1:different", "pdf_hash_kind": "visual-v1"}, None, "different fingerprint remains eligible"),
    ]
    for record, expected, label in hash_cases:
        total += 1
        got = _is_duplicate_by_pdf_hash(state, record, exclude_iid="new")
        if got == expected:
            print(f"[TEST-PASS ] {label}", file=sys.stderr)
        else:
            print(f"[TEST-FAIL ] {label}: got={got!r}, expected={expected!r}", file=sys.stderr)
            failures += 1
    print(f"[TEST] Dedup: {total - failures}/{total} passed, {failures} failed.", file=sys.stderr)
    return failures


def _run_quality_guard_self_tests():
    failures = 0
    cases = [
        ("Read More chevron_right", True),
        ("View All chevron_right", True),
        ("chevron_right", True),
        ("Read More About Recruitment Rules 2026", False),
        ("ADVERTISEMENT FOR NON", False),
        ("Department Name", True),
        ("Registration Number", True),
        ("National Institute of Technology Jamshedpur Main Administrative Building PIN 831014", True),
    ]
    for title, expected in cases:
        got = _is_generic_title(title)
        if got == expected:
            print(f"[TEST-PASS ] Generic-title filter: {title!r}", file=sys.stderr)
        else:
            print(f"[TEST-FAIL ] Generic-title filter {title!r}: got={got}, expected={expected}", file=sys.stderr)
            failures += 1

    old_session_start = (datetime.now(timezone.utc).year if datetime.now(timezone.utc).month >= 7
                         else datetime.now(timezone.utc).year - 1) - 1
    old_session = f"{old_session_start}-{str((old_session_start + 1) % 100).zfill(2)}"
    if _is_stale_notice(f"Provisional list for Ph.D. Admission {old_session}", "", "https://x.ac.in/admission"):
        print("[TEST-PASS ] Old academic admission session suppressed", file=sys.stderr)
    else:
        print("[TEST-FAIL ] Old academic admission session was not suppressed", file=sys.stderr)
        failures += 1

    old_result_cases = [
        "PG SEM-3 EXAM-2023 (2022-24) COMMERCE RESULT",
        "RESULT OF PG SEM 3 (2022-2022) SESSION M.A. AND M.Sc.",
    ]
    for old_result_title in old_result_cases:
        record = {"title": old_result_title, "context": "", "url": "https://x.ac.in/result.pdf"}
        if _is_stale_notice(old_result_title, "", record["url"]) and _keyword_pre_classify(record) is False:
            print(f"[TEST-PASS ] Old result suppressed: {old_result_title[:55]}", file=sys.stderr)
        else:
            print(f"[TEST-FAIL ] Old result not suppressed: {old_result_title[:55]}", file=sys.stderr)
            failures += 1

    if not _meaningful_metadata_change(
        "CLAT 2026 Admission Closure Notice", "CLAT 2026 Admission Closure Notice",
        "CLAT 2026 Admission Closure Notice", "CLAT 2026 Admission Closure Notice Read More chevron_right"
    ):
        print("[TEST-PASS ] Same-title context/UI changes do not reprocess", file=sys.stderr)
    else:
        print("[TEST-FAIL ] Same-title context/UI changes triggered reprocess", file=sys.stderr)
        failures += 1

    if _meaningful_metadata_change(
        "Admission Notice 2026", "Admission Notice 2026",
        "Last date: 10 October 2026", "Last date: 20 October 2026"
    ):
        print("[TEST-PASS ] Same-title deadline change remains meaningful", file=sys.stderr)
    else:
        print("[TEST-FAIL ] Same-title deadline change was ignored", file=sys.stderr)
        failures += 1

    noise_cases = [
        ({"title": "Tender Notice for Supply of Furniture 2026", "url": "https://x.ac.in/tender.pdf"}, True, "tender notice remains eligible"),
        ({"title": "Annual Report 2026", "url": "https://x.ac.in/report.pdf"}, False, "annual report noise suppressed"),
        ({"title": "Faculty Recruitment Notice 2026", "url": "https://x.ac.in/jobs.pdf"}, True, "faculty recruitment remains eligible"),
    ]
    for record, expected, label in noise_cases:
        got = _keyword_pre_classify(record)
        if got is expected:
            print(f"[TEST-PASS ] {label}", file=sys.stderr)
        else:
            print(f"[TEST-FAIL ] {label}: got={got!r}, expected={expected!r}", file=sys.stderr)
            failures += 1

    if baseline_can_complete(True, [f"partial error {i}" for i in range(8)], 10):
        print("[TEST-PASS ] Per-site baseline error budget permits bounded partial failures", file=sys.stderr)
    else:
        print("[TEST-FAIL ] Per-site baseline error budget rejected 8/10 errors", file=sys.stderr)
        failures += 1
    if not baseline_can_complete(True, [f"partial error {i}" for i in range(11)], 10):
        print("[TEST-PASS ] Per-site baseline budget still rejects excessive errors", file=sys.stderr)
    else:
        print("[TEST-FAIL ] Per-site baseline budget accepted excessive errors", file=sys.stderr)
        failures += 1

    if baseline_can_complete(True, ["one broken detail link", "one pagination timeout"]):
        print("[TEST-PASS ] Baseline can complete with a few partial errors", file=sys.stderr)
    else:
        print("[TEST-FAIL ] Baseline blocked by a few partial errors", file=sys.stderr)
        failures += 1
    if not baseline_can_complete(False, []):
        print("[TEST-PASS ] Failed scan cannot complete baseline", file=sys.stderr)
    else:
        print("[TEST-FAIL ] Failed scan incorrectly completed baseline", file=sys.stderr)
        failures += 1

    print(f"[TEST] Quality-guards: {20 - failures}/20 cases, {failures} failed.", file=sys.stderr)
    return failures


def _run_title_cleanup_self_tests():
    failures = 0
    total = 0

    total += 1
    name = _filename_to_title("https://giridih.nic.in/writereaddata/Apprenticeship_Mela_12102026.pdf")
    if "Apprenticeship" in name and "Mela" in name:
        print(f"[TEST-PASS ] filename_to_title → {name!r}", file=sys.stderr)
    else:
        print(f"[TEST-FAIL ] filename_to_title: got {name!r}", file=sys.stderr)
        failures += 1

    total += 1
    garbage = ("Home Whats New Facebook X Whats New 08.10.2026: "
               "Important Apprenticeship Notice From Employment Exchange, Giridih. "
               "Published on: 08/10/2026 Prime Minister National Apprenticeship Mela – 12-10-2026 Sha")
    cleaned = _strip_nav_prefix(garbage)
    if ("Apprenticeship" in cleaned and not cleaned.lower().startswith("home")
            and "Published on" not in cleaned):
        print(f"[TEST-PASS ] strip_nav_prefix → {cleaned[:80]!r}", file=sys.stderr)
    else:
        print(f"[TEST-FAIL ] strip_nav_prefix: got {cleaned!r}", file=sys.stderr)
        failures += 1

    total += 1
    if _looks_like_menu_dump("Home Whats New Facebook X Whats New 08.10.2026"):
        print("[TEST-PASS ] looks_like_menu_dump detected nav run", file=sys.stderr)
    else:
        print("[TEST-FAIL ] looks_like_menu_dump missed nav run", file=sys.stderr)
        failures += 1

    total += 1
    if not _looks_like_menu_dump("Important Recruitment Notice From Employment Exchange, Giridih"):
        print("[TEST-PASS ] clean title not flagged as menu-dump", file=sys.stderr)
    else:
        print("[TEST-FAIL ] clean title wrongly flagged as menu-dump", file=sys.stderr)
        failures += 1

    total += 1
    item = {
        "explicit_title": "10.09.2026: Important Recruitment Notice From Employment Exchange, Giridih.",
        "title": "Home Whats New Facebook X Whats New garbage",
        "context": "site-wide nav",
        "url": "https://giridih.nic.in/writereaddata/x.pdf",
    }
    resolved = _resolve_title(item)
    if resolved.startswith("10.09.2026"):
        print(f"[TEST-PASS ] resolve_title → {resolved[:60]!r}", file=sys.stderr)
    else:
        print(f"[TEST-FAIL ] resolve_title: got {resolved!r}", file=sys.stderr)
        failures += 1

    total += 1
    item = {
        "title": garbage, "context": "",
        "url": "https://giridih.nic.in/writereaddata/Apprenticeship_Mela_12102026.pdf",
    }
    resolved = _resolve_title(item)
    if "Apprenticeship" in resolved and "Home" not in resolved[:10]:
        print(f"[TEST-PASS ] resolve_title cleanup → {resolved[:60]!r}", file=sys.stderr)
    else:
        print(f"[TEST-FAIL ] resolve_title cleanup: got {resolved!r}", file=sys.stderr)
        failures += 1

    total += 1
    html_snippet = """
    <html><body><table>
      <tr><th>Title:</th><td>10.09.2026: Important Recruitment Notice From Employment Exchange, Giridih.</td></tr>
      <tr><th>Description:</th><td>Important Recruitment Notice From Employment Exchange, Giridih.</td></tr>
    </table></body></html>
    """
    soup = BeautifulSoup(html_snippet, "html.parser")
    extracted = _extract_explicit_title(soup)
    if extracted.startswith("10.09.2026") and "Recruitment Notice" in extracted:
        print(f"[TEST-PASS ] extract_explicit_title → {extracted[:60]!r}", file=sys.stderr)
    else:
        print(f"[TEST-FAIL ] extract_explicit_title: got {extracted!r}", file=sys.stderr)
        failures += 1

    total += 1
    if (_is_notice_document_url("https://x.nic.in/writereaddata/a.pdf")
            and _is_notice_document_url("https://x.nic.in/downloadfile?id=5")
            and not _is_notice_document_url("https://x.nic.in/about-us/")):
        print("[TEST-PASS ] is_notice_document_url classifies correctly", file=sys.stderr)
    else:
        print("[TEST-FAIL ] is_notice_document_url misclassified a URL", file=sys.stderr)
        failures += 1

    print(f"[TEST] Title-cleanup: {total - failures}/{total} passed, {failures} failed.", file=sys.stderr)
    return failures


def _should_fetch_pdf(record):
    """
    Only attempt PDF download when the URL looks like an actual file.
    
    Case A: URL explicitly ends in .pdf, or has /downloadfile, /getfile, etc.
            → always fetch (discovery marked is_pdf=True)
    
    Case B: Extensionless URL using KNOWN file-serving endpoints
            (e.g. /writereaddata/xyz, /storage/notices/12345).
            These usually serve raw files. Downloader verifies content-type;
            if it happens to return HTML, we return "html_no_pdf_found" safely.
    
    Case C: Plain HTML pages like /about/, /library/, /notice/xyz
            → skip to prevent HTML-embedded-PDF false positives
            (this fixed the fake [STALE-PDF] bug on faculty profiles).
    """
    if record.get("pdf_extracted") or record.get("pdf_text"):
        return False
    if int(record.get("pdf_attempts", 0)) >= MAX_PDF_ATTEMPTS:
        return False
    url = record.get("url", "")
    url_lower = url.lower()

    if any(pat in url_lower for pat in (
        "/past-notices", "/past_notices", "/whats-new", "/whats_new",
        "/notice_category", "/notice-category", "/document-category",
        "/document_category", "/archive", "/search",
        "/contact-us", "/contact_us", "/contactus",
        "/about-district", "/about_district",
        "/photo-gallery", "/photo_gallery", "/video-gallery", "/video_gallery",
        "/anti-ragging", "/grievance", "/rti",
    )):
        return False
    try:
        parsed = urlparse(url)
        if parsed.path in ("", "/"):
            return False
    except Exception:
        pass

    if record.get("is_pdf", False):
        return True

    if any(hint in url_lower for hint in (
        "/downloadfile", "/download_file", "/downloadpdf", "/download_pdf",
        "/getfile", "/showfile", "/viewfile", "/filedownload",
        "/writereaddata/", "/uploadfile/", "/storage/notices/",
        "/storage/notice/", "/documents/notice", "/notice-documents/",
    )):
        return True

    return False


def _fetch_pdfs_for_batch(batch, scan):
    targets = [(iid, record) for iid, record in batch if _should_fetch_pdf(record)]
    if not targets:
        return
    default_timeout = scan["request_timeout_seconds"]

    def _fetch_one(record):
        try:
            timeout = _SITE_TIMEOUT_BY_ID.get(record.get("site_id"), default_timeout)
            return download_pdf_content(
                record["url"], timeout,
                verify_ssl=_SITE_VERIFY_SSL_BY_ID.get(record.get("site_id"), True),
            )
        except Exception as exc:
            print(f"[WARN] PDF fetch error: {exc}", file=sys.stderr)
            return None, "", False, "error", ""

    workers = max(1, min(OCR_MAX_WORKERS, len(targets)))
    with ThreadPoolExecutor(max_workers=workers) as ex:
        futures = {ex.submit(_fetch_one, record): (iid, record) for iid, record in targets}
        for fut in as_completed(futures):
            iid, record = futures[fut]
            try:
                result_tuple = fut.result()
                content, text, ocr_used, method = result_tuple[:4]
                raw_pdf_text = result_tuple[4] if len(result_tuple) > 4 else ""
            except Exception:
                content, text, ocr_used, method, raw_pdf_text = None, "", False, "error", ""

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

                try:
                    _bt, pdf_summary = _extract_pdf_title_and_summary(
                        raw_pdf_text or text, record.get("title", ""),
                    )
                    if pdf_summary and not record.get("pdf_summary_hint"):
                        record["pdf_summary_hint"] = pdf_summary
                except Exception as exc:
                    print(f"[WARN] PDF summary extraction failed: {exc}", file=sys.stderr)

                effective_title = record.get("explicit_title") or record.get("title", "")
                if _is_stale_notice(
                    effective_title, record.get("context", ""), record.get("url", ""),
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
        effective_title = record.get("explicit_title") or record.get("title", "")
        if _is_stale_notice(
            effective_title, record.get("context", ""), record.get("url", ""),
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
    global _JS_RENDER_COUNT

    _RUNTIME_PDF_CACHE = {}
    with _JS_RENDER_COUNT_LOCK:
        _JS_RENDER_COUNT = 0
    _DEAD_MODELS.clear()
    _GEMINI_QUOTA_EXHAUSTED = False
    _GEMINI_KEYS_POOL = _load_gemini_keys()
    _GEMINI_KEY_INDEX = 0
    _GEMINI_DEAD_KEYS = set()
    _MODELS_DISCOVERED = False
    _DYNAMIC_MODELS = []

    import time as _time
    _START_TIME = _time.monotonic()
    _MAX_RUN_SECONDS = 50 * 60

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

    print(f"[INFO] Playwright available: {_PLAYWRIGHT_AVAILABLE}, JS_RENDER_ENABLED: {JS_RENDER_ENABLED}", file=sys.stderr)

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
                    for err in errors[:5]:
                        print(f"    ↳ {clean_text(str(err), 400)}", file=sys.stderr)
                    if len(errors) > 5:
                        print(f"    ↳ ... and {len(errors) - 5} more error(s)", file=sys.stderr)
            except Exception as exc:
                run_errors += 1
                state["metrics"]["site_scan_failure"][site["id"]] = state["metrics"]["site_scan_failure"].get(site["id"], 0) + 1
                results[site["id"]] = {"candidates": [], "errors": [str(exc)], "success": False}
                mark_site_failure(state, site["id"], str(exc))
                print(f"[ERROR] {site['name']}: {exc}", file=sys.stderr)

    with _JS_RENDER_COUNT_LOCK:
        state.setdefault("metrics", {})["js_renders"] = _JS_RENDER_COUNT

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

        baseline_scan_complete = baseline_can_complete(
            current_scan_success, result.get("errors", []),
            site.get("baseline_max_errors", scan.get("baseline_max_errors", 3)),
        )
        if not ss["baseline_complete"] and baseline_scan_complete:
            for candidate in candidates:
                iid = item_id(sid, candidate["url"], candidate["title"], candidate.get("context", ""))
                state["items"].setdefault(iid, {
                    "site_id": sid, "site_name": site["name"],
                    "url": candidate["url"], "title": candidate["title"],
                    "explicit_title": candidate.get("explicit_title", ""),
                    "context": candidate.get("context", "")[:700],
                    "is_pdf": bool(candidate.get("is_pdf")),
                    "first_seen": utc_now(), "last_seen": utc_now(),
                    "status": "baseline", "attempts": 0, "summary": "",
                    "classification": None, "pdf_extracted": False,
                    "pdf_text": "", "pdf_attempts": 0, "ocr_used": False,
                    "pdf_method": "", "telegram_attempts": 0, "pdf_sent": False,
                    "upload_date": candidate.get("upload_date"),
                    "last_error": None,
                    "etag": None, "last_modified": None, "pdf_hash": None,
                    "pdf_hash_kind": None, "last_content_check_at": None,
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
            effective_cand_title = candidate.get("explicit_title") or candidate.get("title", "")

            if _is_stale_notice(
                effective_cand_title, candidate.get("context", ""),
                candidate.get("url", ""), upload_date=upload_dt,
            ):
                reason = _classify_stale_reason(
                    effective_cand_title, candidate.get("context", ""),
                    candidate.get("url", ""), upload_date=upload_dt,
                ) or "STALE"
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
                        stale_record["last_error"] = f"Stale notice ({reason})"
                else:
                    state["items"][iid] = {
                        "site_id": sid, "site_name": site["name"],
                        "url": candidate["url"], "title": candidate.get("title", ""),
                        "explicit_title": candidate.get("explicit_title", ""),
                        "context": candidate.get("context", "")[:700],
                        "is_pdf": bool(candidate.get("is_pdf")),
                        "first_seen": utc_now(), "last_seen": utc_now(),
                        "status": "baseline", "attempts": 0, "summary": "",
                        "classification": None, "pdf_extracted": False,
                        "pdf_text": "", "pdf_attempts": 0, "ocr_used": False,
                        "pdf_method": "", "telegram_attempts": 0, "pdf_sent": False,
                        "upload_date": candidate.get("upload_date"),
                        "last_error": f"Stale notice ({reason})",
                        "etag": None, "last_modified": None, "pdf_hash": None,
                        "pdf_hash_kind": None, "last_content_check_at": None,
                    }
                    site_items_list.append((iid, candidate.get("title", ""), candidate.get("url", "")))
                print(f"[{reason}] {effective_cand_title[:80]}", file=sys.stderr)
                continue

            is_pdf_or_notice = bool(
                candidate.get("is_pdf") or is_pdf(candidate["url"])
                or _looks_like_pdf_url(candidate["url"])
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
                    metadata_changed = _meaningful_metadata_change(old_title, new_title, old_context, new_context)
                    record["last_seen"] = utc_now()
                    current_status = record.get("status")
                    if metadata_changed and current_status in {"ignored", "baseline"}:
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
                        record.pop("pdf_summary_hint", None)
                        print(f"[RE-PROCESS] Ignored/baseline notice meaningfully changed: {candidate['url'][:100]}")
                    elif metadata_changed and current_status == "sent":
                        print(f"[SKIP-RE-PROCESS] Already sent; metadata-only change ignored: {candidate['url'][:100]}")
                    if new_title:
                        record["title"] = new_title
                    if candidate.get("explicit_title"):
                        record["explicit_title"] = candidate["explicit_title"]
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
                    effective_cand_title, candidate.get("context", ""),
                    candidate["url"], upload_date=upload_dt,
                ):
                    reason = _classify_stale_reason(
                        effective_cand_title, candidate.get("context", ""),
                        candidate["url"], upload_date=upload_dt,
                    ) or "STALE"
                    state["items"][iid] = {
                        "site_id": sid, "site_name": site["name"],
                        "url": candidate["url"], "title": candidate["title"],
                        "explicit_title": candidate.get("explicit_title", ""),
                        "context": candidate.get("context", "")[:700],
                        "is_pdf": is_pdf_or_notice,
                        "first_seen": utc_now(), "last_seen": utc_now(),
                        "status": "baseline", "attempts": 0, "summary": "",
                        "classification": None, "pdf_extracted": False,
                        "pdf_text": "", "pdf_attempts": 0, "ocr_used": False,
                        "pdf_method": "", "telegram_attempts": 0, "pdf_sent": False,
                        "upload_date": candidate.get("upload_date"),
                        "last_error": f"Stale ({reason})",
                        "etag": None, "last_modified": None, "pdf_hash": None,
                        "pdf_hash_kind": None, "last_content_check_at": None,
                    }
                    site_items_list.append((iid, candidate["title"], candidate["url"]))
                    continue

                record = {
                    "site_id": sid, "site_name": site["name"],
                    "url": candidate["url"], "title": candidate["title"],
                    "explicit_title": candidate.get("explicit_title", ""),
                    "context": candidate.get("context", "")[:700],
                    "is_pdf": is_pdf_or_notice,
                    "first_seen": utc_now(), "last_seen": utc_now(),
                    "status": "pending", "attempts": 0, "summary": "",
                    "classification": None, "pdf_extracted": False,
                    "pdf_text": "", "pdf_attempts": 0, "ocr_used": False,
                    "pdf_method": "", "telegram_attempts": 0, "pdf_sent": False,
                    "upload_date": candidate.get("upload_date"),
                    "last_error": None,
                    "etag": None, "last_modified": None, "pdf_hash": None,
                    "pdf_hash_kind": None, "last_content_check_at": None,
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
                                session, candidate["url"], record,
                                verify_ssl=_SITE_VERIFY_SSL_BY_ID.get(record.get("site_id"), True),
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
                                record.pop("pdf_summary_hint", None)
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
                        record.pop("pdf_summary_hint", None)
                        print(f"[RE-PROCESS] Substantive baseline metadata change: {new_title[:80]}")

                if candidate["title"]:
                    record["title"] = candidate["title"]
                if candidate.get("explicit_title"):
                    record["explicit_title"] = candidate["explicit_title"]
                if candidate.get("context"):
                    record["context"] = candidate["context"][:700]
                if candidate.get("upload_date"):
                    record["upload_date"] = candidate["upload_date"]
                record["is_pdf"] = bool(candidate.get("is_pdf", record.get("is_pdf", False))) or is_pdf_or_notice

            if (ss["baseline_complete"] and record.get("status") == "pending"
                    and int(record.get("attempts", 0)) < scan["max_pending_attempts"]):
                pending.append((iid, record))

    suppress_stale_pending_and_ready(state)
    pending = [(iid, record) for iid, record in pending if record.get("status") == "pending"]

    pending = enqueue_persisted_pending(
        state, pending, scan["max_pending_attempts"],
        {site["id"] for site in cfg["websites"]},
    )

    state["initialized"] = all(
        site_state(state, site["id"])["baseline_complete"] for site in cfg["websites"]
    )

    pending = list({iid: record for iid, record in pending}.items())
    pending.sort(key=lambda pair: pending_priority(pair[1], scan["keywords"]), reverse=True)
    max_items_this_run = min(scan["gemini_batch_size"] * scan["gemini_max_calls_per_run"], 45)
    pending = pending[:max_items_this_run]

    batch_size = scan["gemini_batch_size"]
    for start in range(0, len(pending), batch_size):
        if _time_exceeded():
            print("[TIME_LIMIT] Processing budget reached — remaining items pending for next run", file=sys.stderr)
            break

        batch = pending[start : start + batch_size]
        active_batch = []
        for iid, record in batch:
            effective_title = record.get("explicit_title") or record.get("title", "")
            if _is_stale_notice(
                effective_title, record.get("context", ""), record.get("url", ""),
                upload_date=_parse_upload_date(record.get("upload_date")),
                pdf_text=record.get("pdf_text", ""),
            ):
                record["status"] = "baseline"
                record["classification"] = None
                record["summary"] = ""
                record["last_error"] = "Stale notice suppressed before PDF/Gemini processing"
                print(f"[STALE-SKIP] Before PDF/Gemini: {effective_title[:80]}", file=sys.stderr)
                continue
            title_for_gate = record.get("explicit_title") or record.get("title", "")
            if _is_generic_title(title_for_gate):
                record["status"] = "ignored"
                record["classification"] = {"important": False, "category": "other", "pre_classified": True}
                record["last_error"] = "Generic UI/table title suppressed before PDF/Gemini processing"
                record["preclassified_at"] = utc_now()
                print(f"[PRE-IGNORED] Generic title before PDF fetch: {title_for_gate[:80]}", file=sys.stderr)
                continue
            excluded_signal = _matched_excluded_title_signal(
                title_for_gate, scan.get("exclude_title_signals", _DEFAULT_EXCLUDED_TITLE_SIGNALS)
            )
            if excluded_signal:
                record["status"] = "ignored"
                record["classification"] = {"important": False, "category": "other", "pre_classified": True}
                record["last_error"] = f"Excluded low-relevance title signal: {excluded_signal}"
                record["preclassified_at"] = utc_now()
                print(f"[PRE-IGNORED] Excluded title signal {excluded_signal!r}: {title_for_gate[:80]}", file=sys.stderr)
                continue
            active_batch.append((iid, record))
        batch = active_batch
        if not batch:
            continue
        try:
            _fetch_pdfs_for_batch(batch, scan)
        except Exception as exc:
            print(f"[WARN] PDF batch fetch failed: {exc}", file=sys.stderr)
        try:
            gemini_batch = []
            for iid, record in batch:
                if record.get("status") == "baseline" and str(record.get("last_error", "")).startswith("PDF content stale"):
                    continue
                pre = _keyword_pre_classify(record, scan.get("exclude_title_signals", _DEFAULT_EXCLUDED_TITLE_SIGNALS))
                if pre is True:
                    record["classification"] = {
                        "important": True, "category": "notice", "summary": "",
                        "title_hi": None, "pre_classified": True,
                    }
                    record["summary"] = ""
                    record["last_error"] = None
                    record["status"] = "ready"
                    record["preclassified_at"] = utc_now()
                    print(f"[PRE-CLASSIFIED] {record.get('title', '')[:70]}")
                elif pre is False:
                    if _is_stale_notice(
                        record.get("explicit_title") or record.get("title", ""),
                        record.get("context", ""), record.get("url", ""),
                        upload_date=_parse_upload_date(record.get("upload_date")),
                        pdf_text=record.get("pdf_text", ""),
                    ):
                        record["classification"] = None
                        record["summary"] = ""
                        record["status"] = "baseline"
                        record["last_error"] = "Stale notice suppressed before classification"
                        print(f"[STALE-SKIP] {record.get('title', '')[:70]}", file=sys.stderr)
                    else:
                        record["classification"] = {"important": False, "category": "other", "pre_classified": True}
                        record["last_error"] = None
                        record["status"] = "ignored"
                        record["preclassified_at"] = utc_now()
                        print(f"[PRE-IGNORED] Generic/noise title: {record.get('title', '')[:70]}")
                else:
                    gemini_batch.append((iid, record))
            result = {}
            if gemini_batch:
                result = gemini_classify_with_fallback(
                    [record for _, record in gemini_batch], gemini_key, scan["request_timeout_seconds"],
                )
            for index, (_, record) in enumerate(gemini_batch):
                record["attempts"] = int(record.get("attempts", 0)) + 1
                classification = result.get(str(index))
                if classification is None:
                    record["status"] = "pending"
                    record["last_error"] = "Gemini returned no classification"
                    add_review_item(state, record, "classification_missing")
                    continue
                if classification.get("ambiguous") is True or classification.get("needs_review") is True:
                    add_review_item(state, record, "Gemini marked notice ambiguous", classification)
                strong_signals = (
                    "admission", "result", "admit card", "answer key", "examination",
                    "revaluation", "migration", "scholarship", "fee", "syllabus",
                    "timetable", "counselling", "recruitment", "vacancy", "tender",
                    "notice", "notification", "placement", "convocation", "registration",
                    "प्रवेश", "परिणाम", "प्रवेश पत्र", "उत्तर कुंजी", "परीक्षा",
                    "पुनर्मूल्यांकन", "छात्रवृत्ति", "शुल्क", "भर्ती", "निविदा", "सूचना",
                )
                combined_title = " ".join((
                    record.get("explicit_title") or "",
                    record.get("title") or "",
                )).casefold()
                if (not classification.get("important")
                        and record.get("explicit_title")
                        and any(signal in combined_title for signal in strong_signals)):
                    print(
                        f"[OVERRIDE] Explicit website title has a high-specificity notice signal: "
                        f"{(record.get('explicit_title') or '')[:70]}", file=sys.stderr,
                    )
                    classification["important"] = True
                    classification["review_reason"] = "explicit_title_strong_signal_override"
                record["last_error"] = None
                record["classification"] = classification
                record["summary"] = classification.get("summary", "")
                record["status"] = "ready" if classification.get("important") else "ignored"
        except Exception as exc:
            error = clean_text(str(exc), 500)
            for _, record in batch:
                if record.get("status") in {"ready", "ignored"} and (record.get("classification") or {}).get("pre_classified"):
                    continue
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
    ready.sort(key=lambda pair: pair[1].get("first_seen", ""))

    sent_count = 0
    for iid, record in ready[: scan["max_new_items_per_run"]]:
        if _time_exceeded():
            print("[TIME_LIMIT] Processing budget reached — unsent notices remain ready for next run", file=sys.stderr)
            break

        site = next((s for s in cfg["websites"] if s["id"] == record.get("site_id")), None)
        if site is None:
            record["status"] = "permanent_error"
            record["last_error"] = "Configured site no longer exists"
            continue

        duplicate_title = _is_duplicate_by_pdf_hash(state, record, exclude_iid=iid)
        if duplicate_title:
            print(f"[DEDUP-HASH] {record.get('title', '')[:60]} matches sent notice: {duplicate_title[:60]}", file=sys.stderr)
            record["status"] = "ignored"
            record["last_error"] = f"Duplicate PDF fingerprint of sent notice: {duplicate_title[:120]}"
            state.setdefault("metrics", {})["duplicate_rejects"] = int(
                state.setdefault("metrics", {}).get("duplicate_rejects", 0)
            ) + 1
            continue

        full_message = format_message(site, record, record.get("classification"))
        full_message = truncate_telegram(full_message)

        is_pdf_flag = record.get("is_pdf", False)
        if SEND_PDF_ENABLED and is_pdf_flag:
            ok, permanent, detail = send_notification_with_pdf(token, chat_id, record, full_message)
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
            print(f"[WARN] Telegram delivery failed; retry at {record.get('telegram_next_attempt_at')}: {detail}", file=sys.stderr)

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
            state, scan["retention_days"], scan["max_state_items"],
            scan["max_pending_attempts"], scan["max_state_bytes"],
            sent_retention_days=scan["sent_retention_days"],
            ignored_retention_days=scan["ignored_retention_days"],
            baseline_retention_days=scan["baseline_retention_days"],
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
        f"js_renders={state.get('metrics', {}).get('js_renders', 0)} "
        f"elapsed={elapsed:.1f}s"
    )
    return 0


def _run_candidate_pdf_flag_self_tests():
    failures = 0
    html_text = """<html><body>
      <a href="/notice/academic-calendar/">Academic Calendar Notice 2026</a>
      <a href="/uploads/exam-schedule-2026.pdf">Exam Schedule 2026 PDF</a>
    </body></html>"""
    rows = extract_candidates(html_text, "https://x.ac.in/", {"keywords": []}, {
        "keywords": ["notice", "exam", "calendar"], "max_items_per_site": 100,
    })
    by_url = {row["url"]: row for row in rows}
    html_row = by_url.get("https://x.ac.in/notice/academic-calendar/")
    pdf_row = by_url.get("https://x.ac.in/uploads/exam-schedule-2026.pdf")
    if html_row and not html_row.get("is_pdf"):
        print("[TEST-PASS ] HTML notice path is not falsely marked PDF", file=sys.stderr)
    else:
        print(f"[TEST-FAIL ] HTML notice PDF flag wrong: {html_row!r}", file=sys.stderr)
        failures += 1
    if pdf_row and pdf_row.get("is_pdf"):
        print("[TEST-PASS ] Real .pdf URL is marked PDF", file=sys.stderr)
    else:
        print(f"[TEST-FAIL ] Real PDF flag wrong: {pdf_row!r}", file=sys.stderr)
        failures += 1
    print(f"[TEST] Candidate PDF flags: {2 - failures}/2 passed, {failures} failed.", file=sys.stderr)
    return failures


def _run_pdf_table_compat_self_tests():
    failures = 0
    original_open = pdfplumber.open

    class _FakePage:
        def __init__(self, tables):
            self._tables = tables
        def extract_text(self):
            return ""
        def extract_tables(self):
            return self._tables

    class _FakePdf:
        def __init__(self, tables):
            self.pages = [_FakePage(tables)]
        def __enter__(self):
            return self
        def __exit__(self, *_args):
            return False

    class _FakeTable:
        def extract(self):
            return [["Fee Type", "Amount"], ["Tuition Fee", "12000"]]

    cases = [
        ("nested-list", [[ ["Fee Type", "Amount"], ["Tuition Fee", "12000"] ]]),
        ("table-object", [_FakeTable()]),
    ]
    try:
        for label, tables in cases:
            pdfplumber.open = lambda _source, _tables=tables: _FakePdf(_tables)
            extracted = _extract_pdf_text_plumber(b"test-pdf")
            ok = "Fee Type | Amount" in extracted and "Tuition Fee | 12000" in extracted
            if ok:
                print(f"[TEST-PASS ] pdfplumber table compatibility: {label}", file=sys.stderr)
            else:
                print(f"[TEST-FAIL ] pdfplumber table compatibility: {label}; output={extracted!r}", file=sys.stderr)
                failures += 1
    finally:
        pdfplumber.open = original_open
    print(f"[TEST] PDF table compatibility: {len(cases) - failures}/{len(cases)} passed, {failures} failed.", file=sys.stderr)
    return failures


def _run_retention_self_tests():
    failures = 0
    now = datetime.now(timezone.utc)
    old_stamp = (now - timedelta(days=20)).isoformat()
    state = {"items": {
        "sent-old": {"status": "sent", "first_seen": old_stamp, "terminal_at": old_stamp, "last_seen": old_stamp},
        "ignored-old": {"status": "ignored", "first_seen": old_stamp, "terminal_at": old_stamp, "last_seen": old_stamp},
        "baseline-old": {"status": "baseline", "first_seen": old_stamp, "terminal_at": old_stamp, "last_seen": old_stamp},
        "sent-recent": {"status": "sent", "first_seen": now.isoformat(), "terminal_at": now.isoformat(), "last_seen": now.isoformat()},
    }, "review_queue": {}}
    prune_state(
        state, retention_days=90, max_items=3000, max_pending_attempts=500, max_bytes=8000000,
        sent_retention_days=30, ignored_retention_days=10, baseline_retention_days=15,
    )
    expected_present = {"sent-old", "sent-recent"}
    expected_absent = {"ignored-old", "baseline-old"}
    if expected_present.issubset(state["items"]) and expected_absent.isdisjoint(state["items"]):
        print("[TEST-PASS ] Configured sent/ignored/baseline retention periods are honored", file=sys.stderr)
    else:
        print(f"[TEST-FAIL ] Retention policy mismatch: keys={sorted(state['items'])}", file=sys.stderr)
        failures += 1
    print(f"[TEST-SUMMARY] retention: {1 - failures} passed, {failures} failed", file=sys.stderr)
    return failures


def audit_state_read_only():
    try:
        state = load_state()
    except Exception as exc:
        print(f"[AUDIT-ERROR] Could not load state: {type(exc).__name__}: {exc}", file=sys.stderr)
        return 2
    items = state.get("items", {})
    if not isinstance(items, dict):
        print("[AUDIT-ERROR] state.items is not an object", file=sys.stderr)
        return 2
    statuses = Counter()
    generic = []
    stale = []
    duplicate_groups = {}
    for iid, record in items.items():
        if not isinstance(record, dict):
            continue
        status = str(record.get("status", "unknown"))
        statuses[status] += 1
        title = clean_text(record.get("explicit_title") or record.get("title", ""), 500)
        site_id = str(record.get("site_id", "unknown"))
        if _is_generic_title(title):
            generic.append((site_id, title, record.get("url", ""), status))
        if status not in {"sent", "ignored", "permanent_error"} and _is_stale_notice(
            title, record.get("context", ""), record.get("url", ""),
            upload_date=_parse_upload_date(record.get("upload_date")),
            pdf_text=record.get("pdf_text", ""),
        ):
            stale.append((site_id, title, record.get("url", ""), status))
        normalized = re.sub(r"[^\w\s]", " ", title.casefold())
        normalized = re.sub(r"\s+", " ", normalized).strip()
        if len(normalized) >= 12 and not _is_generic_title(title):
            duplicate_groups.setdefault((site_id, normalized), []).append((iid, title, record.get("url", ""), status))
    duplicate_groups = {key: rows for key, rows in duplicate_groups.items() if len(rows) > 1}
    print("[STATE-AUDIT] Read-only; no records were changed.")
    print(f"[STATE-AUDIT] items={len(items)} status_counts={dict(statuses)}")
    print(f"[STATE-AUDIT] generic_titles={len(generic)} stale_unsent_candidates={len(stale)} duplicate_title_groups={len(duplicate_groups)}")
    for label, rows in (("GENERIC", generic), ("STALE", stale)):
        for site_id, title, url, status in rows[:15]:
            print(f"[{label}] site={site_id} status={status} title={title[:100]!r} url={str(url)[:180]}")
    for (site_id, title), rows in list(duplicate_groups.items())[:15]:
        print(f"[DUPLICATE-TITLE] site={site_id} title={title[:100]!r} count={len(rows)}")
        for _iid, row_title, url, status in rows[:3]:
            print(f"    ↳ status={status} title={row_title[:80]!r} url={str(url)[:160]}")
    return 0


if __name__ == "__main__":
    if "--audit-state" in sys.argv:
        raise SystemExit(audit_state_read_only())
    if "--test" in sys.argv:
        _fails = (_run_stale_notice_self_tests()
                  + _run_quality_guard_self_tests()
                  + _run_title_cleanup_self_tests()
                  + _run_dedup_self_tests()
                  + _run_spa_self_tests()
                  + _run_config_self_tests()
                  + _run_pdf_table_compat_self_tests()
                  + _run_candidate_pdf_flag_self_tests()
                  + _run_retention_self_tests())
        print(f"[TEST-SUMMARY] overall: {'FAIL' if _fails else 'PASS'}; failures={_fails}", file=sys.stderr)
        raise SystemExit(1 if _fails else 0)
    raise SystemExit(main())
