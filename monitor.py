import hashlib
import html
import json
import os
import re
import sys
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime, timezone, timedelta
from pathlib import Path
from typing import Any, Dict, List, Tuple
from urllib.parse import urljoin, urlparse, urlunparse

import requests
from bs4 import BeautifulSoup
from requests.adapters import HTTPAdapter
from urllib3.util.retry import Retry


BASE = Path(__file__).resolve().parent
CONFIG_FILE = BASE / "websites.json"
STATE_FILE = BASE / "state.json"

# Gemini model
DEFAULT_MODEL = "gemini-2.5-flash-lite"

USER_AGENT = os.getenv(
    "MONITOR_USER_AGENT",
    "Mozilla/5.0 (compatible; JharkhandNoticeMonitor/3.0)"
)


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
        raise RuntimeError(
            f"Invalid JSON in {path.name}: {exc}"
        ) from exc


def atomic_save_json(path: Path, data: Any) -> None:
    tmp = path.with_suffix(path.suffix + ".tmp")

    with tmp.open("w", encoding="utf-8") as f:
        json.dump(
            data,
            f,
            ensure_ascii=False,
            indent=2
        )
        f.write("\n")
        f.flush()
        os.fsync(f.fileno())

    os.replace(tmp, path)


def canonical_url(raw: str) -> str:
    raw = (raw or "").strip()

    p = urlparse(raw)

    if not p.scheme or not p.netloc:
        return raw

    return urlunparse(
        (
            p.scheme.lower(),
            p.netloc.lower(),
            p.path or "/",
            "",
            p.query,
            "",
        )
    )


def same_host(a: str, b: str) -> bool:
    return (
        urlparse(a).netloc.lower()
        == urlparse(b).netloc.lower()
    )


def is_http_url(url: str) -> bool:
    return urlparse(url).scheme in {
        "http",
        "https"
    }


def is_pdf(url: str) -> bool:
    return urlparse(url).path.lower().endswith(".pdf")


def make_session() -> requests.Session:
    session = requests.Session()

    retry = Retry(
        total=3,
        connect=3,
        read=3,
        status=3,
        backoff_factor=0.7,
        status_forcelist=(
            429,
            500,
            502,
            503,
            504
        ),
        allowed_methods=frozenset({
            "GET",
            "HEAD"
        }),
        respect_retry_after_header=True,
        raise_on_status=False,
    )

    adapter = HTTPAdapter(
        max_retries=retry,
        pool_connections=20,
        pool_maxsize=20,
    )

    session.mount(
        "http://",
        adapter
    )

    session.mount(
        "https://",
        adapter
    )

    session.headers.update({
        "User-Agent": USER_AGENT,
        "Accept": (
            "text/html,"
            "application/xhtml+xml,"
            "application/xml;q=0.9,"
            "*/*;q=0.8"
        ),
        "Accept-Language": "en-IN,en;q=0.8,hi;q=0.7",
        "Cache-Control": "no-cache",
    })

    return session


def get_config() -> Dict[str, Any]:

    cfg = load_json(
        CONFIG_FILE,
        {}
    )

    if not isinstance(cfg, dict):
        raise RuntimeError(
            "websites.json root must be an object"
        )

    scan = cfg.get("scan") or {}

    defaults = {
        "request_timeout_seconds": 25,
        "max_workers": 10,
        "max_items_per_site": 50,
        "max_discovery_pages_per_site": 5,
        "max_new_items_per_run": 30,
        "gemini_batch_size": 8,
        "gemini_max_calls_per_run": 20,
        "retention_days": 90,
        "max_pending_attempts": 12,
        "keywords": [],
        "discovery_keywords": [],
        "sitemap_enabled": True,
    }

    for key, value in defaults.items():
        scan.setdefault(
            key,
            value
        )

    scan["request_timeout_seconds"] = max(
        5,
        int(scan["request_timeout_seconds"])
    )

    scan["max_workers"] = max(
        1,
        int(scan["max_workers"])
    )

    scan["max_items_per_site"] = max(
        1,
        int(scan["max_items_per_site"])
    )

    scan["max_discovery_pages_per_site"] = max(
        1,
        int(scan["max_discovery_pages_per_site"])
    )

    scan["max_new_items_per_run"] = max(
        1,
        int(scan["max_new_items_per_run"])
    )

    scan["gemini_batch_size"] = max(
        1,
        min(
            20,
            int(scan["gemini_batch_size"])
        )
    )

    scan["gemini_max_calls_per_run"] = max(
        1,
        int(scan["gemini_max_calls_per_run"])
    )

    scan["retention_days"] = max(
        7,
        int(scan["retention_days"])
    )

    scan["max_pending_attempts"] = max(
        1,
        int(scan["max_pending_attempts"])
    )

    scan["sitemap_enabled"] = bool(
        scan["sitemap_enabled"]
    )

    scan["keywords"] = [
        clean_text(
            str(x),
            80
        ).lower()
        for x in scan.get(
            "keywords",
            []
        )
        if str(x).strip()
    ]

    scan["discovery_keywords"] = [
        clean_text(
            str(x),
            80
        ).lower()
        for x in scan.get(
            "discovery_keywords",
            []
        )
        if str(x).strip()
    ]

    cfg["scan"] = scan

    sites = cfg.get("websites")

    if not isinstance(sites, list):
        raise RuntimeError(
            "websites.json must contain a 'websites' array"
        )

    enabled = []
    ids = set()

    for raw_site in sites:

        if (
            not isinstance(raw_site, dict)
            or not raw_site.get(
                "enabled",
                True
            )
        ):
            continue

        site = dict(raw_site)

        site["name"] = clean_text(
            str(
                site.get(
                    "name",
                    "Unnamed Site"
                )
            ),
            120
        )

        site["url"] = canonical_url(
            str(
                site.get(
                    "url",
                    ""
                )
            )
        )

        site["id"] = clean_text(
            str(
                site.get(
                    "id",
                    site["name"]
                )
            ),
            100
        )

        if (
            not site["name"]
            or not is_http_url(
                site["url"]
            )
        ):
            print(
                f"[WARN] Skipping invalid site: {raw_site}"
            )
            continue

        if site["id"] in ids:
            print(
                f"[WARN] Duplicate site id skipped: "
                f"{site['id']}"
            )
            continue

        ids.add(site["id"])

        site["keywords"] = [
            clean_text(
                str(x),
                80
            ).lower()
            for x in site.get(
                "keywords",
                []
            )
            if str(x).strip()
        ]

        site["discovery_keywords"] = [
            clean_text(
                str(x),
                80
            ).lower()
            for x in site.get(
                "discovery_keywords",
                []
            )
            if str(x).strip()
        ]

        enabled.append(site)

    cfg["websites"] = enabled

    return cfg


def default_state() -> Dict[str, Any]:
    return {
        "version": 4,
        "initialized": False,
        "last_run": None,
        "items": {},
        "sites": {},
        "stats": {
            "runs": 0,
            "sent": 0,
            "ignored": 0,
            "pending": 0,
            "errors": 0,
        },
    }


def load_state() -> Dict[str, Any]:

    state = load_json(
        STATE_FILE,
        default_state()
    )

    if not isinstance(state, dict):
        state = default_state()

    state.setdefault(
        "version",
        1
    )

    state.setdefault(
        "initialized",
        False
    )

    state.setdefault(
        "last_run",
        None
    )

    state.setdefault(
        "items",
        {}
    )

    state.setdefault(
        "sites",
        {}
    )

    state.setdefault(
        "stats",
        {}
    )

    for key in (
        "runs",
        "sent",
        "ignored",
        "pending",
        "errors"
    ):
        state["stats"].setdefault(
            key,
            0
        )

    for record in state["items"].values():

        if not isinstance(
            record,
            dict
        ):
            continue

        if "status" not in record:

            if record.get("sent") is True:
                record["status"] = "sent"

            elif record.get("ignored") is True:
                record["status"] = "ignored"

            else:
                record["status"] = "baseline"

        record.setdefault(
            "attempts",
            0
        )

        record.setdefault(
            "last_error",
            None
        )

        record.setdefault(
            "summary",
            ""
        )

        record.setdefault(
            "first_seen",
            utc_now()
        )

        record.setdefault(
            "last_seen",
            record["first_seen"]
        )

    state["version"] = 4

    return state


def site_state(
    state: Dict[str, Any],
    site_id: str
) -> Dict[str, Any]:

    s = state.setdefault(
        "sites",
        {}
    ).setdefault(
        site_id,
        {}
    )

    s.setdefault(
        "baseline_complete",
        False
    )

    s.setdefault(
        "consecutive_failures",
        0
    )

    s.setdefault(
        "total_failures",
        0
    )

    s.setdefault(
        "last_success",
        None
    )

    s.setdefault(
        "last_error",
        None
    )

    s.setdefault(
        "last_error_at",
        None
    )

    s.setdefault(
        "last_item_count",
        0
    )

    return s


def mark_site_success(
    state: Dict[str, Any],
    site_id: str,
    count: int
) -> None:

    s = site_state(
        state,
        site_id
    )

    s["consecutive_failures"] = 0
    s["last_success"] = utc_now()
    s["last_error"] = None
    s["last_error_at"] = None
    s["last_item_count"] = count


def mark_site_failure(
    state: Dict[str, Any],
    site_id: str,
    error: str
) -> None:

    s = site_state(
        state,
        site_id
    )

    s["consecutive_failures"] += 1
    s["total_failures"] += 1
    s["last_error"] = clean_text(
        error,
        500
    )
    s["last_error_at"] = utc_now()


def local_score(
    title: str,
    url: str,
    context: str,
    keywords: List[str]
) -> int:

    text = (
        f"{title} "
        f"{url} "
        f"{context}"
    ).lower()

    return sum(
        1
        for kw in keywords
        if kw and kw in text
    )


def item_id(
    site_id: str,
    url: str,
    title: str,
    context: str = ""
) -> str:

    fingerprint = hashlib.sha256(
        clean_text(
            f"{title}|{context}",
            900
        ).lower().encode()
    ).hexdigest()[:12]

    raw = (
        f"{site_id}|"
        f"{canonical_url(url)}|"
        f"{fingerprint}"
    )

    return hashlib.sha256(
        raw.encode("utf-8")
    ).hexdigest()[:32]


def extract_candidates(
    html_text: str,
    page_url: str,
    site: Dict[str, Any],
    scan: Dict[str, Any],
) -> List[Dict[str, Any]]:

    soup = BeautifulSoup(
        html_text,
        "html.parser"
    )

    for tag in soup([
        "script",
        "style",
        "noscript",
        "svg",
        "template"
    ]):
        tag.decompose()

    keywords = list(
        dict.fromkeys(
            scan["keywords"]
            + site.get(
                "keywords",
                []
            )
        )
    )

    out = []
    seen = set()

    for a in soup.find_all(
        "a",
        href=True
    ):

        href = canonical_url(
            urljoin(
                page_url,
                a.get("href", "")
            )
        )

        if (
            not is_http_url(href)
            or not same_host(
                page_url,
                href
            )
        ):
            continue

        title = clean_text(
            a.get_text(
                " ",
                strip=True
            ),
            300
        )

        parent = a.find_parent([
            "li",
            "td",
            "article",
            "section",
            "div"
        ])

        context = clean_text(
            parent.get_text(
                " ",
                strip=True
            )
            if parent
            else "",
            700
        )

        score = local_score(
            title,
            href,
            context,
            keywords
        )

        pdf_bonus = (
            1
            if is_pdf(href)
            else 0
        )

        if score <= 0 and pdf_bonus == 0:
            continue

        if href in seen:
            continue

        seen.add(href)

        out.append({
            "url": href,
            "title": (
                title
                or clean_text(
                    context,
                    180
                )
                or href.rsplit(
                    "/",
                    1
                )[-1]
            ),
            "context": context,
            "source_page": page_url,
            "is_pdf": is_pdf(href),
            "score": score + pdf_bonus,
        })

    out.sort(
        key=lambda x: (
            -x["score"],
            x["title"].lower()
        )
    )

    return out[
        : scan["max_items_per_site"]
    ]


def discover_from_sitemap(
    session: requests.Session,
    base_url: str,
    scan: Dict[str, Any],
) -> List[str]:

    if not scan.get(
        "sitemap_enabled"
    ):
        return []

    parsed = urlparse(
        base_url
    )

    root = (
        f"{parsed.scheme}://"
        f"{parsed.netloc}"
    )

    sitemap_url = urljoin(
        root + "/",
        "sitemap.xml"
    )

    try:

        response = session.get(
            sitemap_url,
            timeout=scan[
                "request_timeout_seconds"
            ]
        )

        if response.status_code >= 400:
            return []

        soup = BeautifulSoup(
            response.text,
            "xml"
        )

        urls = []

        for loc in soup.find_all(
            "loc"
        )[:100]:

            url = canonical_url(
                loc.get_text(
                    strip=True
                )
            )

            if (
                is_http_url(url)
                and same_host(
                    base_url,
                    url
                )
            ):

                if any(
                    keyword in url.lower()
                    for keyword
                    in scan[
                        "discovery_keywords"
                    ]
                    if keyword
                ):
                    urls.append(url)

        return urls[
            : scan[
                "max_discovery_pages_per_site"
            ] * 3
        ]

    except Exception:
        return []


def discover_site(
    session: requests.Session,
    site: Dict[str, Any],
    scan: Dict[str, Any],
) -> Tuple[
    str,
    List[Dict[str, Any]],
    List[str],
    bool
]:

    base_url = site["url"]

    timeout = scan[
        "request_timeout_seconds"
    ]

    max_pages = scan[
        "max_discovery_pages_per_site"
    ]

    discovery_keywords = list(
        dict.fromkeys(
            scan[
                "discovery_keywords"
            ]
            + site.get(
                "discovery_keywords",
                []
            )
            + scan["keywords"]
        )
    )

    queue = [
        base_url
    ]

    queue.extend(
        discover_from_sitemap(
            session,
            base_url,
            scan
        )
    )

    visited = set()
    candidates = {}
    errors = []

    successful_pages = 0

    while (
        queue
        and len(visited) < max_pages
    ):

        page = canonical_url(
            queue.pop(0)
        )

        if (
            page in visited
            or not same_host(
                base_url,
                page
            )
        ):
            continue

        visited.add(page)

        try:

            response = session.get(
                page,
                timeout=timeout,
                allow_redirects=True
            )

            if response.status_code >= 400:
                raise RuntimeError(
                    f"HTTP {response.status_code}"
                )

            final_url = canonical_url(
                response.url
            )

            content_type = response.headers.get(
                "content-type",
                ""
            ).lower()

            if (
                is_pdf(final_url)
                or "application/pdf"
                in content_type
            ):

                filename = (
                    final_url.rsplit(
                        "/",
                        1
                    )[-1]
                    or "PDF Notice"
                )

                candidates[
                    final_url
                ] = {
                    "url": final_url,
                    "title": clean_text(
                        filename,
                        300
                    ),
                    "context": "Direct PDF notice",
                    "source_page": page,
                    "is_pdf": True,
                    "score": 2,
                }

                successful_pages += 1

                continue

            if (
                content_type
                and "html"
                not in content_type
                and "xhtml"
                not in content_type
            ):
                continue

            found = extract_candidates(
                response.text,
                final_url,
                site,
                scan
            )

            for row in found:

                old = candidates.get(
                    row["url"]
                )

                if (
                    old is None
                    or row["score"]
                    > old["score"]
                ):
                    candidates[
                        row["url"]
                    ] = row

            successful_pages += 1

            soup = BeautifulSoup(
                response.text,
                "html.parser"
            )

            for a in soup.find_all(
                "a",
                href=True
            ):

                href = canonical_url(
                    urljoin(
                        final_url,
                        a.get(
                            "href",
                            ""
                        )
                    )
                )

                if (
                    not is_http_url(href)
                    or not same_host(
                        base_url,
                        href
                    )
                    or href in visited
                    or href in queue
                ):
                    continue

                anchor = clean_text(
                    a.get_text(
                        " ",
                        strip=True
                    ),
                    220
                ).lower()

                path = urlparse(
                    href
                ).path.lower()

                haystack = (
                    f"{anchor} {path}"
                )

                if any(
                    keyword in haystack
                    for keyword
                    in discovery_keywords
                    if keyword
                ):
                    queue.append(href)

                    if (
                        len(queue)
                        >= max_pages * 2
                    ):
                        break

        except Exception as exc:

            errors.append(
                f"{page}: "
                f"{clean_text(str(exc), 250)}"
            )

    values = list(
        candidates.values()
    )

    values.sort(
        key=lambda x: (
            -x["score"],
            x["title"].lower()
        )
    )

    return (
        site["id"],
        values[
            : scan[
                "max_items_per_site"
            ]
        ],
        errors,
        successful_pages > 0
    )


def scan_site(
    site: Dict[str, Any],
    scan: Dict[str, Any]
):
    return discover_site(
        make_session(),
        site,
        scan
    )


def gemini_classify(
    items: List[Dict[str, Any]],
    api_key: str,
    model: str,
    timeout: int,
) -> Dict[
    str,
    Dict[str, Any]
]:

    if not items:
        return {}

    prompt_items = [
        {
            "id": str(index),
            "title": item["title"],
            "url": item["url"],
            "context": item.get(
                "context",
                ""
            )[:700],
        }
        for index, item
        in enumerate(items)
    ]

    prompt = (
        "You classify links from official "
        "Indian government/district websites. "
        "Return JSON only using the exact "
        "schema below. "
        "important=true only for useful "
        "public-service information such as "
        "recruitment/job, result, admit card, "
        "answer key, scholarship, admission, "
        "official scheme/update, tender, "
        "appointment, order, district notice, "
        "or similar actionable official information. "
        "important=false for navigation, "
        "contact/about pages, generic category "
        "pages, tourism, generic news, or "
        "unrelated pages. "
        "Do not invent facts. "
        "summary must be <= 180 characters "
        "and based only on supplied data. "
        "Schema: "
        "{\"items\":["
        "{\"id\":\"0\","
        "\"important\":true,"
        "\"summary\":\"...\"}"
        "]}\\n\\n"
        + json.dumps(
            prompt_items,
            ensure_ascii=False
        )
    )

    endpoint = (
        "https://generativelanguage.googleapis.com/"
        f"v1beta/models/{model}:generateContent"
    )

    payload = {
        "contents": [
            {
                "parts": [
                    {
                        "text": prompt
                    }
                ]
            }
        ],
        "generationConfig": {
            "responseMimeType": "application/json",
            "maxOutputTokens": 4096,
        },
    }

    headers = {
        "x-goog-api-key": api_key,
        "Content-Type": "application/json",
    }

    last_error = (
        "Gemini classification failed"
    )

    for attempt in range(3):

        try:

            response = requests.post(
                endpoint,
                headers=headers,
                json=payload,
                timeout=timeout
            )

            if response.status_code in (
                429,
                500,
                502,
                503,
                504
            ):

                last_error = (
                    f"Gemini HTTP "
                    f"{response.status_code}"
                )

                if attempt < 2:
                    time.sleep(
                        min(
                            10,
                            2 ** attempt
                        )
                    )
                    continue

                raise RuntimeError(
                    last_error
                )

            if response.status_code >= 400:
                raise RuntimeError(
                    "Gemini HTTP "
                    f"{response.status_code}: "
                    f"{clean_text(response.text, 500)}"
                )

            data = response.json()

            parts = (
                data.get(
                    "candidates",
                    [{}]
                )[0]
                .get(
                    "content",
                    {}
                )
                .get(
                    "parts",
                    []
                )
            )

            text = "".join(
                str(
                    part.get(
                        "text",
                        ""
                    )
                )
                for part in parts
                if isinstance(
                    part,
                    dict
                )
            ).strip()

            if not text:
                raise RuntimeError(
                    "Gemini returned empty response"
                )

            parsed = json.loads(
                text
            )

            result = {}

            for row in parsed.get(
                "items",
                []
            ):

                idx = str(
                    row.get(
                        "id",
                        ""
                    )
                )

                if (
                    idx.isdigit()
                    and 0 <= int(idx)
                    < len(items)
                ):

                    result[idx] = {
                        "important": bool(
                            row.get(
                                "important",
                                False
                            )
                        ),
                        "summary": clean_text(
                            str(
                                row.get(
                                    "summary",
                                    ""
                                )
                            ),
                            180
                        ),
                    }

            if not result:
                raise RuntimeError(
                    "Gemini returned no "
                    "usable classifications"
                )

            return result

        except (
            requests.RequestException,
            ValueError,
            KeyError,
            TypeError,
            RuntimeError
        ) as exc:

            last_error = str(exc)

            if attempt < 2:
                time.sleep(
                    min(
                        10,
                        2 ** attempt
                    )
                )

    raise RuntimeError(
        last_error
    )


def telegram_request(
    method: str,
    token: str,
    payload: Dict[str, Any],
    timeout: int = 20
) -> requests.Response:

    return requests.post(
        (
            "https://api.telegram.org/"
            f"bot{token}/{method}"
        ),
        json=payload,
        timeout=timeout
    )


def validate_telegram_token(
    token: str
) -> None:

    response = telegram_request(
        "getMe",
        token,
        {},
        timeout=15
    )

    if not response.ok:
        raise RuntimeError(
            "Telegram bot token invalid: "
            f"HTTP {response.status_code}: "
            f"{clean_text(response.text, 300)}"
        )


def send_telegram(
    token: str,
    chat_id: str,
    text: str
) -> Tuple[
    bool,
    bool,
    str
]:

    for attempt in range(3):

        try:

            response = telegram_request(
                "sendMessage",
                token,
                {
                    "chat_id": chat_id,
                    "text": text,
                    "parse_mode": "HTML",
                    "disable_web_page_preview": False,
                }
            )

            if response.ok:
                return (
                    True,
                    False,
                    "sent"
                )

            try:

                data = response.json()

                description = clean_text(
                    str(
                        data.get(
                            "description",
                            response.text
                        )
                    ),
                    400
                )

                retry_after = int(
                    (
                        data.get(
                            "parameters"
                        )
                        or {}
                    ).get(
                        "retry_after",
                        0
                    )
                    or 0
                )

            except Exception:

                description = clean_text(
                    response.text,
                    400
                )

                retry_after = 0

            if response.status_code in (
                400,
                401,
                403,
                404
            ):

                return (
                    False,
                    True,
                    (
                        f"Telegram HTTP "
                        f"{response.status_code}: "
                        f"{description}"
                    )
                )

            if (
                response.status_code == 429
                and attempt < 2
            ):

                time.sleep(
                    min(
                        max(
                            retry_after + 1,
                            2
                        ),
                        60
                    )
                )

                continue

            if (
                response.status_code >= 500
                and attempt < 2
            ):

                time.sleep(
                    min(
                        10,
                        2 ** attempt
                    )
                )

                continue

            return (
                False,
                False,
                (
                    f"Telegram HTTP "
                    f"{response.status_code}: "
                    f"{description}"
                )
            )

        except requests.RequestException as exc:

            if attempt < 2:

                time.sleep(
                    min(
                        10,
                        2 ** attempt
                    )
                )

                continue

            return (
                False,
                False,
                f"Telegram network error: {exc}"
            )

    return (
        False,
        False,
        "Telegram send failed"
    )


def format_message(
    site: Dict[str, Any],
    item: Dict[str, Any],
    summary: str
) -> str:

    title = html.escape(
        clean_text(
            item.get(
                "title",
                "Notification"
            ),
            300
        )
    )

    site_name = html.escape(
        site["name"]
    )

    url = html.escape(
        item["url"],
        quote=True
    )

    summary = html.escape(
        summary
        or "नई महत्वपूर्ण सूचना मिली है।"
    )

    kind = (
        "PDF Notice"
        if item.get("is_pdf")
        else "Official Notice"
    )

    return (
        f"🔔 <b>नई सूचना — "
        f"{site_name}</b>\n\n"
        f"<b>{title}</b>\n\n"
        f"{summary}\n\n"
        f"📌 {kind}\n"
        f'🔗 <a href="{url}">'
        f"पूरी सूचना देखें</a>"
    )


def prune_state(
    state: Dict[str, Any],
    retention_days: int
) -> None:

    cutoff = (
        datetime.now(timezone.utc)
        - timedelta(
            days=retention_days
        )
    )

    remove = []

    for key, record in state.get(
        "items",
        {}
    ).items():

        if not isinstance(
            record,
            dict
        ):
            remove.append(key)
            continue

        stamp = (
            record.get(
                "last_seen"
            )
            or record.get(
                "first_seen"
            )
        )

        try:

            dt = datetime.fromisoformat(
                stamp.replace(
                    "Z",
                    "+00:00"
                )
            )

        except Exception:

            dt = datetime.now(
                timezone.utc
            )

        if (
            dt < cutoff
            and record.get(
                "status"
            ) in {
                "sent",
                "ignored",
                "permanent_error",
                "baseline"
            }
        ):
            remove.append(key)

    for key in remove:
        state["items"].pop(
            key,
            None
        )


def refresh_stats(
    state: Dict[str, Any]
) -> None:

    counts = {
        "sent": 0,
        "ignored": 0,
        "pending": 0
    }

    for record in state.get(
        "items",
        {}
    ).values():

        status = record.get(
            "status"
        )

        if status in counts:
            counts[status] += 1

    state["stats"]["pending"] = (
        counts["pending"]
    )

    state["stats"]["ignored"] = (
        counts["ignored"]
    )

    state["stats"]["sent"] = (
        counts["sent"]
    )


def main() -> int:

    try:

        cfg = get_config()
        state = load_state()

    except Exception as exc:

        print(
            f"[FATAL] "
            f"Configuration/state error: {exc}",
            file=sys.stderr
        )

        return 2

    token = os.getenv(
        "TELEGRAM_BOT_TOKEN",
        ""
    ).strip()

    chat_id = os.getenv(
        "TELEGRAM_CHAT_ID",
        ""
    ).strip()

    gemini_key = os.getenv(
        "GEMINI_API_KEY",
        ""
    ).strip()

    # Workflow does not define GEMINI_MODEL.
    model = (
        os.getenv(
            "GEMINI_MODEL",
            ""
        ).strip()
        or DEFAULT_MODEL
    )

    if (
        not token
        or not chat_id
        or not gemini_key
    ):

        print(
            "[FATAL] "
            "TELEGRAM_BOT_TOKEN, "
            "TELEGRAM_CHAT_ID and "
            "GEMINI_API_KEY are required.",
            file=sys.stderr
        )

        return 2

    if not cfg["websites"]:

        print(
            "[FATAL] "
            "No enabled websites configured.",
            file=sys.stderr
        )

        return 2

    try:

        validate_telegram_token(
            token
        )

    except Exception as exc:

        print(
            f"[FATAL] "
            f"Telegram validation failed: {exc}",
            file=sys.stderr
        )

        return 2

    scan = cfg["scan"]

    state["stats"]["runs"] = int(
        state["stats"].get(
            "runs",
            0
        )
    ) + 1

    state["last_run"] = utc_now()

    run_errors = 0

    results = {}

    workers = min(
        scan["max_workers"],
        len(cfg["websites"])
    )

    with ThreadPoolExecutor(
        max_workers=max(
            1,
            workers
        )
    ) as executor:

        futures = {
            executor.submit(
                scan_site,
                site,
                scan
            ): site
            for site in cfg["websites"]
        }

        for future in as_completed(
            futures
        ):

            site = futures[
                future
            ]

            try:

                (
                    sid,
                    candidates,
                    errors,
                    success
                ) = future.result()

                results[sid] = {
                    "candidates": candidates,
                    "errors": errors,
                    "success": success,
                }

                if success:

                    mark_site_success(
                        state,
                        sid,
                        len(candidates)
                    )

                    print(
                        f"[OK] "
                        f"{site['name']}: "
                        f"{len(candidates)} "
                        f"candidate(s), "
                        f"{len(errors)} "
                        f"partial error(s)"
                    )

                else:

                    run_errors += 1

                    mark_site_failure(
                        state,
                        sid,
                        "; ".join(errors)
                        or
                        "No page could be fetched"
                    )

                    print(
                        f"[ERROR] "
                        f"{site['name']}: "
                        f"no page could be fetched",
                        file=sys.stderr
                    )

            except Exception as exc:

                run_errors += 1

                results[
                    site["id"]
                ] = {
                    "candidates": [],
                    "errors": [str(exc)],
                    "success": False,
                }

                mark_site_failure(
                    state,
                    site["id"],
                    str(exc)
                )

                print(
                    f"[ERROR] "
                    f"{site['name']}: {exc}",
                    file=sys.stderr
                )

    pending = []

    for site in cfg["websites"]:

        sid = site["id"]

        ss = site_state(
            state,
            sid
        )

        result = results.get(
            sid,
            {
                "candidates": [],
                "success": False
            }
        )

        candidates = result[
            "candidates"
        ]

        current_scan_success = bool(
            result["success"]
        )

        # First successful scan of each site
        # creates its baseline.
        if (
            not ss["baseline_complete"]
            and current_scan_success
        ):

            for candidate in candidates:

                iid = item_id(
                    sid,
                    candidate["url"],
                    candidate["title"],
                    candidate.get(
                        "context",
                        ""
                    )
                )

                state["items"].setdefault(
                    iid,
                    {
                        "site_id": sid,
                        "site_name": site["name"],
                        "url": candidate["url"],
                        "title": candidate["title"],
                        "context": candidate.get(
                            "context",
                            ""
                        )[:700],
                        "is_pdf": bool(
                            candidate.get(
                                "is_pdf"
                            )
                        ),
                        "first_seen": utc_now(),
                        "last_seen": utc_now(),
                        "status": "baseline",
                        "attempts": 0,
                        "summary": "",
                        "last_error": None,
                    }
                )

            ss["baseline_complete"] = True

            print(
                f"[BASELINE] "
                f"{site['name']} initialized "
                f"with {len(candidates)} "
                f"existing item(s)"
            )

            continue

        for candidate in candidates:

            iid = item_id(
                sid,
                candidate["url"],
                candidate["title"],
                candidate.get(
                    "context",
                    ""
                )
            )

            record = state[
                "items"
            ].get(iid)

            if record is None:

                record = {
                    "site_id": sid,
                    "site_name": site["name"],
                    "url": candidate["url"],
                    "title": candidate["title"],
                    "context": candidate.get(
                        "context",
                        ""
                    )[:700],
                    "is_pdf": bool(
                        candidate.get(
                            "is_pdf"
                        )
                    ),
                    "first_seen": utc_now(),
                    "last_seen": utc_now(),
                    "status": "pending",
                    "attempts": 0,
                    "summary": "",
                    "last_error": None,
                }

                state[
                    "items"
                ][iid] = record

            else:

                record["last_seen"] = (
                    utc_now()
                )

                record["title"] = (
                    candidate["title"]
                    or record.get(
                        "title",
                        ""
                    )
                )

                record["context"] = (
                    candidate.get(
                        "context",
                        ""
                    )[:700]
                )

                record["is_pdf"] = bool(
                    candidate.get(
                        "is_pdf",
                        record.get(
                            "is_pdf",
                            False
                        )
                    )
                )

            if (
                ss["baseline_complete"]
                and record.get(
                    "status"
                ) in {
                    "pending",
                    "ready"
                }
                and int(
                    record.get(
                        "attempts",
                        0
                    )
                )
                < scan[
                    "max_pending_attempts"
                ]
            ):

                pending.append(
                    (
                        iid,
                        record
                    )
                )

    state["initialized"] = all(
        site_state(
            state,
            site["id"]
        )[
            "baseline_complete"
        ]
        for site in cfg[
            "websites"
        ]
    )

    pending.sort(
        key=lambda pair: (
            -local_score(
                pair[1]["title"],
                pair[1]["url"],
                pair[1].get(
                    "context",
                    ""
                ),
                scan["keywords"]
            ),
            pair[1].get(
                "first_seen",
                ""
            )
        )
    )

    pending = pending[
        :
        scan["gemini_batch_size"]
        * scan["gemini_max_calls_per_run"]
    ]

    batch_size = scan[
        "gemini_batch_size"
    ]

    for start in range(
        0,
        len(pending),
        batch_size
    ):

        batch = pending[
            start:
            start + batch_size
        ]

        try:

            result = gemini_classify(
                [
                    record
                    for _, record
                    in batch
                ],
                gemini_key,
                model,
                scan[
                    "request_timeout_seconds"
                ]
            )

            for index, (
                _,
                record
            ) in enumerate(batch):

                record["attempts"] = int(
                    record.get(
                        "attempts",
                        0
                    )
                ) + 1

                classification = result.get(
                    str(index)
                )

                if classification is None:

                    record["status"] = (
                        "pending"
                    )

                    record["last_error"] = (
                        "Gemini returned "
                        "no classification"
                    )

                    continue

                record["last_error"] = None

                if classification[
                    "important"
                ]:

                    record["status"] = (
                        "ready"
                    )

                    record["summary"] = (
                        classification.get(
                            "summary",
                            ""
                        )
                    )

                else:

                    record["status"] = (
                        "ignored"
                    )

                    record["summary"] = (
                        classification.get(
                            "summary",
                            ""
                        )
                    )

        except Exception as exc:

            error = clean_text(
                str(exc),
                500
            )

            for _, record in batch:

                record["attempts"] = int(
                    record.get(
                        "attempts",
                        0
                    )
                ) + 1

                record["status"] = (
                    "pending"
                )

                record["last_error"] = (
                    error
                )

            run_errors += 1

            print(
                f"[ERROR] Gemini "
                f"classification failed: "
                f"{error}",
                file=sys.stderr
            )

            # Remaining batches are kept pending
            # for a future run.
            break

    ready = [
        (
            iid,
            record
        )
        for iid, record
        in state["items"].items()
        if record.get(
            "status"
        ) == "ready"
    ]

    ready.sort(
        key=lambda pair:
        pair[1].get(
            "first_seen",
            ""
        )
    )

    sent_count = 0

    for iid, record in ready[
        : scan[
            "max_new_items_per_run"
        ]
    ]:

        site = next(
            (
                s
                for s
                in cfg[
                    "websites"
                ]
                if s["id"]
                == record.get(
                    "site_id"
                )
            ),
            None
        )

        if site is None:

            record["status"] = (
                "permanent_error"
            )

            record["last_error"] = (
                "Configured site "
                "no longer exists"
            )

            continue

        (
            ok,
            permanent,
            detail
        ) = send_telegram(
            token,
            chat_id,
            format_message(
                site,
                record,
                record.get(
                    "summary",
                    ""
                )
            )
        )

        if ok:

            record["status"] = (
                "sent"
            )

            record["last_error"] = None

            sent_count += 1

        elif permanent:

            record["status"] = (
                "permanent_error"
            )

            record["last_error"] = (
                detail
            )

            run_errors += 1

            print(
                "[ERROR] Permanent "
                "Telegram error for "
                f"{record['url']}: "
                f"{detail}",
                file=sys.stderr
            )

        else:

            record["status"] = (
                "ready"
            )

            record["last_error"] = (
                detail
            )

            run_errors += 1

            print(
                "[WARN] Telegram delivery "
                "failed; will retry: "
                f"{detail}",
                file=sys.stderr
            )

    state["stats"]["errors"] = int(
        state["stats"].get(
            "errors",
            0
        )
    ) + run_errors

    refresh_stats(
        state
    )

    prune_state(
        state,
        scan["retention_days"]
    )

    atomic_save_json(
        STATE_FILE,
        state
    )

    print(
        f"[DONE] "
        f"initialized={state['initialized']} "
        f"sites={len(cfg['websites'])} "
        f"sent_this_run={sent_count} "
        f"pending={state['stats']['pending']} "
        f"errors_this_run={run_errors}"
    )

    return 0


if __name__ == "__main__":
    raise SystemExit(
        main()
    )
