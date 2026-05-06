#!/usr/bin/env python3
"""
Step 2 — PDF download
=====================
Reads scholar_results_serpapi.csv and attempts to download a PDF for each row.

Download strategy (tried in order):
  0. Direct URLs from 'Resources' / 'Link' columns
  1. OpenAlex free OA PDF URLs (from locations/best_oa_location)
  2. Unpaywall OA PDF URLs (free API, needs DOI)
  3. OpenAlex Content API (100 credits/file)
  4. Domain-specific handlers (Taylor&Francis→Anna's Archive, SSRN, Springer,
     MUSE, OpenEdition, Persee, Cairn, Google Books→Anna's Archive)
  5. Sci-Hub local library (scihub.py, fast, no browser)
     then Sci-Hub via requests/browser (tries DOI, article Link, Resources URLs)
  6. Anna's Archive — HTML scraping (annas-archive.li)
  6b. Anna's Archive — RapidAPI (book + journal search, annas-archive-api.p.rapidapi.com)
  7. LibGen (libgen_api_enhanced — title + author search, multiple mirrors)
  8. Garbage World public API (garbage.world)
  9. CSV fallback — try 'Link' and 'Resources' columns directly

Generic landing-page discovery is also used for unhandled publisher and
repository pages by scraping citation_pdf_url metadata, embedded PDF viewers,
and PDF/download/fulltext links.

Usage:
    python scholar_2_download.py [options]

Options:
    --start-from N      Skip the first N rows that need PDFs (useful for resuming)
    --limit N           Process at most N rows (useful for testing)
    --dry-run           Show what would be done without downloading anything
    --no-scihub         Disable Sci-Hub
    --no-content-api    Disable OpenAlex Content API (saves credits)
    --no-annas          Disable Anna's Archive
    --no-libgen         Disable LibGen
"""

import argparse
import os
import sys
import csv
import json
import time
import uuid
import re
import signal
import logging
from difflib import SequenceMatcher
from urllib.parse import quote_plus, urljoin, urlparse

import requests
import urllib3
from bs4 import BeautifulSoup

urllib3.disable_warnings(urllib3.exceptions.InsecureRequestWarning)

# Optional local SciHub library
try:
    sys.path.insert(0, '/Users/edekeulenaar/Code/scihub.py-master/scihub')
    from scihub import SciHub as _SciHub
    SCIHUB_LOCAL_AVAILABLE = True
except Exception:
    SCIHUB_LOCAL_AVAILABLE = False

# Optional LibGen client
try:
    from libgen_api_enhanced import LibgenSearch as _LibgenSearch
    LIBGEN_AVAILABLE = True
except Exception:
    LIBGEN_AVAILABLE = False

# Optional: read browser cookies (used to inject Brave KB session into headless Chrome)
try:
    import browser_cookie3 as _browser_cookie3
    BROWSER_COOKIE3_AVAILABLE = True
except ImportError:
    BROWSER_COOKIE3_AVAILABLE = False

# Optional browser automation (for ProQuest, EBSCO)
try:
    from selenium import webdriver
    from selenium.webdriver.common.by import By
    from selenium.webdriver.common.keys import Keys as SeleniumKeys
    from selenium.webdriver.support.ui import WebDriverWait
    from selenium.webdriver.support import expected_conditions as EC
    from selenium.webdriver.chrome.options import Options as ChromeOptions
    from selenium.webdriver.chrome.service import Service as ChromeService
    from selenium.common.exceptions import TimeoutException, WebDriverException
    SELENIUM_AVAILABLE = True
except ImportError:
    SELENIUM_AVAILABLE = False

# ─── Configuration ────────────────────────────────────────────────────────────

BASE_DIR      = '/Users/edekeulenaar/Projects/PhDs/PhD 2020-2025/Publications 📇/Censorship and moderation'
SCHOLAR_CSV   = os.path.join(BASE_DIR, 'scholar_results_serpapi.csv')
PDF_FOLDER    = os.path.join(BASE_DIR, 'PDF downloads')
METADATA_JSON = os.path.join(PDF_FOLDER, '_metadata.json')
FAILED_LOG    = os.path.join(BASE_DIR, 'failed_downloads.csv')
PROGRESS_LOG  = os.path.join(BASE_DIR, 'download_progress.log')

OPENALEX_API      = 'https://api.openalex.org/works'
OPENALEX_API_KEY  = ''  # redacted
UNPAYWALL_API     = 'https://api.unpaywall.org/v2'
SCIHUB_BASES      = ['https://sci-hub.st', 'https://www.sci-hub.in']

# Domains that Sci-Hub cannot resolve — skip to avoid wasting browser time.
# Includes all domains with dedicated handlers (they already ran earlier).
_SCIHUB_SKIP_DOMAINS = (
    'books.google', 'google.com/books',
    'academia.edu', 'researchgate.net',
    'youtube.com', 'wikipedia.org',
    'twitter.com', 'facebook.com',
    # Handled by dedicated domain handlers — Sci-Hub browser won't help
    'persee.fr',
    'hal.science', 'hal.archives-ouvertes.fr', 'hal.inria.fr', 'hal-amu.archives',
    'journals.openedition.org', 'openedition.org',
    'cairn.info',
    'proquest.com',
    'ebscohost.com', 'ebsco.com',
    # JSTOR full-page URLs: DOI is extracted separately and tried via Sci-Hub
    'jstor.org',
    # Publisher pages Sci-Hub cannot resolve
    'classiques-garnier.com',
    'cris.unibo.it',
    'droit.cairn.info',
    # ACM: handled by try_acm (which calls Sci-Hub internally with a clean DOI)
    'dl.acm.org',
)

# ── Chrome / ChromeDriver version management ─────────────────────────────────
# We pin explicit Chrome-for-Testing + matching ChromeDriver binaries from
# Selenium's local cache to avoid "session not created" version-mismatch errors.
#
# _CHROME_BINARY / _CHROMEDRIVER_BIN  — default pair used by _get_browser()
#   and all domain handlers (Sci-Hub, SSRN, ProQuest, T&F…).  Kept at 141
#   for backward-compatibility with the other handlers that have worked stably.
#
# _KB_CHROME_BINARY / _KB_CHROMEDRIVER_BIN  — pair used exclusively by the KB
#   library strategy.  Updated to 148 so Brave CDP attach (which may run Chrome
#   148) and the headless fallback both work without version-mismatch errors.

_SELENIUM_CACHE = os.path.expanduser('~/.cache/selenium')

_CHROME_BINARY = os.path.expanduser(
    '~/.cache/selenium/chrome/mac-arm64/141.0.7390.54/'
    'Google Chrome for Testing.app/Contents/MacOS/Google Chrome for Testing')
_CHROMEDRIVER_BIN = os.path.expanduser(
    '~/.cache/selenium/chromedriver/mac-arm64/141.0.7390.54/chromedriver')

# KB-specific pair — Chrome 148 + ChromeDriver 148 (downloaded separately).
# These are used only by _kb_attach_or_new(); all other handlers keep 141.
_KB_CHROME_BINARY = os.path.expanduser(
    '~/.cache/selenium/chrome/mac-arm64/148.0.7778.97/'
    'Google Chrome for Testing.app/Contents/MacOS/Google Chrome for Testing')
_KB_CHROMEDRIVER_BIN = os.path.expanduser(
    '~/.cache/selenium/chromedriver/mac-arm64/148.0.7778.97/chromedriver')
ANNAS_ARCHIVE_BASE     = 'https://annas-archive.li'
ANNAS_ARCHIVE_API_KEY  = ''  # redacted

USER_EMAIL = 'edekeulenaar@gmail.com'   # for OpenAlex / Unpaywall polite pool

SCIHUB_ENABLED        = True
ANNAS_ARCHIVE_ENABLED = True
USE_CONTENT_API       = True   # set False to skip (saves OpenAlex credits)
LIBGEN_ENABLED        = True

# Anna's Archive RapidAPI (alternative to HTML scraping)
ANNAS_RAPIDAPI_KEY     = ''  # redacted
ANNAS_RAPIDAPI_HOST    = 'annas-archive-api.p.rapidapi.com'
ANNAS_RAPIDAPI_HEADERS = {
    'x-rapidapi-key':  ANNAS_RAPIDAPI_KEY,
    'x-rapidapi-host': ANNAS_RAPIDAPI_HOST,
}

# Overridden by CLI flags in main()
DRY_RUN = False

TITLE_SIMILARITY_THRESHOLD = 0.80

API_DELAY        = 0.15
DOWNLOAD_DELAY   = 0.5
DOWNLOAD_TIMEOUT = 60

SELECT_FIELDS = 'id,title,doi,publication_year,open_access,best_oa_location,primary_location,locations,has_content,content_urls'

# ─── Logging ──────────────────────────────────────────────────────────────────

logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s [%(levelname)s] %(message)s',
    force=True,   # override any root-logger config set by imported libraries
    handlers=[
        logging.FileHandler(PROGRESS_LOG, encoding='utf-8'),
        logging.StreamHandler(sys.stdout)
    ]
)
log = logging.getLogger(__name__)

# ─── Helpers ──────────────────────────────────────────────────────────────────

def sanitize_filename(name: str) -> str:
    return re.sub(r'[^\w\s\-]', '', str(name)).strip()


def generate_filename(row: dict) -> str:
    author = sanitize_filename(row.get('Authors') or 'Unknown')
    year = row.get('Year') or 'Unknown'
    try:
        year = str(int(float(year)))
    except (ValueError, TypeError):
        year = sanitize_filename(str(year)) if year else 'Unknown'
    title = sanitize_filename(row.get('Title') or 'Untitled')
    uid = row.get('Result ID') or str(uuid.uuid4())[:8]
    if len(title) > 150:
        title = title[:150].rsplit(' ', 1)[0]
    return f"{author} - {year} - {title} - {uid}.pdf"


def strip_html(text: str) -> str:
    return re.sub(r'<[^>]+>', '', text)


def normalize_title(title: str) -> str:
    if not title:
        return ''
    t = strip_html(title)
    t = re.sub(r'[^\w\s]', '', t.lower())
    return re.sub(r'\s+', ' ', t).strip()


def title_similarity(a: str, b: str) -> float:
    na, nb = normalize_title(a), normalize_title(b)
    if not na or not nb:
        return 0.0
    ratio = SequenceMatcher(None, na, nb).ratio()
    shorter, longer = (na, nb) if len(na) <= len(nb) else (nb, na)
    if longer.startswith(shorter):
        ratio = max(ratio, len(shorter) / len(longer))
    return ratio


def sanitize_search_query(title: str) -> str:
    t = re.sub(r'[,:"\'<>{}()\[\]|\\]', ' ', title.strip())
    return re.sub(r'\s+', ' ', t).strip()


def extract_doi(link: str) -> str | None:
    if not link:
        return None
    match = re.search(r'(10\.\d{4,9}/[^\s,;\"\'#?]+)', link)
    if match:
        doi = match.group(1)
        doi = re.sub(r'\.pdf$', '', doi)
        doi = re.sub(r'/pdf$', '', doi)
        return doi.rstrip('.')
    return None


def extract_first_author_lastname(authors: str) -> str | None:
    names = extract_author_lastnames(authors)
    return names[0] if names else None


def extract_author_lastnames(authors: str) -> list[str]:
    """Extract probable author surnames from common delimiter formats."""
    if not authors:
        return []
    parts = re.split(r'\s*(?:,|;|\band\b|&)\s*', authors, flags=re.IGNORECASE)
    out: list[str] = []
    seen = set()
    for part in parts:
        words = re.findall(r"[A-Za-zÀ-ÖØ-öø-ÿ'`\-]+", part)
        if not words:
            continue
        candidate = words[-1].strip("-'`").lower()
        if len(candidate) < 2 or candidate in {'et', 'al'}:
            continue
        if candidate not in seen:
            seen.add(candidate)
            out.append(candidate)
    return out


def is_valid_pdf(filepath: str, min_size: int = 1024) -> bool:
    try:
        if os.path.getsize(filepath) < min_size:
            return False
        with open(filepath, 'rb') as f:
            header = f.read(8)
        return header[:5] == b'%PDF-'
    except Exception:
        return False


def _remove_if_exists(path: str):
    try:
        os.remove(path)
    except OSError:
        pass


def load_metadata() -> dict:
    if os.path.exists(METADATA_JSON):
        with open(METADATA_JSON, encoding='utf-8') as f:
            return json.load(f)
    return {}


def save_metadata(meta: dict):
    os.makedirs(PDF_FOLDER, exist_ok=True)
    with open(METADATA_JSON, 'w', encoding='utf-8') as f:
        json.dump(meta, f, ensure_ascii=False, indent=2)


def build_session(email: str = None) -> requests.Session:
    session = requests.Session()
    ua = 'Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36'
    session.headers.update({
        'User-Agent': ua,
        'Accept': 'application/pdf,application/octet-stream,text/html,*/*',
    })
    if email:
        session.headers['X-Mailto'] = email

    # Login to Anna's Archive if credentials available
    if ANNAS_ARCHIVE_API_KEY:
        try:
            session.post(f'{ANNAS_ARCHIVE_BASE}/account/',
                        data={'key': ANNAS_ARCHIVE_API_KEY},
                        timeout=15, verify=False)
            log.info("Logged in to Anna's Archive")
        except Exception as e:
            log.debug(f"Anna's Archive login failed: {e}")

    return session


# ─── OpenAlex Search ──────────────────────────────────────────────────────────

def _pick_best_match(results: list, title: str) -> tuple[dict | None, float]:
    best_match = None
    best_score = 0.0
    for work in results:
        score = title_similarity(title, work.get('title', ''))
        if score > best_score:
            best_score = score
            best_match = work
    return best_match, best_score


def _api_search(session: requests.Session, params: dict) -> list:
    try:
        resp = session.get(OPENALEX_API, params=params, timeout=30)
        resp.raise_for_status()
        return resp.json().get('results', [])
    except requests.RequestException as e:
        log.debug(f"  API error: {e}")
        return []


def search_openalex(title: str, year: str = None, authors: str = None,
                    link: str = None, session: requests.Session = None,
                    email: str = None) -> tuple[dict | None, str | None]:
    """
    Search OpenAlex. Returns (work_dict, doi_str) tuple.
    The DOI is extracted from either the Link column or the OpenAlex result.
    """
    if not title or not title.strip():
        return None, extract_doi(link)

    session = session or requests.Session()
    base_params = {'per_page': 5, 'select': SELECT_FIELDS}
    if email:
        base_params['mailto'] = email

    doi = extract_doi(link)

    # Strategy 0: DOI lookup
    if doi:
        try:
            resp = session.get(f'{OPENALEX_API}/doi:{doi}',
                               params={'select': SELECT_FIELDS,
                                       **(({'mailto': email} if email else {}))},
                               timeout=30)
            if resp.status_code == 200:
                work = resp.json()
                if work.get('id'):
                    log.info(f"  Found via DOI: {doi}")
                    # Extract DOI from work if we didn't have one
                    work_doi = (work.get('doi') or '').replace('https://doi.org/', '')
                    return work, work_doi or doi
        except requests.RequestException:
            pass
        time.sleep(API_DELAY)

    search_title = sanitize_search_query(title)
    if not search_title:
        return None, doi

    author_lastname = extract_first_author_lastname(authors)

    # Strategy 1: title + year
    if year:
        try:
            y = int(float(year))
            if 1800 <= y <= 2030:
                params = {**base_params,
                          'filter': f'title.search:{search_title},publication_year:{y}'}
                results = _api_search(session, params)
                if results:
                    match, score = _pick_best_match(results, title)
                    if match and score >= TITLE_SIMILARITY_THRESHOLD:
                        work_doi = (match.get('doi') or '').replace('https://doi.org/', '')
                        return match, work_doi or doi
                time.sleep(API_DELAY)
        except (ValueError, TypeError):
            pass

    # Strategy 2: title + author
    if author_lastname:
        author_clean = sanitize_search_query(author_lastname)
        if author_clean:
            params = {**base_params,
                      'filter': f'title.search:{search_title},raw_author_name.search:{author_clean}'}
            results = _api_search(session, params)
            if results:
                match, score = _pick_best_match(results, title)
                if match and score >= TITLE_SIMILARITY_THRESHOLD:
                    work_doi = (match.get('doi') or '').replace('https://doi.org/', '')
                    return match, work_doi or doi
            time.sleep(API_DELAY)

    # Strategy 3: title only
    params = {**base_params, 'filter': f'title.search:{search_title}'}
    results = _api_search(session, params)
    if results:
        match, score = _pick_best_match(results, title)
        if match and score >= TITLE_SIMILARITY_THRESHOLD:
            work_doi = (match.get('doi') or '').replace('https://doi.org/', '')
            return match, work_doi or doi

    return None, doi


# ─── PDF URL Extraction ──────────────────────────────────────────────────────

def extract_oa_pdf_urls(work: dict) -> list[str]:
    urls = []
    seen = set()

    def add(url):
        if url and url not in seen and url.startswith('http'):
            seen.add(url)
            urls.append(url)

    oa_loc = work.get('best_oa_location') or {}
    add(oa_loc.get('pdf_url'))

    primary = work.get('primary_location') or {}
    add(primary.get('pdf_url'))

    for loc in (work.get('locations') or []):
        add(loc.get('pdf_url'))

    oa = work.get('open_access') or {}
    oa_url = oa.get('oa_url')
    if oa_url and oa_url.lower().endswith('.pdf'):
        add(oa_url)

    return urls


def get_content_api_url(work: dict) -> str | None:
    has_content = work.get('has_content') or {}
    if has_content.get('pdf'):
        content_urls = work.get('content_urls') or {}
        return content_urls.get('pdf')
    return None


# ─── Download Functions ───────────────────────────────────────────────────────

def try_download_pdf(url: str, save_path: str, session: requests.Session,
                     params: dict = None, verify_ssl: bool = True) -> bool:
    try:
        resp = session.get(url, params=params, timeout=DOWNLOAD_TIMEOUT,
                           stream=True, allow_redirects=True, verify=verify_ssl)
        if resp.status_code != 200:
            return False

        content_type = resp.headers.get('Content-Type', '').lower()
        if 'html' in content_type and 'pdf' not in content_type:
            return False

        with open(save_path, 'wb') as f:
            for chunk in resp.iter_content(chunk_size=8192):
                f.write(chunk)

        if is_valid_pdf(save_path):
            return True

        _remove_if_exists(save_path)
        return False

    except requests.RequestException:
        _remove_if_exists(save_path)
        return False


def _looks_like_pdf_url(url: str) -> bool:
    lower = (url or '').lower()
    return any(h in lower for h in (
        '.pdf', '/pdf/', '/pdf?', 'download', 'bitstream', 'fulltext',
        '/stable/pdf', 'pdfdirect', 'content/pdf', '/file/', '/document',
        'download=true',
    ))


def _candidate_pdf_urls_from_html(html: str, page_url: str) -> list[str]:
    """Extract likely PDF URLs from a scholarly landing page.

    Covers common repository/publisher patterns:
      • citation_pdf_url / eprints.document_url meta tags
      • anchor tags with PDF/download/fulltext/bitstream hints
      • embedded PDF viewers
      • arXiv abs pages
    """
    soup = BeautifulSoup(html or '', 'html.parser')
    candidates: list[str] = []
    seen: set[str] = set()

    def add(raw_url: str):
        if not raw_url:
            return
        url = requests.compat.urljoin(page_url, raw_url.strip())
        url = url.split('#')[0]
        if not url.startswith('http') or url in seen:
            return
        seen.add(url)
        candidates.append(url)

    meta_names = (
        'citation_pdf_url',
        'eprints.document_url',
        'bepress_citation_pdf_url',
        'dc.identifier',
        'dc.relation.ispartof',
    )
    for meta in soup.find_all('meta'):
        name = (meta.get('name') or meta.get('property') or '').strip().lower()
        content = (meta.get('content') or '').strip()
        if not content:
            continue
        if name in meta_names and (_looks_like_pdf_url(content) or content.lower().endswith('.pdf')):
            add(content)

    for tag in soup.find_all(['a', 'iframe', 'embed', 'object'], href=True):
        href = tag.get('href') or ''
        text = tag.get_text(' ', strip=True).lower()
        if _looks_like_pdf_url(href) or ('pdf' in text and any(t in text for t in ('download', 'view', 'full'))):
            add(href)

    for tag in soup.find_all(['iframe', 'embed', 'object']):
        src = tag.get('src') or tag.get('data') or ''
        if _looks_like_pdf_url(src):
            add(src)

    # Repository buttons sometimes store the URL in data-* attributes.
    for tag in soup.find_all(attrs=True):
        for attr, value in tag.attrs.items():
            if not attr.startswith('data-'):
                continue
            if isinstance(value, str) and _looks_like_pdf_url(value):
                add(value)

    m = re.search(r'arxiv\.org/abs/([0-9]+\.[0-9v]+)', page_url)
    if m:
        add(f'https://arxiv.org/pdf/{m.group(1)}.pdf')

    return candidates


def try_landing_page_pdf(url: str, save_path: str, session: requests.Session) -> bool:
    """Fetch an HTML landing page and try PDF URLs advertised in the page."""
    if not url or not url.startswith('http'):
        return False
    try:
        resp = session.get(
            url,
            timeout=30,
            allow_redirects=True,
            headers={
                'Accept': 'text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8',
                'Accept-Language': 'en,fr,it,es,pt;q=0.8',
            },
        )
        if resp.status_code != 200:
            return False

        content_type = resp.headers.get('Content-Type', '').lower()
        if 'pdf' in content_type:
            with open(save_path, 'wb') as f:
                f.write(resp.content)
            if is_valid_pdf(save_path):
                return True
            _remove_if_exists(save_path)
            return False

        if 'html' not in content_type and '<html' not in resp.text[:500].lower():
            return False

        for pdf_url in _candidate_pdf_urls_from_html(resp.text, resp.url or url)[:8]:
            if pdf_url.rstrip('/') == (resp.url or url).rstrip('/'):
                continue
            log.info(f'  [Landing] Found candidate PDF: {pdf_url[:100]}')
            if try_download_pdf(pdf_url, save_path, session):
                return True
            time.sleep(DOWNLOAD_DELAY)
    except Exception as e:
        log.debug(f'  Landing-page PDF discovery error ({url[:80]}): {e}')
    return False


def try_content_api(content_url: str, save_path: str, session: requests.Session) -> bool:
    return try_download_pdf(content_url, save_path, session,
                            params={'api_key': OPENALEX_API_KEY})


# ─── Unpaywall ────────────────────────────────────────────────────────────────

def try_unpaywall(doi: str, save_path: str, session: requests.Session,
                  email: str) -> bool:
    """Query Unpaywall for OA PDF URLs. Free API, just needs an email."""
    if not doi or not email:
        return False
    try:
        resp = session.get(f'{UNPAYWALL_API}/{doi}',
                           params={'email': email}, timeout=20)
        if resp.status_code != 200:
            return False
        data = resp.json()
        if not data.get('is_oa'):
            return False

        # Collect all PDF URLs from Unpaywall locations
        pdf_urls = []
        best = data.get('best_oa_location') or {}
        if best.get('url_for_pdf'):
            pdf_urls.append(best['url_for_pdf'])
        for loc in (data.get('oa_locations') or []):
            url = loc.get('url_for_pdf')
            if url and url not in pdf_urls:
                pdf_urls.append(url)

        for url in pdf_urls:
            log.info(f"  [Unpaywall] Trying: {url[:100]}")
            if try_download_pdf(url, save_path, session):
                return True
            time.sleep(DOWNLOAD_DELAY)

    except requests.RequestException as e:
        log.debug(f"  Unpaywall error: {e}")
    return False


# ─── Sci-Hub ──────────────────────────────────────────────────────────────────

def _parse_scihub_page(content: bytes, base_url: str, save_path: str,
                       session: requests.Session) -> bool:
    """Parse a Sci-Hub HTML page and try all known PDF extraction methods."""
    soup = BeautifulSoup(content, 'html.parser')

    # Method 1: <object data="/storage/...pdf"> tag
    obj = soup.find('object', {'type': 'application/pdf'})
    if obj and obj.get('data'):
        pdf_path = obj['data'].split('#')[0]
        if pdf_path.startswith('/'):
            pdf_url = f'{base_url}{pdf_path}'
        elif not pdf_path.startswith('http'):
            pdf_url = f'{base_url}/{pdf_path}'
        else:
            pdf_url = pdf_path
        if try_download_pdf(pdf_url, save_path, session, verify_ssl=False):
            return True

    # Method 2: <a href="/download/...pdf"> link
    download_link = soup.find('a', href=re.compile(r'/download/.*\.pdf'))
    if download_link:
        pdf_url = f'{base_url}{download_link["href"]}'
        if try_download_pdf(pdf_url, save_path, session, verify_ssl=False):
            return True

    # Method 3: <iframe src="..."> (legacy)
    iframe = soup.find('iframe')
    if iframe and iframe.get('src'):
        src = iframe['src']
        if src.startswith('//'):
            src = 'https:' + src
        elif src.startswith('/'):
            src = f'{base_url}{src}'
        if try_download_pdf(src, save_path, session, verify_ssl=False):
            return True

    # Method 4: <embed src="...">
    embed = soup.find('embed')
    if embed and embed.get('src'):
        src = embed['src']
        if src.startswith('/'):
            src = f'{base_url}{src}'
        if try_download_pdf(src, save_path, session, verify_ssl=False):
            return True

    return False


def try_scihub(identifier: str, save_path: str, session: requests.Session) -> bool:
    """
    Download from Sci-Hub using a DOI or URL.
    Phase 0: local scihub.py library (fast, no browser)
    Phase 1: requests against mirrors (fast, may hit Cloudflare)
    Phase 2: Selenium browser automation (bypasses Cloudflare)
    """
    if not identifier:
        return False

    # Phase 0: local scihub.py library — fast, no browser required
    if SCIHUB_LOCAL_AVAILABLE:
        if try_scihub_local(identifier, save_path):
            return True

    # Phase 1: Try with requests (fast, but may hit Cloudflare)
    for base_url in SCIHUB_BASES:
        try:
            resp = session.get(f'{base_url}/{identifier}',
                               timeout=30, verify=False)
            if resp.status_code != 200:
                continue

            # If response is already a PDF
            if resp.headers.get('Content-Type', '').startswith('application/pdf'):
                with open(save_path, 'wb') as f:
                    f.write(resp.content)
                if is_valid_pdf(save_path):
                    return True
                _remove_if_exists(save_path)
                continue

            # Check for Cloudflare challenge
            if b'Just a moment' in resp.content[:500] or \
               b'cf-browser-verification' in resp.content[:2000]:
                log.debug(f"  Sci-Hub ({base_url}): Cloudflare challenge, will try browser")
                continue

            if _parse_scihub_page(resp.content, base_url, save_path, session):
                return True

        except requests.RequestException as e:
            log.debug(f"  Sci-Hub error ({base_url}): {e}")
        except Exception as e:
            log.debug(f"  Sci-Hub parse error ({base_url}): {e}")

    # Phase 2: Try with browser automation (bypasses Cloudflare).
    # If the first mirror confirms "article not in database", all mirrors share
    # the same database so we stop immediately instead of retrying each one.
    if SELENIUM_AVAILABLE:
        for base_url in SCIHUB_BASES:
            result = _try_scihub_browser(base_url, identifier, save_path, session)
            if result is True:
                return True
            # _try_scihub_browser returns 'not_found' string when article absent
            if result == 'not_found':
                break

    return False


def _try_scihub_browser(base_url: str, identifier: str, save_path: str,
                        session: requests.Session) -> bool:
    """Use Selenium to search Sci-Hub (bypasses Cloudflare) and download PDF.

    Navigates to {base_url}/{identifier} (DOI, URL, or article link all work).
    If Cloudflare blocks the direct URL, falls back to submitting the identifier
    via the Sci-Hub search form.  PDF URL is extracted via JavaScript, BeautifulSoup,
    and/or clicking the download button, then downloaded either via requests (with
    transferred cookies) or via the browser itself.
    """
    download_dir = os.path.dirname(save_path)
    driver = _get_browser(download_dir)
    if not driver:
        return False

    try:
        # ── Step 1: Navigate directly to the article ──────────────────────────
        url = f'{base_url}/{identifier}'
        log.info(f"  [Sci-Hub/browser] Loading: {url[:80]}")
        driver.get(url)
        time.sleep(8)  # Cloudflare typically resolves in 5–8 s

        # ── Step 2: Fast-exit if Sci-Hub says article not in database ────────
        title_lower = driver.title.lower()
        body_lower  = driver.page_source[:2000].lower()
        not_found_phrases = (
            'not available', 'no articles found', 'not yet available',
            'paper is not yet', 'unavailable',
            'search proxy',             # sci-hub.in wording
            'request this article',     # sci-hub.in community-request page
        )
        if any(p in title_lower or p in body_lower for p in not_found_phrases):
            log.debug(f"  [Sci-Hub/browser] Article not in database ({base_url})")
            return 'not_found'

        # ── Step 3: If Cloudflare challenge still showing, try the search form ─
        if any(cf in title_lower for cf in ('just a moment', 'attention required',
                                             'checking your browser', 'please wait')):
            log.debug("  [Sci-Hub/browser] Cloudflare challenge — trying search form")
            time.sleep(10)
            try:
                driver.get(base_url)
                time.sleep(6)
                search = driver.find_element(
                    By.CSS_SELECTOR,
                    'input[name="request"], input[id="request"], input[type="text"]')
                search.clear()
                search.send_keys(identifier)
                search.send_keys(SeleniumKeys.RETURN)
                time.sleep(10)
            except Exception:
                pass

        # ── Step 4: Extract PDF URL from the rendered page ────────────────────
        pdf_url = None

        # Method A: JavaScript scan of live DOM (most reliable on rendered page)
        try:
            pdf_url = driver.execute_script("""
                // 1. embed / iframe / object tags
                var tags = document.querySelectorAll('embed, iframe, object');
                for (var t of tags) {
                    var src = t.getAttribute('src') || t.getAttribute('data') || '';
                    if (src && src !== '#' && (
                            src.includes('/storage/') || src.endsWith('.pdf') ||
                            src.includes('/pdf/') || src.includes('sci-hub'))) {
                        return t.src || src;
                    }
                }
                // 2. <a> download links
                var links = document.querySelectorAll('a[href]');
                for (var a of links) {
                    var h = a.getAttribute('href') || '';
                    if (h.includes('/download/') && h.includes('.pdf')) return a.href;
                    if (h.endsWith('.pdf') && h.length > 10) return a.href;
                }
                // 3. onclick="location.href='...'" patterns (Sci-Hub save button)
                var elems = document.querySelectorAll('[onclick]');
                for (var e of elems) {
                    var oc = e.getAttribute('onclick') || '';
                    var m = oc.match(/location\\.href=['"]([^'"]+)['"]/);
                    if (m) return m[1];
                }
                // 4. #save button (Sci-Hub specific)
                var save = document.getElementById('save');
                if (save) {
                    var oc2 = save.getAttribute('onclick') || '';
                    var m2 = oc2.match(/location\\.href=['"]([^'"]+)['"]/);
                    if (m2) return m2[1];
                    if (save.href) return save.href;
                }
                return null;
            """)
        except Exception:
            pass

        # Method B: BeautifulSoup on static page source (backup)
        if not pdf_url:
            soup = BeautifulSoup(driver.page_source, 'html.parser')
            for tag_name in ('embed', 'object', 'iframe'):
                for tag in soup.find_all(tag_name):
                    src = tag.get('src') or tag.get('data') or ''
                    if src and src != '#' and (
                        '/storage/' in src or src.endswith('.pdf') or '/pdf/' in src
                    ):
                        pdf_url = src
                        break
                if pdf_url:
                    break
            if not pdf_url:
                for a in soup.find_all('a', href=True):
                    href = a['href']
                    if ('/download/' in href and '.pdf' in href) or \
                       (href.endswith('.pdf') and len(href) > 10):
                        pdf_url = href
                        break

        # Method C: Click the #save / download button; check for triggered download
        if not pdf_url:
            try:
                btn = driver.find_element(
                    By.CSS_SELECTOR,
                    '#save, button[id="save"], a[id="download"], '
                    'a[href$=".pdf"], button[onclick*="location"]')
                onclick = btn.get_attribute('onclick') or ''
                href    = btn.get_attribute('href') or ''
                m = re.search(r"location\.href=['\"]([^'\"]+)['\"]", onclick)
                if m:
                    pdf_url = m.group(1)
                elif href and (href.endswith('.pdf') or '/download/' in href):
                    pdf_url = href
                else:
                    btn.click()
                    time.sleep(8)
                    # Check if the browser auto-downloaded a PDF
                    for fn in sorted(os.listdir(download_dir),
                                     key=lambda f: os.path.getmtime(
                                         os.path.join(download_dir, f)),
                                     reverse=True):
                        if fn.lower().endswith('.pdf') and not fn.endswith('.crdownload'):
                            fp = os.path.join(download_dir, fn)
                            if time.time() - os.path.getmtime(fp) < 30 and \
                               is_valid_pdf(fp):
                                os.rename(fp, save_path)
                                return True
            except Exception:
                pass

        # ── Step 5: Download the PDF ──────────────────────────────────────────
        if pdf_url:
            if pdf_url.startswith('//'):
                pdf_url = 'https:' + pdf_url
            elif pdf_url.startswith('/'):
                pdf_url = f'{base_url}{pdf_url}'
            pdf_url = pdf_url.split('#')[0]

            log.info(f"  [Sci-Hub/browser] PDF URL: {pdf_url[:80]}")

            # Transfer browser cookies → requests session (needed for CDN auth)
            for cookie in driver.get_cookies():
                session.cookies.set(cookie['name'], cookie['value'],
                                    domain=cookie.get('domain', ''))

            # Primary: download via requests (fast, respects cookies)
            if try_download_pdf(pdf_url, save_path, session, verify_ssl=False):
                return True

            # Fallback: navigate browser to the PDF URL and wait for auto-download
            driver.get(pdf_url)
            time.sleep(10)
            for fn in sorted(os.listdir(download_dir),
                             key=lambda f: os.path.getmtime(os.path.join(download_dir, f)),
                             reverse=True):
                if fn.lower().endswith('.pdf') and not fn.endswith('.crdownload'):
                    fp = os.path.join(download_dir, fn)
                    if time.time() - os.path.getmtime(fp) < 30 and is_valid_pdf(fp):
                        os.rename(fp, save_path)
                        return True

    except Exception as e:
        log.debug(f"  Sci-Hub browser error ({base_url}): {e}")
    return False


# ─── Anna's Archive API ──────────────────────────────────────────────────────

def try_annas_archive_isbn(isbn: str, save_path: str,
                           session: requests.Session) -> bool:
    """Search Anna's Archive by ISBN and download the first PDF result."""
    if not isbn:
        return False
    try:
        resp = session.get(
            f'{ANNAS_ARCHIVE_BASE}/search',
            params={'q': isbn, 'ext': 'pdf'},
            timeout=30, verify=False)
        if resp.status_code != 200:
            return False
        soup = BeautifulSoup(resp.text, 'html.parser')
        # Find first result link
        result_link = soup.find('a', href=re.compile(r'/md5/'))
        if not result_link:
            return False
        md5_url = requests.compat.urljoin(ANNAS_ARCHIVE_BASE,
                                           result_link['href'])
        return _download_from_annas_page(md5_url, save_path, session)
    except Exception as e:
        log.debug(f"  Anna's Archive ISBN error: {e}")
    return False


def try_annas_archive_title(title: str, authors: str, save_path: str,
                            session: requests.Session) -> bool:
    """Search Anna's Archive by title and download best match."""
    if not title:
        return False

    last_names = []
    if authors:
        for n in str(authors).split(','):
            parts = n.strip().split()
            if parts and len(parts[-1]) > 1:
                last_names.append(parts[-1].lower())

    try:
        resp = session.get(
            f'{ANNAS_ARCHIVE_BASE}/search',
            params={'q': title, 'ext': 'pdf'},
            timeout=30, verify=False)
        if resp.status_code != 200:
            return False

        soup = BeautifulSoup(resp.text, 'html.parser')
        results = soup.find_all('a', href=re.compile(r'/md5/'))

        # Deduplicate MD5 links (each result appears twice on Anna's Archive)
        seen_md5 = set()
        unique_results = []
        for result in results:
            md5_hash = result['href'].split('/md5/')[-1].split('?')[0]
            if md5_hash not in seen_md5:
                seen_md5.add(md5_hash)
                unique_results.append(result)

        # Try results: first check for author match, then title match
        tried_urls = set()
        for result in unique_results[:5]:
            text = result.get_text(' ', strip=True).lower()
            md5_url = requests.compat.urljoin(ANNAS_ARCHIVE_BASE,
                                               result['href'])
            if md5_url in tried_urls:
                continue

            # Check if title appears in result text
            norm_title = normalize_title(title)
            if not text or norm_title not in text.replace(',', ' ').lower():
                if text and len(text) > 10:
                    continue

            tried_urls.add(md5_url)
            log.info(f"  [Anna's Archive] Trying MD5: {md5_url.split('/')[-1][:16]}...")
            if _download_from_annas_page(md5_url, save_path, session):
                return True

            if len(tried_urls) >= 2:
                break

    except Exception as e:
        log.debug(f"  Anna's Archive title search error: {e}")
    return False


def _download_from_annas_page(md5_url: str, save_path: str,
                              session: requests.Session) -> bool:
    """Visit an Anna's Archive MD5 page and find/download the PDF.
    Prioritizes external links (libgen) which don't require membership."""
    try:
        resp = session.get(md5_url, timeout=30, verify=False)
        if resp.status_code != 200:
            return False
        soup = BeautifulSoup(resp.text, 'html.parser')

        # Collect download links in priority order
        download_urls = []

        for a in soup.find_all('a', href=True):
            href = a['href']
            text = a.get_text(' ', strip=True).lower()

            # 1) IPFS gateways (direct file download, no membership)
            if 'cloudflare-ipfs.com' in href or 'gateway.ipfs.io' in href \
                    or 'gateway.pinata.cloud' in href:
                download_urls.append(('ipfs', href))

            # 2) libgen.pw / libgen.rs direct links
            elif 'libgen.pw' in href or 'libgen.rs' in href:
                if 'get.php' in href:
                    download_urls.append(('libgen_direct', href))

            # 3) libgen.is book page (needs a second hop)
            elif 'libgen.is/book/' in href:
                download_urls.append(('libgen_page', href))

            # 4) libgen.li ads/file page
            elif 'libgen.li/ads.php' in href or 'libgen.li/file.php' in href:
                download_urls.append(('libgen_page', href))

            # 5) library.lol direct links
            elif 'library.lol' in href:
                download_urls.append(('library_lol', href))

            # 6) Anna's Archive partner links (may need membership)
            elif '/fast_download/' in href and '?' not in href:
                download_urls.append(('partner', href))
            elif '/slow_download/' in href:
                download_urls.append(('partner', href))

        for link_type, dl_url in download_urls[:4]:
            if dl_url.startswith('/'):
                dl_url = requests.compat.urljoin(ANNAS_ARCHIVE_BASE, dl_url)

            try:
                if link_type == 'ipfs':
                    # IPFS: direct download
                    if try_download_pdf(dl_url, save_path, session,
                                       verify_ssl=False):
                        return True

                elif link_type in ('libgen_direct', 'library_lol'):
                    # Direct GET link
                    if try_download_pdf(dl_url, save_path, session,
                                       verify_ssl=False):
                        return True

                elif link_type == 'libgen_page':
                    # Libgen HTML page — find inner download link (get.php)
                    dl_resp = session.get(dl_url, timeout=20, verify=False)
                    if dl_resp.status_code != 200:
                        continue
                    inner_soup = BeautifulSoup(dl_resp.text, 'html.parser')

                    inner_urls = []
                    for inner_a in inner_soup.find_all('a', href=True):
                        ih = inner_a['href']
                        it = inner_a.get_text(' ', strip=True)
                        # get.php with key — this is the actual download
                        if 'get.php' in ih:
                            if ih.startswith('http'):
                                inner_urls.insert(0, ih)  # Priority
                            else:
                                p = urlparse(dl_url)
                                inner_urls.insert(0,
                                    f"{p.scheme}://{p.netloc}/{ih.lstrip('/')}")
                        # IPFS gateways
                        elif 'cloudflare-ipfs.com' in ih or 'ipfs.io' in ih:
                            inner_urls.append(ih)
                        # Other download links
                        elif it.upper() in ('GET', 'DOWNLOAD'):
                            if ih.startswith('http'):
                                inner_urls.append(ih)
                            elif ih.startswith('/'):
                                p = urlparse(dl_url)
                                inner_urls.append(
                                    f"{p.scheme}://{p.netloc}{ih}")

                    for inner_url in inner_urls[:4]:
                        if try_download_pdf(inner_url, save_path, session,
                                           verify_ssl=False):
                            return True

                elif link_type == 'partner':
                    # Anna's Archive partner — may need membership
                    dl_resp = session.get(dl_url, timeout=DOWNLOAD_TIMEOUT,
                                         verify=False, allow_redirects=True)
                    if dl_resp.status_code == 200:
                        ct = dl_resp.headers.get('Content-Type', '').lower()
                        if 'pdf' in ct or 'octet-stream' in ct:
                            with open(save_path, 'wb') as f:
                                f.write(dl_resp.content)
                            if is_valid_pdf(save_path):
                                return True
                            _remove_if_exists(save_path)

            except Exception:
                continue

    except Exception as e:
        log.debug(f"  Anna's Archive page error: {e}")
    return False


# ─── Sci-Hub local library ────────────────────────────────────────────────────

def try_scihub_local(identifier: str, save_path: str) -> bool:
    """Fast Sci-Hub attempt using the local scihub.py library (no browser needed)."""
    if not SCIHUB_LOCAL_AVAILABLE or not identifier:
        return False
    try:
        sh  = _SciHub()
        res = sh.fetch(identifier)
        if res and 'pdf' in res and res['pdf']:
            with open(save_path, 'wb') as f:
                f.write(res['pdf'])
            if is_valid_pdf(save_path):
                log.info(f"  [Sci-Hub/local] Downloaded via: {res.get('url', '')[:80]}")
                return True
            _remove_if_exists(save_path)
    except Exception as e:
        log.debug(f"  Sci-Hub local error: {e}")
    return False


# ─── Anna's Archive RapidAPI ──────────────────────────────────────────────────

def try_annas_archive_rapidapi(title: str, authors: str, save_path: str,
                                session: requests.Session) -> bool:
    """Search Anna's Archive via RapidAPI — book endpoint first, then journal."""
    if not title or not ANNAS_RAPIDAPI_KEY:
        return False

    last_names = []
    for n in str(authors or '').split(','):
        parts = n.strip().split()
        if parts and len(parts[-1]) > 1:
            last_names.append(parts[-1].lower())

    def _download_md5(md5: str, fmt: str) -> bool:
        endpoint = ('https://annas-archive-api.p.rapidapi.com/download/journal'
                    if fmt and fmt.lower() not in ('pdf',)
                    else 'https://annas-archive-api.p.rapidapi.com/download')
        try:
            resp = requests.get(endpoint, headers=ANNAS_RAPIDAPI_HEADERS,
                                params={'md5': md5}, timeout=30)
            if resp.status_code == 200:
                data = resp.json()
                if data and isinstance(data, list) and data[0]:
                    return try_download_pdf(data[0], save_path, session,
                                            verify_ssl=False)
        except Exception as e:
            log.debug(f"  [AA/RapidAPI] Download error: {e}")
        return False

    def _search_endpoint(url: str, params: dict) -> tuple[str | None, str | None]:
        """Returns (md5, format) of the best-matching result, or (None, None)."""
        try:
            resp = requests.get(url, headers=ANNAS_RAPIDAPI_HEADERS,
                                params=params, timeout=30)
            if resp.status_code != 200:
                return None, None
            for book in resp.json().get('books', []):
                author_field = (book.get('author') or '').lower()
                if not last_names or any(ln in author_field for ln in last_names):
                    return book.get('md5'), book.get('format')
        except Exception as e:
            log.debug(f"  [AA/RapidAPI] Search error: {e}")
        return None, None

    # Book search
    log.info(f"  [AA/RapidAPI] Book search: {title[:60]}")
    md5, fmt = _search_endpoint(
        'https://annas-archive-api.p.rapidapi.com/search',
        {'q': title, 'skip': '0', 'limit': '20', 'ext': 'pdf,epub',
         'sort': 'mostRelevant', 'source': 'libgenLi,libgenRs'})
    if md5 and _download_md5(md5, fmt):
        return True

    # Journal search
    log.info(f"  [AA/RapidAPI] Journal search: {title[:60]}")
    md5, fmt = _search_endpoint(
        'https://annas-archive-api.p.rapidapi.com/search/journal',
        {'q': title, 'skip': '0', 'limit': '20',
         'sort': 'mostRelevant', 'source': 'libgenLi,zLibrary'})
    if md5 and _download_md5(md5, fmt):
        return True

    return False


# ─── LibGen ───────────────────────────────────────────────────────────────────

def try_libgen(title: str, authors: str, save_path: str,
               session: requests.Session) -> bool:
    """Search LibGen by title + author using libgen_api_enhanced, then download."""
    if not LIBGEN_AVAILABLE or not title:
        return False

    last_names = []
    for n in str(authors or '').split(','):
        parts = n.strip().split()
        if parts and len(parts[-1]) > 1:
            last_names.append(parts[-1].lower())

    norm = re.sub(r'\W+', ' ', title.lower()).strip()

    def _download_book(book) -> bool:
        """Try all mirrors on a libgen_api_enhanced Book object."""
        # Prefer resolved direct download link
        try:
            book.resolve_direct_download_link()
            if book.resolved_download_link:
                if try_download_pdf(book.resolved_download_link, save_path,
                                    session, verify_ssl=False):
                    return True
        except Exception:
            pass
        # Try all mirrors
        for mirror in (book.mirrors or []):
            try:
                # Mirror URLs are often HTML pages; follow the get.php link inside
                resp = session.get(mirror, timeout=20, verify=False)
                if resp.status_code != 200:
                    continue
                ct = resp.headers.get('Content-Type', '').lower()
                if 'application/pdf' in ct or 'octet-stream' in ct:
                    with open(save_path, 'wb') as f:
                        f.write(resp.content)
                    if is_valid_pdf(save_path):
                        return True
                    _remove_if_exists(save_path)
                    continue
                # Parse for get.php link
                soup = BeautifulSoup(resp.text, 'html.parser')
                for a in soup.find_all('a', href=True):
                    href = a['href']
                    if 'get.php' in href:
                        if not href.startswith('http'):
                            p = urlparse(mirror)
                            href = f"{p.scheme}://{p.netloc}/{href.lstrip('/')}"
                        if try_download_pdf(href, save_path, session,
                                            verify_ssl=False):
                            return True
            except Exception:
                continue
        return False

    # Try mirrors in order; libgen.li is often blocked, libgen.is is more reliable
    _LIBGEN_MIRRORS = ['is', 'rs', 'li']
    lg = None
    for _mirror in _LIBGEN_MIRRORS:
        try:
            _test = _LibgenSearch(mirror=_mirror)
            # Quick connectivity probe — avoid using a mirror that's down
            import urllib.request
            urllib.request.urlopen(f'https://libgen.{_mirror}/', timeout=5)
            lg = _test
            break
        except Exception:
            continue
    if lg is None:
        log.debug('  LibGen: no reachable mirror found, skipping')
        return False

    # Strategy A: search_title
    try:
        hits = lg.search_title(title)
        filtered = [b for b in hits
                    if norm in re.sub(r'\W+', ' ', b.title.lower()).strip()]
        for book in (filtered or hits)[:8]:
            author_lc = book.author.lower()
            if not last_names or any(ln in author_lc for ln in last_names):
                log.info(f"  [LibGen] Trying: {book.title[:60]!r} ({book.author[:40]})")
                if _download_book(book):
                    return True
    except Exception as e:
        log.debug(f"  LibGen title search error: {e}")

    # Strategy B: search_author (for each last name)
    for ln in last_names[:2]:
        try:
            auth_hits = lg.search_author(ln)
            for book in auth_hits[:6]:
                if norm in re.sub(r'\W+', ' ', book.title.lower()).strip():
                    log.info(f"  [LibGen/author] Trying: {book.title[:60]!r}")
                    if _download_book(book):
                        return True
        except Exception as e:
            log.debug(f"  LibGen author search error ({ln}): {e}")

    return False


# ─── Garbage World API ────────────────────────────────────────────────────────

def try_garbage_world(title: str, save_path: str, session: requests.Session) -> bool:
    """Garbage World public API — search by title, download first match."""
    if not title:
        return False
    try:
        q = requests.utils.quote(title)
        resp = session.get(f'https://garbage.world/api/library/search?query={q}',
                           timeout=20)
        if resp.status_code != 200:
            return False
        data = resp.json()
        if not isinstance(data, list):
            return False
        for item in data:
            name = (item.get('name') or item.get('title') or '').strip()
            if title.lower() in name.lower():
                dl_url = f'https://garbage.world/api/library/download?name={requests.utils.quote(name)}'
                log.info(f"  [Garbage World] Trying: {name[:60]!r}")
                if try_download_pdf(dl_url, save_path, session):
                    return True
    except Exception as e:
        log.debug(f"  Garbage World error: {e}")
    return False


# ─── Domain-specific handlers ─────────────────────────────────────────────────

def try_openedition(url: str, save_path: str, session: requests.Session) -> bool:
    """OpenEdition: try direct PDF URL construction first, then scrape."""
    log.info(f'  [OpenEdition] Trying {url[:80]}')

    # Strategy 1: direct /pdf/ URL construction
    # journals.openedition.org/xxx/1234  →  journals.openedition.org/xxx/pdf/1234
    m = re.search(r'(journals\.openedition\.org/[^/]+)/(\d+)', url)
    if m:
        pdf_url = f'https://{m.group(1)}/pdf/{m.group(2)}'
        log.info(f'  [OpenEdition] Trying direct PDF: {pdf_url}')
        if try_download_pdf(pdf_url, save_path, session):
            return True

    # Strategy 2: scrape page for PDF link
    try:
        resp = session.get(url, timeout=20,
                           headers={'Accept': 'text/html,application/xhtml+xml',
                                    'Accept-Language': 'fr,en;q=0.9'})
        if resp.status_code == 200:
            soup = BeautifulSoup(resp.text, 'html.parser')
            # Pattern: /xxx/pdf/1234
            for a in soup.find_all('a', href=re.compile(r'/pdf/\d+')):
                pdf_url = requests.compat.urljoin(url, a['href'])
                log.info(f'  [OpenEdition] Found PDF link: {pdf_url[:80]}')
                if try_download_pdf(pdf_url, save_path, session):
                    return True
            # Fallback: any .pdf link
            for a in soup.find_all('a', href=True):
                href = a['href']
                if href.lower().endswith('.pdf'):
                    pdf_url = requests.compat.urljoin(url, href)
                    if try_download_pdf(pdf_url, save_path, session):
                        return True
    except Exception as e:
        log.debug(f'  [OpenEdition] error: {e}')

    log.info(f'  [OpenEdition] FAILED — no PDF found for {url[:80]}')
    return False


def try_persee(url: str, save_path: str, session: requests.Session) -> bool:
    """Persee: try three strategies to get the PDF.

    1. GET  /docAsPDF/…pdf  (works when no captcha is shown)
    2. POST to the #pdf-download-form action URL (bypasses the captcha gate
       for many articles — the form action *is* the PDF URL)
    3. Scrape the page for any docAsPDF or .pdf link
    """
    # Strategy 1: simple URL rewrite GET
    pdf_url = re.sub(r'/doc/', '/docAsPDF/', url)
    if not pdf_url.lower().endswith('.pdf'):
        pdf_url = pdf_url.rstrip('/') + '.pdf'
    log.info(f'  [Persee] GET {pdf_url[:80]}')
    if try_download_pdf(pdf_url, save_path, session):
        return True

    # Strategy 2: scrape page → find form action → POST to it
    try:
        resp = session.get(url, timeout=20,
                           headers={'Referer': 'https://www.persee.fr/'})
        if resp.status_code == 200:
            soup = BeautifulSoup(resp.text, 'html.parser')

            # 2a: PDF download form (id="pdf-download-form" or action*=docAsPDF)
            form = (soup.find('form', id='pdf-download-form') or
                    soup.find('form', action=re.compile(r'docAsPDF', re.I)))
            if form and form.get('action'):
                action_url = form['action']
                if not action_url.startswith('http'):
                    action_url = requests.compat.urljoin(url, action_url)
                log.info(f'  [Persee] POST {action_url[:80]}')
                try:
                    post_resp = session.post(
                        action_url, data={},
                        headers={'Referer': url, 'Origin': 'https://www.persee.fr'},
                        timeout=30, stream=True, verify=False)
                    if post_resp.status_code == 200:
                        ct = post_resp.headers.get('Content-Type', '').lower()
                        if 'pdf' in ct or 'octet-stream' in ct:
                            with open(save_path, 'wb') as fh:
                                for chunk in post_resp.iter_content(8192):
                                    fh.write(chunk)
                            if is_valid_pdf(save_path):
                                return True
                            _remove_if_exists(save_path)
                        # If response is HTML (captcha shown), fall through
                except Exception as e:
                    log.debug(f'  [Persee] POST error: {e}')

            # 2b: any docAsPDF or .pdf link on the page
            for a in soup.find_all('a', href=True):
                href = a['href']
                if 'docAsPDF' in href or href.lower().endswith('.pdf'):
                    if not href.startswith('http'):
                        href = requests.compat.urljoin(url, href)
                    if try_download_pdf(href, save_path, session):
                        return True
    except Exception as e:
        log.debug(f'  [Persee] scrape error: {e}')
    return False


def try_hal(url: str, save_path: str, session: requests.Session) -> bool:
    """HAL Science / HAL open-access repositories.
    The /document endpoint is a direct redirect to the deposited PDF."""
    log.info(f'  [HAL] Trying {url[:80]}')
    base = re.sub(r'/(document|file|pdf)$', '', url.rstrip('/'))

    # Strategy 1: /document and /file suffixes — both redirect to the PDF
    for suffix in ['/document', '/file']:
        candidate = base + suffix
        log.info(f'  [HAL] Trying {candidate[:80]}')
        if try_download_pdf(candidate, save_path, session):
            return True

    # Strategy 2: HAL API — resolve the HAL ID to get the PDF URL
    # hal-XXXXXXX or hal.science/hal-XXXXXXX → api.archives-ouvertes.fr
    m = re.search(r'(hal-\d+)', url, re.IGNORECASE)
    if m:
        hal_id = m.group(1)
        api_url = (f'https://api.archives-ouvertes.fr/search/'
                   f'?q=halId_s:{hal_id}&fl=fileMain_s&wt=json')
        try:
            r = session.get(api_url, timeout=15)
            data = r.json()
            docs = data.get('response', {}).get('docs', [])
            if docs and docs[0].get('fileMain_s'):
                pdf_url = docs[0]['fileMain_s']
                log.info(f'  [HAL] API found PDF: {pdf_url[:80]}')
                if try_download_pdf(pdf_url, save_path, session):
                    return True
        except Exception as e:
            log.debug(f'  [HAL] API error: {e}')

    # Strategy 3: scrape the page for any PDF link
    try:
        resp = session.get(base, timeout=20)
        if resp.status_code == 200:
            soup = BeautifulSoup(resp.text, 'html.parser')
            for a in soup.find_all('a', href=True):
                href = a['href']
                text = a.get_text(' ', strip=True).lower()
                if href.lower().endswith('.pdf') or 'télécharger' in text or \
                        'download' in text or '/document' in href:
                    if not href.startswith('http'):
                        href = requests.compat.urljoin(base, href)
                    log.info(f'  [HAL] Scrape found link: {href[:80]}')
                    if try_download_pdf(href, save_path, session):
                        return True
    except Exception as e:
        log.debug(f'  [HAL] scrape error: {e}')

    log.info(f'  [HAL] FAILED — no PDF found for {url[:80]}')
    return False


def try_jstor(url: str, save_path: str, session: requests.Session) -> bool:
    """JSTOR: extract the implicit 10.2307/XXXX DOI and try Sci-Hub with it."""
    m = re.search(r'jstor\.org/stable/(\d+)', url)
    if m:
        doi = f'10.2307/{m.group(1)}'
        log.info(f'  [JSTOR] Extracted DOI: {doi}')
        return try_scihub(doi, save_path, session)
    return False


def try_acm(url: str, save_path: str, row: dict,
            session: requests.Session) -> bool:
    """ACM Digital Library: extract DOI and try Sci-Hub / Anna's Archive."""
    log.info(f'  [ACM] Trying {url[:80]}')

    # Strategy 1: extract DOI from URL and send to Sci-Hub
    # dl.acm.org/doi/10.1145/XXXXXXX  or  dl.acm.org/doi/abs/10.1145/XXXXXXX
    doi_match = re.search(r'dl\.acm\.org/doi/(?:abs/|full/|pdf/)?'
                          r'(10\.\d{4,}/[^\s?#&]+)', url)
    if doi_match:
        doi = doi_match.group(1).rstrip('/')
        log.info(f'  [ACM] Extracted DOI: {doi}')
        if try_scihub(doi, save_path, session):
            return True
        # Strategy 2: try the ACM direct PDF URL
        pdf_url = f'https://dl.acm.org/doi/pdf/{doi}'
        log.info(f'  [ACM] Trying direct PDF: {pdf_url[:80]}')
        if try_download_pdf(pdf_url, save_path, session):
            return True
        # Strategy 3: Anna's Archive by title
        title = row.get('Title') or ''
        authors = row.get('Authors') or ''
        if title:
            log.info(f"  [ACM] Trying Anna's Archive: {title[:60]}")
            if try_annas_archive_title(title, authors, save_path, session):
                return True

    log.info(f'  [ACM] FAILED — no PDF found for {url[:80]}')
    return False


def try_cairn(url: str, save_path: str, session: requests.Session) -> bool:
    """Cairn.info: try several PDF URL patterns then scrape."""
    log.info(f'  [Cairn] Trying {url[:80]}')
    base = url.split('?')[0].rstrip('/')

    # Strategy 1: texte-integral → append /pdf
    if 'texte-integral' in url:
        pdf_url = base + '/pdf?lang=fr'
        log.info(f'  [Cairn] texte-integral PDF: {pdf_url[:80]}')
        if try_download_pdf(pdf_url, save_path, session):
            return True
        # Also try without lang param
        if try_download_pdf(base + '/pdf', save_path, session):
            return True

    # Strategy 2: article page → append /epub or /pdf
    # e.g. shs.cairn.info/revue-xxx-2020-1-page-1 → .../pdf
    for suffix in ['/pdf', '/epub']:
        if not base.endswith(suffix):
            candidate = base + suffix
            log.info(f'  [Cairn] Trying {candidate[:80]}')
            if try_download_pdf(candidate, save_path, session):
                return True

    # Strategy 3: scrape page for PDF link
    try:
        headers = {
            'Accept': 'text/html,application/xhtml+xml',
            'Accept-Language': 'fr,en;q=0.9',
            'Referer': 'https://shs.cairn.info/',
        }
        resp = session.get(url, timeout=20, headers=headers)
        if resp.status_code == 200:
            soup = BeautifulSoup(resp.text, 'html.parser')
            # Look for links with "PDF", "Télécharger", or href*=pdf
            for a in soup.find_all('a', href=True):
                href = a['href']
                text = a.get_text(' ', strip=True).lower()
                if ('pdf' in href.lower() or 'pdf' in text or
                        'télécharger' in text or 'download' in text):
                    if not href.startswith('http'):
                        href = requests.compat.urljoin(url, href)
                    log.info(f'  [Cairn] Found link: {href[:80]}')
                    if try_download_pdf(href, save_path, session):
                        return True
    except Exception as e:
        log.debug(f'  [Cairn] scrape error: {e}')

    log.info(f'  [Cairn] FAILED — no PDF found for {url[:80]}')
    return False


def _extract_taylor_francis_isbn(url: str) -> str | None:
    """
    Extract ISBN from Taylor & Francis book/chapter URLs.
    Books:    /books/mono/10.4324/9780429306259/title → 9780429306259
    Chapters: /chapters/edit/10.4324/9780203977415-5/title → 9780203977415
    """
    if '/books/' in url:
        # Books: ISBN is the number between /10.XXXX/ and the next /
        match = re.search(r'/10\.\d+/(\d{10,13})(?:/|$)', url)
        if match:
            return match.group(1)
    elif '/chapters/' in url:
        # Chapters: ISBN is the number before the -XX suffix
        match = re.search(r'/10\.\d+/(\d{10,13})-', url)
        if match:
            return match.group(1)
    # Fallback: any 10-13 digit number after /10.XXXX/
    match = re.search(r'/10\.\d+/(\d{10,13})', url)
    if match:
        return match.group(1)
    return None


def try_taylor_francis(url: str, save_path: str, row: dict,
                       session: requests.Session) -> bool:
    """Taylor & Francis books/chapters: extract ISBN, search Anna's Archive."""
    isbn = _extract_taylor_francis_isbn(url)
    if isbn:
        log.info(f"  [T&F] Extracted ISBN: {isbn}")
        if try_annas_archive_isbn(isbn, save_path, session):
            return True
    # Fallback: search by title on Anna's Archive
    title = row.get('Title') or ''
    authors = row.get('Authors') or ''
    if title:
        log.info(f"  [T&F] Trying Anna's Archive title search")
        return try_annas_archive_title(title, authors, save_path, session)
    return False


def try_ssrn(url: str, save_path: str, session: requests.Session) -> bool:
    """SSRN: extract the Delivery.cfm link (rendered by JS) via Selenium,
    or fall back to requests scraping and URL construction."""
    log.info(f'  [SSRN] Trying {url[:80]}')

    def _find_delivery_link(soup: BeautifulSoup, base_url: str) -> str | None:
        """Return the absolute Delivery.cfm PDF URL from parsed HTML, or None."""
        # <a href="Delivery.cfm/SSRN_IDxxxxxx_codeYYYYY.pdf?...">
        dl_link = soup.find('a', href=re.compile(r'Delivery\.cfm', re.IGNORECASE))
        if dl_link and dl_link.get('href'):
            href = dl_link['href']
            if not href.startswith('http'):
                href = requests.compat.urljoin(base_url, href)
            return href
        # "Download This Paper" text
        dl_btn = soup.find('a', string=re.compile(r'Download This Paper', re.I))
        if dl_btn and dl_btn.get('href'):
            href = dl_btn['href']
            if not href.startswith('http'):
                href = requests.compat.urljoin(base_url, href)
            return href
        # data-abstract-id attribute
        dl_btn2 = soup.find('a', attrs={'data-abstract-id': True})
        if dl_btn2 and dl_btn2.get('href'):
            href = dl_btn2['href']
            if not href.startswith('http'):
                href = requests.compat.urljoin(base_url, href)
            return href
        return None

    # ── Method 1: plain requests (works if Delivery.cfm is in the SSR HTML) ──
    try:
        headers = {
            'User-Agent': ('Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) '
                           'AppleWebKit/537.36 (KHTML, like Gecko) '
                           'Chrome/120.0.0.0 Safari/537.36'),
            'Accept': 'text/html,application/xhtml+xml',
        }
        resp = session.get(url, timeout=30, headers=headers)
        if resp.status_code == 200:
            soup = BeautifulSoup(resp.text, 'html.parser')
            pdf_url = _find_delivery_link(soup, url)
            if pdf_url:
                log.info(f'  [SSRN] requests: found {pdf_url[:80]}')
                if try_download_pdf(pdf_url, save_path, session):
                    return True
    except Exception as e:
        log.debug(f'  [SSRN] requests error: {e}')

    # ── Method 2: Selenium (JS-rendered page exposes the real code in the link) ──
    if SELENIUM_AVAILABLE:
        driver = None
        try:
            driver = _get_browser(os.path.dirname(save_path))
            if driver:
                log.info(f'  [SSRN] Selenium loading page…')
                driver.get(url)
                # Wait for the download button to appear
                try:
                    WebDriverWait(driver, 15).until(
                        EC.presence_of_element_located(
                            (By.XPATH,
                             "//a[contains(@href,'Delivery.cfm') or "
                             "contains(text(),'Download This Paper')]")))
                except TimeoutException:
                    pass
                time.sleep(2)
                soup = BeautifulSoup(driver.page_source, 'html.parser')
                # Transfer cookies to requests session
                for cookie in driver.get_cookies():
                    session.cookies.set(cookie['name'], cookie['value'],
                                        domain=cookie.get('domain', ''))
                pdf_url = _find_delivery_link(soup, url)
                if pdf_url:
                    log.info(f'  [SSRN] Selenium: found {pdf_url[:80]}')
                    if try_download_pdf(pdf_url, save_path, session):
                        return True
        except Exception as e:
            log.debug(f'  [SSRN] Selenium error: {e}')
        finally:
            if driver:
                try:
                    driver.quit()
                except Exception:
                    pass

    # ── Method 3: constructed URL (abstract_id only — code suffix is guessed) ──
    match = re.search(r'abstract[_=]?(?:id)?[=]?(\d+)', url, re.IGNORECASE)
    if not match:
        match = re.search(r'/(\d{6,})', url)
    if match:
        abstract_id = match.group(1)
        # Try mirid=1 (full paper) — the code suffix is session-specific, but
        # sometimes servers accept the guessed form (code1) for open-access papers.
        pdf_url = (f'https://papers.ssrn.com/sol3/Delivery.cfm/'
                   f'SSRN_ID{abstract_id}_code1.pdf'
                   f'?abstractid={abstract_id}&mirid=1')
        log.info(f'  [SSRN] constructed URL for abstract {abstract_id}')
        if try_download_pdf(pdf_url, save_path, session):
            return True

    log.info(f'  [SSRN] FAILED — no PDF found for {url[:80]}')
    return False


def try_springer_chapter(url: str, save_path: str,
                         session: requests.Session) -> bool:
    """Springer: check for 'Book PDF', 'Chapter PDF', or 'Download PDF' buttons.
    The button is <a data-book-pdf="true" href="/content/pdf/..."> or similar."""
    try:
        resp = session.get(url, timeout=30)
        if resp.status_code != 200:
            return False
        soup = BeautifulSoup(resp.text, 'html.parser')

        # Method 1: <a data-book-pdf="true" href="/content/pdf/...">
        book_pdf = soup.find('a', attrs={'data-book-pdf': 'true'})
        if book_pdf and book_pdf.get('href'):
            pdf_url = book_pdf['href']
            if pdf_url.startswith('/'):
                pdf_url = f'https://link.springer.com{pdf_url}'
            log.info(f"  [Springer] Book PDF: {pdf_url[:80]}")
            if try_download_pdf(pdf_url, save_path, session):
                return True

        # Method 2: <a data-test="pdf-link"> (chapter or article)
        pdf_link = soup.find('a', attrs={'data-test': 'pdf-link'})
        if pdf_link and pdf_link.get('href'):
            pdf_url = pdf_link['href']
            if pdf_url.startswith('/'):
                pdf_url = f'https://link.springer.com{pdf_url}'
            log.info(f"  [Springer] PDF link: {pdf_url[:80]}")
            if try_download_pdf(pdf_url, save_path, session):
                return True

        # Method 3: <a class="c-pdf-download__link" href="/content/pdf/...">
        pdf_dl = soup.find('a', class_=re.compile(r'c-pdf-download'))
        if pdf_dl and pdf_dl.get('href'):
            pdf_url = pdf_dl['href']
            if pdf_url.startswith('/'):
                pdf_url = f'https://link.springer.com{pdf_url}'
            log.info(f"  [Springer] c-pdf-download: {pdf_url[:80]}")
            if try_download_pdf(pdf_url, save_path, session):
                return True

        # Method 4: any link with "pdf" in both text and href
        for a in soup.find_all('a', href=True):
            href = a['href']
            text = a.get_text(' ', strip=True).lower()
            if ('book pdf' in text or 'chapter pdf' in text or
                    ('download' in text and 'pdf' in text)):
                pdf_url = href
                if pdf_url.startswith('/'):
                    pdf_url = f'https://link.springer.com{pdf_url}'
                log.info(f"  [Springer] Found: {pdf_url[:80]}")
                if try_download_pdf(pdf_url, save_path, session):
                    return True

        # Method 5: construct PDF URL from DOI in the URL
        doi_match = re.search(r'(10\.\d{4,9}/[^\s,;\"\'#?]+)', url)
        if doi_match:
            doi = doi_match.group(1)
            for pattern in [
                f'https://link.springer.com/content/pdf/{doi}.pdf',
                f'https://link.springer.com/content/pdf/{doi}',
            ]:
                log.info(f"  [Springer] Trying constructed: {pattern[:80]}")
                if try_download_pdf(pattern, save_path, session):
                    return True

    except Exception as e:
        log.debug(f"  Springer error: {e}")
    return False


def try_muse(url: str, save_path: str, session: requests.Session) -> bool:
    """MUSE: look for 'Download PDF' link.
    Button: <a href="/pub/26/article/38003/pdf" class="summarylinkboxdownload">
    Also handles /edited_volume/chapter/ URLs."""
    try:
        resp = session.get(url, timeout=30)
        if resp.status_code != 200:
            return False
        soup = BeautifulSoup(resp.text, 'html.parser')

        # Method 1: <a class="summarylinkboxdownload" href="...pdf">
        pdf_link = soup.find('a', class_='summarylinkboxdownload')
        if pdf_link and pdf_link.get('href'):
            pdf_url = pdf_link['href']
            if not pdf_url.startswith('http'):
                pdf_url = f'https://muse.jhu.edu{pdf_url}'
            log.info(f"  [MUSE] summarylinkboxdownload: {pdf_url[:80]}")
            if try_download_pdf(pdf_url, save_path, session):
                return True

        # Method 2: href matching /pub/XX/article/XXXX/pdf or /chapter/XXXX/pdf
        for pattern in [r'/pub/\d+/article/\d+/pdf',
                       r'/pub/\d+/edited_volume/chapter/\d+/pdf',
                       r'/chapter/\d+/pdf']:
            pdf_link = soup.find('a', href=re.compile(pattern))
            if pdf_link and pdf_link.get('href'):
                pdf_url = pdf_link['href']
                if not pdf_url.startswith('http'):
                    pdf_url = f'https://muse.jhu.edu{pdf_url}'
                log.info(f"  [MUSE] Found: {pdf_url[:80]}")
                if try_download_pdf(pdf_url, save_path, session):
                    return True

        # Method 3: any link with "Download PDF" or "PDF" text
        for a in soup.find_all('a', href=True):
            text = a.get_text(' ', strip=True).lower()
            if 'download pdf' in text or text.strip() == 'pdf':
                href = a['href']
                if not href.startswith('http'):
                    href = f'https://muse.jhu.edu{href}'
                if try_download_pdf(href, save_path, session):
                    return True

        # Method 4: construct PDF URL from the article/chapter URL
        # e.g. /pub/6/article/447618/summary → /pub/6/article/447618/pdf
        m = re.search(r'(muse\.jhu\.edu/pub/\d+/(?:article|edited_volume/chapter)/\d+)', url)
        if m:
            pdf_url = f'https://{m.group(1)}/pdf'
            log.info(f"  [MUSE] Constructed: {pdf_url[:80]}")
            if try_download_pdf(pdf_url, save_path, session):
                return True

    except Exception as e:
        log.debug(f"  MUSE error: {e}")
    return False


def try_google_books(url: str, save_path: str, row: dict,
                     session: requests.Session) -> bool:
    """Google Books: search title on Anna's Archive."""
    title = row.get('Title') or ''
    authors = row.get('Authors') or ''
    if title:
        log.info(f"  [Google Books] Searching Anna's Archive for title")
        return try_annas_archive_title(title, authors, save_path, session)
    return False


# ─── KB Royal Danish Library (soeg.kb.dk) ────────────────────────────────────

# KB Primo search URL template
_KB_SEARCH_URL = (
    'https://soeg.kb.dk/discovery/search'
    '?query=any,contains,{q}'
    '&tab=Everything'
    '&search_scope=MyInst_and_CI'
    '&vid=45KBDK_KGL:KGL'
    '&lang=en'
    '&offset=0'
)

# Remote-debugging port that Brave must be started with for CDP attach:
#   open -a "Brave Browser" --args --remote-debugging-port=9222
_KB_CDP_PORT = 9222

# Selenium wait timeout for Angular SPA rendering
_KB_WAIT_SECS = 20


def _kb_inject_brave_cookies(driver) -> int:
    """Read Brave's cookie store and inject all KB-related cookies into *driver*.

    Must be called **after** the driver has already navigated to
    https://soeg.kb.dk (or any page on that origin) so Chrome accepts cookies
    for that domain.

    Returns the number of cookies successfully injected.
    """
    if not BROWSER_COOKIE3_AVAILABLE:
        return 0

    # Domains whose cookies are relevant to a KB Primo session:
    #   soeg.kb.dk  — the Primo portal itself (carries the session token)
    #   .kb.dk      — parent domain, covers related services
    #   .wayf.dk    — Danish federated login (WAYF IdP hub)
    target_domains = ('.kb.dk', 'soeg.kb.dk', '.wayf.dk', 'wayf.dk')
    injected = 0
    try:
        all_cookies = list(_browser_cookie3.brave())
    except Exception as e:
        log.debug(f'  [KB] browser_cookie3 read error: {e}')
        return 0

    for c in all_cookies:
        dom = c.domain or ''
        if not any(dom == td or dom.endswith(td) for td in target_domains):
            continue
        cookie_dict = {
            'name':   c.name,
            'value':  c.value,
            'domain': dom.lstrip('.') or 'soeg.kb.dk',
            'path':   c.path or '/',
            'secure': bool(c.secure),
        }
        # Selenium rejects cookies that span beyond the current origin, so
        # normalise the domain to the current host when needed.
        try:
            driver.add_cookie(cookie_dict)
            injected += 1
        except Exception:
            # Try without the domain field — Chrome will scope it automatically
            try:
                no_domain = {k: v for k, v in cookie_dict.items() if k != 'domain'}
                driver.add_cookie(no_domain)
                injected += 1
            except Exception:
                pass

    return injected


def _kb_port_open(host: str = 'localhost', port: int = _KB_CDP_PORT,
                  timeout: float = 1.0) -> bool:
    """Return True if host:port accepts a TCP connection within *timeout* s."""
    import socket
    try:
        with socket.create_connection((host, port), timeout=timeout):
            return True
    except OSError:
        return False


def _kb_attach_or_new(download_dir: str):
    """Return a (driver, attached) tuple for KB Primo searches.

    Strategy order
    ──────────────
    1. CDP attach to a running Brave with --remote-debugging-port=9222
       → fully authenticated, reuses live session.
       Only attempted when the port is actually open (fast TCP probe first).
    2. Headless Chrome 148 + Brave cookie injection via browser_cookie3
       → authenticated (soeg.kb.dk session cookie transferred from Brave).
    3. Plain headless Chrome (no auth)
       → anonymous; Unpaywall/OA "Get PDF" links still work.

    ``attached=True`` only for strategy 1 — we must not quit a browser
    we didn't create.
    """
    if not SELENIUM_AVAILABLE:
        return None, False

    # ── Strategy 1: CDP attach (only if port is open) ─────────────────────────
    if _kb_port_open('localhost', _KB_CDP_PORT):
        for host in ('localhost', '127.0.0.1'):
            attach_opts = ChromeOptions()
            attach_opts.add_experimental_option('debuggerAddress',
                                                f'{host}:{_KB_CDP_PORT}')
            # Try the KB-specific ChromeDriver 148 first (matches Brave 148),
            # then fall through to the older pinned 141.
            cdrivers = []
            if os.path.exists(_KB_CHROMEDRIVER_BIN):
                cdrivers.append(_KB_CHROMEDRIVER_BIN)
            if os.path.exists(_CHROMEDRIVER_BIN):
                cdrivers.append(_CHROMEDRIVER_BIN)
            cdrivers.append(None)   # None → let Selenium Manager decide

            for cdrv_path in cdrivers:
                try:
                    svc = (ChromeService(executable_path=cdrv_path)
                           if cdrv_path else ChromeService())
                    drv = webdriver.Chrome(service=svc, options=attach_opts)
                    _   = drv.title
                    log.info(f'  [KB] Attached to Brave on {host}:{_KB_CDP_PORT} ✓')
                    return drv, True
                except Exception as e:
                    log.debug(f'  [KB] CDP attach failed ({host}, drv={cdrv_path}): {e}')
    else:
        log.debug(f'  [KB] Port {_KB_CDP_PORT} not open — skipping CDP attach')

    # ── Strategy 2 & 3: headless Chrome 148 ──────────────────────────────────
    opts = ChromeOptions()
    opts.add_argument('--headless=new')
    opts.add_argument('--no-sandbox')
    opts.add_argument('--disable-dev-shm-usage')
    opts.add_argument('--disable-gpu')
    opts.add_argument('--window-size=1920,1080')
    opts.add_argument(
        'user-agent=Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) '
        'AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36')

    # Use Chrome 148 + ChromeDriver 148 for KB — avoids the 141/148 mismatch.
    if os.path.exists(_KB_CHROME_BINARY):
        opts.binary_location = _KB_CHROME_BINARY
    elif os.path.exists(_CHROME_BINARY):
        opts.binary_location = _CHROME_BINARY

    if download_dir:
        opts.add_experimental_option('prefs', {
            'download.default_directory':     download_dir,
            'download.prompt_for_download':   False,
            'plugins.always_open_pdf_externally': True,
        })

    cdrv_path = (_KB_CHROMEDRIVER_BIN if os.path.exists(_KB_CHROMEDRIVER_BIN)
                 else _CHROMEDRIVER_BIN)
    try:
        svc = ChromeService(executable_path=cdrv_path)
        drv = webdriver.Chrome(service=svc, options=opts)
        drv.set_page_load_timeout(30)
        log.debug(f'  [KB] Headless Chrome launched (driver={os.path.basename(cdrv_path)})')
    except WebDriverException as e:
        log.debug(f'  [KB] headless browser init error: {e}')
        return None, False

    # Navigate to the origin first so add_cookie() is allowed for that domain
    try:
        drv.get('https://soeg.kb.dk')
        time.sleep(1)
    except Exception:
        pass

    if BROWSER_COOKIE3_AVAILABLE:
        n = _kb_inject_brave_cookies(drv)
        if n:
            log.info(f'  [KB] Injected {n} Brave cookie(s) into headless session ✓')
        else:
            log.info(
                '  [KB] No Brave KB cookies found — searching without login. '
                'Log in to soeg.kb.dk in Brave once to enable authenticated searches.'
            )
    else:
        log.warning(
            '  [KB] browser_cookie3 not available — searching without login. '
            'Run: pip install browser-cookie3'
        )

    return drv, False


def _kb_parse_results(driver) -> list[dict]:
    """Extract result items from the rendered Primo SPA.

    Returns a list of dicts with keys:
      title, authors, get_pdf_url, has_get_pdf, available_online_url, record_url
    """
    results = []
    try:
        # Each brief-result lives inside <prm-brief-result-container>
        items = driver.find_elements(By.CSS_SELECTOR, 'prm-brief-result-container')
        if not items:
            # Fallback: look for <li> items with data-recordid
            items = driver.find_elements(By.CSS_SELECTOR, 'li[data-recordid]')

        for item in items:
            # ── Title ──────────────────────────────────────────────────────────
            title_text = ''
            for sel in ('h3.item-title span', 'h3.item-title', '[ng-bind-html]',
                        '.item-title span'):
                try:
                    el = item.find_element(By.CSS_SELECTOR, sel)
                    title_text = el.text.strip() or el.get_attribute('innerHTML') or ''
                    title_text = re.sub(r'<[^>]+>', '', title_text).strip()
                    if title_text:
                        break
                except Exception:
                    pass

            # ── Authors ────────────────────────────────────────────────────────
            authors_text = ''
            for sel in ('[data-field-selector="creator"]',
                        '.item-details [data-field-selector]',
                        'span.creator', '.result-item-text .item-details span'):
                try:
                    el = item.find_element(By.CSS_SELECTOR, sel)
                    authors_text = el.text.strip()
                    if authors_text:
                        break
                except Exception:
                    pass

            # ── Record/full-display URL (fallback for detail-page extraction) ──
            record_url = ''
            for sel in ('h3.item-title a[href]',
                        'a.item-title[href]',
                        'a[href*="fulldisplay"]'):
                try:
                    link_el = item.find_element(By.CSS_SELECTOR, sel)
                    href = (link_el.get_attribute('href') or '').strip()
                    if href:
                        record_url = urljoin('https://soeg.kb.dk', href)
                        break
                except Exception:
                    pass

            # ── "Get PDF" / "Available Online" / "Tilgængelig online" ───────────
            pdf_url    = ''
            has_get_pdf = False
            online_url  = ''

            def _inner_text(el) -> str:
                """Return full visible text of element including nested spans."""
                try:
                    t = el.get_attribute('innerText') or el.text or ''
                    return t.strip().lower()
                except Exception:
                    return ''

            # Check every anchor inside this result card
            try:
                all_links = item.find_elements(By.CSS_SELECTOR, 'a[href]')
            except Exception:
                all_links = []

            for link_el in all_links:
                href  = (link_el.get_attribute('href') or '').strip()
                if not href or href.startswith('javascript'):
                    continue
                label = (link_el.get_attribute('aria-label') or '').lower()
                inner = _inner_text(link_el)

                # "Get PDF" — highest priority
                if ('get pdf' in label or 'get pdf' in inner
                        or href.lower().endswith('.pdf')
                        or ('/pdf' in href.lower() and 'soeg.kb.dk' not in href)):
                    has_get_pdf = True
                    pdf_url = href
                    break

                # "Available Online" / "Tilgængelig online" (Danish) / variant spellings
                _ao_tokens = ('available online', 'tilgængelig online',
                              'tilgaengelig online', 'tilgängelig online',
                              'fulltext_linktorsrc')
                if any(t in label or t in inner for t in _ao_tokens):
                    if not online_url:          # keep first match
                        online_url = href

            # Fallback: check availability-status span for "fulltext" signal.
            # If the span exists but no link was captured above, mark the item
            # so the detail-page lookup can find the link.
            if not has_get_pdf and not online_url:
                try:
                    item.find_element(
                        By.CSS_SELECTOR,
                        '.availability-status.fulltext_linktorsrc, '
                        '[class*="fulltext_linktorsrc"]')
                    has_get_pdf = True  # signal: something is available online
                except Exception:
                    pass
            # XPath fallback for "Get PDF" text
            if not has_get_pdf:
                try:
                    item.find_element(
                        By.XPATH,
                        ".//*[self::a or self::button]"
                        "[contains(translate(normalize-space(string(.)),"
                        "'ABCDEFGHIJKLMNOPQRSTUVWXYZ','abcdefghijklmnopqrstuvwxyz'),"
                        "'get pdf')]")
                    has_get_pdf = True
                except Exception:
                    pass

            if title_text or pdf_url:
                results.append({
                    'title':       title_text,
                    'authors':     authors_text,
                    'get_pdf_url': pdf_url,
                    'has_get_pdf': has_get_pdf,
                    'available_online_url': online_url,
                    'record_url':  record_url,
                })
    except Exception as e:
        log.debug(f'  [KB] parse_results error: {e}')
    return results


def _kb_docid_to_pdf_url(record_url: str) -> str:
    """Try to derive a direct PDF or landing URL from a Primo CDI record URL.

    Primo encodes the provider + source ID in the ``docid`` query parameter:
      cdi_hal_primary_oai_HAL_hal_01330383v1  → https://hal.science/hal-01330383/document
      cdi_arxiv_papers_oai_arXiv_org_2101_12345 → https://arxiv.org/pdf/2101.12345.pdf
      cdi_crossref_primary_10_1145_XXXXXXX     → DOI-based (returned as doi:10…)
      cdi_doaj_primary_oai_doaj_org_XXXXX      → DOAJ record page
      cdi_pubmed_primary_XXXXXXX               → PubMed (no direct PDF)
      alma990XXXXXXX                            → physical item (skip)

    Returns a URL string, or '' if no pattern matched.
    """
    m = re.search(r'[?&]docid=([^&]+)', record_url)
    if not m:
        return ''
    docid = m.group(1)

    # ── HAL (all archive variants) ────────────────────────────────────────────
    # CDI encodes HAL OAI identifiers as:
    #   cdi_hal_primary_oai_HAL_hal_01330383v1  (main hal.science)
    #   cdi_hal_primary_oai_HAL_sic_00359466v1  (archivesic.ccsd.cnrs.fr)
    #   cdi_hal_primary_oai_HAL_tel_XXXXXXX     (theses.hal.science)
    #   cdi_hal_primary_oai_HAL_halshs_XXXXXXX  (shs.hal.science)
    #   ... and many other HAL subdomains
    # All share the same oai_HAL_{prefix}_{number}{version} pattern.
    # hal.science is the unified portal and resolves all subdomain IDs.
    if 'cdi_hal' in docid or 'oai_HAL' in docid or 'oai_hal' in docid:
        # HAL is a federated archive; each sub-discipline has its own subdomain
        # and URL format.  Navigating to the correct subdomain landing page is
        # essential — hal.science embeds those pages but doesn't expose the
        # direct /file/*.pdf download button that the subdomain landing page does.
        #
        # Subdomain map: prefix → (base_url, id_separator)
        #   separator='_' → archivesic.ccsd.cnrs.fr/sic_XXXXXXX (underscore in URL)
        #   separator='-' → theses.hal.science/tel-XXXXXXX       (dash in URL)
        _HAL_SUBDOMAIN: dict[str, tuple[str, str]] = {
            'hal':      ('https://hal.science',                     '-'),
            'sic':      ('https://archivesic.ccsd.cnrs.fr',        '_'),
            'tel':      ('https://theses.hal.science',              '-'),
            'halshs':   ('https://shs.hal.science',                 '-'),
            'halhs':    ('https://hal.science',                     '-'),
            'inria':    ('https://inria.hal.science',               '-'),
            'pastel':   ('https://pastel.hal.science',              '-'),
            'hal-amu':  ('https://hal-amu.archives-ouvertes.fr',    '-'),
            'inserm':   ('https://inserm.hal.science',              '-'),
            'cea':      ('https://cea.hal.science',                 '-'),
            'enpc':     ('https://enpc.hal.science',                '-'),
            'hal-univ-paris': ('https://hal.science',              '-'),
        }
        m_oai = re.search(r'oai_HAL_([a-z\-]+)[_-](\d+)', docid, re.IGNORECASE)
        if m_oai:
            hal_prefix = m_oai.group(1).lower()
            hal_num    = m_oai.group(2)
            base, sep  = _HAL_SUBDOMAIN.get(hal_prefix,
                                             ('https://hal.science', '-'))
            hal_id     = f'{hal_prefix}{sep}{hal_num}'
            return f'{base}/{hal_id}'
        # Fallback: any hal-XXXXXX pattern already using dashes
        m_dash = re.search(r'\b(hal-\d+)', docid, re.IGNORECASE)
        if m_dash:
            return f'https://hal.science/{m_dash.group(1).lower()}'

    # ── arXiv ─────────────────────────────────────────────────────────────────
    # cdi_arxiv_papers_oai_arXiv_org_2101_12345
    if 'arxiv' in docid.lower():
        arxiv = re.search(r'(\d{4}[._]\d{4,5}(?:v\d+)?)', docid)
        if arxiv:
            aid = arxiv.group(1).replace('_', '.')
            return f'https://arxiv.org/pdf/{aid}.pdf'

    # ── CrossRef / DOI ────────────────────────────────────────────────────────
    # cdi_crossref_primary_10_XXXX_YYYY  (dots encoded as underscores after first one)
    if 'crossref' in docid.lower() or 'doi' in docid.lower():
        doi = re.search(r'(10[._]\d{4,}[._].+)', docid)
        if doi:
            raw = doi.group(1)
            # Primo replaces '/' with '_' in the suffix; reconstruct carefully.
            # Pattern: 10_XXXX_rest  →  10.XXXX/rest
            doi_clean = re.sub(r'^10[_.](\d{4,})[_.](.+)$',
                               lambda x: f'10.{x.group(1)}/{x.group(2).replace("_", "/")}',
                               raw)
            if doi_clean.startswith('10.'):
                return f'doi:{doi_clean}'

    # ── DOAJ ─────────────────────────────────────────────────────────────────
    if 'doaj' in docid.lower():
        doaj = re.search(r'doaj_art_([a-f0-9]+)', docid, re.IGNORECASE)
        if doaj:
            return f'https://doaj.org/article/{doaj.group(1)}'

    return ''


def _kb_extract_pdf_from_online_page(driver, start_url: str) -> str:
    """Navigate to an 'Available Online' / 'Tilgængelig online' destination and
    return the first usable direct PDF URL found there.

    Handles:
      • Link-resolver redirects (soeg.kb.dk resolver → HAL / publisher page)
      • HAL.science pages  (Download button → /hal-XXXvN/document)
      • Generic scholarly pages (citation_pdf_url meta, .pdf hrefs, download
        buttons labelled "Download", "Télécharger", "PDF", etc.)
      • Direct PDF responses (content-type sniff via JS)
    """
    try:
        driver.get(start_url)
    except Exception:
        return ''

    # ── Wait for any resolver redirect to settle ──────────────────────────────
    # Primo link-resolvers often do 1-2 HTTP redirects before landing on the
    # actual resource page.  Poll up to 8 s for the URL to leave the origin.
    deadline = time.time() + 8
    while time.time() < deadline:
        cur = driver.current_url or ''
        if cur and cur != start_url and 'soeg.kb.dk' not in cur:
            break   # redirect complete
        time.sleep(0.5)
    else:
        time.sleep(1)   # give the final page one extra second to render

    cur = driver.current_url or start_url
    log.debug(f'  [KB/online] landed on: {cur[:80]}')

    # ── 1. citation_pdf_url meta tag (HAL, EPrints, many OA repos) ────────────
    try:
        meta = driver.find_element(
            By.CSS_SELECTOR,
            'meta[name="citation_pdf_url"], meta[property="citation_pdf_url"]')
        href = (meta.get_attribute('content') or '').strip()
        if href:
            return urljoin(cur, href)
    except Exception:
        pass

    # ── 2. Direct /file/*.pdf link (HAL, archivesic, etc.) ───────────────────
    # HAL landing pages expose a /file/XXXX.pdf link alongside the /document
    # endpoint.  The /file/ URL serves the PDF directly without any bot-
    # protection challenge, making it the most reliable download path.
    try:
        for a in driver.find_elements(By.CSS_SELECTOR, 'a[href]'):
            href = (a.get_attribute('href') or '').strip()
            if href.lower().endswith('.pdf') and '/file/' in href:
                return urljoin(cur, href)
    except Exception:
        pass

    # ── 3. HAL /document endpoint link ───────────────────────────────────────
    # Fallback when no direct .pdf link is found; /document redirects to the
    # deposited PDF (may require the browser to pass an Anubis PoW challenge,
    # which the caller's browser-navigate fallback handles).
    try:
        for a in driver.find_elements(By.CSS_SELECTOR,
                                      'a[href*="/document"], a[href*="/file"]'):
            href = (a.get_attribute('href') or '').strip()
            text = (a.get_attribute('innerText') or a.text or '').strip().lower()
            if not href:
                continue
            if (text in ('download', 'télécharger', 'pdf', 'télécharger le pdf',
                         'download pdf', 'télécharger le fichier')
                    or '/document' in href.lower()
                    or '/file/' in href.lower()):
                return urljoin(cur, href)
    except Exception:
        pass

    # ── 4. Generic: any <a> with a direct .pdf href ───────────────────────────
    try:
        for a in driver.find_elements(By.CSS_SELECTOR, 'a[href]'):
            href = (a.get_attribute('href') or '').strip()
            text = (a.get_attribute('innerText') or a.text or '').strip().lower()
            if not href:
                continue
            if href.lower().endswith('.pdf'):
                return urljoin(cur, href)
            if text in ('download', 'télécharger', 'pdf') and (
                    '.pdf' in href.lower() or '/pdf' in href.lower()):
                return urljoin(cur, href)
    except Exception:
        pass

    # ── 5. <a download> attribute ─────────────────────────────────────────────
    try:
        a = driver.find_element(By.CSS_SELECTOR, 'a[download][href]')
        href = (a.get_attribute('href') or '').strip()
        if href:
            return urljoin(cur, href)
    except Exception:
        pass

    # ── 6. HAL / HAL-subdomain stable fallback ───────────────────────────────
    # If we're on any HAL-family page but found no explicit link, construct the
    # /document URL for the browser-navigate fallback to handle.
    hal_cur = re.search(
        r'(https?://[^/]*(?:hal\.science|ccsd\.cnrs\.fr|hal\.[a-z]+\.[a-z]+)'
        r'/([a-z]+-\d+))',
        cur, re.IGNORECASE)
    if hal_cur:
        return f'{hal_cur.group(1)}/document'
    hal_cur2 = re.search(
        r'(https?://[^/]*(?:hal\.science|ccsd\.cnrs\.fr|hal\.[a-z]+\.[a-z]+)'
        r'/([a-z]+_\d+))',
        cur, re.IGNORECASE)
    if hal_cur2:
        hal_id = hal_cur2.group(2).replace('_', '-')
        host   = hal_cur2.group(1).rsplit('/', 1)[0]
        return f'{host}/{hal_id}/document'

    # ── 7. ArXiv fallback ─────────────────────────────────────────────────────
    m2 = re.search(r'arxiv\.org/abs/([0-9]+\.[0-9v]+)', cur)
    if m2:
        return f'https://arxiv.org/pdf/{m2.group(1)}.pdf'

    return ''


def try_kb_library(title: str, authors: str, save_path: str,
                   session: requests.Session) -> bool:
    """Search the Royal Danish Library Primo portal (soeg.kb.dk) for the title,
    match against author name(s), and download the first "Get PDF" OA link found.

    Attaches to an existing Brave window (--remote-debugging-port=9222) when
    available so it reuses the authenticated session; otherwise uses a fresh
    headless Chrome (Unpaywall-resolved OA links work without authentication).
    """
    if not SELENIUM_AVAILABLE or not title:
        return False

    log.info(f'  [KB] Searching: {title[:70]}')

    # Build author last-names for matching
    author_lnames = extract_author_lastnames(authors)

    search_url = _KB_SEARCH_URL.format(q=quote_plus(title))
    download_dir = os.path.dirname(save_path)

    driver = None
    attached = False
    try:
        driver, attached = _kb_attach_or_new(download_dir)
        if driver is None:
            return False
        log.info(f'  [KB] Loading search page…')
        driver.get(search_url)

        # Wait for Angular to render at least one result item
        try:
            WebDriverWait(driver, _KB_WAIT_SECS).until(
                EC.presence_of_element_located((
                    By.CSS_SELECTOR,
                    'prm-brief-result-container, li[data-recordid]')))
            time.sleep(2)   # let Angular finish rendering quick-links
        except TimeoutException:
            log.debug('  [KB] Timed out waiting for results')
            return False

        results = _kb_parse_results(driver)
        log.info(f'  [KB] {len(results)} result(s) rendered')

        candidates = []
        for res in results:
            sim = title_similarity(title, res['title'])
            if sim < 0.70:
                log.debug(f'  [KB] skip (sim={sim:.2f}): {res["title"][:60]}')
                continue

            # ── Author match (at least one last-name must appear) ─────────────
            authors_lc = res['authors'].lower()
            author_hits = 0
            if author_lnames:
                author_hits = sum(1 for ln in author_lnames if ln in authors_lc)
                if author_hits < 1:
                    log.debug(f'  [KB] skip (author mismatch): {res["title"][:50]}')
                    continue

            candidates.append((author_hits, sim, res))

        # Prefer the strongest title+author match first.
        candidates.sort(key=lambda x: (x[0], x[1]), reverse=True)

        _ao_labels = ('available online', 'tilgængelig online',
                      'tilgaengelig online', 'tilgängelig online',
                      'fulltext_linktorsrc')

        for author_hits, sim, res in candidates:
            # ── PDF / Available Online checks ─────────────────────────────────
            pdf_url = (res.get('get_pdf_url') or '').strip()
            if pdf_url:
                pdf_url = urljoin('https://soeg.kb.dk', pdf_url)
            online_url = (res.get('available_online_url') or '').strip()
            if online_url:
                online_url = urljoin('https://soeg.kb.dk', online_url)

            # ── Fast path: derive URL directly from the CDI docid ─────────────
            # The record_url contains ?docid=cdi_hal_primary_oai_HAL_hal_XXXXXXX
            # which lets us short-circuit to a direct PDF URL for known providers
            # (HAL, arXiv, …) without navigating to the detail page at all.
            if not pdf_url and not online_url and res.get('record_url'):
                docid_url = _kb_docid_to_pdf_url(res['record_url'])
                if docid_url:
                    if docid_url.startswith('doi:'):
                        # Treat as an online_url resolved later via Unpaywall
                        online_url = docid_url
                    else:
                        online_url = docid_url
                    log.debug(f'  [KB] docid→url: {online_url[:80]}')

            # ── Click-based fallback (list-view button → new tab) ─────────────
            # "Available Online" / "Tilgængelig online" buttons are Angular
            # elements with no plain href.  Click them, switch to the new tab,
            # and extract the PDF URL from the destination page.
            if not pdf_url and not online_url and res.get('has_get_pdf'):
                try:
                    # Re-find the result card (may have become stale after earlier nav)
                    items_now = driver.find_elements(
                        By.CSS_SELECTOR, 'prm-brief-result-container')
                    # Match by title text
                    target_item = None
                    for it in items_now:
                        try:
                            t = (it.find_element(By.CSS_SELECTOR, 'h3.item-title')
                                 .get_attribute('innerText') or '')
                            if title_similarity(title, t) >= 0.70:
                                target_item = it
                                break
                        except Exception:
                            pass

                    if target_item:
                        # Find the clickable button: span.button-content that
                        # contains a fulltext_linktorsrc / pdf / "get" label.
                        btn = None
                        for el in target_item.find_elements(
                                By.CSS_SELECTOR,
                                'span.button-content, '
                                'button[class*="availability"], '
                                'a[class*="availability"]'):
                            inner = (el.get_attribute('innerText') or
                                     el.text or '').strip().lower()
                            cls   = el.get_attribute('class') or ''
                            if ('fulltext' in cls or
                                    any(t in inner for t in
                                        ('available online', 'tilgængelig online',
                                         'tilgaengelig online', 'get pdf', 'pdf'))):
                                btn = el
                                break

                        if btn:
                            orig_handles = set(driver.window_handles)
                            try:
                                btn.click()
                                time.sleep(3)
                            except Exception:
                                pass
                            new_handles = set(driver.window_handles) - orig_handles
                            if new_handles:
                                new_tab = new_handles.pop()
                                driver.switch_to.window(new_tab)
                                time.sleep(2)
                                online_url = driver.current_url
                                log.debug(f'  [KB] button click → {online_url[:80]}')
                                driver.close()
                                driver.switch_to.window(
                                    list(orig_handles)[0])
                            elif driver.current_url != search_url:
                                # Navigated in same tab
                                online_url = driver.current_url
                                driver.back()
                                time.sleep(1)
                except Exception as e:
                    log.debug(f'  [KB] click fallback error: {e}')

            # ── Detail-page lookup (when list-view had no direct URL) ──────────
            # Navigate to the record's full-display page and find the
            # "Available Online" / "Get PDF" / "Tilgængelig online" link there.
            if not pdf_url and not online_url and res.get('record_url'):
                try:
                    driver.get(res['record_url'])
                    # Wait for the full-display Angular components to render
                    try:
                        WebDriverWait(driver, 10).until(
                            EC.presence_of_element_located((
                                By.CSS_SELECTOR,
                                'prm-full-view, prm-service-button, '
                                'prm-alma-viewit-items, .full-view-inner-container')))
                    except TimeoutException:
                        pass
                    time.sleep(2)

                    for a in driver.find_elements(By.CSS_SELECTOR, 'a[href]'):
                        href  = (a.get_attribute('href') or '').strip()
                        label = (a.get_attribute('aria-label') or '').lower()
                        inner = (a.get_attribute('innerText') or
                                 a.text or '').strip().lower()
                        if not href or 'soeg.kb.dk/discovery' in href:
                            continue   # skip internal navigation links

                        # "Get PDF"
                        if ('get pdf' in label or 'get pdf' in inner
                                or href.lower().endswith('.pdf')):
                            pdf_url = href; break

                        # "Available Online" / "Tilgængelig online"
                        if any(t in label or t in inner for t in _ao_labels):
                            if not online_url:
                                online_url = href

                except Exception as e:
                    log.debug(f'  [KB] detail-page lookup failed: {e}')

            if not pdf_url and online_url:
                log.info(f'  [KB] Following Available Online → {online_url[:80]}')
                pdf_url = _kb_extract_pdf_from_online_page(driver, online_url)
                if not pdf_url:
                    log.debug(f'  [KB] No PDF found via Available Online for: {res["title"][:50]}')
                    continue

            if not pdf_url:
                log.debug(f'  [KB] No PDF/online link for: {res["title"][:50]}')
                continue

            log.info(
                f'  [KB] Match (sim={sim:.2f}, author_hits={author_hits}) '
                f'→ {pdf_url[:80]}'
            )

            # Transfer browser cookies to requests session (needed for some
            # institution-gated redirects)
            try:
                for ck in driver.get_cookies():
                    session.cookies.set(
                        ck['name'], ck['value'],
                        domain=ck.get('domain', ''))
            except Exception:
                pass

            if try_download_pdf(pdf_url, save_path, session):
                log.info(f'  [KB] ✅ Downloaded via Primo OA link')
                return True

            # If direct download failed, navigate the browser to the URL.
            # For HAL /document endpoints on some subdomains (e.g. archivesic),
            # an Anubis bot-protection page appears but the browser solves the
            # JS proof-of-work automatically and triggers the PDF download.
            try:
                driver.get(pdf_url)
                # Wait up to 15 s — Anubis PoW can take 5–10 s to resolve
                for _ in range(15):
                    time.sleep(1)
                    recent = [
                        fn for fn in os.listdir(download_dir)
                        if (fn.lower().endswith('.pdf') and
                            not fn.endswith('.crdownload') and
                            time.time() - os.path.getmtime(
                                os.path.join(download_dir, fn)) < 30)
                    ]
                    if recent:
                        fp = os.path.join(download_dir,
                                          max(recent, key=lambda f:
                                              os.path.getmtime(
                                                  os.path.join(download_dir, f))))
                        if is_valid_pdf(fp):
                            os.rename(fp, save_path)
                            log.info('  [KB] ✅ Browser auto-downloaded PDF')
                            return True
                # Page is the PDF in the browser viewer
                ct = driver.execute_script(
                    "return document.contentType || ''") or ''
                if 'pdf' in ct.lower():
                    pdf_bytes = driver.execute_script("""
                        var x = new XMLHttpRequest();
                        x.open('GET', window.location.href, false);
                        x.responseType = 'arraybuffer';
                        x.send();
                        var b = new Uint8Array(x.response);
                        return Array.from(b);
                    """)
                    if pdf_bytes:
                        with open(save_path, 'wb') as fh:
                            fh.write(bytes(pdf_bytes))
                        if is_valid_pdf(save_path):
                            return True
                        _remove_if_exists(save_path)
            except Exception as e:
                log.debug(f'  [KB] browser-nav error: {e}')

        log.info(f'  [KB] No matching "Get PDF" link found for: {title[:60]}')

    except Exception as e:
        log.debug(f'  [KB] error: {e}')
    finally:
        # Only quit if we launched a fresh browser — never close the user's Brave
        if driver and not attached:
            try:
                driver.quit()
            except Exception:
                pass

    return False


# ─── Browser automation handlers ──────────────────────────────────────────────

_browser_driver = None

def _get_browser(download_dir: str = None):
    """Get or create a headless Chrome browser instance for automation.

    Uses a pinned Chrome 141 + ChromeDriver 141 pair from Selenium's cache to
    avoid the version-mismatch "session not created" crash that occurs when
    Selenium auto-selects Chrome 146 while PATH still has ChromeDriver 141.
    """
    global _browser_driver
    if _browser_driver is not None:
        try:
            _browser_driver.title  # Check if still alive
            return _browser_driver
        except Exception:
            _browser_driver = None

    if not SELENIUM_AVAILABLE:
        return None

    opts = ChromeOptions()
    opts.add_argument('--headless=new')
    opts.add_argument('--no-sandbox')
    opts.add_argument('--disable-dev-shm-usage')
    opts.add_argument('--disable-gpu')
    opts.add_argument('--window-size=1920,1080')
    opts.add_argument('user-agent=Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) '
                      'AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36')

    # Pin to Chrome 141 binary so it matches ChromeDriver 141 in PATH
    if os.path.exists(_CHROME_BINARY):
        opts.binary_location = _CHROME_BINARY

    if download_dir:
        prefs = {
            'download.default_directory': download_dir,
            'download.prompt_for_download': False,
            'plugins.always_open_pdf_externally': True,
        }
        opts.add_experimental_option('prefs', prefs)

    try:
        svc = ChromeService(executable_path=_CHROMEDRIVER_BIN)
        _browser_driver = webdriver.Chrome(service=svc, options=opts)
        _browser_driver.set_page_load_timeout(30)
        log.debug("  Browser started (Chrome 141 + ChromeDriver 141)")
        return _browser_driver
    except WebDriverException as e:
        log.debug(f"  Browser init error: {e}")
        return None


def _close_browser():
    global _browser_driver
    if _browser_driver:
        try:
            _browser_driver.quit()
        except Exception:
            pass
        _browser_driver = None


def try_proquest_browser(url: str, save_path: str,
                         session: requests.Session) -> bool:
    """ProQuest: scrape the page for 'Download PDF' link (media.proquest.com)
    and download via requests. Falls back to Selenium if needed."""
    # First try scraping with requests — the <a class="wt-download-pdf"> tag
    # has a direct href to media.proquest.com
    try:
        resp = session.get(url, timeout=30)
        if resp.status_code == 200:
            soup = BeautifulSoup(resp.text, 'html.parser')
            # Look for the download button: <a class="wt-download-pdf" href="...">
            dl_link = soup.find('a', class_=re.compile(r'wt-download-pdf'))
            if not dl_link:
                dl_link = soup.find('a', attrs={'title': re.compile(r'Download PDF', re.I)})
            if not dl_link:
                dl_link = soup.find('a', id='openViewPDFMobileButton')
            if dl_link and dl_link.get('href'):
                pdf_url = dl_link['href']
                if not pdf_url.startswith('http'):
                    pdf_url = requests.compat.urljoin(url, pdf_url)
                log.info(f"  [ProQuest] Found PDF link: {pdf_url[:80]}")
                if try_download_pdf(pdf_url, save_path, session):
                    return True
    except Exception as e:
        log.debug(f"  ProQuest scrape error: {e}")

    # Fallback: browser automation
    if not SELENIUM_AVAILABLE:
        return False

    download_dir = os.path.dirname(save_path)
    driver = _get_browser(download_dir)
    if not driver:
        return False

    try:
        driver.get(url)
        time.sleep(4)

        # Find the download link and extract its href
        for selector in [
            "a.wt-download-pdf",
            "a[title='Download PDF']",
            "a#openViewPDFMobileButton",
        ]:
            try:
                elem = WebDriverWait(driver, 5).until(
                    EC.presence_of_element_located((By.CSS_SELECTOR, selector)))
                pdf_url = elem.get_attribute('href')
                if pdf_url and ('media.proquest.com' in pdf_url or pdf_url.endswith('.pdf')):
                    log.info(f"  [ProQuest/browser] Found: {pdf_url[:80]}")
                    if try_download_pdf(pdf_url, save_path, session):
                        return True
                # Also try clicking it
                elem.click()
                time.sleep(5)
                # Check for downloaded file
                for fn in os.listdir(download_dir):
                    if fn.lower().endswith('.pdf') and ('proquest' in fn.lower() or fn.startswith('ORIG')):
                        downloaded_file = os.path.join(download_dir, fn)
                        if is_valid_pdf(downloaded_file):
                            os.rename(downloaded_file, save_path)
                            return True
                        _remove_if_exists(downloaded_file)
            except (TimeoutException, Exception):
                continue

    except Exception as e:
        log.debug(f"  ProQuest browser error: {e}")
    return False


def try_tandfonline(url: str, save_path: str,
                    session: requests.Session) -> bool:
    """Tandfonline: try /doi/pdf/ and /doi/epdf/ URL patterns, then Selenium."""
    log.info(f'  [T&F Online] Trying {url[:80]}')

    # Extract DOI path from any tandfonline URL variant
    doi_match = re.search(
        r'tandfonline\.com/doi/(?:abs|full|epdf|epub|pdf)/(.+?)(?:\?|$)', url)
    if doi_match:
        doi_path = doi_match.group(1).rstrip('/')
        # Try /doi/pdf/ first (machine-readable PDF)
        for variant in [
            f'https://www.tandfonline.com/doi/pdf/{doi_path}?needAccess=true&download=true',
            f'https://www.tandfonline.com/doi/pdf/{doi_path}',
            f'https://www.tandfonline.com/doi/epdf/{doi_path}?needAccess=true',
            f'https://www.tandfonline.com/doi/epub/{doi_path}',
        ]:
            log.info(f'  [T&F Online] Trying {variant[:80]}')
            if try_download_pdf(variant, save_path, session):
                return True

    # Scrape page for PDF / epdf links (works when JS is not required)
    try:
        headers = {
            'User-Agent': ('Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) '
                           'AppleWebKit/537.36 (KHTML, like Gecko) '
                           'Chrome/120.0.0.0 Safari/537.36'),
            'Accept': 'text/html,application/xhtml+xml',
            'Referer': 'https://www.tandfonline.com/',
        }
        resp = session.get(url, timeout=30, headers=headers)
        if resp.status_code == 200:
            soup = BeautifulSoup(resp.text, 'html.parser')
            for pdf_link in soup.find_all('a', href=re.compile(r'/doi/(?:pdf|epdf)/')):
                href = pdf_link['href']
                if not href.startswith('http'):
                    href = f'https://www.tandfonline.com{href}'
                log.info(f'  [T&F Online] Scraped: {href[:80]}')
                if try_download_pdf(href, save_path, session):
                    return True
    except Exception as e:
        log.debug(f'  [T&F Online] scrape error: {e}')

    # Selenium fallback — the "View PDF" / "Download PDF" button is JS-rendered
    if SELENIUM_AVAILABLE:
        driver = None
        try:
            driver = _get_browser(os.path.dirname(save_path))
            if driver:
                log.info(f'  [T&F Online] Selenium loading page…')
                driver.get(url)
                # Wait for the PDF link to appear
                try:
                    elem = WebDriverWait(driver, 15).until(
                        EC.presence_of_element_located(
                            (By.XPATH,
                             "//a[contains(@href,'/doi/pdf/') or "
                             "contains(@href,'/doi/epdf/')]")))
                    pdf_href = elem.get_attribute('href')
                    if pdf_href:
                        if not pdf_href.startswith('http'):
                            pdf_href = f'https://www.tandfonline.com{pdf_href}'
                        # Transfer cookies
                        for cookie in driver.get_cookies():
                            session.cookies.set(cookie['name'], cookie['value'],
                                                domain=cookie.get('domain', ''))
                        log.info(f'  [T&F Online] Selenium found: {pdf_href[:80]}')
                        if try_download_pdf(pdf_href, save_path, session):
                            return True
                except TimeoutException:
                    log.debug('  [T&F Online] Selenium: PDF link not found')
        except Exception as e:
            log.debug(f'  [T&F Online] Selenium error: {e}')
        finally:
            if driver:
                try:
                    driver.quit()
                except Exception:
                    pass

    log.info(f'  [T&F Online] FAILED — no PDF found for {url[:80]}')
    return False


def try_ebsco_browser(url: str, save_path: str,
                      session: requests.Session) -> bool:
    """EBSCO: sign in via institutional login and download PDF."""
    if not SELENIUM_AVAILABLE:
        log.info("  [EBSCO] Skipping (selenium not available)")
        return False

    download_dir = os.path.dirname(save_path)
    driver = _get_browser(download_dir)
    if not driver:
        return False

    try:
        driver.get(url)
        time.sleep(3)

        # Check if we need to sign in — look for institutional login options
        page_src = driver.page_source.lower()
        if 'login' in page_src or 'sign in' in page_src or 'shibboleth' in page_src:
            # Look for "KØBENHAVNS BIBLIOTEKER" or similar institutional login
            for selector in [
                "//a[contains(., 'KØBENHAVNS')]",
                "//a[contains(., 'Copenhagen')]",
                "//a[contains(., 'bibliotek')]",
                "//option[contains(., 'KØBENHAVNS')]",
                "//a[contains(., 'Institutional Login')]",
                "//a[contains(., 'Sign in')]",
            ]:
                try:
                    elem = driver.find_element(By.XPATH, selector)
                    elem.click()
                    time.sleep(3)
                    break
                except Exception:
                    continue

        time.sleep(2)

        # Try to find PDF download link
        for selector in [
            "a[title*='PDF']",
            "a.pdf-ft",
            "a[href*='pdf']",
            "a.lnk-pdf",
            "a[data-auto='pdf-link']",
        ]:
            try:
                elem = WebDriverWait(driver, 5).until(
                    EC.presence_of_element_located((By.CSS_SELECTOR, selector)))
                pdf_url = elem.get_attribute('href')
                if pdf_url:
                    log.info(f"  [EBSCO] Found PDF link: {pdf_url[:80]}")
                    # Transfer cookies from Selenium to requests session
                    for cookie in driver.get_cookies():
                        session.cookies.set(cookie['name'], cookie['value'],
                                          domain=cookie.get('domain', ''))
                    if try_download_pdf(pdf_url, save_path, session):
                        return True
                # Try clicking
                elem.click()
                time.sleep(5)
                # Check for downloaded file
                for fn in os.listdir(download_dir):
                    if fn.lower().endswith('.pdf'):
                        downloaded_file = os.path.join(download_dir, fn)
                        if is_valid_pdf(downloaded_file) and \
                                os.path.getmtime(downloaded_file) > time.time() - 30:
                            os.rename(downloaded_file, save_path)
                            return True
            except (TimeoutException, Exception):
                continue

    except Exception as e:
        log.debug(f"  EBSCO browser error: {e}")
    return False


def try_domain_handlers(url: str, save_path: str, session: requests.Session,
                        row: dict = None) -> bool:
    """Route URL to the appropriate domain-specific handler."""
    if not url:
        return False
    d = url.lower()
    row = row or {}

    if 'jstor.org' in d:
        return try_jstor(url, save_path, session)
    elif 'hal.science' in d or 'hal.archives-ouvertes.fr' in d or \
            'hal.inria.fr' in d or 'hal-amu.archives' in d:
        return try_hal(url, save_path, session)
    elif 'journals.openedition.org' in d:
        return try_openedition(url, save_path, session)
    elif 'persee.fr' in d:
        return try_persee(url, save_path, session)
    elif 'shs.cairn.info' in d or 'cairn.info' in d:
        return try_cairn(url, save_path, session)
    elif 'taylorfrancis.com/books/' in d or 'taylorfrancis.com/chapters/' in d:
        return try_taylor_francis(url, save_path, row, session)
    elif 'papers.ssrn.com' in d or 'ssrn.com' in d:
        return try_ssrn(url, save_path, session)
    elif 'link.springer.com/chapter' in d or 'link.springer.com/content/pdf' in d:
        return try_springer_chapter(url, save_path, session)
    elif 'muse.jhu.edu' in d:
        return try_muse(url, save_path, session)
    elif 'books.google.com' in d:
        return try_google_books(url, save_path, row, session)
    elif 'search.proquest.com' in d:
        return try_proquest_browser(url, save_path, session)
    elif 'ebscohost.com' in d or 'ebsco.com' in d:
        return try_ebsco_browser(url, save_path, session)
    elif 'tandfonline.com' in d:
        # tandfonline.com articles — try direct PDF construction from DOI
        return try_tandfonline(url, save_path, session)
    elif 'dl.acm.org' in d:
        return try_acm(url, save_path, row, session)
    elif any(host in d for host in (
        'journals.sagepub.com',
        'academic.oup.com',
        'sciencedirect.com',
        'wiley.com',
        'onlinelibrary.wiley.com',
        'torrossa.com',
        'rivisteweb.it',
        'scielo.',
        'doaj.org',
        'ssoar.info',
        'zenodo.org',
        'osf.io',
        'repository',
        'iris.',
        'air.unimi.it',
        'boa.unimib.it',
        'usiena-air.unisi.it',
    )):
        return try_landing_page_pdf(url, save_path, session)
    return try_landing_page_pdf(url, save_path, session)


# ─── CSV Fallback ─────────────────────────────────────────────────────────────

def try_csv_fallback(row: dict, save_path: str, session: requests.Session) -> bool:
    """Last-resort direct download of any URL in the CSV row.

    Domain handlers already ran in Strategy 4 — do NOT call them again here.
    Only try plain HTTP downloads for URLs that look like direct PDF links,
    then any remaining URL not covered by a dedicated handler.
    """
    urls_to_try = []
    seen: set = set()
    for col in ('Resources', 'Link'):
        for url in (row.get(col) or '').split(', '):
            url = url.strip()
            if url.startswith('http') and url not in seen:
                seen.add(url)
                urls_to_try.append(url)

    # URLs that look like direct PDF links — try these first
    pdf_hints = ['.pdf', '/pdf/', 'download', 'bitstream', 'fulltext',
                 '/stable/pdf', 'pdfdirect', 'content/pdf']
    for url in urls_to_try:
        if any(h in url.lower() for h in pdf_hints):
            if try_download_pdf(url, save_path, session):
                return True
            if try_landing_page_pdf(url, save_path, session):
                return True
            time.sleep(DOWNLOAD_DELAY)

    # Remaining plain URLs — skip any domain that has a dedicated handler
    # (those already ran; calling them again wastes minutes per row)
    handler_domains = [
        'books.google.com', 'taylorfrancis.com', 'papers.ssrn.com', 'ssrn.com',
        'muse.jhu.edu', 'link.springer.com', 'search.proquest.com',
        'ebscohost.com', 'tandfonline.com', 'jstor.org',
        'hal.science', 'hal.archives-ouvertes.fr', 'persee.fr',
        'cairn.info', 'journals.openedition.org',
    ]
    for url in urls_to_try:
        lower = url.lower()
        if any(h in lower for h in pdf_hints):
            continue
        if any(d in lower for d in handler_domains):
            continue
        if try_download_pdf(url, save_path, session):
            return True
        if try_landing_page_pdf(url, save_path, session):
            return True
        time.sleep(DOWNLOAD_DELAY)

    return False


# ─── Main ─────────────────────────────────────────────────────────────────────

def main():
    global SCIHUB_ENABLED, ANNAS_ARCHIVE_ENABLED, USE_CONTENT_API, LIBGEN_ENABLED, DRY_RUN

    parser = argparse.ArgumentParser(
        description='Download PDFs for scholar_results_serpapi.csv rows.')
    parser.add_argument('--start-from', type=int, default=0, metavar='N',
                        help='Skip the first N rows that need PDFs (for resuming).')
    parser.add_argument('--limit', type=int, default=None, metavar='N',
                        help='Process at most N rows.')
    parser.add_argument('--dry-run', action='store_true',
                        help='Show what would be done without downloading anything.')
    parser.add_argument('--no-scihub', action='store_true',
                        help='Disable Sci-Hub.')
    parser.add_argument('--no-content-api', action='store_true',
                        help='Disable OpenAlex Content API (saves credits).')
    parser.add_argument('--no-annas', action='store_true',
                        help="Disable Anna's Archive (both HTML scraping and RapidAPI).")
    parser.add_argument('--no-libgen', action='store_true',
                        help='Disable LibGen.')
    args = parser.parse_args()

    if args.no_scihub:
        SCIHUB_ENABLED = False
    if args.no_content_api:
        USE_CONTENT_API = False
    if args.no_annas:
        ANNAS_ARCHIVE_ENABLED = False
    if args.no_libgen:
        LIBGEN_ENABLED = False
    DRY_RUN = args.dry_run

    if DRY_RUN:
        log.info("DRY RUN — no files will be written.")

    log.info(f"Reading CSV: {SCHOLAR_CSV}")
    with open(SCHOLAR_CSV, 'r', encoding='utf-8') as f:
        reader = csv.DictReader(f, delimiter=';')
        fieldnames = reader.fieldnames
        rows = list(reader)

    log.info(f"Total rows: {len(rows)}")

    os.makedirs(PDF_FOLDER, exist_ok=True)

    # Load metadata (tracks what's already downloaded; also used by step 3)
    metadata = load_metadata()
    existing_titles = {
        normalize_title(m.get('title', ''))
        for m in metadata.values() if m.get('title')
    }

    needs_pdf = []
    for i, row in enumerate(rows):
        pdf_path = (row.get('PDF Path') or '').strip()
        if pdf_path and os.path.exists(pdf_path) and is_valid_pdf(pdf_path):
            continue  # already downloaded
        norm_t = normalize_title(row.get('Title') or '')
        if norm_t and norm_t in existing_titles:
            continue  # duplicate title, already have it
        needs_pdf.append(i)

    log.info(f"Rows needing PDFs: {len(needs_pdf)}")

    if args.start_from:
        needs_pdf = needs_pdf[args.start_from:]
        log.info(f"  Skipping first {args.start_from} → {len(needs_pdf)} remaining")
    if args.limit is not None:
        needs_pdf = needs_pdf[:args.limit]
        log.info(f"  Limiting to {args.limit} rows → {len(needs_pdf)} to process")

    existing_files = {f for f in os.listdir(PDF_FOLDER) if f.endswith('.pdf')}

    # Build lookup: Result ID → filename for existing PDFs
    existing_by_id = {}
    for f in existing_files:
        m = re.search(r' - ([A-Za-z0-9_\-]+)\.pdf$', f)
        if m:
            existing_by_id[m.group(1)] = f

    log.info(f"Existing PDFs on disk: {len(existing_files)}")

    session = build_session(USER_EMAIL)
    failed_rows = []

    # Save CSV on interrupt (Ctrl+C) so progress is never lost
    def _handle_interrupt(sig, frame):
        log.info("\nInterrupted! Saving progress before exit...")
        _save_csv(rows, fieldnames)
        _save_failures(failed_rows)
        save_metadata(metadata)
        _close_browser()
        log.info("Progress saved. You can resume by re-running the same command.")
        sys.exit(0)

    signal.signal(signal.SIGINT, _handle_interrupt)
    signal.signal(signal.SIGTERM, _handle_interrupt)

    stats = {
        'openalex_match': 0,
        'downloaded_direct_url': 0,
        'downloaded_oa_url': 0,
        'downloaded_unpaywall': 0,
        'downloaded_content_api': 0,
        'downloaded_domain_handler': 0,
        'downloaded_scihub': 0,
        'downloaded_annas_archive': 0,
        'downloaded_annas_rapidapi': 0,
        'downloaded_libgen': 0,
        'downloaded_garbage_world': 0,
        'downloaded_csv_fallback': 0,
        'no_match': 0,
        'download_failed': 0,
        'content_api_credits_used': 0,
    }

    for count, row_idx in enumerate(needs_pdf, 1):
        row = rows[row_idx]
        title   = (row.get('Title')   or '').strip()
        year    = (row.get('Year')    or '').strip()
        authors = (row.get('Authors') or '').strip()
        link    = (row.get('Link')    or '').strip()

        log.info(f"[{count}/{len(needs_pdf)}] Row {row_idx}: {title[:80]}...")

        filename = generate_filename(row)
        save_path = os.path.join(PDF_FOLDER, filename)

        if os.path.exists(save_path) and is_valid_pdf(save_path):
            log.info(f"  Already on disk (exact name), updating CSV path")
            rows[row_idx]['PDF Path'] = save_path
            stats['downloaded_oa_url'] += 1
            _save_csv(rows, fieldnames)
            continue

        # Check if a file with this row's Result ID already exists
        uid = (row.get('Result ID') or '').strip()
        if uid and uid in existing_by_id:
            candidate = os.path.join(PDF_FOLDER, existing_by_id[uid])
            if os.path.exists(candidate) and is_valid_pdf(candidate):
                log.info(f"  Already on disk (ID match), updating CSV path")
                rows[row_idx]['PDF Path'] = candidate
                stats['downloaded_oa_url'] += 1
                _save_csv(rows, fieldnames)
                continue

        if DRY_RUN:
            log.info(f"  [DRY RUN] Would attempt download for: {title[:80]}")
            continue

        downloaded = False
        download_source = None

        # Strategy 0: Try Resources and Link URLs directly (Google Scholar often
        # includes direct PDF links here — try them first before any API calls)
        _seen_direct = set()
        direct_urls = []
        for col in ('Resources', 'Link'):
            val = (row.get(col) or '').strip()
            # Resources may be comma-joined list of URLs; split and try each
            for u in val.split(', '):
                u = u.strip()
                if u.startswith('http') and u not in _seen_direct:
                    _seen_direct.add(u)
                    direct_urls.append(u)
        for url in direct_urls:
            log.info(f"  [Direct] Trying: {url[:100]}")
            if try_download_pdf(url, save_path, session):
                downloaded = True
                download_source = 'direct_url'
                break
            time.sleep(DOWNLOAD_DELAY)

        # ── Search OpenAlex (also extracts DOI) ──
        work, doi = search_openalex(title, year, authors, link, session, USER_EMAIL)
        time.sleep(API_DELAY)

        if work:
            stats['openalex_match'] += 1
            oa_title = strip_html(work.get('title', ''))
            log.info(f"  Matched: {oa_title[:80]}")

            # Strategy 1: Free OA PDF URLs from OpenAlex
            oa_urls = extract_oa_pdf_urls(work) if not downloaded else []
            for url in oa_urls:
                log.info(f"  [OA] Trying: {url[:100]}")
                if try_download_pdf(url, save_path, session):
                    downloaded = True
                    download_source = 'oa_url'
                    break
                time.sleep(DOWNLOAD_DELAY)

            # Strategy 2: Unpaywall (free, needs DOI)
            if not downloaded and doi and USER_EMAIL:
                log.info(f"  [Unpaywall] Checking DOI: {doi}")
                if try_unpaywall(doi, save_path, session, USER_EMAIL):
                    downloaded = True
                    download_source = 'unpaywall'

            # Strategy 3: Content API
            if not downloaded and USE_CONTENT_API:
                content_url = get_content_api_url(work)
                if content_url:
                    log.info(f"  [Content API] Trying: {content_url}")
                    if try_content_api(content_url, save_path, session):
                        downloaded = True
                        download_source = 'content_api'
                        stats['content_api_credits_used'] += 100
                    time.sleep(DOWNLOAD_DELAY)
        else:
            stats['no_match'] += 1
            log.info(f"  No OpenAlex match (DOI: {doi})")

            # Even without OpenAlex match, try Unpaywall if we have a DOI
            if not downloaded and doi and USER_EMAIL:
                log.info(f"  [Unpaywall] Checking DOI: {doi}")
                if try_unpaywall(doi, save_path, session, USER_EMAIL):
                    downloaded = True
                    download_source = 'unpaywall'

        # Strategy 4: Domain-specific handlers (T&F, SSRN, Springer, MUSE, etc.)
        # Deduplicate URLs across Link and Resources before calling handlers.
        if not downloaded:
            _seen_s4: set = set()
            for col in ('Link', 'Resources'):
                for url in (row.get(col) or '').split(', '):
                    url = url.strip()
                    if url.startswith('http') and url not in _seen_s4:
                        _seen_s4.add(url)
                        if try_domain_handlers(url, save_path, session, row=row):
                            downloaded = True
                            download_source = 'domain_handler'
                            break
                        time.sleep(DOWNLOAD_DELAY)
                if downloaded:
                    break

        # Strategy 5: Sci-Hub — try DOI first, then article Link, then Resources URLs.
        # Article links work directly as Sci-Hub search queries (no DOI required).
        # Skip known non-journal domains (Google Books, Academia.edu, etc.) that
        # Sci-Hub will never resolve, to avoid wasting browser time.
        if not downloaded and SCIHUB_ENABLED:
            _seen_sc = set()
            scihub_candidates = []
            for _cand in ([doi] if doi else []) + [link] + \
                    [(u.strip()) for u in (row.get('Resources') or '').split(', ')]:
                _cand = (_cand or '').strip()
                if not _cand or _cand in _seen_sc:
                    continue
                # Skip domains that Sci-Hub cannot handle
                if any(skip in _cand for skip in _SCIHUB_SKIP_DOMAINS):
                    continue
                _seen_sc.add(_cand)
                scihub_candidates.append(_cand)
            for scihub_id in scihub_candidates:
                log.info(f"  [Sci-Hub] Trying: {scihub_id[:60]}")
                if try_scihub(scihub_id, save_path, session):
                    downloaded = True
                    download_source = 'scihub'
                    break
                time.sleep(DOWNLOAD_DELAY)

        # Strategy 6: Anna's Archive HTML scraping
        if not downloaded and ANNAS_ARCHIVE_ENABLED:
            log.info(f"  [Anna's Archive] Searching by title...")
            if try_annas_archive_title(title, authors, save_path, session):
                downloaded = True
                download_source = 'annas_archive'
            time.sleep(DOWNLOAD_DELAY)

        # Strategy 6b: Anna's Archive RapidAPI (book + journal)
        if not downloaded and ANNAS_ARCHIVE_ENABLED:
            log.info(f"  [AA/RapidAPI] Searching...")
            if try_annas_archive_rapidapi(title, authors, save_path, session):
                downloaded = True
                download_source = 'annas_rapidapi'
            time.sleep(DOWNLOAD_DELAY)

        # Strategy 7: LibGen (libgen_api_enhanced)
        if not downloaded and LIBGEN_ENABLED:
            log.info(f"  [LibGen] Searching by title+author...")
            if try_libgen(title, authors, save_path, session):
                downloaded = True
                download_source = 'libgen'
            time.sleep(DOWNLOAD_DELAY)

        # Strategy 8: Garbage World public API
        if not downloaded:
            log.info(f"  [Garbage World] Searching...")
            if try_garbage_world(title, save_path, session):
                downloaded = True
                download_source = 'garbage_world'
            time.sleep(DOWNLOAD_DELAY)

        # Strategy 9: CSV fallback URLs (direct download attempts)
        if not downloaded:
            log.info(f"  [Fallback] Trying CSV URLs...")
            if try_csv_fallback(row, save_path, session):
                downloaded = True
                download_source = 'csv_fallback'

        # ── Result ──
        if downloaded:
            rows[row_idx]['PDF Path'] = save_path
            basename = os.path.basename(save_path)
            existing_files.add(basename)
            if uid:
                existing_by_id[uid] = basename
            norm_t = normalize_title(title)
            metadata[basename] = {
                'query':     row.get('Query') or '',
                'title':     title,
                'authors':   authors,
                'year':      year,
                'snippet':   row.get('Snippet') or '',
                'result_id': row.get('Result ID') or '',
                'link':      link,
            }
            existing_titles.add(norm_t)
            save_metadata(metadata)
            stat_key = f'downloaded_{download_source}'
            if stat_key in stats:
                stats[stat_key] += 1
            log.info(f"  SUCCESS via {download_source}: {filename[:80]}")
            _save_csv(rows, fieldnames)
        else:
            stats['download_failed'] += 1
            failed_rows.append({
                'Row': row_idx,
                'Title': title,
                'Authors': authors,
                'Year': year,
                'DOI': doi or '',
                'Link': link,
                'Resources': row.get('Resources') or '',
                'OpenAlex_Match': 'Yes' if work else 'No',
            })
            log.info(f"  FAILED: No PDF could be downloaded")

        # Periodic progress log + failure save
        if count % 50 == 0:
            log.info(f"  --- Progress: {count}/{len(needs_pdf)} ---")
            _save_failures(failed_rows)

    _save_csv(rows, fieldnames)
    _save_failures(failed_rows)

    log.info("=" * 60)
    log.info("SUMMARY")
    log.info("=" * 60)
    log.info(f"  OpenAlex matches:             {stats['openalex_match']}")
    log.info(f"  Downloaded (Direct URLs):     {stats['downloaded_direct_url']}")
    log.info(f"  Downloaded (OA URLs):         {stats['downloaded_oa_url']}")
    log.info(f"  Downloaded (Unpaywall):       {stats['downloaded_unpaywall']}")
    log.info(f"  Downloaded (Content API):     {stats['downloaded_content_api']}")
    log.info(f"  Downloaded (Domain handlers): {stats['downloaded_domain_handler']}")
    log.info(f"  Downloaded (Sci-Hub):         {stats['downloaded_scihub']}")
    log.info(f"  Downloaded (Anna's Archive):  {stats['downloaded_annas_archive']}")
    log.info(f"  Downloaded (AA RapidAPI):     {stats['downloaded_annas_rapidapi']}")
    log.info(f"  Downloaded (LibGen):          {stats['downloaded_libgen']}")
    log.info(f"  Downloaded (Garbage World):   {stats['downloaded_garbage_world']}")
    log.info(f"  Downloaded (CSV fallback):    {stats['downloaded_csv_fallback']}")
    log.info(f"  No OpenAlex match:            {stats['no_match']}")
    log.info(f"  Download failed:              {stats['download_failed']}")
    total = sum(v for k, v in stats.items() if k.startswith('downloaded_'))
    log.info(f"  TOTAL DOWNLOADED:             {total}")
    log.info(f"  Content API credits used:     {stats['content_api_credits_used']}")
    log.info(f"  Failed log: {FAILED_LOG}")

    _close_browser()


def _save_csv(rows, fieldnames):
    with open(SCHOLAR_CSV, 'w', newline='', encoding='utf-8') as f:
        writer = csv.DictWriter(
            f, fieldnames=fieldnames, delimiter=';',
            quoting=csv.QUOTE_MINIMAL, extrasaction='ignore')
        writer.writeheader()
        writer.writerows(rows)


def _save_failures(failed_rows):
    if not failed_rows:
        return
    fnames = ['Row', 'Title', 'Authors', 'Year', 'DOI', 'Link', 'Resources',
              'OpenAlex_Match']
    with open(FAILED_LOG, 'w', newline='', encoding='utf-8') as f:
        writer = csv.DictWriter(f, fieldnames=fnames)
        writer.writeheader()
        writer.writerows(failed_rows)


if __name__ == '__main__':
    main()
