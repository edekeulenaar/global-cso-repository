#!/usr/bin/env python3
"""
Step 9 — Download PDFs for Gemini-relevant items
=================================================
Reads master_bibliography.csv, selects rows where Relevant = YES or MAYBE,
skips rows that already have a valid local PDF, and downloads the rest using
the full strategy chain from scholar_2_download.py (OpenAlex → Unpaywall →
Content API → domain handlers → Sci-Hub → Anna's Archive → LibGen → fallback).
Before downloading, it now harvests URLs from all Zotero/Scholar link fields
and resolves missing DOIs from embedded URLs or Crossref metadata.

Resume-safe:
  • Rows whose Local PDF Path points to a valid existing PDF are silently skipped.
  • Failed-log retries match by row number, Zotero Key, Result ID, or title.
  • Results are flushed to master_bibliography.csv every SAVE_EVERY rows.
  • Interrupt (Ctrl+C) triggers a clean save before exit.

Usage:
    python scholar_9_download_relevant.py
    python scholar_9_download_relevant.py --limit 20
    python scholar_9_download_relevant.py --start-from 50
    python scholar_9_download_relevant.py --from-failed-log --kb-only --workers 1
    python scholar_9_download_relevant.py --no-scihub --no-annas --no-libgen
    python scholar_9_download_relevant.py --dry-run
"""

import argparse
import csv
import importlib.util
import logging
import os
import re
import signal
import sys
import threading
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from urllib.parse import quote_plus, unquote, urlparse

# ═══════════════════════════════════════════════════════════════════════════════
# PATHS
# ═══════════════════════════════════════════════════════════════════════════════

BASE_DIR     = '/Users/edekeulenaar/Projects/PhDs/PhD 2020-2025/Publications 📇/Censorship and moderation'
MASTER_CSV   = os.path.join(BASE_DIR, 'master_bibliography.csv')
PDF_FOLDER   = os.path.join(BASE_DIR, 'PDF downloads')
FAILED_LOG   = os.path.join(BASE_DIR, 'failed_downloads_relevant.csv')
PROGRESS_LOG = os.path.join(BASE_DIR, 'download_progress.log')

SAVE_EVERY   = 5   # flush master CSV every N processed rows
DOI_RE       = re.compile(r'10\.\d{4,9}/[^\s,;\"\'<>#?]+', re.IGNORECASE)

# ═══════════════════════════════════════════════════════════════════════════════
# IMPORT DOWNLOAD FUNCTIONS FROM scholar_2_download.py
# (done via importlib so we can load it by absolute path without side-effects
#  on sys.modules and without needing an __init__.py)
# ═══════════════════════════════════════════════════════════════════════════════

_SCRIPTS_DIR = os.path.join(BASE_DIR, 'Scripts')
_DL_PATH     = os.path.join(_SCRIPTS_DIR, 'scholar_2_download.py')

_spec = importlib.util.spec_from_file_location('scholar_2_download', _DL_PATH)
_dl   = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_dl)   # runs module-level code incl. logging setup

# Re-configure logging so this script's messages also go to the shared log file
# (scholar_2_download already called basicConfig(force=True), so we just add our
#  stream handler on top; the FileHandler for PROGRESS_LOG is already attached).
log = logging.getLogger(__name__)

# ── Thread-local session storage ──────────────────────────────────────────────
# requests.Session is NOT thread-safe; each worker thread gets its own.
_thread_local = threading.local()

def _get_session() -> object:
    """Return a per-thread requests.Session, creating it on first access."""
    if not hasattr(_thread_local, 'session'):
        _thread_local.session = _dl.build_session(_dl.USER_EMAIL)
    return _thread_local.session

# Selenium can only safely run one browser at a time; gate it with a semaphore.
_selenium_lock = threading.Semaphore(1)

# ═══════════════════════════════════════════════════════════════════════════════
# HELPERS
# ═══════════════════════════════════════════════════════════════════════════════

def _has_valid_pdf(row: dict) -> bool:
    """Return True if the row already has a reachable, valid PDF on disk."""
    for col in ('Local PDF Path', 'File Attachments'):
        raw = (row.get(col) or '').strip()
        if not raw:
            continue
        for path in _candidate_attachment_paths(raw):
            if os.path.isfile(path) and _dl.is_valid_pdf(path):
                return True
    return False


def _candidate_attachment_paths(raw: str) -> list[str]:
    """Return possible filesystem paths from Zotero attachment fields.

    Zotero exports can contain absolute paths, file:// URLs, semicolon-delimited
    attachment lists, and descriptive prefixes. Keep this permissive so we avoid
    re-downloading PDFs that are already present.
    """
    if not raw:
        return []
    out = []
    for part in re.split(r'\s*;\s*|\s*\|\s*', raw):
        part = part.strip().strip('"')
        if not part:
            continue
        if part.startswith('file://'):
            part = unquote(part[7:])
        # Zotero sometimes stores "Title: /path/to/file.pdf".
        m = re.search(r'(/[^;|]+?\.pdf)\b', part, flags=re.IGNORECASE)
        candidates = [part]
        if m:
            candidates.insert(0, m.group(1))
        for candidate in candidates:
            candidate = candidate.strip()
            if candidate and candidate not in out:
                out.append(candidate)
    return out


def _clean_text(value) -> str:
    return re.sub(r'\s+', ' ', str(value or '')).strip()


def _normalise_doi(value: str) -> str:
    if not value:
        return ''
    value = value.strip()
    value = re.sub(r'^https?://(?:dx\.)?doi\.org/', '', value, flags=re.I)
    value = re.sub(r'^doi:\s*', '', value, flags=re.I)
    value = value.rstrip('.,;:)]}>')
    return value.lower()


def _extract_dois_from_text(text: str) -> list[str]:
    out = []
    for match in DOI_RE.finditer(text or ''):
        doi = _normalise_doi(match.group(0))
        if doi and doi not in out:
            out.append(doi)
    return out


def _extract_urls_from_text(text: str) -> list[str]:
    if not text:
        return []
    urls = []
    for match in re.finditer(r'https?://[^\s<>"\']+', text):
        url = match.group(0).rstrip('.,;:)]}>')
        if url and url not in urls:
            urls.append(url)
    return urls


def _collect_row_urls(row: dict) -> list[str]:
    """Harvest every useful URL-like field from master_bibliography.csv."""
    urls = []
    for col in (
        'Scholar Link', 'Url', 'Additional Link', 'Resources',
        'Link Attachments', 'File Attachments', 'Extra',
    ):
        for url in _extract_urls_from_text(row.get(col) or ''):
            if url not in urls:
                urls.append(url)
    doi = _normalise_doi(row.get('DOI') or '')
    if doi:
        doi_url = f'https://doi.org/{doi}'
        if doi_url not in urls:
            urls.insert(0, doi_url)
    return urls


def _master_row_to_dl_row(row: dict) -> dict:
    """
    Build the 'virtual row' dict that scholar_2_download's functions expect.

    scholar_2_download uses:
        Authors, Year, Title, Link, Resources, Result ID, Snippet, DOI
    master_bibliography.csv uses:
        Author, Publication Year / Scholar Year, Title,
        Scholar Link / Url, Resources, Result ID, Snippet, DOI
    """
    year = (row.get('Publication Year') or row.get('Scholar Year') or '').strip()
    urls = _collect_row_urls(row)
    link = urls[0] if urls else (row.get('Scholar Link') or row.get('Url') or '').strip()
    resources = ', '.join(urls)
    doi = _normalise_doi(row.get('DOI') or '')
    if not doi:
        for col in ('Scholar Link', 'Url', 'Additional Link', 'Resources', 'Extra', 'DOI'):
            dois = _extract_dois_from_text(row.get(col) or '')
            if dois:
                doi = dois[0]
                break
    return {
        'Title':     (row.get('Title')     or '').strip(),
        'Authors':   (row.get('Author')    or '').strip(),
        'Year':      year,
        'Link':      link,
        'Resources': resources,
        'Result ID': (row.get('Result ID') or '').strip(),
        'Snippet':   (row.get('Snippet')   or row.get('Abstract Note') or '').strip(),
        'DOI':       doi,
        'PDF Path':  '',   # will be written back as Local PDF Path
    }


def _flush(rows: list, fieldnames: list):
    """Write master_bibliography.csv atomically (unique temp → rename).
    Uses a unique temp name so concurrent writes from scholar_7 never collide."""
    import tempfile
    fd, tmp = tempfile.mkstemp(dir=BASE_DIR, suffix='.tmp', prefix='master_bib_s9_')
    try:
        with os.fdopen(fd, 'w', newline='', encoding='utf-8') as f:
            writer = csv.DictWriter(f, fieldnames=fieldnames,
                                    extrasaction='ignore',
                                    quoting=csv.QUOTE_ALL)
            writer.writeheader()
            writer.writerows(rows)
        os.replace(tmp, MASTER_CSV)   # atomic on POSIX / macOS
    except Exception:
        try:
            os.unlink(tmp)
        except OSError:
            pass
        raise
    log.info(f'  💾 Saved → {os.path.basename(MASTER_CSV)}')


def _load_failed_row_indices(path: str) -> set[int]:
    """Read failed_downloads_relevant.csv and return valid master-row indices."""
    out: set[int] = set()
    if not os.path.isfile(path):
        return out
    try:
        with open(path, newline='', encoding='utf-8') as f:
            for row in csv.DictReader(f):
                raw = (row.get('Row') or '').strip()
                if not raw:
                    continue
                try:
                    idx = int(raw)
                    if idx >= 0:
                        out.add(idx)
                except ValueError:
                    continue
    except Exception as e:
        log.warning(f'Could not read failed-log rows from {path}: {e}')
    return out


def _load_failed_selectors(path: str) -> list[dict]:
    """Read failed-log selectors for stable retry matching."""
    if not os.path.isfile(path):
        return []
    try:
        with open(path, newline='', encoding='utf-8') as f:
            return list(csv.DictReader(f))
    except Exception as e:
        log.warning(f'Could not read failed-log selectors from {path}: {e}')
        return []


def _matches_failed_selector(idx: int, row: dict, selectors: list[dict]) -> bool:
    if not selectors:
        return False
    key = (row.get('Key') or '').strip()
    rid = (row.get('Result ID') or '').strip()
    norm_title = _dl.normalize_title(row.get('Title') or '')
    for selector in selectors:
        raw_row = (selector.get('Row') or '').strip()
        if raw_row:
            try:
                if int(raw_row) == idx:
                    return True
            except ValueError:
                pass
        if key and key == (selector.get('Key') or '').strip():
            return True
        if rid and rid == (selector.get('Result ID') or '').strip():
            return True
        if norm_title and norm_title == (selector.get('Norm Title') or '').strip():
            return True
    return False


def _host_from_url(url: str) -> str:
    try:
        return urlparse(url).netloc.lower().removeprefix('www.')
    except Exception:
        return ''


def _resolve_doi_crossref(title: str, year: str, authors: str,
                          session: object) -> tuple[str, str]:
    """Resolve a likely DOI from Crossref using title/year/author metadata."""
    title = _clean_text(title)
    if not title:
        return '', ''
    params = {
        'query.title': title,
        'rows': 5,
        'select': 'DOI,title,issued,published-print,published-online,author,container-title',
    }
    first_author = _dl.extract_first_author_lastname(authors)
    if first_author:
        params['query.author'] = first_author

    try:
        resp = session.get('https://api.crossref.org/works', params=params, timeout=20)
        if resp.status_code != 200:
            return '', ''
        items = resp.json().get('message', {}).get('items', [])
    except Exception as e:
        log.debug(f'  Crossref DOI lookup error: {e}')
        return '', ''

    wanted_year = None
    try:
        wanted_year = int(float(year)) if year else None
    except (TypeError, ValueError):
        wanted_year = None

    best = None
    best_score = 0.0
    for item in items:
        item_title = ''
        titles = item.get('title') or []
        if titles:
            item_title = titles[0]
        score = _dl.title_similarity(title, item_title)

        item_year = None
        for key in ('issued', 'published-print', 'published-online'):
            parts = item.get(key, {}).get('date-parts') or []
            if parts and parts[0]:
                item_year = parts[0][0]
                break
        if wanted_year and item_year:
            delta = abs(wanted_year - int(item_year))
            if delta == 0:
                score += 0.05
            elif delta > 2:
                score -= 0.10

        if first_author:
            author_lastnames = [
                _clean_text(a.get('family')).lower()
                for a in item.get('author') or []
                if a.get('family')
            ]
            if any(first_author.lower() == a for a in author_lastnames):
                score += 0.05

        if score > best_score:
            best_score = score
            best = item

    if best and best_score >= 0.82:
        doi = _normalise_doi(best.get('DOI') or '')
        if doi:
            return doi, f'crossref:{best_score:.2f}'
    return '', ''


def _resolve_missing_doi(dl_row: dict, session: object) -> tuple[str, str]:
    doi = _normalise_doi(dl_row.get('DOI') or '')
    if doi:
        return doi, 'csv'

    for field in ('Link', 'Resources', 'Snippet'):
        dois = _extract_dois_from_text(dl_row.get(field) or '')
        if dois:
            return dois[0], f'{field.lower()}_text'

    return _resolve_doi_crossref(
        dl_row.get('Title') or '',
        dl_row.get('Year') or '',
        dl_row.get('Authors') or '',
        session,
    )


# ═══════════════════════════════════════════════════════════════════════════════
# MAIN
# ═══════════════════════════════════════════════════════════════════════════════

def main():
    parser = argparse.ArgumentParser(
        description='Download PDFs for YES/MAYBE relevant rows in master_bibliography.csv.')
    parser.add_argument('--limit',      type=int, default=None, metavar='N',
                        help='Process at most N rows.')
    parser.add_argument('--start-from', type=int, default=0,    metavar='N',
                        help='Skip first N todo rows (for resuming).')
    parser.add_argument('--dry-run',    action='store_true',
                        help='Show what would happen without downloading anything.')
    parser.add_argument('--no-scihub',  action='store_true', help='Disable Sci-Hub.')
    parser.add_argument('--no-annas',   action='store_true', help="Disable Anna's Archive.")
    parser.add_argument('--no-libgen',  action='store_true', help='Disable LibGen.')
    parser.add_argument('--no-content-api', action='store_true',
                        help='Disable OpenAlex Content API (saves credits).')
    parser.add_argument('--no-kb', action='store_true',
                        help='Disable KB Royal Danish Library search.')
    parser.add_argument('--kb-first', action='store_true',
                        help='Try KB Royal Danish Library before OpenAlex/domain strategies.')
    parser.add_argument('--kb-only', action='store_true',
                        help='Only run KB Royal Danish Library retrieval.')
    parser.add_argument('--from-failed-log', action='store_true',
                        help='Only process rows listed in failed_downloads_relevant.csv.')
    parser.add_argument('--watch', action='store_true',
                        help='Keep running: re-check master CSV every --poll-minutes '
                             'for new YES/MAYBE rows as scholar_7 screens them.')
    parser.add_argument('--poll-minutes', type=float, default=5, metavar='N',
                        help='Polling interval in watch mode (default: 5 minutes).')
    parser.add_argument('--workers', type=int, default=3, metavar='N',
                        help='Parallel download workers (default: 3). '
                             'Each worker runs the full strategy chain independently.')
    args = parser.parse_args()

    # Override flags on the imported download module
    if args.no_scihub:
        _dl.SCIHUB_ENABLED = False
    if args.no_annas:
        _dl.ANNAS_ARCHIVE_ENABLED = False
    if args.no_libgen:
        _dl.LIBGEN_ENABLED = False
    if args.no_content_api:
        _dl.USE_CONTENT_API = False
    KB_ENABLED = not args.no_kb
    if args.kb_only and not KB_ENABLED:
        parser.error('--kb-only cannot be combined with --no-kb.')
    _dl.DRY_RUN = args.dry_run

    if args.from_failed_log:
        log.warning(
            'Running with --from-failed-log: only rows listed in '
            'failed_downloads_relevant.csv will be processed.'
        )

    poll_secs   = int(args.poll_minutes * 60)
    first_pass  = True
    pass_number = 0

    # ── Persistent state (kept across watch-mode iterations) ──────────────────
    os.makedirs(PDF_FOLDER, exist_ok=True)
    session     = _dl.build_session(_dl.USER_EMAIL)
    metadata    = _dl.load_metadata()
    existing_titles = {
        _dl.normalize_title(m.get('title', ''))
        for m in metadata.values() if m.get('title')
    }
    existing_files = {f for f in os.listdir(PDF_FOLDER) if f.endswith('.pdf')}
    existing_by_id: dict = {}
    for fname in existing_files:
        m = re.search(r' - ([A-Za-z0-9_\-]+)\.pdf$', fname)
        if m:
            existing_by_id[m.group(1)] = fname

    failed_rows: list = []
    stats = {k: 0 for k in (
        'downloaded_direct_url', 'downloaded_oa_url', 'downloaded_unpaywall',
        'downloaded_content_api', 'downloaded_domain_handler', 'downloaded_kb_library',
        'downloaded_scihub', 'downloaded_annas_archive', 'downloaded_annas_rapidapi',
        'downloaded_libgen', 'downloaded_garbage_world', 'downloaded_csv_fallback',
        'openalex_match', 'no_match', 'download_failed', 'content_api_credits_used',
        'doi_resolved',
    )}

    # ── Interrupt handler ──────────────────────────────────────────────────────
    rows: list      = []
    fieldnames: list = []
    dirty           = False

    def _on_interrupt(sig, frame):
        log.info('\nInterrupted — saving progress…')
        if dirty and rows:
            _flush(rows, fieldnames)
        _save_failures(failed_rows)
        _dl.save_metadata(metadata)
        _dl._close_browser()
        sys.exit(0)

    signal.signal(signal.SIGINT,  _on_interrupt)
    signal.signal(signal.SIGTERM, _on_interrupt)

    # ══════════════════════════════════════════════════════════════════════════
    # WATCH LOOP — iterates once normally, then keeps polling in --watch mode
    # ══════════════════════════════════════════════════════════════════════════
    while True:
        if not first_pass:
            log.info(f'\n⏳ Watch mode — sleeping {args.poll_minutes:.0f} min…')
            time.sleep(poll_secs)
        first_pass = False
        pass_number += 1

        log.info('═' * 60)
        log.info('STEP 9: Download PDFs for relevant items')
        log.info('═' * 60)

        # ── Re-read CSV fresh every iteration ─────────────────────────────────
        with open(MASTER_CSV, newline='', encoding='utf-8') as f:
            reader     = csv.DictReader(f)
            fieldnames = list(reader.fieldnames or [])
            rows       = list(reader)

        log.info(f'Loaded {len(rows):,} rows from master_bibliography.csv')

        if 'Local PDF Path' not in fieldnames:
            fieldnames.append('Local PDF Path')
            for r in rows:
                r.setdefault('Local PDF Path', '')

        # ── Build todo list ────────────────────────────────────────────────────
        todo_indices = []
        already_have = not_relevant = 0
        for i, row in enumerate(rows):
            verdict = (row.get('Relevant') or '').strip().upper()
            if verdict not in ('YES', 'MAYBE'):
                not_relevant += 1
                continue
            if _has_valid_pdf(row):
                already_have += 1
                continue
            todo_indices.append(i)

        if args.from_failed_log:
            failed_selectors = _load_failed_selectors(FAILED_LOG)
            before = len(todo_indices)
            todo_indices = [
                i for i in todo_indices
                if _matches_failed_selector(i, rows[i], failed_selectors)
            ]
            log.info(f'  Filtered by failed-log rows:      {before} → {len(todo_indices):,}')

        log.info(f'  Not relevant (NO / unscreened): {not_relevant:,}')
        log.info(f'  Already have PDF:               {already_have:,}')
        log.info(f'  To download:                    {len(todo_indices):,}')

        # start-from / limit only apply on the very first pass
        if args.start_from and pass_number == 1:
            todo_indices = todo_indices[args.start_from:]
            log.info(f'  Skipping first {args.start_from} → {len(todo_indices):,} remaining')
        if args.limit is not None and pass_number == 1:
            todo_indices = todo_indices[:args.limit]
            log.info(f'  Limiting to {args.limit} → {len(todo_indices):,} to process')

        if not todo_indices:
            if args.watch:
                log.info('Nothing to do yet — watching for new YES/MAYBE rows. '
                         'Ctrl+C to stop.')
                continue   # sleep at top of next iteration
            log.info('Nothing to do.')
            break

        # ── Per-item worker (runs in thread) ──────────────────────────────────
        def _download_one(task: tuple) -> dict:
            """Full strategy chain for one row. Returns a result dict.
            Reads shared state but never writes it — all writes happen in the
            main thread under _state_lock after the future completes."""
            idx, row, dl_row = task
            session  = _get_session()
            title    = dl_row['Title']
            authors  = dl_row['Authors']
            year     = dl_row['Year']
            link     = dl_row['Link']
            uid      = dl_row['Result ID']
            norm_t   = _dl.normalize_title(title)
            filename = _dl.generate_filename(dl_row)
            save_path = os.path.join(PDF_FOLDER, filename)

            result = dict(idx=idx, downloaded=False, save_path=save_path,
                          source=None, uid=uid, norm_t=norm_t, title=title,
                          authors=authors, year=year, link=link, doi='',
                          work_found=False, dl_row=dl_row, row=row,
                          filename=filename, doi_resolved=False,
                          doi_source='', attempted_hosts=[])
            result['attempted_hosts'] = sorted({
                _host_from_url(u)
                for u in _extract_urls_from_text((dl_row.get('Resources') or '') + ' ' + link)
                if _host_from_url(u)
            })

            # Already on disk — exact filename?
            if os.path.isfile(save_path) and _dl.is_valid_pdf(save_path):
                log.info(f'  [{title[:50]}] Already on disk (exact name)')
                result['downloaded'] = True; result['source'] = 'already_on_disk'
                return result

            # Already on disk — by Result ID?
            if uid and uid in existing_by_id:
                candidate = os.path.join(PDF_FOLDER, existing_by_id[uid])
                if os.path.isfile(candidate) and _dl.is_valid_pdf(candidate):
                    log.info(f'  [{title[:50]}] Already on disk (ID match)')
                    result['downloaded'] = True; result['source'] = 'already_on_disk'
                    result['save_path'] = candidate
                    return result

            # Already on disk — by normalised title?
            if norm_t and norm_t in existing_titles:
                for fname, meta in metadata.items():
                    if _dl.normalize_title(meta.get('title', '')) == norm_t:
                        candidate = os.path.join(PDF_FOLDER, fname)
                        if os.path.isfile(candidate) and _dl.is_valid_pdf(candidate):
                            log.info(f'  [{title[:50]}] Already on disk (title match)')
                            result['downloaded'] = True; result['source'] = 'already_on_disk'
                            result['save_path'] = candidate
                            return result

            doi, doi_source = _resolve_missing_doi(dl_row, session)
            if doi:
                dl_row['DOI'] = doi
                doi_url = f'https://doi.org/{doi}'
                resources = dl_row.get('Resources') or ''
                if doi_url not in resources:
                    dl_row['Resources'] = (resources + ', ' + doi_url).strip(', ')
                if doi_source != 'csv':
                    result['doi_resolved'] = True
                    result['doi_source'] = doi_source
                    log.info(f'    [DOI] Resolved {doi} via {doi_source}')
            result['doi'] = doi

            log.info(f'  Downloading: {title[:70]}')

            def _try_kb_once() -> bool:
                if not (KB_ENABLED and title):
                    return False
                log.info(f'    [KB] {title[:60]}')
                with _selenium_lock:
                    got = _dl.try_kb_library(title, authors, save_path, session)
                if got:
                    result['downloaded'] = True
                    result['source'] = 'kb_library'
                    return True
                time.sleep(_dl.DOWNLOAD_DELAY)
                return False

            if args.kb_only:
                _try_kb_once()
                return result

            if args.kb_first and _try_kb_once():
                return result

            # Strategy 0: Direct URLs
            _seen_direct: set = set()
            for col in ('Resources', 'Link'):
                for u in (dl_row.get(col) or '').split(', '):
                    u = u.strip()
                    if u.startswith('http') and u not in _seen_direct:
                        _seen_direct.add(u)
                        log.info(f'    [Direct] {u[:100]}')
                        if _dl.try_download_pdf(u, save_path, session):
                            result['downloaded'] = True; result['source'] = 'direct_url'
                            return result
                        time.sleep(_dl.DOWNLOAD_DELAY)

            # OpenAlex lookup
            work = None
            work, doi = _dl.search_openalex(
                title, year, authors, link, session, _dl.USER_EMAIL)
            result['doi'] = doi
            time.sleep(_dl.API_DELAY)

            if work:
                result['work_found'] = True
                log.info(f'    OpenAlex: {_dl.strip_html(work.get("title",""))[:70]}')
                for url in _dl.extract_oa_pdf_urls(work):
                    log.info(f'    [OA] {url[:100]}')
                    if _dl.try_download_pdf(url, save_path, session):
                        result['downloaded'] = True; result['source'] = 'oa_url'
                        return result
                    time.sleep(_dl.DOWNLOAD_DELAY)
                if doi and _dl.try_unpaywall(doi, save_path, session, _dl.USER_EMAIL):
                    result['downloaded'] = True; result['source'] = 'unpaywall'
                    return result
                if _dl.USE_CONTENT_API:
                    content_url = _dl.get_content_api_url(work)
                    if content_url:
                        if _dl.try_content_api(content_url, save_path, session):
                            result['downloaded'] = True; result['source'] = 'content_api'
                            result['used_content_api'] = True
                            return result
                        time.sleep(_dl.DOWNLOAD_DELAY)
            else:
                log.info(f'    No OpenAlex match (DOI: {doi})')
                if doi and _dl.try_unpaywall(doi, save_path, session, _dl.USER_EMAIL):
                    result['downloaded'] = True; result['source'] = 'unpaywall'
                    return result

            # Strategy 4: Domain handlers
            _seen_s4: set = set()
            for col in ('Link', 'Resources'):
                for u in (dl_row.get(col) or '').split(', '):
                    u = u.strip()
                    if u.startswith('http') and u not in _seen_s4:
                        _seen_s4.add(u)
                        if _dl.try_domain_handlers(u, save_path, session, row=dl_row):
                            result['downloaded'] = True; result['source'] = 'domain_handler'
                            return result
                        time.sleep(_dl.DOWNLOAD_DELAY)

            # Strategy 4b: KB Royal Danish Library — Primo "Get PDF" OA links
            if not args.kb_first and _try_kb_once():
                return result

            # Strategy 5: Sci-Hub (browser calls are gated by _selenium_lock)
            if _dl.SCIHUB_ENABLED:
                _seen_sc: set = set()
                for _c in ([doi] if doi else []) + [link] + \
                        [u.strip() for u in (dl_row.get('Resources') or '').split(', ')]:
                    _c = (_c or '').strip()
                    if not _c or _c in _seen_sc:
                        continue
                    if any(s in _c for s in _dl._SCIHUB_SKIP_DOMAINS):
                        continue
                    _seen_sc.add(_c)
                    log.info(f'    [Sci-Hub] {_c[:70]}')
                    with _selenium_lock:
                        got = _dl.try_scihub(_c, save_path, session)
                    if got:
                        result['downloaded'] = True; result['source'] = 'scihub'
                        return result
                    time.sleep(_dl.DOWNLOAD_DELAY)

            # Strategy 6: Anna's Archive
            if _dl.ANNAS_ARCHIVE_ENABLED:
                log.info(f"    [Anna's Archive] {title[:60]}")
                if _dl.try_annas_archive_title(title, authors, save_path, session):
                    result['downloaded'] = True; result['source'] = 'annas_archive'
                    return result
                time.sleep(_dl.DOWNLOAD_DELAY)

            # Strategy 6b: Anna's Archive RapidAPI
            if _dl.ANNAS_ARCHIVE_ENABLED:
                log.info(f'    [AA/RapidAPI] {title[:60]}')
                if _dl.try_annas_archive_rapidapi(title, authors, save_path, session):
                    result['downloaded'] = True; result['source'] = 'annas_rapidapi'
                    return result
                time.sleep(_dl.DOWNLOAD_DELAY)

            # Strategy 7: LibGen
            if _dl.LIBGEN_ENABLED:
                log.info(f'    [LibGen] {title[:60]}')
                if _dl.try_libgen(title, authors, save_path, session):
                    result['downloaded'] = True; result['source'] = 'libgen'
                    return result
                time.sleep(_dl.DOWNLOAD_DELAY)

            # Strategy 8: Garbage World
            log.info(f'    [Garbage World] {title[:60]}')
            if _dl.try_garbage_world(title, save_path, session):
                result['downloaded'] = True; result['source'] = 'garbage_world'
                return result
            time.sleep(_dl.DOWNLOAD_DELAY)

            # Strategy 9: CSV fallback
            log.info(f'    [Fallback] {title[:60]}')
            if _dl.try_csv_fallback(dl_row, save_path, session):
                result['downloaded'] = True; result['source'] = 'csv_fallback'
                return result

            return result   # downloaded=False

        # ── Concurrent download ────────────────────────────────────────────────
        if args.dry_run:
            for batch_n, idx in enumerate(todo_indices, 1):
                log.info(f'[{batch_n}/{len(todo_indices)}] [DRY RUN] '
                         f'{rows[idx].get("Title","")[:80]}')
        else:
            _state_lock = threading.Lock()
            completed = dirty = 0
            total     = len(todo_indices)

            log.info(f'Starting {total} downloads with {args.workers} workers…')

            tasks = [(idx, rows[idx], _master_row_to_dl_row(rows[idx]))
                     for idx in todo_indices]

            with ThreadPoolExecutor(max_workers=args.workers) as executor:
                futures = {executor.submit(_download_one, task): task
                           for task in tasks}

                for future in as_completed(futures):
                    try:
                        r = future.result()
                    except Exception as e:
                        task = futures[future]
                        idx  = task[0]
                        log.error(f'  Worker exception for row {idx}: {e}')
                        r = dict(idx=idx, downloaded=False, source=None,
                                 title=rows[idx].get('Title',''), doi='',
                                 link='', authors='', year='', uid='',
                                 norm_t='', work_found=False, dl_row=task[2],
                                 row=task[1], save_path='', filename='',
                                 doi_resolved=False, doi_source='',
                                 attempted_hosts=[])

                    completed += 1
                    with _state_lock:
                        idx = r['idx']
                        if r.get('doi') and not (rows[idx].get('DOI') or '').strip():
                            rows[idx]['DOI'] = r['doi']
                        if r.get('doi_resolved'):
                            stats['doi_resolved'] += 1
                        if r['downloaded']:
                            rows[idx]['Local PDF Path'] = r['save_path']
                            fname_base = os.path.basename(r['save_path'])
                            existing_files.add(fname_base)
                            if r['uid']:
                                existing_by_id[r['uid']] = fname_base
                            metadata[fname_base] = {
                                'query':     rows[idx].get('Query') or '',
                                'title':     r['title'],
                                'authors':   r['authors'],
                                'year':      r['year'],
                                'snippet':   r['dl_row'].get('Snippet') or '',
                                'result_id': r['uid'],
                                'link':      r['link'],
                                'doi':       r.get('doi') or '',
                            }
                            existing_titles.add(r['norm_t'])
                            _dl.save_metadata(metadata)
                            src = r['source'] or 'unknown'
                            stats[f'downloaded_{src}'] = \
                                stats.get(f'downloaded_{src}', 0) + 1
                            if r.get('used_content_api'):
                                stats['content_api_credits_used'] += 100
                            if r.get('work_found'):
                                stats['openalex_match'] += 1
                            log.info(f'  ✅ [{completed}/{total}] {r["title"][:60]} '
                                     f'← {src}')
                        else:
                            if r.get('work_found'):
                                stats['openalex_match'] += 1
                            else:
                                stats['no_match'] += 1
                            stats['download_failed'] += 1
                            failed_rows.append({
                                'Row':          idx,
                                'Key':          rows[idx].get('Key') or '',
                                'Result ID':    rows[idx].get('Result ID') or r.get('uid') or '',
                                'Norm Title':   r.get('norm_t') or '',
                                'Title':        r['title'],
                                'Authors':      r['authors'],
                                'Year':         r['year'],
                                'DOI':          r['doi'] or '',
                                'DOI Source':   r.get('doi_source') or '',
                                'Link':         r['link'],
                                'Resources':    r['dl_row'].get('Resources') or '',
                                'Attempted Hosts': '; '.join(r.get('attempted_hosts') or []),
                                'Primary Host': _host_from_url(r['link']),
                                'OpenAlex_Match': 'Yes' if r['work_found'] else 'No',
                                'Relevant':     rows[idx].get('Relevant') or '',
                            })
                            log.info(f'  ✗ [{completed}/{total}] {r["title"][:60]}')

                        dirty += 1
                        if dirty % SAVE_EVERY == 0 or completed == total:
                            _flush(rows, fieldnames)
                            _save_failures(failed_rows)
                            dirty = 0

        # ── End of batch ───────────────────────────────────────────────────────
        if not args.dry_run:
            _flush(rows, fieldnames)
            _save_failures(failed_rows)

        total_dl = sum(v for k, v in stats.items() if k.startswith('downloaded_'))
        log.info('\n' + '═' * 60)
        log.info('SUMMARY (cumulative)')
        log.info('═' * 60)
        for k, v in stats.items():
            if v:
                log.info(f'  {k:<35} {v:,}')
        log.info(f'  {"TOTAL DOWNLOADED":<35} {total_dl:,}')
        log.info(f'  {"FAILED":<35} {stats["download_failed"]:,}')

        if not args.watch:
            break
        # else: loop back, sleep at top of next iteration

    _dl._close_browser()
    log.info(f'\nResults written to {MASTER_CSV}')
    log.info(f'Failed log:         {FAILED_LOG}')


# ═══════════════════════════════════════════════════════════════════════════════
# FAILURE LOG
# ═══════════════════════════════════════════════════════════════════════════════

def _save_failures(failed_rows: list):
    if not failed_rows:
        return
    fnames = [
        'Row', 'Key', 'Result ID', 'Norm Title',
        'Title', 'Authors', 'Year', 'DOI', 'DOI Source',
        'Link', 'Resources', 'Attempted Hosts', 'Primary Host',
        'OpenAlex_Match', 'Relevant',
    ]
    with open(FAILED_LOG, 'w', newline='', encoding='utf-8') as f:
        writer = csv.DictWriter(f, fieldnames=fnames, extrasaction='ignore')
        writer.writeheader()
        writer.writerows(failed_rows)


if __name__ == '__main__':
    main()
