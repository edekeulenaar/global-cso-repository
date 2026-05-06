#!/usr/bin/env python3
"""
Step 7 — Relevance screening with Gemini
=========================================
Reads master_bibliography.csv and asks Gemini to classify each item as
YES / NO / MAYBE relevant to censorship or content moderation research.

Criteria
--------
  YES   — clearly relevant: censorship, content moderation, platform
           governance, speech regulation, information control, media law,
           propaganda, deplatforming, shadowbanning, algorithmic curation,
           press freedom, index/indexing of forbidden books, computer science
           or AI applied to moderation, etc.
  MAYBE — uncertain relevance (tangentially related topic, vague abstract)
  NO    — clearly not relevant: medicine, psychology, psychiatry, physics,
           chemistry, biology, or other STEM unless directly about
           censorship/moderation; also general history, literature, law,
           philosophy, etc. with no connection to censorship or moderation.

Input:  master_bibliography.csv  (columns: Key, Author, Title,
                                   Abstract Note, Snippet, Url, …)
Output: master_bibliography.csv  — two new columns added in place:
          Relevant      YES | NO | MAYBE
          Relevant Note brief reason from the model

Resume-safe: rows that already have a non-empty Relevant value are skipped.
Results are flushed to disk every SAVE_EVERY rows.

Usage:
    python scholar_7_relevance.py                 # screen all unprocessed rows
    python scholar_7_relevance.py --limit 20      # test on 20 rows
    python scholar_7_relevance.py --start-from 50
    python scholar_7_relevance.py --model gemini-2.5-flash-preview-04-17
"""

import argparse
import csv
import logging
import os
import re
import sys
import time


# ═══════════════════════════════════════════════════════════════════════════════
# CONFIGURATION
# ═══════════════════════════════════════════════════════════════════════════════

GEMINI_API_KEY = ""  # set via environment or paste your key
GEMINI_MODEL   = "gemini-2.5-flash-lite"

BASE_DIR    = '/Users/edekeulenaar/Projects/PhDs/PhD 2020-2025/Publications 📇/Censorship and moderation'
MASTER_CSV  = os.path.join(BASE_DIR, 'master_bibliography.csv')

SAVE_EVERY  = 5     # flush to disk every N processed rows
REQUEST_DELAY = 4   # seconds between API calls — keeps us under 15 RPM free-tier limit

NEW_COLS = ['Relevant', 'Relevant Note']


# ═══════════════════════════════════════════════════════════════════════════════
# PROMPT
# ═══════════════════════════════════════════════════════════════════════════════

SYSTEM_PROMPT = """\
You are a research assistant screening academic literature for a PhD project \
on the history and theory of censorship and moderation.

Decide whether the item below is relevant to that project.

RELEVANT topics include (non-exhaustive):
- Censorship in any historical period or country
- Speech moderation in philosophy, political theory, sociology and other social science disciplines
- Moderation in conflict resolution
- Content moderation, platform governance, trust & safety
- Speech regulation, hate speech, harmful content policies
- Information control, propaganda, disinformation policy
- Press freedom, media law, broadcasting regulation
- Deplatforming, shadowbanning, algorithmic demotion
- Index of forbidden books, publication bans, prior restraint
- Computer science / AI / NLP applied to moderation or censorship
- Internet governance, online safety legislation
- The moderation of public debates (in any media)
- The moderation of public conflicts
- Moderating powers and roles in political and media systems
- Moderation in political philosophy, or philosophy in general
- The moderating role of different societal actors, such as media, schools, or other institutions
- Moderation in media, political, and religious contexts

NOT RELEVANT (answer NO):
- Medicine, clinical psychology, psychiatry, neuroscience
- Physics, chemistry, biology, ecology, earth sciences
- Engineering, materials science (unless about moderation tech)
- Mathematics (unless applied to moderation/censorship)
- Veterinary, agriculture, food science
- Items where censorship/moderation is mentioned only incidentally \
  (e.g. a history book that happens to mention a censor once)

Answer with EXACTLY one of: YES  /  NO  /  MAYBE
"""

ITEM_TEMPLATE = """\
Title:    {title}
Author:   {author}
URL:      {url}
Abstract: {abstract}
"""


# ═══════════════════════════════════════════════════════════════════════════════
# LOGGING
# ═══════════════════════════════════════════════════════════════════════════════

logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s [%(levelname)s] %(message)s',
    force=True,
    handlers=[logging.StreamHandler(sys.stdout)],
)
log = logging.getLogger(__name__)


# ═══════════════════════════════════════════════════════════════════════════════
# GEMINI CALL  (text-only — no file upload)
# ═══════════════════════════════════════════════════════════════════════════════

def classify_with_gemini(item_text: str, model_name: str) -> str:
    """Send item metadata to Gemini and return the raw response text.
    Retries up to 5 times on 429 / quota errors with increasing back-off."""
    from google import genai
    from google.genai import types as gt

    client = genai.Client(api_key=GEMINI_API_KEY)

    for attempt in range(5):
        try:
            response = client.models.generate_content(
                model=model_name,
                contents=SYSTEM_PROMPT + '\n\n' + item_text,
                config=gt.GenerateContentConfig(
                    temperature=0,          # deterministic
                    max_output_tokens=60,   # verdict + short reason is plenty
                ),
            )
            return (response.text or '').strip()
        except Exception as e:
            err = str(e)
            if '429' in err or 'quota' in err.lower() or 'rate' in err.lower():
                wait = 60 * (attempt + 1)   # 60 s, 120 s, 180 s …
                log.warning(f'  Rate limit hit (attempt {attempt+1}/5) — waiting {wait}s…')
                time.sleep(wait)
            else:
                raise   # non-rate-limit error: let the caller handle it

    raise RuntimeError('Max retries exceeded after repeated rate-limit errors')


# ═══════════════════════════════════════════════════════════════════════════════
# PARSE RESPONSE
# ═══════════════════════════════════════════════════════════════════════════════

_VERDICT_RE = re.compile(r'\b(YES|NO|MAYBE)\b', re.IGNORECASE)

def parse_verdict(text: str) -> tuple[str, str]:
    """Return (verdict, note) from model response."""
    m = _VERDICT_RE.search(text)
    if not m:
        return ('MAYBE', text[:120])
    verdict = m.group(1).upper()
    # Everything after the first pipe (if any) is the note
    if '|' in text:
        note = text.split('|', 1)[1].strip()
    else:
        note = text[m.end():].strip().lstrip('–—-:').strip()
    return verdict, note[:200]


# ═══════════════════════════════════════════════════════════════════════════════
# MAIN
# ═══════════════════════════════════════════════════════════════════════════════

def main():
    parser = argparse.ArgumentParser(description='Screen bibliography items for relevance.')
    parser.add_argument('--limit',      type=int, default=None, metavar='N')
    parser.add_argument('--start-from', type=int, default=0,    metavar='N')
    parser.add_argument('--model',      default=GEMINI_MODEL,   metavar='MODEL')
    args = parser.parse_args()

    # ── Load CSV (master_bibliography.csv is always comma-delimited) ──────────
    with open(MASTER_CSV, newline='', encoding='utf-8') as f:
        reader = csv.DictReader(f)   # default delimiter = comma
        fieldnames = list(reader.fieldnames or [])
        rows = list(reader)

    # Add new columns if not present
    for col in NEW_COLS:
        if col not in fieldnames:
            fieldnames.append(col)
            for r in rows:
                r.setdefault(col, '')

    log.info(f'Loaded {len(rows):,} rows from {os.path.basename(MASTER_CSV)}')

    # ── Build todo list ───────────────────────────────────────────────────────
    todo_indices = [
        i for i, r in enumerate(rows)
        if not (r.get('Relevant') or '').strip()
    ]
    log.info(f'Already screened: {len(rows) - len(todo_indices):,}')
    log.info(f'To screen:        {len(todo_indices):,}')

    if args.start_from:
        todo_indices = todo_indices[args.start_from:]
        log.info(f'Skipping first {args.start_from} → {len(todo_indices):,} remaining')
    if args.limit is not None:
        todo_indices = todo_indices[:args.limit]
        log.info(f'Limiting to {args.limit} → {len(todo_indices):,} to process')

    if not todo_indices:
        log.info('Nothing to do.')
        return

    # ── Processing loop ───────────────────────────────────────────────────────
    dirty = False  # tracks unsaved changes

    def flush():
        """Write to a unique temp file then atomically rename — crash-safe.
        Unique name avoids collision when scholar_9 flushes at the same time."""
        nonlocal dirty
        if not dirty:
            return
        import tempfile
        fd, tmp = tempfile.mkstemp(dir=BASE_DIR, suffix='.tmp', prefix='master_bib_s7_')
        try:
            with os.fdopen(fd, 'w', newline='', encoding='utf-8') as f:
                writer = csv.DictWriter(f, fieldnames=fieldnames,
                                        extrasaction='ignore',
                                        quoting=csv.QUOTE_ALL)
                writer.writeheader()
                writer.writerows(rows)
            os.replace(tmp, MASTER_CSV)
        except Exception:
            try:
                os.unlink(tmp)
            except OSError:
                pass
            raise
        log.info(f'  💾 Saved to {os.path.basename(MASTER_CSV)}')
        dirty = False

    for batch_n, idx in enumerate(todo_indices, 1):
        row = rows[idx]
        title    = (row.get('Title')         or '').strip()
        author   = (row.get('Author')        or '').strip()
        url      = (row.get('Url')           or row.get('Scholar Link') or '').strip()
        abstract = (row.get('Abstract Note') or row.get('Snippet') or '').strip()

        # Trim abstract to keep prompt small
        if len(abstract) > 500:
            abstract = abstract[:500] + '…'

        item_text = ITEM_TEMPLATE.format(
            title=title or '(no title)',
            author=author or '(unknown)',
            url=url or '(none)',
            abstract=abstract or '(none)',
        )

        log.info(f'[{batch_n}/{len(todo_indices)}] {title[:70]}')

        verdict = note = ''
        try:
            raw = classify_with_gemini(item_text, args.model)
            verdict, note = parse_verdict(raw)
            log.info(f'  → {verdict} | {note[:60]}')
        except Exception as e:
            log.error(f'  Error: {e}')
            verdict, note = 'MAYBE', f'Error: {e}'

        rows[idx]['Relevant']      = verdict
        rows[idx]['Relevant Note'] = note
        dirty = True

        if batch_n % SAVE_EVERY == 0 or batch_n == len(todo_indices):
            flush()

        time.sleep(REQUEST_DELAY)

    log.info(f'\nDone. Results written to {MASTER_CSV}')

    # ── Summary ───────────────────────────────────────────────────────────────
    counts = {'YES': 0, 'NO': 0, 'MAYBE': 0, '': 0}
    for r in rows:
        v = (r.get('Relevant') or '').upper()
        counts[v if v in counts else ''] += 1
    log.info(f"  YES: {counts['YES']:,}  |  NO: {counts['NO']:,}  "
             f"|  MAYBE: {counts['MAYBE']:,}  |  unscreened: {counts['']:,}")


if __name__ == '__main__':
    main()
