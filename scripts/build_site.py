#!/usr/bin/env python3
"""
Build a static GitHub-Pages-ready directory of CSOs from
cso_extraction_results.csv, joined with master_bibliography_disciplines_enriched.csv
for URLs and Topics.

Pipeline
--------
1. Read both CSVs.
2. Normalise with Gemini (cached → reruns only normalise NEW values):
     - Where → split into {countries:[...], media:[...]}
              (drop vague regions; collapse subdivisions to country;
               expand "MENA, specifically X, Y, Z" → those countries;
               Media = platforms / media types / AI model families)
     - When  → {label, start, end}  e.g. "Cold War" → 1947–1991
     - Norms → list of atomic norms / values / interests
3. Group rows by canonical CSO name → one card per CSO with the list of
   source papers that mention it.
4. Emit site/data.json + site/index.html.

Usage:
    python3 build_site.py                # incremental
    python3 build_site.py --skip-norm    # don't call Gemini at all
    python3 build_site.py --rebuild      # invalidate cache, normalise everything
"""

import argparse
import csv
import json
import os
import re
import sys
import threading
import time
import unicodedata
from collections import defaultdict, Counter
from concurrent.futures import ThreadPoolExecutor, as_completed

# ─── Paths ───────────────────────────────────────────────────────────────────
HERE = os.path.dirname(os.path.abspath(__file__))
EXTRACT_CSV = os.path.join(HERE, 'cso_extraction_results.csv')
BIB_CSV = (
    '/Users/edekeulenaar/Projects/PhDs/PhD 2020-2025/Publications 📇/'
    'Censorship and moderation/Analyses/'
    'master_bibliography_disciplines_enriched.csv'
)
SITE_DIR = os.path.join(HERE, 'site')
CACHE = os.path.join(HERE, 'normalizations.json')

GEMINI_API_KEY = ""  # set via environment or paste your key
GEMINI_MODEL = "gemini-2.5-flash"
BATCH_SIZE = 40


# ─── Prompts ─────────────────────────────────────────────────────────────────

WHERE_PROMPT = """\
You normalise messy "place / setting" strings extracted from academic papers
on censorship, moderation, and AI alignment into TWO atomic facet lists:
COUNTRIES and MEDIA.

For each input string, return:
  countries: list of countries (English canonical names) and supranational
             units when no specific country is named.
             - Prefer specific countries; collapse subdivisions to country
               ("Kanawha County, West Virginia, and the United States"
                → ["United States"]).
             - Expand region lists ("MENA region, specifically Morocco,
               Algeria, Tunisia, Libya, Lebanon, Syria, and Gulf countries"
                → ["Morocco","Algeria","Tunisia","Libya","Lebanon","Syria","Gulf countries"]).
             - Use the same canonical English form everywhere ("United States",
               not "USA"/"US"/"America"; "United Kingdom" not "UK").
             - Include historical polities as named ("Soviet Union", "Holy
               Roman Empire", "Weimar Republic").
             - "Global", "global focus", "worldwide" → ["Global"].
  media:     list of platforms, media types, or AI models named.
             - Platforms ("Facebook", "Weibo", "Twitter", "Reddit", "YouTube"
               "TikTok").
             - Media types ("printed pamphlets", "broadcast television",
               "samizdat", "newspapers", "books").
             - AI model families ("GPT-4", "Claude 3", "Llama 2", "Gemini").
             - Same canonical form across inputs.

Drop vague things (just "platforms", "the internet", "social media" alone) —
those are too generic to be useful filters.

If empty / "n/a" / "uncertain" → {"countries": [], "media": []}.
Never invent facets not implied by the input.

INPUT: a JSON array of strings.
OUTPUT: a JSON array of objects {countries:[], media:[]} — same length, same order.
Wrap in ```json fences.

Example:
Input:  ["Weibo, China", "Kanawha County, WV, USA", "n/a", "GPT-4 (USA)"]
Output: [
  {"countries":["China"],"media":["Weibo"]},
  {"countries":["United States"],"media":[]},
  {"countries":[],"media":[]},
  {"countries":["United States"],"media":["GPT-4"]}
]
"""

WHEN_PROMPT = """\
You normalise messy "time / epoch" strings extracted from academic papers on
censorship, moderation, and AI alignment.

For each input string, return an object:
  label: ONE canonical period label.
         - Pre-1900 → century label ("16th century", "17th century").
         - 20th c. → century or well-known period ("Weimar", "Nazi Germany",
           "Cold War", "post-WWII", "1960s", "1980s").
         - Post-2000 → "21st century" or "post-2010 platform era".
         - Year ranges in one century → that century.
         - Year ranges crossing centuries → "16th–17th century" etc.
         - Empty/"n/a"/"uncertain" → "unspecified".
  start: integer year >= 1400 (best estimate). null if "unspecified".
         If a paper alludes to deeper antiquity for an organisation
         that exists today (e.g. "the Catholic Church since antiquity"),
         use 1400 as the start, NOT a BCE year.
  end:   integer year <= 2025. Use 2025 for "present"/ongoing. null if
         "unspecified".

Reference periods:
- "16th century": 1500–1599
- "17th century": 1600–1699
- "Reformation": 1517–1648
- "early modern": 1500–1800
- "Enlightenment": 1685–1815
- "Weimar": 1918–1933
- "Nazi Germany": 1933–1945
- "Cold War": 1947–1991
- "post-WWII": 1945–1991
- "post-2010 platform era": 2010–2025
- "21st century": 2000–2025

INPUT: a JSON array of strings.
OUTPUT: a JSON array of {label, start, end} objects — same length, same order.
Wrap in ```json fences.
"""

NORMS_PROMPT = """\
You normalise messy "norms / values / interests" strings extracted from
academic papers on censorship, moderation, and AI alignment into a list of
atomic, filterable facets.

RULES
- Output a list of 1–5 atomic facets per input.
- Use SHORT canonical noun phrases in lowercase English ("free speech",
  "public morals", "trade monopoly", "religious orthodoxy", "national
  security", "child safety", "professional honour", "workers' rights",
  "scientific integrity", "anti-misinformation", "AI safety", "harm
  reduction", "platform autonomy", "user safety", "democratic integrity").
- Use the SAME canonical form across inputs (e.g. always "free speech",
  not "freedom of expression"/"free expression"; always "public morals"
  not "morality"/"morals"). Collapse near-synonyms.
- Empty/"n/a" → [].
- Never invent facets not implied by the input.

INPUT: a JSON array of strings.
OUTPUT: a JSON array of arrays — same length, same order.
Wrap in ```json fences.
"""


# ─── Gemini ──────────────────────────────────────────────────────────────────

def gemini_call(prompt: str, values: list[str]):
    from google import genai
    client = genai.Client(api_key=GEMINI_API_KEY)
    payload = prompt + '\n\nINPUT:\n' + json.dumps(values, ensure_ascii=False)
    resp = client.models.generate_content(model=GEMINI_MODEL, contents=payload)
    text = resp.text or ''
    m = re.search(r'```(?:json)?\s*([\s\S]*?)\s*```', text)
    raw = m.group(1) if m else text
    try:
        out = json.loads(raw)
    except json.JSONDecodeError:
        m2 = re.search(r'\[[\s\S]*\]', raw)
        out = json.loads(m2.group(0)) if m2 else None
    if not isinstance(out, list) or len(out) != len(values):
        raise ValueError(f'bad shape: got {type(out).__name__} '
                         f'len {len(out) if isinstance(out, list) else "?"} '
                         f'vs expected {len(values)}')
    return out


_cache_lock = threading.Lock()

def batched(values: list[str], prompt: str, kind: str, default,
            workers: int = 8):
    """Parallelise Gemini batches across `workers` threads.
    Cache writes are serialised via _cache_lock; cache is saved after every
    completed batch.
    """
    out = {}
    n = len(values)
    batches = [values[i:i + BATCH_SIZE] for i in range(0, n, BATCH_SIZE)]
    completed = [0]
    start = time.time()

    def _do_batch(batch_idx, batch):
        for attempt in range(1, 4):
            try:
                results = gemini_call(prompt, batch)
                return batch_idx, batch, results, None
            except Exception as e:
                wait = 5 * attempt
                if attempt < 3:
                    time.sleep(wait)
                else:
                    return batch_idx, batch, None, e

    with ThreadPoolExecutor(max_workers=workers) as ex:
        futures = [ex.submit(_do_batch, i, b) for i, b in enumerate(batches)]
        for fut in as_completed(futures):
            bi, batch, results, err = fut.result()
            if err is not None:
                d = default() if callable(default) else default
                results = [d] * len(batch)
                print(f'  [{kind}] batch {bi} FAILED: {str(err)[:100]}')
            with _cache_lock:
                for v, r in zip(batch, results):
                    out[v] = r
                    _cache_global[kind][v] = r
                completed[0] += 1
                done_items = min(completed[0] * BATCH_SIZE, n)
                # save every 10 batches to limit disk I/O
                if completed[0] % 10 == 0 or completed[0] == len(batches):
                    save_cache(_cache_global)
                rate = done_items / max(time.time() - start, 0.1)
                eta = (n - done_items) / rate if rate > 0 else 0
                print(f'  [{kind}] {done_items}/{n}  '
                      f'({rate:.0f}/s, ETA {eta:.0f}s)')
    return out


# ─── Cache ───────────────────────────────────────────────────────────────────

_cache_global = {'where': {}, 'when': {}, 'norms': {}}

# Known platform / media-type / model atoms (lowercase keys → canonical form)
_KNOWN_MEDIA = {x.lower(): x for x in [
    # Platforms
    'Facebook','Instagram','WhatsApp','Threads','Twitter','X','TikTok','YouTube',
    'Reddit','LinkedIn','Pinterest','Snapchat','Tumblr','Telegram','WeChat',
    'Weibo','Sina Weibo','Douyin','Kuaishou','Baidu Tieba','Renren','VKontakte',
    'Odnoklassniki','Discord','Twitch','Mastodon','Bluesky','Parler','Gab',
    'Truth Social','Rumble','BitChute','4chan','8kun','8chan','Quora','Medium',
    'Wikipedia','GitHub','Stack Overflow','Spotify','Steam','Roblox','OnlyFans',
    'Clubhouse','Slack','Signal','Line','KakaoTalk','Naver','Daum',
    # Media types
    'newspapers','print','printed pamphlets','pamphlets','books',
    'broadcast television','television','radio','cinema','film',
    'samizdat','bulletin board systems','BBS','newsgroups','forums',
    # AI models
    'GPT-3','GPT-4','GPT-4o','GPT-5','ChatGPT','Claude','Claude 2','Claude 3',
    'Claude 3.5','Claude 4','Llama','Llama 2','Llama 3','Gemini','Gemini 1.5',
    'Gemini 2','Bard','Mistral','Mixtral','DeepSeek','Qwen','Grok','PaLM',
    'PaLM 2','LaMDA','Phi','Cohere','Command R',
]}

def _migrate_where(old: list) -> dict:
    """Old schema: list[str]. Split into countries vs media via _KNOWN_MEDIA."""
    countries, media = [], []
    for v in old:
        if not isinstance(v, str): continue
        v = v.strip()
        if not v: continue
        canon = _KNOWN_MEDIA.get(v.lower())
        if canon:
            if canon not in media: media.append(canon)
        else:
            if v not in countries: countries.append(v)
    return {'countries': countries, 'media': media}


YEAR_MIN, YEAR_MAX = 1400, 2025  # clamp window for the timeline

def _clamp_year(y):
    if y is None: return None
    try: y = int(y)
    except (TypeError, ValueError): return None
    if y < YEAR_MIN: return YEAR_MIN
    if y > YEAR_MAX: return YEAR_MAX
    return y


_PERIOD_TABLE = {
    'unspecified': (None, None),
    'early modern': (1500, 1800),
    'enlightenment': (1685, 1815),
    'reformation': (1517, 1648),
    'long nineteenth century': (1789, 1914),
    'fin de siècle': (1880, 1914),
    'fin de siecle': (1880, 1914),
    'belle époque': (1880, 1914),
    'belle epoque': (1880, 1914),
    'edwardian': (1901, 1914),
    'victorian': (1837, 1901),
    'georgian': (1714, 1837),
    'tudor': (1485, 1603),
    'stuart': (1603, 1714),
    'interwar': (1918, 1939),
    'weimar': (1918, 1933),
    'nazi germany': (1933, 1945),
    'wwii': (1939, 1945),
    'world war ii': (1939, 1945),
    'wwi': (1914, 1918),
    'world war i': (1914, 1918),
    'post-wwii': (1945, 1991),
    'post-war': (1945, 1991),
    'cold war': (1947, 1991),
    'post-cold war': (1991, 2025),
    'post-soviet': (1991, 2025),
    '1950s': (1950,1959),'1960s':(1960,1969),'1970s':(1970,1979),
    '1980s': (1980,1989),'1990s':(1990,1999),'2000s':(2000,2009),
    '2010s': (2010,2019),'2020s':(2020,2025),
    'web 1.0 era': (1990, 2004),
    'web 2.0 era': (2004, 2010),
    'pre-platform era': (1990, 2010),
    'platform era': (2010, 2025),
    'post-2010 platform era': (2010, 2025),
    'social media era': (2005, 2025),
    'present': (2020, 2025),
    'contemporary': (2000, 2025),
    'modern': (1900, 2025),
}

_CENTURY_RE = re.compile(r'(\d{1,2})\s*(?:st|nd|rd|th)?[\s\-–]*(?:to|[-–])?[\s]*(\d{1,2})?\s*(?:st|nd|rd|th)?\s*centur(?:y|ies)', re.I)
_YEAR_RANGE_RE = re.compile(r'(1[0-9]{3}|2[0-9]{3})\s*[-–]\s*(1[0-9]{3}|2[0-9]{3})')
_SINGLE_YEAR_RE = re.compile(r'\b(1[5-9]\d{2}|20\d{2})\b')

def _migrate_when(label: str) -> dict:
    """Old schema: str. Parse to {label, start, end} locally."""
    if not label or label.strip().lower() in ('unspecified', 'n/a', 'uncertain', ''):
        return {'label': 'unspecified', 'start': None, 'end': None}
    raw = label.strip()
    low = raw.lower()
    # exact-match table
    if low in _PERIOD_TABLE:
        s, e = _PERIOD_TABLE[low]
        return {'label': raw, 'start': s, 'end': e}
    # year range "1789–1815"
    m = _YEAR_RANGE_RE.search(raw)
    if m:
        return {'label': raw, 'start': int(m.group(1)), 'end': int(m.group(2))}
    # century "16th century" or "16th–17th century"
    m = _CENTURY_RE.search(raw)
    if m:
        a = int(m.group(1)); b = int(m.group(2)) if m.group(2) else a
        s = (a - 1) * 100; e = b * 100 - 1
        return {'label': raw, 'start': s, 'end': e}
    # bare year
    m = _SINGLE_YEAR_RE.search(raw)
    if m:
        y = int(m.group(1)); return {'label': raw, 'start': y, 'end': y}
    # substring against table (e.g. "Cold War, USA-focused")
    for k, (s, e) in _PERIOD_TABLE.items():
        if k in low and s is not None:
            return {'label': raw, 'start': s, 'end': e}
    return None  # caller falls through to Gemini


def load_cache(rebuild: bool = False) -> dict:
    if rebuild or not os.path.exists(CACHE):
        return {'where': {}, 'when': {}, 'norms': {}}
    with open(CACHE, encoding='utf-8') as f:
        c = json.load(f)

    # ── Where migration ────────────────────────────────────────────────
    where = c.get('where', {}) or {}
    sample = next(iter(where.values()), None)
    if isinstance(sample, list):
        migrated = {k: _migrate_where(v) for k, v in where.items()}
        print(f'[cache] migrated {len(migrated):,} where entries '
              f'(local, no Gemini)')
        where = migrated

    # ── When migration ─────────────────────────────────────────────────
    when = c.get('when', {}) or {}
    sample = next(iter(when.values()), None)
    if isinstance(sample, str):
        migrated = {}
        unresolved = 0
        for k, v in when.items():
            r = _migrate_when(v)
            if r is None:
                # leave for Gemini to handle
                unresolved += 1
            else:
                migrated[k] = r
        print(f'[cache] migrated {len(migrated):,}/{len(when):,} when entries '
              f'(local, no Gemini); {unresolved} need Gemini')
        when = migrated

    return {'where': where, 'when': when, 'norms': c.get('norms', {})}


def save_cache(cache: dict) -> None:
    with open(CACHE, 'w', encoding='utf-8') as f:
        json.dump(cache, f, ensure_ascii=False, indent=2)


# ─── CSV helpers ─────────────────────────────────────────────────────────────

def read_csv_safe(path: str) -> list[dict]:
    """utf-8-sig + delimiter sniffing, no in-place rewriting."""
    with open(path, newline='', encoding='utf-8-sig') as f:
        sample = f.read(8192); f.seek(0)
        try:
            dialect = csv.Sniffer().sniff(sample, delimiters=',;\t')
        except csv.Error:
            dialect = csv.excel
        return list(csv.DictReader(f, dialect=dialect))


def norm_path(p: str) -> str:
    return os.path.normpath((p or '').strip()) if p else ''


def first(d: dict, keys: list[str]) -> str:
    for k in keys:
        v = (d.get(k) or '').strip()
        if v:
            return v
    return ''


def cso_key(name: str) -> str:
    """Case-insensitive, accent-folded, whitespace-normalised key for merging."""
    s = unicodedata.normalize('NFKD', name).encode('ascii', 'ignore').decode().lower()
    s = re.sub(r'\s+', ' ', s).strip()
    s = re.sub(r'^(the|le|la|les|el|los|las|der|die|das|de|het|il|lo|gli)\s+', '', s)
    return s


# ─── Build ───────────────────────────────────────────────────────────────────

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--skip-norm', action='store_true',
                    help='Use cache only; do not call Gemini for new values.')
    ap.add_argument('--rebuild', action='store_true',
                    help='Invalidate cache and re-normalise everything.')
    args = ap.parse_args()

    global _cache_global
    cache = load_cache(rebuild=args.rebuild)
    _cache_global = cache

    # ── Bibliography → indices ─────────────────────────────────────────────
    bib_rows = read_csv_safe(BIB_CSV)
    by_path: dict[str, dict] = {}
    by_title: dict[str, dict] = {}

    def make_url(r: dict) -> str:
        u = first(r, ['Url', 'Additional Link', 'Scholar Link'])
        if u:
            return u
        doi = first(r, ['DOI'])
        if doi:
            return f'https://doi.org/{doi.lstrip("/")}'
        return ''

    for r in bib_rows:
        entry = {
            'url':   make_url(r),
            'topic': first(r, ['Query']),
            'doi':   first(r, ['DOI']),
        }
        p = norm_path(r.get('Local PDF Path', ''))
        if p:
            by_path[p] = entry
        t = (r.get('Title') or '').strip().lower()
        if t and t not in by_title:
            by_title[t] = entry

    print(f'Bibliography: {len(bib_rows):,} rows '
          f'({len(by_path):,} indexed by path, {len(by_title):,} by title)')

    # ── Extraction CSV ─────────────────────────────────────────────────────
    rows = read_csv_safe(EXTRACT_CSV)
    SENTINELS = {'n/a', 'na', 'none', 'null', 'nil', '-', '—', '–',
                 'unknown', 'unspecified', 'not applicable', 'not specified'}
    def _is_real_cso(r):
        name = ((r.get('Canonical name') or '').strip()
                or (r.get('Name in text') or '').strip())
        return bool(name) and name.lower() not in SENTINELS
    rows = [r for r in rows if _is_real_cso(r)]
    print(f'Extraction rows with a real CSO: {len(rows):,}')

    # ── Collect unique values to normalise ─────────────────────────────────
    wheres = sorted({(r.get('Where') or '').strip() for r in rows
                     if (r.get('Where') or '').strip()})
    whens  = sorted({(r.get('When')  or '').strip() for r in rows
                     if (r.get('When')  or '').strip()})
    norms  = sorted({(r.get('Norms/values/interests') or '').strip() for r in rows
                     if (r.get('Norms/values/interests') or '').strip()})

    new_w = [v for v in wheres if v not in cache['where']]
    new_t = [v for v in whens  if v not in cache['when']]
    new_n = [v for v in norms  if v not in cache['norms']]
    print(f'Unique — Where: {len(wheres):,} ({len(new_w)} new), '
          f'When: {len(whens):,} ({len(new_t)} new), '
          f'Norms: {len(norms):,} ({len(new_n)} new)')

    if not args.skip_norm:
        if new_w:
            cache['where'].update(batched(
                new_w, WHERE_PROMPT, 'where',
                default=lambda: {'countries': [], 'media': []}))
            save_cache(cache)
        if new_t:
            cache['when'].update(batched(
                new_t, WHEN_PROMPT, 'when',
                default=lambda: {'label': 'unspecified', 'start': None, 'end': None}))
            save_cache(cache)
        if new_n:
            cache['norms'].update(batched(
                new_n, NORMS_PROMPT, 'norms',
                default=lambda: []))
            save_cache(cache)
    else:
        for v in new_w: cache['where'].setdefault(v, {'countries': [], 'media': []})
        for v in new_t: cache['when'].setdefault(v, {'label': 'unspecified', 'start': None, 'end': None})
        for v in new_n: cache['norms'].setdefault(v, [])

    # ── Group rows by canonical CSO ─────────────────────────────────────────
    csos: dict[str, dict] = {}

    for r in rows:
        canonical = (r.get('Canonical name') or '').strip() \
                    or (r.get('Name in text') or '').strip()
        if not canonical:
            continue
        key = cso_key(canonical)
        cso = csos.setdefault(key, {
            'name': canonical,
            'aliases': set(),
            'types': Counter(),
            'norms': set(),
            'countries': set(),
            'media': set(),
            'when_periods': set(),
            'when_min': None,
            'when_max': None,
            'topics': set(),
            'papers': [],
        })
        cso['aliases'].add(canonical)

        ctype = (r.get('Type') or '').strip()
        if ctype:
            cso['types'][ctype] += 1

        # Where
        w_raw = (r.get('Where') or '').strip()
        w_norm = cache['where'].get(w_raw, {'countries': [], 'media': []}) if w_raw else {'countries': [], 'media': []}
        cso['countries'].update(w_norm.get('countries') or [])
        cso['media'].update(w_norm.get('media') or [])

        # When (clamp to [YEAR_MIN, YEAR_MAX] — Gemini sometimes emits BCE
        # dates or future years for organisations whose history a paper
        # discusses in passing, e.g. Catholic Church → -4000)
        t_raw = (r.get('When') or '').strip()
        t_norm = cache['when'].get(t_raw, {'label': 'unspecified', 'start': None, 'end': None}) if t_raw else {'label': 'unspecified', 'start': None, 'end': None}
        if t_norm['label'] != 'unspecified':
            cso['when_periods'].add(t_norm['label'])
        s = _clamp_year(t_norm.get('start'))
        e = _clamp_year(t_norm.get('end'))
        # Reject overly broad single-paper periods (>200y) — usually
        # "ancient → modern" hand-waves that pollute aggregate bounds.
        if s is not None and e is not None and (e - s) > 200:
            s = e = None
        if s is not None:
            cso['when_min'] = s if cso['when_min'] is None else min(cso['when_min'], s)
        if e is not None:
            cso['when_max'] = e if cso['when_max'] is None else max(cso['when_max'], e)

        # Norms
        n_raw = (r.get('Norms/values/interests') or '').strip()
        n_norm = cache['norms'].get(n_raw, []) if n_raw else []
        cso['norms'].update(n_norm)

        # Bibliography join → URL + Topic
        path_key = norm_path(r.get('File Path', ''))
        title_key = (r.get('Title') or '').strip().lower()
        bib_entry = by_path.get(path_key) or by_title.get(title_key) or {}
        topic = bib_entry.get('topic', '')
        if topic:
            cso['topics'].add(topic)

        cso['papers'].append({
            'title': (r.get('Title') or '').strip(),
            'author': (r.get('Author') or '').strip(),
            'year':  (r.get('Year') or '').strip(),
            'mechanism': (r.get('Mechanism') or '').strip(),
            'quote': (r.get('Verbatim quote') or '').strip(),
            'page':  (r.get('Page') or '').strip(),
            'url':   bib_entry.get('url', ''),
            'topic': topic,
            'where': w_raw,
            'when':  t_raw,
        })

    print(f'Distinct CSOs: {len(csos):,}')

    # ── Materialise to plain JSON shapes ───────────────────────────────────
    out = []
    for c in csos.values():
        # Dedup papers by (title + page) and drop empty mechanism duplicates
        seen = set(); papers = []
        for p in c['papers']:
            k = (p['title'], p['mechanism'][:200])
            if k in seen:
                continue
            seen.add(k)
            papers.append(p)
        # Sort papers by year desc
        papers.sort(key=lambda p: (p['year'] or '0'), reverse=True)
        out.append({
            'name': c['name'],
            'aliases': sorted(c['aliases']),
            'type':  (c['types'].most_common(1)[0][0] if c['types'] else ''),
            'types_all': [t for t, _ in c['types'].most_common()],
            'countries': sorted(c['countries']),
            'media':     sorted(c['media']),
            'norms':     sorted(c['norms']),
            'topics':    sorted(c['topics']),
            'when_periods': sorted(c['when_periods']),
            'when_min':  c['when_min'],
            'when_max':  c['when_max'],
            'paper_count': len(papers),
            'papers':    papers,
        })
    # Sort CSOs by paper_count desc, then name
    out.sort(key=lambda c: (-c['paper_count'], c['name'].lower()))

    os.makedirs(SITE_DIR, exist_ok=True)
    with open(os.path.join(SITE_DIR, 'data.json'), 'w', encoding='utf-8') as f:
        json.dump(out, f, ensure_ascii=False)
    print(f'Wrote site/data.json  ({len(out):,} CSOs)')

    # Stamp the build version into index.html so each new build busts cache
    build_version = str(int(time.time()))
    html = INDEX_HTML.replace(
        '<script>',
        f'<script>window.BUILD_VERSION = {build_version!r};',
        1,
    )
    with open(os.path.join(SITE_DIR, 'index.html'), 'w', encoding='utf-8') as f:
        f.write(html)
    print(f'Wrote site/index.html (build {build_version})')

    print('\nPreview:')
    print(f"    cd '{SITE_DIR}' && python3 -m http.server 8000")


# ─── Static site ─────────────────────────────────────────────────────────────

INDEX_HTML = r"""<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<title>Civil society in censorship, moderation & AI alignment</title>
<meta name="viewport" content="width=device-width,initial-scale=1">
<style>
  :root {
    --bg:#fafaf7; --ink:#1c1c1c; --muted:#6a6a6a; --accent:#9b1c1c;
    --chip:#eee8d8; --chip-on:#9b1c1c; --chip-on-ink:#fff; --line:#dcd6c5;
    --card:#fff;
  }
  * { box-sizing: border-box; }
  html,body { margin:0; padding:0; background:var(--bg); color:var(--ink);
              font: 15px/1.45 ui-serif, Georgia, "Iowan Old Style", serif; }
  header { padding: 16px 22px; border-bottom: 1px solid var(--line); }
  header h1 { margin:0; font-size: 20px; font-weight:600; }
  header p  { margin:4px 0 0; color:var(--muted); font-size: 13px; }
  main { display:grid; grid-template-columns: 320px 1fr; min-height: calc(100vh - 60px); }
  aside { border-right:1px solid var(--line); padding: 14px 16px; overflow-y:auto;
          max-height: calc(100vh - 60px); position:sticky; top:0;
          font: 14px ui-sans-serif, system-ui, sans-serif; }
  aside h2 { font-size: 11px; letter-spacing: .08em; text-transform: uppercase;
             color: var(--muted); margin: 14px 0 6px;
             font-family: ui-sans-serif, system-ui; font-weight: 700; }
  aside input[type=search] { width:100%; padding:6px 8px; border:1px solid var(--line);
             border-radius:6px; background:white; font: inherit; }
  .facet { margin-bottom: 8px; }
  .facet input[type=text] { width:100%; padding:4px 6px; border:1px solid var(--line);
             border-radius:4px; background:white; font: 13px ui-sans-serif,system-ui;
             margin-bottom: 4px; }
  .chips { display:flex; flex-wrap:wrap; gap:4px; max-height: 160px; overflow-y:auto;
           padding-right: 4px; }
  .chip { font-size: 12px; padding: 2px 8px; border-radius: 999px;
          background: var(--chip); cursor: pointer; user-select:none;
          border: 1px solid transparent; font-family: ui-sans-serif, system-ui; }
  .chip:hover { border-color: var(--ink); }
  .chip.on { background: var(--chip-on); color: var(--chip-on-ink); }
  .chip .n { color:var(--muted); margin-left:4px; font-variant-numeric: tabular-nums; }
  .chip.on .n { color: rgba(255,255,255,.7); }

  /* Timeline */
  .timeline { padding: 4px 0 8px; }
  .timeline .yrs { display:flex; justify-content:space-between;
                   font: 12px ui-sans-serif, system-ui; color:var(--muted);
                   font-variant-numeric: tabular-nums; }
  .timeline .double { position: relative; height: 32px; margin-top: 4px; }
  .timeline .double input[type=range] {
    position: absolute; left:0; right:0; width:100%; pointer-events:none;
    -webkit-appearance: none; background: transparent; height: 32px;
  }
  .timeline .double input[type=range]::-webkit-slider-thumb {
    -webkit-appearance:none; pointer-events:auto;
    width:16px; height:16px; border-radius:50%;
    background:var(--accent); border:2px solid white;
    box-shadow: 0 0 0 1px var(--accent);
    margin-top:-7px; cursor:pointer;
  }
  .timeline .double input[type=range]::-moz-range-thumb {
    pointer-events:auto; width:14px; height:14px; border-radius:50%;
    background:var(--accent); border:2px solid white; cursor:pointer;
  }
  .timeline .track { position:absolute; left:0; right:0; top:14px;
                     height:4px; background:var(--line); border-radius:2px; }
  .timeline .fill  { position:absolute; top:14px; height:4px;
                     background:var(--accent); border-radius:2px; }
  .timeline .toggle { font-size:12px; color:var(--muted); margin-top:4px;
                      font-family: ui-sans-serif, system-ui; }
  .timeline .toggle label { cursor:pointer; }

  section.results { padding: 14px 22px 40px; }
  .meta { color: var(--muted); font-size: 13px; margin-bottom: 10px;
          font-family: ui-sans-serif, system-ui; }
  .clear { color: var(--accent); cursor: pointer; margin-left: 8px; }
  .toolbar { display:flex; flex-wrap:wrap; gap: 14px; padding: 8px 0 12px;
             border-bottom: 1px solid var(--line); margin-bottom: 12px;
             font: 13px ui-sans-serif, system-ui; color: var(--muted); }
  .toolbar label { cursor:pointer; user-select:none; }
  .toolbar input { vertical-align: middle; margin-right: 4px; }
  .toolbar button { font: inherit; padding: 4px 10px; border: 1px solid var(--accent);
                    background: white; color: var(--accent); border-radius: 6px;
                    cursor: pointer; }
  .toolbar button:hover { background: var(--accent); color: white; }

  .card { background: var(--card); border: 1px solid var(--line);
          border-radius: 8px; padding: 14px 16px; margin-bottom: 12px;
          box-shadow: 0 1px 0 rgba(0,0,0,.02); }
  .card .name { font-weight: 600; font-size: 17px; }
  .card .type { color: var(--muted); font-size: 11px; margin-left: 8px;
                text-transform: uppercase; letter-spacing: .05em;
                font-family: ui-sans-serif, system-ui; font-weight: 700; }
  .card .summary { color:var(--muted); font-size: 13px; margin: 4px 0 8px;
                   font-family: ui-sans-serif, system-ui; }
  .card .tags { margin-top: 6px; display:flex; flex-wrap:wrap; gap:4px; }
  .card .tags .tag { font-size: 11px; padding: 1px 7px; border-radius:4px;
                     background:#f0e9d5; color:#444; cursor:pointer;
                     font-family: ui-sans-serif, system-ui; }
  .card .tags .tag.k-country { background: #d9e4ec; }
  .card .tags .tag.k-media   { background: #e0d9ec; }
  .card .tags .tag.k-when    { background: #e2d9ec; }
  .card .tags .tag.k-type    { background: #e9d9d9; }
  .card .tags .tag.k-norms   { background: #d9e9d9; }
  .card .tags .tag.k-topic   { background: #efe4d4; }
  .card .tags .tag:hover { filter: brightness(.93); }

  .card details { margin-top: 10px; }
  .card details > summary {
    list-style: none; cursor: pointer; color: var(--accent); font-size: 13px;
    font-family: ui-sans-serif, system-ui;
  }
  .card details > summary::-webkit-details-marker { display:none; }
  .card details[open] > summary::after { content: ' ▾'; }
  .card details:not([open]) > summary::after { content: ' ▸'; }

  .papers { margin-top: 8px; padding-left: 0; list-style: none; }
  .papers li { padding: 8px 0; border-top: 1px dashed var(--line); }
  .papers li:first-child { border-top: none; }
  .papers .ptitle { font-weight: 500; }
  .papers .pmeta { font-size: 12px; color: var(--muted);
                   font-family: ui-sans-serif, system-ui; }
  .papers .pmech { margin: 3px 0; font-size: 14px; }
  .papers .pquote { font-size: 13px; color: #333;
                    border-left: 3px solid var(--accent); padding: 4px 10px;
                    margin: 6px 0; background: #fbf6e8; }
  .papers .pquote .lbl { font: 700 10px ui-sans-serif, system-ui;
                         letter-spacing: .08em; text-transform: uppercase;
                         color: var(--muted); display: block; margin-bottom: 2px; }
  .papers .ppage { display: inline-block; margin-left: 6px;
                   padding: 1px 7px; border-radius: 999px;
                   background: #efe4d4; color: #5a3a00;
                   font: 700 11px ui-sans-serif, system-ui;
                   font-variant-numeric: tabular-nums; vertical-align: 1px; }
  .papers a { color: var(--accent); text-decoration: none; }
  .papers a:hover { text-decoration: underline; }
  .empty { padding: 30px 0; color: var(--muted);
           font-family: ui-sans-serif, system-ui; }

  @media (max-width: 760px) {
    main { grid-template-columns: 1fr; }
    aside { position: static; max-height: none; border-right: none;
            border-bottom: 1px solid var(--line); }
  }
</style>
</head>
<body>
<header>
  <h1>Civil society organisations in censorship, moderation & AI alignment</h1>
  <p>Faceted directory across <span id="paper-stat">academic literature</span>.</p>
</header>
<main>
  <aside>
    <input type="search" id="q" placeholder="Search names, mechanisms, papers…">
    <div id="filters"></div>
  </aside>
  <section class="results">
    <div class="meta"><span id="count"></span><span id="active"></span></div>
    <div class="toolbar">
      <span>Show on cards:</span>
      <label><input type="checkbox" data-show="when"      checked> When</label>
      <label><input type="checkbox" data-show="countries" checked> Country</label>
      <label><input type="checkbox" data-show="media"     checked> Platform/media</label>
      <label><input type="checkbox" data-show="type"      checked> Type</label>
      <label><input type="checkbox" data-show="topics"    checked> Topic</label>
      <label><input type="checkbox" data-show="norms"     checked> Norms</label>
      <span style="flex:1"></span>
      <button id="dl-csv" type="button">⬇ Download CSV</button>
    </div>
    <div id="rows"></div>
  </section>
</main>

<script>
const FACETS = [
  { key: 'countries', label: 'Country / polity' },
  { key: 'media',     label: 'Platform / media' },
  { key: 'topics',    label: 'Topic' },
  { key: 'type',      label: 'Type', single: true },
  { key: 'norms',     label: 'Norms / values / interests' },
];

const TL_MIN = 1400, TL_MAX = 2025;
const state = {
  rows: [],
  selected: { countries:new Set(), media:new Set(),
              topics:new Set(), type:new Set(), norms:new Set() },
  q: '',
  tlFrom: TL_MIN, tlTo: TL_MAX,
  tlIncludeUnknown: true,
  show: loadShow(),
};

function loadShow() {
  const def = { when:true, countries:true, media:true, type:true, topics:true, norms:true };
  try {
    const s = JSON.parse(localStorage.getItem('cso_show') || '{}');
    return { ...def, ...s };
  } catch (e) { return def; }
}
function saveShow() {
  try { localStorage.setItem('cso_show', JSON.stringify(state.show)); } catch (e) {}
}

fetch('data.json?v=' + (window.BUILD_VERSION || Date.now()), {cache: 'no-cache'}).then(r => r.json()).then(rows => {
  state.rows = rows;
  const totalPapers = rows.reduce((a,c) => a + c.paper_count, 0);
  document.querySelector('#paper-stat').textContent =
      `${rows.length.toLocaleString()} CSOs across ${totalPapers.toLocaleString()} paper mentions`;
  buildFilters();
  hydrateFromHash();
  render();
});

document.querySelector('#q').addEventListener('input', e => {
  state.q = e.target.value.trim().toLowerCase(); render();
});

document.querySelectorAll('.toolbar input[data-show]').forEach(cb => {
  cb.checked = !!state.show[cb.dataset.show];
  cb.addEventListener('change', e => {
    state.show[e.target.dataset.show] = e.target.checked;
    saveShow(); render();
  });
});

document.querySelector('#dl-csv').addEventListener('click', downloadCSV);

const CSV_FIELDS = [
  'Canonical name','Aliases','Type','All types','Countries','Platform/Media',
  'Topics (CSO)','Norms/values/interests','When periods','When min','When max',
  'Paper count',
  'Paper title','Paper author','Paper year','Paper URL','Page','Mechanism',
  'Verbatim quote','Paper topic','Paper Where (raw)','Paper When (raw)',
];

function csvEscape(v) {
  if (v == null) return '';
  v = String(v);
  if (/[",\n\r]/.test(v)) return '"' + v.replace(/"/g, '""') + '"';
  return v;
}

function downloadCSV() {
  const filtered = state.rows.filter(matches);
  const lines = [CSV_FIELDS.map(csvEscape).join(',')];
  for (const r of filtered) {
    const base = [
      r.name,
      (r.aliases || []).join('; '),
      r.type || '',
      (r.types_all || []).join('; '),
      (r.countries || []).join('; '),
      (r.media || []).join('; '),
      (r.topics || []).join('; '),
      (r.norms || []).join('; '),
      (r.when_periods || []).join('; '),
      r.when_min == null ? '' : r.when_min,
      r.when_max == null ? '' : r.when_max,
      r.paper_count,
    ];
    if (!r.papers || !r.papers.length) {
      lines.push(base.concat(['','','','','','','','','','']).map(csvEscape).join(','));
      continue;
    }
    for (const p of r.papers) {
      lines.push(base.concat([
        p.title || '', p.author || '', p.year || '', p.url || '',
        p.page || '', p.mechanism || '', p.quote || '',
        p.topic || '', p.where || '', p.when || '',
      ]).map(csvEscape).join(','));
    }
  }
  const blob = new Blob(['﻿' + lines.join('\n')], {type: 'text/csv;charset=utf-8'});
  const url = URL.createObjectURL(blob);
  const a = document.createElement('a');
  a.href = url;
  const stamp = new Date().toISOString().slice(0,16).replace(/[:T]/g, '-');
  a.download = `csos-${stamp}.csv`;
  document.body.appendChild(a); a.click();
  setTimeout(() => { URL.revokeObjectURL(url); a.remove(); }, 0);
}

function buildFilters() {
  const root = document.querySelector('#filters');
  root.innerHTML = '';

  // Timeline FIRST
  const tlSec = document.createElement('div');
  tlSec.className = 'timeline';
  tlSec.innerHTML = `
    <h2>When</h2>
    <div class="yrs"><span id="tl-from">${TL_MIN}</span><span id="tl-to">${TL_MAX}</span></div>
    <div class="double">
      <div class="track"></div><div class="fill" id="tl-fill"></div>
      <input type="range" id="tl-r1" min="${TL_MIN}" max="${TL_MAX}" value="${TL_MIN}" step="5">
      <input type="range" id="tl-r2" min="${TL_MIN}" max="${TL_MAX}" value="${TL_MAX}" step="5">
    </div>
    <div class="toggle">
      <label><input type="checkbox" id="tl-unknown" checked> include CSOs with unknown period</label>
    </div>`;
  root.appendChild(tlSec);
  const r1 = tlSec.querySelector('#tl-r1');
  const r2 = tlSec.querySelector('#tl-r2');
  const fill = tlSec.querySelector('#tl-fill');
  function syncFill(){
    const a = Math.min(+r1.value, +r2.value), b = Math.max(+r1.value, +r2.value);
    state.tlFrom = a; state.tlTo = b;
    document.querySelector('#tl-from').textContent = a;
    document.querySelector('#tl-to').textContent = b;
    const w = TL_MAX - TL_MIN;
    fill.style.left  = ((a - TL_MIN)/w*100).toFixed(2)+'%';
    fill.style.right = ((TL_MAX - b)/w*100).toFixed(2)+'%';
    render();
  }
  r1.addEventListener('input', syncFill);
  r2.addEventListener('input', syncFill);
  tlSec.querySelector('#tl-unknown').addEventListener('change', e => {
    state.tlIncludeUnknown = e.target.checked; render();
  });
  syncFill();

  // Categorical facets
  for (const f of FACETS) {
    const counts = new Map();
    for (const r of state.rows) {
      const vals = f.single ? [r[f.key]] : (r[f.key] || []);
      for (const v of vals) {
        if (!v) continue;
        counts.set(v, (counts.get(v) || 0) + 1);
      }
    }
    const sorted = [...counts.entries()].sort((a,b) => b[1]-a[1] || a[0].localeCompare(b[0]));
    if (!sorted.length) continue;
    const sec = document.createElement('div');
    sec.className = 'facet';
    sec.innerHTML = `<h2>${f.label} <span style="color:var(--muted);font-weight:normal">(${sorted.length})</span></h2>
                     <input type="text" placeholder="filter ${f.label.toLowerCase()}…">
                     <div class="chips" data-key="${f.key}"></div>`;
    root.appendChild(sec);
    const chipBox = sec.querySelector('.chips');
    for (const [val, n] of sorted) {
      const c = document.createElement('span');
      c.className = 'chip';
      c.dataset.key = f.key; c.dataset.val = val;
      c.innerHTML = `${escapeHtml(val)}<span class="n">${n}</span>`;
      c.onclick = () => toggle(f.key, val);
      chipBox.appendChild(c);
    }
    sec.querySelector('input[type=text]').addEventListener('input', e => {
      const term = e.target.value.toLowerCase();
      chipBox.querySelectorAll('.chip').forEach(ch => {
        ch.style.display = ch.dataset.val.toLowerCase().includes(term) ? '' : 'none';
      });
    });
  }
  refreshChips();
}

function toggle(key, val) {
  const s = state.selected[key];
  if (s.has(val)) s.delete(val); else s.add(val);
  refreshChips(); render();
}

function refreshChips() {
  document.querySelectorAll('.chip').forEach(ch => {
    ch.classList.toggle('on', !!state.selected[ch.dataset.key]?.has(ch.dataset.val));
  });
}

function matches(r) {
  for (const f of FACETS) {
    const sel = state.selected[f.key];
    if (!sel.size) continue;
    const vals = f.single ? [r[f.key]] : (r[f.key] || []);
    let ok = false;
    for (const v of vals) if (v && sel.has(v)) { ok = true; break; }
    if (!ok) return false;
  }
  // Timeline filter
  const hasPeriod = (r.when_min != null && r.when_max != null);
  if (!hasPeriod) {
    if (!state.tlIncludeUnknown) return false;
  } else {
    // overlap with [tlFrom, tlTo]
    if (r.when_max < state.tlFrom || r.when_min > state.tlTo) return false;
  }
  if (state.q) {
    const hay = (r.name + ' ' + r.papers.map(p => p.title + ' ' + p.author + ' ' + p.mechanism).join(' ')).toLowerCase();
    if (!hay.includes(state.q)) return false;
  }
  return true;
}

function render() {
  const filtered = state.rows.filter(matches);
  document.querySelector('#count').textContent =
      `${filtered.length.toLocaleString()} CSO${filtered.length===1?'':'s'}`;
  document.querySelector('#active').innerHTML =
      activeBits() ? ` · ${activeBits()} <span class="clear" onclick="clearAll()">clear all</span>` : '';

  const box = document.querySelector('#rows');
  box.innerHTML = '';
  if (!filtered.length) {
    box.innerHTML = '<div class="empty">No matches. Try clearing some filters.</div>';
    syncHash(); return;
  }
  const frag = document.createDocumentFragment();
  for (const r of filtered.slice(0, 400)) frag.appendChild(renderCard(r));
  if (filtered.length > 400) {
    const more = document.createElement('div');
    more.className = 'empty';
    more.textContent = `Showing first 400 of ${filtered.length.toLocaleString()}. Refine filters to narrow down.`;
    frag.appendChild(more);
  }
  box.appendChild(frag);
  syncHash();
}

function renderCard(r) {
  const div = document.createElement('div');
  div.className = 'card';
  const tags = [];
  if (state.show.countries) for (const v of r.countries) tags.push(tag('countries', v, 'country'));
  if (state.show.media)     for (const v of r.media)     tags.push(tag('media',     v, 'media'));
  if (state.show.topics)    for (const v of r.topics)    tags.push(tag('topics',    v, 'topic'));
  if (state.show.type && r.type) tags.push(tag('type', r.type, 'type'));
  if (state.show.norms)     for (const v of r.norms) tags.push(tag('norms', v, 'norms'));

  const periodLabel = r.when_min != null && r.when_max != null
    ? (r.when_periods.length === 1 ? r.when_periods[0]
       : (r.when_min === r.when_max ? r.when_min
          : r.when_min + '–' + r.when_max))
    : '';
  if (state.show.when && periodLabel) tags.unshift(`<span class="tag k-when">${escapeHtml(periodLabel)}</span>`);

  div.innerHTML = `
    <div><span class="name">${escapeHtml(r.name)}</span>
         ${r.type ? `<span class="type">${escapeHtml(r.type)}</span>` : ''}</div>
    <div class="summary">Cited by <strong>${r.paper_count}</strong> paper${r.paper_count===1?'':'s'}${
       r.aliases.length > 1 ? ' · also: ' + r.aliases.filter(a=>a!==r.name).map(escapeHtml).join('; ') : ''}</div>
    <div class="tags">${tags.join('')}</div>
    <details>
      <summary>Show ${r.paper_count} citation${r.paper_count===1?'':'s'}</summary>
      <ul class="papers">${r.papers.map(renderPaper).join('')}</ul>
    </details>`;
  div.querySelectorAll('.tag').forEach(el => {
    if (el.dataset.key) el.onclick = () => toggle(el.dataset.key, el.dataset.val);
  });
  return div;
}

function renderPaper(p) {
  const cite = `<em>${escapeHtml(p.title)}</em>${p.author ? ' — ' + escapeHtml(p.author) : ''}${p.year ? ' (' + escapeHtml(p.year) + ')' : ''}`;
  const titleHtml = p.url
    ? `<a href="${escapeAttr(p.url)}" target="_blank" rel="noopener noreferrer">${cite}</a>`
    : cite;
  const pageBadge = p.page ? `<span class="ppage">p. ${escapeHtml(p.page)}</span>` : '';
  return `<li>
    <div class="ptitle">${titleHtml}${pageBadge}</div>
    ${p.mechanism ? `<div class="pmech">${escapeHtml(p.mechanism)}</div>` : ''}
    ${p.quote ? `<div class="pquote"><span class="lbl">Verbatim passage${p.page ? ' (p. ' + escapeHtml(p.page) + ')' : ''}</span>“${escapeHtml(p.quote)}”</div>` : ''}
    <div class="pmeta">${p.topic ? 'Topic: ' + escapeHtml(p.topic) + ' · ' : ''}${p.where ? escapeHtml(p.where) + ' · ' : ''}${p.when ? escapeHtml(p.when) : ''}</div>
  </li>`;
}

function tag(key, val, klass) {
  return `<span class="tag k-${klass}" data-key="${key}" data-val="${escapeAttr(val)}">${escapeHtml(val)}</span>`;
}

function activeBits() {
  const parts = [];
  for (const f of FACETS) {
    if (state.selected[f.key].size)
      parts.push(`${f.label}: ${[...state.selected[f.key]].map(escapeHtml).join(', ')}`);
  }
  if (state.tlFrom !== TL_MIN || state.tlTo !== TL_MAX)
    parts.push(`When: ${state.tlFrom}–${state.tlTo}`);
  return parts.join(' · ');
}

function clearAll() {
  for (const k of Object.keys(state.selected)) state.selected[k].clear();
  state.q = '';
  document.querySelector('#q').value = '';
  state.tlFrom = TL_MIN; state.tlTo = TL_MAX;
  document.querySelector('#tl-r1').value = TL_MIN;
  document.querySelector('#tl-r2').value = TL_MAX;
  document.querySelector('#tl-r1').dispatchEvent(new Event('input'));
  refreshChips();
}

function syncHash() {
  const s = {};
  for (const k of Object.keys(state.selected))
    if (state.selected[k].size) s[k] = [...state.selected[k]];
  if (state.q) s.q = state.q;
  if (state.tlFrom !== TL_MIN) s.from = state.tlFrom;
  if (state.tlTo   !== TL_MAX) s.to   = state.tlTo;
  if (!state.tlIncludeUnknown) s.no_unk = 1;
  const h = Object.keys(s).length ? '#' + encodeURIComponent(JSON.stringify(s)) : '';
  if (location.hash !== h) history.replaceState(null, '', h || '#');
}

function hydrateFromHash() {
  if (location.hash.length < 2) return;
  try {
    const s = JSON.parse(decodeURIComponent(location.hash.slice(1)));
    for (const k of Object.keys(s)) {
      if (k === 'q') { state.q = s[k]; document.querySelector('#q').value = s[k]; }
      else if (k === 'from') { state.tlFrom = s[k]; document.querySelector('#tl-r1').value = s[k]; }
      else if (k === 'to')   { state.tlTo   = s[k]; document.querySelector('#tl-r2').value = s[k]; }
      else if (k === 'no_unk') { state.tlIncludeUnknown = false;
                                 document.querySelector('#tl-unknown').checked = false; }
      else if (state.selected[k]) state.selected[k] = new Set(s[k]);
    }
    document.querySelector('#tl-r1').dispatchEvent(new Event('input'));
    refreshChips();
  } catch (e) {}
}

function escapeHtml(s) {
  return String(s ?? '').replace(/[&<>"']/g, c => ({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
}
function escapeAttr(s) { return escapeHtml(s); }
</script>
</body>
</html>
"""


if __name__ == '__main__':
    main()
