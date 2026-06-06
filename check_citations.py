#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
check_citations.py — Hallucinated-citation detector for LaTeX .bib files.

For every BibTeX entry it verifies the **title**, **authors** and **year**
against authoritative web sources, and — when the entry carries a unique
identifier (arXiv id / DOI) — checks that the identifier actually exists and
points to the *same* paper.

Sources (no API key required, pure stdlib HTTP):
  * DBLP            — primary cross-check for published CS papers
  * arXiv API       — authoritative for `arXiv:XXXX.XXXXX` preprints
  * Crossref        — authoritative for DOIs
  * OpenReview API  — authoritative for ICLR/NeurIPS/COLM `openreview.net?id=` papers
                      (gives the real proceedings venue + year, resolving
                      preprint-vs-conference year mismatches)
  * URL liveness    — for @misc / @software (blogs, model cards, repos)

A "hallucinated" citation typically shows up as one of:
  - an arXiv id / DOI that does not exist at all;
  - an identifier that resolves to a *different* paper than the title claims;
  - a title with no match anywhere + authors/year that cannot be confirmed.

Usage:
    python3 check_citations.py example-bib.bib
    python3 check_citations.py refs.bib --md report.md --json report.json
    python3 check_citations.py refs.bib --only shao2024deepseekmath wan2025qwenlongl1
    python3 check_citations.py refs.bib --delay 1.5 --no-cache

The tool only reads the network and writes the report files you ask for; it
never modifies the input .bib.
"""

import argparse
import difflib
import html
import json
import os
import re
import sys
import time
import unicodedata
import urllib.parse
import urllib.request
import urllib.error
import xml.etree.ElementTree as ET

UA = "citation-hallucination-checker/1.0 (mailto:noreply@example.com)"
# Many sites (Cloudflare-fronted blogs, model-card hosts) reject or reset
# non-browser agents; use a realistic one for plain URL-liveness checks.
BROWSER_UA = ("Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) "
              "AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0 Safari/537.36")
CACHE_PATH = os.path.join(os.path.dirname(os.path.abspath(__file__)), ".citecheck_cache.json")

# ----------------------------------------------------------------------------
# Severity model
# ----------------------------------------------------------------------------
# Ordered from best to worst; the entry verdict is the worst issue it contains.
OK, INFO, MINOR, WARN, FAIL = "OK", "INFO", "MINOR", "WARN", "FAIL"
SEV_ORDER = {OK: 0, INFO: 1, MINOR: 2, WARN: 3, FAIL: 4}
SEV_ICON = {OK: "✅", INFO: "ℹ️ ", MINOR: "🟡", WARN: "⚠️ ", FAIL: "❌"}
SEV_LABEL = {
    OK:    "OK",
    INFO:  "UNVERIFIABLE",
    MINOR: "MINOR",
    WARN:  "WARNING",
    FAIL:  "SUSPECT",
}


# ----------------------------------------------------------------------------
# Terminal colours
# ----------------------------------------------------------------------------
class C:
    enabled = sys.stdout.isatty()

    @staticmethod
    def wrap(code, s):
        return f"\033[{code}m{s}\033[0m" if C.enabled else s

    @staticmethod
    def green(s):  return C.wrap("32", s)
    @staticmethod
    def yellow(s): return C.wrap("33", s)
    @staticmethod
    def red(s):    return C.wrap("31", s)
    @staticmethod
    def blue(s):   return C.wrap("36", s)
    @staticmethod
    def dim(s):    return C.wrap("2", s)
    @staticmethod
    def bold(s):   return C.wrap("1", s)


SEV_COLOR = {OK: C.green, INFO: C.blue, MINOR: C.yellow, WARN: C.yellow, FAIL: C.red}


# ============================================================================
# 1. BibTeX parsing (brace-aware, no external deps)
# ============================================================================
def parse_bib(text):
    """Return a list of dicts: {type, key, fields:{name:value}, line}."""
    entries = []
    i, n = 0, len(text)
    # Count line numbers lazily.
    line_starts = [0] + [m.end() for m in re.finditer(r"\n", text)]

    def line_of(pos):
        # binary-ish search
        lo, hi = 0, len(line_starts) - 1
        while lo < hi:
            mid = (lo + hi + 1) // 2
            if line_starts[mid] <= pos:
                lo = mid
            else:
                hi = mid - 1
        return lo + 1

    while i < n:
        at = text.find("@", i)
        if at == -1:
            break
        m = re.match(r"@(\w+)\s*\{", text[at:])
        if not m:
            i = at + 1
            continue
        etype = m.group(1).lower()
        if etype in ("comment", "preamble", "string"):
            i = at + m.end()
            continue
        body_start = at + m.end()  # just after the opening brace
        # find matching closing brace
        depth = 1
        j = body_start
        while j < n and depth > 0:
            ch = text[j]
            if ch == "{":
                depth += 1
            elif ch == "}":
                depth -= 1
            j += 1
        body = text[body_start:j - 1]
        entry = parse_entry_body(etype, body, line_of(at))
        if entry:
            entries.append(entry)
        i = j
    return entries


def parse_entry_body(etype, body, line):
    # First token up to first comma is the cite key.
    comma = body.find(",")
    if comma == -1:
        return None
    key = body[:comma].strip()
    rest = body[comma + 1:]
    fields = {}
    k = 0
    m = len(rest)
    while k < m:
        eq = rest.find("=", k)
        if eq == -1:
            break
        name = rest[k:eq].strip().lower()
        v = eq + 1
        # skip whitespace
        while v < m and rest[v] in " \t\r\n":
            v += 1
        if v >= m:
            break
        if rest[v] == "{":
            depth, p = 1, v + 1
            while p < m and depth > 0:
                if rest[p] == "{":
                    depth += 1
                elif rest[p] == "}":
                    depth -= 1
                p += 1
            value = rest[v + 1:p - 1]
            k = p
        elif rest[v] == '"':
            p = v + 1
            depth = 0
            while p < m:
                if rest[p] == "{":
                    depth += 1
                elif rest[p] == "}":
                    depth -= 1
                elif rest[p] == '"' and depth == 0:
                    break
                p += 1
            value = rest[v + 1:p]
            k = p + 1
        else:
            # bare value up to next comma
            p = v
            while p < m and rest[p] != ",":
                p += 1
            value = rest[v:p].strip()
            k = p
        # advance past trailing comma/space
        while k < m and rest[k] in " \t\r\n,":
            k += 1
        if name:
            fields[name] = value.strip()
    return {"type": etype, "key": key, "fields": fields, "line": line}


# ============================================================================
# 2. Text / name normalisation
# ============================================================================
_ACCENT_RE = re.compile(r"\\[`'\"^~=.cuvHtdbr]\s*\{?\\?(\w)\}?")
_CMD_RE = re.compile(r"\\[a-zA-Z]+")


def delatex(s):
    """Strip LaTeX markup down to comparable plain text."""
    if not s:
        return ""
    s = s.replace("\n", " ").replace("\t", " ")
    s = re.sub(r"\\url\{([^}]*)\}", r"\1", s)
    s = _ACCENT_RE.sub(r"\1", s)             # {\'e} -> e
    s = s.replace("\\&", "&").replace("\\_", "_").replace("\\%", "%").replace("\\$", "$")
    s = re.sub(r"\$[^$]*\$", lambda m: re.sub(r"[^0-9A-Za-z]", "", m.group(0)), s)  # math -> alnum
    s = _CMD_RE.sub("", s)                    # drop remaining \commands
    s = s.replace("{", "").replace("}", "")
    s = re.sub(r"\s+", " ", s).strip()
    return s


def asciifold(s):
    return unicodedata.normalize("NFKD", s).encode("ascii", "ignore").decode("ascii")


def norm_title(s):
    s = asciifold(delatex(s)).lower()
    s = re.sub(r"[^a-z0-9]+", " ", s)
    return re.sub(r"\s+", " ", s).strip()


def title_ratio(a, b):
    a, b = norm_title(a), norm_title(b)
    if not a or not b:
        return 0.0
    return difflib.SequenceMatcher(None, a, b).ratio()


def surname_of_full(name):
    """'Nelson F. Liu' / 'Yang Zhang 0001' -> 'liu' / 'zhang'."""
    name = asciifold(delatex(name)).strip()
    toks = [t for t in name.split() if not t.isdigit()]
    if not toks:
        return ""
    last = toks[-1]
    return re.sub(r"[^a-z0-9\- ]", "", last.lower())


def namekey(name):
    """Whole-name key: ascii-folded, lowercased, only alnum (no spaces/punct).
    Lets 'YuYue' == 'Yu Yue' and 'Wei-Ying Ma' == 'WeiYing Ma'."""
    return re.sub(r"[^a-z0-9]", "", asciifold(delatex(name)).lower())


def parse_bib_authors(raw):
    """BibTeX author string -> list of {display:'First Last', surname:'last'}.

    Keeps a human-readable display name (normalised to 'First Last' order) so the
    HTML report can show exactly what the .bib wrote alongside the source record.
    """
    raw = delatex(raw)
    out = []
    for p in re.split(r"\s+and\s+", raw):
        p = p.strip().strip(",")
        if not p:
            continue
        if "," in p:
            last, _, first = p.partition(",")
            last = last.strip()
            display = (first.strip() + " " + last).strip()
        else:
            toks = p.split()
            last = toks[-1] if toks else p
            display = p
        surname = re.sub(r"[^a-z0-9\- ]", "", asciifold(last).lower().strip())
        if surname:
            out.append({"display": display, "surname": surname})
    return out


CORPORATE_HINTS = (
    "team", "openai", "deepseek", "google", "deepmind", "qwen", "ai", "org",
    "lab", "labs", "research", "inc", "analysis", "lmsys", "anthropic", "meta",
)

# Entry types that are actual DBLP-indexable publications (vs blogs/repos/cards).
PAPER_TYPES = {"article", "inproceedings", "incollection", "inbook", "book",
               "phdthesis", "mastersthesis", "techreport", "conference"}


def looks_corporate(bib_author_raw):
    """True if the bib author field is a group/organization, not a person list."""
    raw = delatex(bib_author_raw).strip()
    if not raw:
        return False
    if re.search(r"\sand\s", raw):       # multiple authors => people
        return False
    if "," in raw:                       # 'Last, First' => a person
        return False
    tokens = raw.split()
    low = raw.lower()
    has_hint = any(h in re.split(r"[\s/\-]+", low) for h in CORPORATE_HINTS)
    camel = bool(re.search(r"[a-z][A-Z]", raw))   # OpenAI, DeepMind, DeepSeek-AI
    return has_hint or camel or len(tokens) == 1


# ============================================================================
# 3. HTTP layer with cache + retry
# ============================================================================
class Net:
    def __init__(self, delay=0.8, use_cache=True, timeout=30, verbose=False):
        self.delay = delay
        self.timeout = timeout
        self.verbose = verbose
        self.use_cache = use_cache
        self.cache = {}
        self._last = 0.0
        if use_cache and os.path.exists(CACHE_PATH):
            try:
                with open(CACHE_PATH, encoding="utf-8") as f:
                    self.cache = json.load(f)
            except Exception:
                self.cache = {}

    def save(self):
        if self.use_cache:
            try:
                with open(CACHE_PATH, "w", encoding="utf-8") as f:
                    json.dump(self.cache, f)
            except Exception:
                pass

    def _throttle(self):
        wait = self.delay - (time.time() - self._last)
        if wait > 0:
            time.sleep(wait)
        self._last = time.time()

    def get(self, url, accept=None, retries=3, ua=None):
        ck = (accept or "") + "|" + url
        if self.use_cache and ck in self.cache:
            c = self.cache[ck]
            return c["status"], c["body"]
        headers = {"User-Agent": ua or UA}
        if accept:
            headers["Accept"] = accept
        result = (None, "")
        for attempt in range(retries):
            self._throttle()
            try:
                req = urllib.request.Request(url, headers=headers)
                with urllib.request.urlopen(req, timeout=self.timeout) as r:
                    status = r.getcode()
                    body = r.read().decode("utf-8", "replace")
                result = (status, body)
                break
            except urllib.error.HTTPError as e:
                status = e.code
                body = ""
                try:
                    body = e.read().decode("utf-8", "replace")
                except Exception:
                    pass
                if status in (429, 500, 502, 503, 504) and attempt < retries - 1:
                    time.sleep(1.5 * (attempt + 1))
                    continue
                result = (status, body)
                break
            except Exception:  # URLError, timeout, SSL/Cloudflare reset, ...
                if attempt < retries - 1:
                    time.sleep(1.0 * (attempt + 1))
                    continue
                result = (None, "")
                break
        if self.verbose:
            sys.stderr.write(C.dim(f"    GET {result[0]} {url}\n"))
        if self.use_cache and result[0] is not None:
            self.cache[ck] = {"status": result[0], "body": result[1]}
        return result


# ============================================================================
# 4. Source clients -> normalized record
#    record = {source, title, authors(list of surnames), year, venue, doi,
#              url, raw_authors, found(bool), note}
# ============================================================================
def extract_arxiv_id(entry):
    f = entry["fields"]
    blob = " ".join([f.get("journal", ""), f.get("eprint", ""), f.get("url", ""),
                     f.get("note", ""), f.get("howpublished", "")])
    m = re.search(r"arxiv[:/ ]*?(\d{4}\.\d{4,5})", blob, re.I)
    if not m:
        m = re.search(r"arxiv\.org/abs/(\d{4}\.\d{4,5})", blob, re.I)
    if m:
        return m.group(1)
    # bare eprint field "2402.03300"
    ep = f.get("eprint", "").strip()
    if re.fullmatch(r"\d{4}\.\d{4,5}", ep):
        return ep
    return None


def extract_doi(entry):
    f = entry["fields"]
    doi = f.get("doi", "").strip()
    if doi:
        doi = re.sub(r"^https?://(dx\.)?doi\.org/", "", doi, flags=re.I)
        return doi
    m = re.search(r"doi\.org/(10\.\S+)", f.get("url", ""), re.I)
    return m.group(1) if m else None


def extract_openreview_id(entry):
    f = entry["fields"]
    blob = " ".join([f.get("url", ""), f.get("howpublished", ""), f.get("note", "")])
    m = re.search(r"openreview\.net/(?:forum|pdf)\?id=([A-Za-z0-9_\-]+)", blob)
    return m.group(1) if m else None


def arxiv_lookup(net, arxiv_id):
    arxiv_id = arxiv_id.split("v")[0]
    url = "https://export.arxiv.org/api/query?id_list=" + urllib.parse.quote(arxiv_id)
    status, body = net.get(url)
    if status != 200 or not body:
        return {"source": "arXiv", "found": False, "note": f"HTTP {status}"}
    ns = {"a": "http://www.w3.org/2005/Atom"}
    try:
        root = ET.fromstring(body)
    except ET.ParseError:
        return {"source": "arXiv", "found": False, "note": "parse error"}
    entries = root.findall("a:entry", ns)
    if not entries:
        return {"source": "arXiv", "found": False, "note": "id not found"}
    e = entries[0]
    title = (e.findtext("a:title", "", ns) or "").strip()
    if title.lower().startswith("error"):
        return {"source": "arXiv", "found": False, "note": "id not found"}
    authors = [surname_of_full((a.findtext("a:name", "", ns) or "")) for a in e.findall("a:author", ns)]
    raw_authors = [(a.findtext("a:name", "", ns) or "").strip() for a in e.findall("a:author", ns)]
    published = e.findtext("a:published", "", ns) or ""
    year = published[:4] if published[:4].isdigit() else None
    idu = (e.findtext("a:id", "", ns) or "").strip()
    return {"source": "arXiv", "found": True, "title": title,
            "authors": [a for a in authors if a], "raw_authors": raw_authors,
            "year": year, "venue": "arXiv", "doi": None, "url": idu, "note": ""}


def crossref_lookup(net, doi):
    url = "https://api.crossref.org/works/" + urllib.parse.quote(doi)
    status, body = net.get(url, accept="application/json")
    if status == 404:
        return {"source": "Crossref", "found": False, "note": "DOI not registered"}
    if status != 200 or not body:
        return {"source": "Crossref", "found": False, "note": f"HTTP {status}"}
    try:
        msg = json.loads(body)["message"]
    except Exception:
        return {"source": "Crossref", "found": False, "note": "parse error"}
    title = (msg.get("title") or [""])[0]
    authors, raw = [], []
    for a in msg.get("author", []) or []:
        fam = a.get("family") or a.get("name") or ""
        raw.append((a.get("given", "") + " " + fam).strip() or fam)
        if fam:
            authors.append(re.sub(r"[^a-z0-9\- ]", "", asciifold(fam).lower()))
    year = None
    for k in ("published", "published-print", "published-online", "issued", "created"):
        dp = (msg.get(k) or {}).get("date-parts")
        if dp and dp[0] and dp[0][0]:
            year = str(dp[0][0])
            break
    venue = (msg.get("container-title") or [""])[0]
    return {"source": "Crossref", "found": True, "title": title, "authors": authors,
            "raw_authors": raw, "year": year, "venue": venue,
            "doi": msg.get("DOI"), "url": msg.get("URL"), "note": ""}


def openreview_lookup(net, oid):
    """Look up an OpenReview submission by forum id (api2). Authoritative for the
    real publication venue + year (e.g. 'ICLR 2026 Oral')."""
    base = "https://api2.openreview.net/notes?"
    for q in ("id=" + urllib.parse.quote(oid), "forum=" + urllib.parse.quote(oid)):
        status, body = net.get(base + q, accept="application/json")
        if status != 200 or not body:
            continue
        try:
            notes = json.loads(body).get("notes", [])
        except Exception:
            continue
        # prefer the submission note itself (id == forum)
        note = None
        for nn in notes:
            if nn.get("id") == oid:
                note = nn
                break
        note = note or (notes[0] if notes else None)
        if not note:
            continue
        c = note.get("content", {})

        def gv(k):
            v = c.get(k)
            return v.get("value") if isinstance(v, dict) else v

        title = (gv("title") or "").strip()
        if not title:
            continue
        raw_authors = gv("authors") or []
        if isinstance(raw_authors, str):
            raw_authors = [raw_authors]
        raw_authors = [a for a in raw_authors if a and a.lower() != "anonymous"]
        venue = (gv("venue") or gv("venueid") or "").strip()
        m = re.search(r"(19|20)\d\d", venue)
        year = m.group(0) if m else None
        if not year:
            for k in ("pdate", "odate", "cdate"):
                ms = note.get(k)
                if isinstance(ms, (int, float)):
                    year = time.strftime("%Y", time.gmtime(ms / 1000))
                    break
        authors = [surname_of_full(a) for a in raw_authors]
        return {"source": "OpenReview", "found": True, "title": title,
                "authors": [a for a in authors if a], "raw_authors": raw_authors,
                "year": year, "venue": venue, "doi": None,
                "url": "https://openreview.net/forum?id=" + oid, "note": ""}
    return {"source": "OpenReview", "found": False, "note": "forum id not found"}


def _as_list(x):
    if x is None:
        return []
    return x if isinstance(x, list) else [x]


def dblp_search(net, title):
    q = norm_title(title)
    if not q:
        return {"source": "DBLP", "found": False, "note": "empty title"}
    url = ("https://dblp.org/search/publ/api?format=json&h=15&q="
           + urllib.parse.quote(q))
    status, body = net.get(url, accept="application/json")
    if status != 200 or not body:
        return {"source": "DBLP", "found": False, "note": f"HTTP {status}"}
    try:
        hits = json.loads(body)["result"]["hits"]
    except Exception:
        return {"source": "DBLP", "found": False, "note": "parse error"}
    if hits.get("@total", "0") == "0" or "hit" not in hits:
        return {"source": "DBLP", "found": False, "note": "no DBLP hit"}
    # Score every hit by title similarity. When the same paper appears as both a
    # preprint ("CoRR") and a published version, prefer the published one so the
    # reported year/venue is the proceedings year, not the preprint year.
    scored = []
    for h in _as_list(hits["hit"]):
        info = h.get("info", {})
        scored.append((title_ratio(title, info.get("title", "")), info))
    scored.sort(key=lambda x: x[0], reverse=True)
    best_r = scored[0][0] if scored else 0.0
    if not scored or best_r < 0.82:
        return {"source": "DBLP", "found": False, "note": "no close DBLP title match",
                "best_ratio": round(best_r, 2)}
    # among near-ties (within 0.03 of the top), prefer a non-CoRR venue
    near = [info for r, info in scored if best_r - r <= 0.03]
    best = next((i for i in near if (i.get("venue") or "").upper() != "CORR"), near[0])
    authors_raw = []
    auth = best.get("authors", {}).get("author") if best.get("authors") else None
    for a in _as_list(auth):
        nm = a.get("text", "") if isinstance(a, dict) else str(a)
        authors_raw.append(nm)
    authors = [surname_of_full(a) for a in authors_raw]
    return {"source": "DBLP", "found": True, "title": best.get("title", ""),
            "authors": [a for a in authors if a], "raw_authors": authors_raw,
            "year": str(best.get("year", "")) or None, "venue": best.get("venue", ""),
            "doi": best.get("doi"), "url": best.get("ee") or best.get("url"),
            "note": "", "match_ratio": round(best_r, 2)}


def url_check(net, url):
    """Best-effort liveness check for @misc/@software URLs."""
    url = url.strip()
    m = re.search(r"\\url\{([^}]*)\}", url)
    if m:
        url = m.group(1)
    m = re.search(r"https?://\S+", url)
    if not m:
        return {"url": url, "status": None, "note": "no URL"}
    url = m.group(0).rstrip(".,;)}")
    status, _ = net.get(url, ua=BROWSER_UA)
    return {"url": url, "status": status}


# ============================================================================
# 5. Comparison + verdict
# ============================================================================
def cmp_title(bib_title, rec):
    r = title_ratio(bib_title, rec.get("title", ""))
    if r >= 0.90:
        return OK, r, None
    if r >= 0.72:
        return MINOR, r, f"title differs slightly (sim={r:.2f}) vs “{delatex(rec.get('title',''))}”"
    return FAIL, r, (f"title does NOT match {rec['source']} record "
                     f"(sim={r:.2f}) — {rec['source']} says “{delatex(rec.get('title',''))}”")


def cmp_authors(bib_raw, rec):
    """Return (severity, message, diff). `diff` is None unless there is an
    author mismatch worth visualising, in which case it is:
        {source, bib:[{display,matched}], src:[{display,matched}]}
    where `matched` flags whether that name appears on the other side."""
    if looks_corporate(bib_raw):
        return INFO, "group/organization author — not individually verifiable", None
    bib = parse_bib_authors(bib_raw)
    src_surn = rec.get("authors", [])
    src_raw = rec.get("raw_authors") or []
    if not bib:
        return INFO, "no parseable authors in bib", None
    if not src_surn:
        return INFO, f"{rec['source']} record has no author list", None
    src_set = set(src_surn)
    # full-name keys (all alnum, no spaces) tolerate spacing variants like
    # 'YuYue' vs 'Yu Yue' or 'Wei-Ying' vs 'WeiYing'.
    src_fullkeys = {namekey(s) for s in src_raw}

    def in_src(b):
        # Direct surname match, or last-token match for multi-token surnames
        # ('Duong Nguyen' -> 'nguyen'), or a whole-name match ignoring spacing.
        if b["surname"] in src_set:
            return True
        toks = b["surname"].split()
        if len(toks) > 1 and toks[-1] in src_set:
            return True
        return namekey(b["display"]) in src_fullkeys

    # bib-side keys for the reverse direction
    bib_surn, bib_fullkeys = set(), set()
    for b in bib:
        bib_surn.add(b["surname"])
        t = b["surname"].split()
        if len(t) > 1:
            bib_surn.add(t[-1])
        bib_fullkeys.add(namekey(b["display"]))

    def in_bib(raw):
        return surname_of_full(raw) in bib_surn or namekey(raw) in bib_fullkeys

    for b in bib:
        b["matched"] = in_src(b)
    matched = [b for b in bib if b["matched"]]
    overlap = len(matched) / len(bib)
    first_ok = bib[0]["matched"]
    missing = [b["display"] for b in bib if not b["matched"]]

    diff = {
        "source": rec["source"],
        "bib": [{"display": b["display"], "matched": b["matched"]} for b in bib],
        "src": [{"display": delatex(s), "matched": in_bib(s)} for s in src_raw],
    }
    detail = (f"bib {len(bib)} authors vs {rec['source']} {len(src_raw)}; "
              f"overlap {len(matched)}/{len(bib)}")
    miss_str = f"; not in {rec['source']}: {', '.join(missing)}" if missing else ""
    if overlap >= 0.99 and len(bib) == len(src_raw):
        return OK, detail, None
    if first_ok and overlap >= 0.85:
        return MINOR, detail + miss_str, diff
    if not first_ok:
        return WARN, (f"first author “{bib[0]['display']}” not found in "
                      f"{rec['source']} author list"), diff
    # first author matches but several listed authors are absent from the source:
    # a likely sign of an incorrect / partially fabricated author list.
    return WARN, ("listed authors disagree with " + rec["source"] + " — "
                  + detail + miss_str), diff


def cmp_year(bib_year, rec, expect_published=False):
    """Compare the bib year against a source record.

    `expect_published`: the entry claims a real venue (e.g. @inproceedings at
    ICLR/NeurIPS) but the only year we have comes from a *preprint* (arXiv / DBLP
    CoRR). The proceedings year is normally the preprint year + 1, so a bib year
    that is 0–2 years AFTER the preprint is expected and not flagged."""
    by = re.sub(r"\D", "", bib_year or "")
    ry = re.sub(r"\D", "", rec.get("year") or "")
    if not by or not ry:
        return INFO, f"year not comparable (bib={bib_year!r}, {rec['source']}={rec.get('year')!r})"
    if by == ry:
        return OK, None
    d = int(by) - int(ry)
    if expect_published and 0 <= d <= 2:
        return OK, None  # publication year legitimately follows the preprint
    if abs(d) == 1:
        return MINOR, f"year off by 1 (bib={by}, {rec['source']}={ry}) — common preprint/proceedings gap"
    return WARN, f"year mismatch (bib={by}, {rec['source']}={ry})"


def verify_entry(net, entry):
    f = entry["fields"]
    bib_title = f.get("title", "")
    bib_authors = f.get("author", "")
    bib_year = f.get("year", "")
    issues = []          # list of (severity, message)
    evidence = []        # list of records consulted

    def add(sev, msg):
        issues.append((sev, msg))

    arxiv_id = extract_arxiv_id(entry)
    doi = extract_doi(entry)
    openreview_id = extract_openreview_id(entry)

    recs = {}            # source name -> normalized record (found ones only)

    # --- identifier-authoritative checks -----------------------------------
    if arxiv_id:
        rec = arxiv_lookup(net, arxiv_id)
        rec["queried"] = arxiv_id
        evidence.append(rec)
        if not rec["found"]:
            add(FAIL, f"arXiv id {arxiv_id} does NOT exist on arXiv ({rec.get('note','')}) "
                      f"— fabricated identifier")
        else:
            recs["arXiv"] = rec
    if doi:
        rec = crossref_lookup(net, doi)
        rec["queried"] = doi
        evidence.append(rec)
        if not rec["found"]:
            add(FAIL, f"DOI {doi} does NOT resolve on Crossref ({rec.get('note','')})")
        else:
            recs["Crossref"] = rec
    if openreview_id:
        rec = openreview_lookup(net, openreview_id)
        rec["queried"] = openreview_id
        evidence.append(rec)
        if rec["found"]:
            recs["OpenReview"] = rec
        else:
            add(INFO, f"OpenReview id {openreview_id} could not be fetched "
                      f"({rec.get('note','')}) — may be withdrawn/private")

    # --- DBLP cross-check (primary source for real publications) -----------
    # Only meaningful for paper-type entries; blogs/repos/model cards (@misc,
    # @software) are not in DBLP, and a loose fuzzy hit there causes false alarms.
    if bib_title and entry["type"] in PAPER_TYPES:
        dblp = dblp_search(net, bib_title)
        evidence.append(dblp)
        if dblp.get("found"):
            recs["DBLP"] = dblp

    # --- pick references ---------------------------------------------------
    # Title/authors: prefer arXiv (canonical, full author list); then the
    # published-venue records. Year: prefer a venue source, because the correct
    # citation year is the *publication* year (e.g. an ICLR 2026 paper whose
    # arXiv preprint is dated 2025) — only fall back to arXiv when no venue is known.
    title_ref = (recs.get("arXiv") or recs.get("Crossref")
                 or recs.get("OpenReview") or recs.get("DBLP"))
    year_ref = (recs.get("OpenReview") or recs.get("Crossref")
                or recs.get("DBLP") or recs.get("arXiv"))

    # --- field comparisons -------------------------------------------------
    title_status = None
    author_diff = None
    if title_ref:
        title_status, _, msg = cmp_title(bib_title, title_ref)
        if msg:
            add(title_status, msg)
        sa, amsg, adiff = cmp_authors(bib_authors, title_ref)
        if sa != OK:
            add(sa, "authors: " + amsg)
        if adiff:
            author_diff = adiff
    if year_ref:
        # If the only year evidence is a preprint (arXiv, or DBLP's CoRR record)
        # but the entry claims a real published venue, the proceedings year is
        # expected to follow the preprint — don't flag that gap.
        yr_src = year_ref.get("source")
        yr_is_preprint = (yr_src == "arXiv" or
                          (yr_src == "DBLP" and (year_ref.get("venue") or "").upper() == "CORR"))
        claims_venue = entry["type"] in ("inproceedings", "incollection", "conference") or bool(
            entry["fields"].get("booktitle"))
        sy, ymsg = cmp_year(bib_year, year_ref,
                            expect_published=yr_is_preprint and claims_venue)
        if ymsg:
            add(sy, ymsg)

    venue_note = _venue_check(entry, recs)
    if venue_note:
        add(*venue_note)

    # --- unverifiable entries (misc/software/blogs) ------------------------
    confirmed = bool(title_ref and title_status in (OK, MINOR))
    if not confirmed and not any(s == FAIL for s, _ in issues):
        url_field = f.get("url") or f.get("howpublished") or f.get("note") or ""
        if url_field:
            uc = url_check(net, url_field)
            evidence.append({"source": "URL", **uc})
            if uc.get("status") == 200:
                add(INFO, f"no academic record found; URL is live (HTTP 200): {uc['url']}")
            elif uc.get("status") in (301, 302, 303, 307, 308, 401, 403, 405, 406, 429):
                add(INFO, f"no academic record; URL reachable (HTTP {uc['status']}): {uc['url']}")
            elif uc.get("status") in (404, 410):
                add(WARN, f"no academic record and URL returns HTTP {uc['status']} "
                          f"(resource does not exist): {uc['url']}")
            elif uc.get("status") is None:
                add(INFO, f"no academic record; could not reach URL (network/anti-bot — "
                          f"verify manually): {uc.get('url')}")
            else:
                add(WARN, f"no academic record; URL returned HTTP {uc.get('status')}: {uc.get('url')}")
        else:
            add(WARN, "no identifier, no DBLP match, and no URL to verify")

    # --- verdict: driven by hard checks, not by informational notes --------
    sevs = [s for s, _ in issues]
    if FAIL in sevs:
        verdict = FAIL
    elif WARN in sevs:
        verdict = WARN
    elif MINOR in sevs:
        verdict = MINOR
    elif confirmed:
        verdict = OK          # title (+year/authors) confirmed; INFO notes don't downgrade
    else:
        verdict = INFO        # nothing problematic, but nothing academically confirmable
    return {"entry": entry, "verdict": verdict, "issues": issues,
            "evidence": evidence, "arxiv_id": arxiv_id, "doi": doi,
            "openreview_id": openreview_id, "reference": title_ref,
            "author_diff": author_diff}


def _venue_check(entry, recs):
    """Soft check: an @inproceedings claiming a real venue that nobody confirms.
    Suppressed once any published-venue source (OpenReview/DBLP/Crossref) agrees."""
    if entry["type"] != "inproceedings":
        return None
    booktitle = entry["fields"].get("booktitle", "")
    if not booktitle:
        return None
    if recs.get("OpenReview") or recs.get("DBLP") or recs.get("Crossref"):
        return None
    if recs.get("arXiv"):
        return (INFO, f"claims venue “{delatex(booktitle)}” but only an arXiv preprint "
                      f"was found (not yet indexed as published — verify the venue manually)")
    return None


# ============================================================================
# 6. Reporting
# ============================================================================
def fmt_console(res):
    e = res["entry"]
    v = res["verdict"]
    color = SEV_COLOR[v]
    head = f"{SEV_ICON[v]} {color(SEV_LABEL[v]):<12} {C.bold(e['key'])}  {C.dim('(@'+e['type']+', L'+str(e['line'])+')')}"
    lines = [head]
    title = delatex(e["fields"].get("title", ""))
    lines.append("    " + C.dim(title[:96] + ("…" if len(title) > 96 else "")))
    for sev, msg in res["issues"]:
        lines.append("      " + SEV_COLOR[sev](SEV_ICON[sev]) + " " + msg)
    if v == OK:
        ref = res["reference"]
        src = ref["source"] if ref else "?"
        lines.append("      " + C.green("✓") + C.dim(f" title/authors/year confirmed via {src}"))
    return "\n".join(lines)


def build_html(results, bibfile):
    n = len(results)
    counts = {}
    for r in results:
        counts[r["verdict"]] = counts.get(r["verdict"], 0) + 1
    order = {FAIL: 0, WARN: 1, MINOR: 2, INFO: 3, OK: 4}
    esc = html.escape

    # palette per severity (border, badge bg, text)
    PAL = {
        FAIL:  ("#e5484d", "#fdecec"),
        WARN:  ("#f76b15", "#fdefe3"),
        MINOR: ("#e0a400", "#fdf6e3"),
        INFO:  ("#4a7fd0", "#eef3fb"),
        OK:    ("#30a46c", "#e9f7f0"),
    }
    SEV_HTML_LABEL = {FAIL: "SUSPECT", WARN: "WARNING", MINOR: "MINOR",
                      INFO: "UNVERIFIABLE", OK: "OK"}

    def linkify(text):
        """Turn bare URLs in a finding message into clickable links (escaped)."""
        out, last = [], 0
        for m in re.finditer(r"https?://[^\s)]+", text):
            out.append(esc(text[last:m.start()]))
            u = m.group(0)
            out.append(f'<a href="{esc(u)}" target="_blank" rel="noopener">{esc(u)}</a>')
            last = m.end()
        out.append(esc(text[last:]))
        return "".join(out)

    def badge(sev, big=False):
        c = PAL[sev]
        cls = "badge big" if big else "badge"
        return (f'<span class="{cls}" style="background:{c[1]};color:{c[0]};'
                f'border:1px solid {c[0]}">{SEV_ICON[sev].strip()} {SEV_HTML_LABEL[sev]}</span>')

    cards = []
    for r in sorted(results, key=lambda r: (order[r["verdict"]], r["entry"]["line"])):
        e = r["entry"]
        v = r["verdict"]
        border = PAL[v][0]
        title = delatex(e["fields"].get("title", ""))
        ids = []
        if r["arxiv_id"]:
            ax = esc(r["arxiv_id"])
            ids.append(f'arXiv <a href="https://arxiv.org/abs/{ax}" target="_blank" '
                       f'rel="noopener"><code>{ax}</code></a>')
        if r["doi"]:
            d = esc(r["doi"])
            ids.append(f'DOI <a href="https://doi.org/{d}" target="_blank" '
                       f'rel="noopener"><code>{d}</code></a>')
        if r.get("openreview_id"):
            o = esc(r["openreview_id"])
            ids.append(f'OpenReview <a href="https://openreview.net/forum?id={o}" '
                       f'target="_blank" rel="noopener"><code>{o}</code></a>')
        id_html = (' &nbsp;·&nbsp; '.join(ids))

        findings = []
        if r["issues"]:
            for sev, msg in r["issues"]:
                findings.append(
                    f'<li><span class="dot" style="color:{PAL[sev][0]}">'
                    f'{SEV_ICON[sev].strip()}</span> {linkify(msg)}</li>')
        else:
            ref = r["reference"]
            src = ref["source"] if ref else "?"
            findings.append(f'<li><span class="dot" style="color:{PAL[OK][0]}">✓</span> '
                            f'title, authors and year confirmed via {esc(src)}</li>')

        evidence = []
        for rec in r["evidence"]:
            if rec.get("source") in ("arXiv", "Crossref", "DBLP", "OpenReview") and rec.get("found"):
                ra = rec.get("raw_authors") or []
                authstr = esc(", ".join(ra[:8]) + (" …" if len(ra) > 8 else ""))
                url = rec.get("url")
                t = esc(delatex(rec.get("title", "")))
                link = (f'<a href="{esc(url)}" target="_blank" rel="noopener">{t}</a>'
                        if url else t)
                ven = rec.get("venue")
                ven_html = f' <span class="ven">{esc(ven)}</span>' if ven and rec["source"] in ("OpenReview", "DBLP", "Crossref") else ""
                evidence.append(
                    f'<div class="evi"><span class="src">{esc(rec["source"])}</span> '
                    f'“{link}” <span class="yr">({esc(str(rec.get("year")))})</span>{ven_html}'
                    f'<div class="auth">{authstr}</div></div>')
        evi_html = ("".join(evidence))

        # author diff (correct vs. written), side by side with mismatches marked
        diff_html = ""
        ad = r.get("author_diff")
        if ad:
            def names_html(items):
                cells = []
                for it in items:
                    cls = "ok" if it["matched"] else "bad"
                    mark = "" if it["matched"] else ' <span class="x">✗</span>'
                    cells.append(f'<li class="{cls}">{esc(it["display"])}{mark}</li>')
                return "<ol class='names'>" + "".join(cells) + "</ol>"
            src_name = esc(ad["source"])
            diff_html = (
                '<div class="diff">'
                '<div class="diff-label">Author comparison '
                '<span class="lg"><span class="sw bad"></span>not found on the other side</span></div>'
                '<div class="cols">'
                f'<div class="col"><div class="ch">Your .bib</div>{names_html(ad["bib"])}</div>'
                f'<div class="col"><div class="ch">{src_name} (authoritative)</div>{names_html(ad["src"])}</div>'
                '</div></div>')

        cards.append(f"""
      <article class="card" data-verdict="{v}" style="border-left:6px solid {border}">
        <div class="card-head">
          {badge(v)}
          <span class="key">{esc(e['key'])}</span>
          <span class="meta">@{esc(e['type'])} · line {e['line']}</span>
        </div>
        <div class="title">{esc(title)}</div>
        {f'<div class="ids">{id_html}</div>' if id_html else ''}
        <ul class="findings">{''.join(findings)}</ul>
        {diff_html}
        {f'<div class="evidence"><div class="evi-label">Matched record(s)</div>{evi_html}</div>' if evi_html else ''}
      </article>""")

    chips = []
    for k in (FAIL, WARN, MINOR, INFO, OK):
        c = counts.get(k, 0)
        col = PAL[k][0]
        chips.append(
            f'<button class="chip" data-filter="{k}" style="--c:{col}">'
            f'{SEV_ICON[k].strip()} {SEV_HTML_LABEL[k]} <b>{c}</b></button>')
    chips_html = ('<button class="chip active" data-filter="ALL">All <b>'
                  + str(n) + '</b></button>' + "".join(chips))

    generated = time.strftime("%Y-%m-%d %H:%M:%S")
    flagged = counts.get(FAIL, 0) + counts.get(WARN, 0)

    return f"""<!doctype html>
<html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Citation verification — {esc(os.path.basename(bibfile))}</title>
<style>
  :root {{ --bg:#f6f7f9; --card:#fff; --ink:#1c2024; --muted:#6b7280; --line:#e5e7eb; }}
  * {{ box-sizing:border-box; }}
  body {{ margin:0; background:var(--bg); color:var(--ink);
         font:15px/1.55 -apple-system,BlinkMacSystemFont,"Segoe UI",Roboto,"PingFang SC","Microsoft YaHei",sans-serif; }}
  header {{ background:linear-gradient(180deg,#fff,#fbfcfd); border-bottom:1px solid var(--line);
           padding:26px 28px; }}
  h1 {{ margin:0 0 6px; font-size:21px; }}
  .sub {{ color:var(--muted); font-size:13px; }}
  .sub code {{ background:#eef0f3; padding:1px 6px; border-radius:5px; }}
  .wrap {{ max-width:1000px; margin:0 auto; padding:0 16px 60px; }}
  .toolbar {{ position:sticky; top:0; z-index:5; background:var(--bg);
             padding:16px 0 10px; display:flex; flex-wrap:wrap; gap:8px; align-items:center; }}
  .chip {{ cursor:pointer; border:1px solid var(--line); background:#fff; color:#374151;
          padding:6px 12px; border-radius:999px; font-size:13px; }}
  .chip b {{ color:var(--c,#374151); margin-left:3px; }}
  .chip.active {{ background:#111827; color:#fff; border-color:#111827; }}
  .chip.active b {{ color:#fff; }}
  .search {{ margin-left:auto; padding:7px 11px; border:1px solid var(--line);
            border-radius:8px; font-size:13px; min-width:200px; }}
  .card {{ background:var(--card); border:1px solid var(--line); border-radius:12px;
          padding:14px 16px; margin:12px 0; box-shadow:0 1px 2px rgba(0,0,0,.03); }}
  .card-head {{ display:flex; align-items:center; gap:10px; flex-wrap:wrap; }}
  .badge {{ font-size:11.5px; font-weight:700; letter-spacing:.02em; padding:3px 9px;
           border-radius:999px; white-space:nowrap; }}
  .key {{ font-weight:650; font-family:ui-monospace,SFMono-Regular,Menlo,monospace; font-size:14px; }}
  .meta {{ color:var(--muted); font-size:12.5px; }}
  .title {{ margin:8px 0 2px; font-size:15.5px; font-weight:550; }}
  .ids {{ font-size:13px; color:#374151; margin-top:4px; }}
  .ids code {{ background:#eef0f3; padding:1px 5px; border-radius:5px; }}
  ul.findings {{ list-style:none; margin:10px 0 0; padding:0; }}
  ul.findings li {{ padding:3px 0; font-size:14px; }}
  .dot {{ display:inline-block; width:1.4em; }}
  .evidence {{ margin-top:11px; padding:10px 12px; background:#fafbfc;
              border:1px dashed var(--line); border-radius:9px; }}
  .evi-label {{ font-size:11px; text-transform:uppercase; letter-spacing:.06em;
               color:var(--muted); margin-bottom:5px; }}
  .evi {{ font-size:13px; margin:5px 0; }}
  .evi .src {{ display:inline-block; font-weight:700; font-size:11px; color:#374151;
              background:#eef0f3; padding:1px 6px; border-radius:5px; margin-right:5px; }}
  .evi .yr {{ color:var(--muted); }}
  .evi .ven {{ color:#6b7280; font-size:12.5px; font-style:italic; }}
  .evi .auth {{ color:var(--muted); font-size:12.5px; margin-top:1px; }}
  .diff {{ margin-top:11px; padding:10px 12px; background:#fff;
          border:1px solid var(--line); border-radius:9px; }}
  .diff-label {{ font-size:11px; text-transform:uppercase; letter-spacing:.06em;
                color:var(--muted); margin-bottom:8px; }}
  .diff-label .lg {{ text-transform:none; letter-spacing:0; margin-left:8px; font-size:11.5px; }}
  .diff-label .sw {{ display:inline-block; width:10px; height:10px; border-radius:2px;
                    vertical-align:middle; margin-right:3px; }}
  .sw.bad {{ background:#fde2e1; border:1px solid #e5484d; }}
  .cols {{ display:grid; grid-template-columns:1fr 1fr; gap:12px; }}
  @media (max-width:640px) {{ .cols {{ grid-template-columns:1fr; }} }}
  .col .ch {{ font-size:12px; font-weight:700; color:#374151; margin-bottom:4px; }}
  ol.names {{ margin:0; padding-left:22px; }}
  ol.names li {{ font-size:13px; padding:1px 4px; border-radius:4px; }}
  ol.names li.bad {{ background:#fdecec; color:#b4262a; font-weight:600; }}
  ol.names li .x {{ font-weight:700; }}
  a {{ color:#2563eb; text-decoration:none; }}
  a:hover {{ text-decoration:underline; }}
  .hidden {{ display:none; }}
  .legend {{ font-size:12.5px; color:var(--muted); margin-top:8px; }}
  footer {{ text-align:center; color:var(--muted); font-size:12px; padding:24px; }}
</style></head>
<body>
<header>
  <div class="wrap" style="padding-bottom:0">
    <h1>Citation verification report</h1>
    <div class="sub">File <code>{esc(bibfile)}</code> &nbsp;·&nbsp; {n} entries &nbsp;·&nbsp;
      <b style="color:{PAL[FAIL][0] if flagged else PAL[OK][0]}">{flagged} need attention</b>
      &nbsp;·&nbsp; generated {esc(generated)}</div>
    <div class="legend">❌ <b>SUSPECT</b> fabricated/invalid identifier or wrong title ·
      ⚠️ <b>WARNING</b> notable mismatch · 🟡 <b>MINOR</b> small diff (e.g. preprint/proceedings year) ·
      ℹ️ <b>UNVERIFIABLE</b> no academic source (blog/repo/model card) · ✅ <b>OK</b> confirmed.
      Sources: DBLP, arXiv, Crossref, OpenReview.</div>
  </div>
</header>
<div class="wrap">
  <div class="toolbar">
    {chips_html}
    <input class="search" id="q" type="search" placeholder="filter by key or title…">
  </div>
  <main id="cards">
    {''.join(cards)}
  </main>
  <footer>Generated by check_citations.py — verify flagged entries manually before trusting/deleting.</footer>
</div>
<script>
  const cards = [...document.querySelectorAll('.card')];
  let curFilter = 'ALL', curQ = '';
  function apply() {{
    for (const c of cards) {{
      const okV = curFilter === 'ALL' || c.dataset.verdict === curFilter;
      const txt = c.textContent.toLowerCase();
      const okQ = !curQ || txt.includes(curQ);
      c.classList.toggle('hidden', !(okV && okQ));
    }}
  }}
  document.querySelectorAll('.chip').forEach(ch => ch.addEventListener('click', () => {{
    document.querySelectorAll('.chip').forEach(x => x.classList.remove('active'));
    ch.classList.add('active');
    curFilter = ch.dataset.filter; apply();
  }}));
  document.getElementById('q').addEventListener('input', e => {{
    curQ = e.target.value.trim().toLowerCase(); apply();
  }});
</script>
</body></html>"""


def build_json(results, bibfile):
    data = {"file": bibfile, "entries": []}
    for r in results:
        e = r["entry"]
        data["entries"].append({
            "key": e["key"], "type": e["type"], "line": e["line"],
            "verdict": r["verdict"], "verdict_label": SEV_LABEL[r["verdict"]],
            "title": delatex(e["fields"].get("title", "")),
            "arxiv_id": r["arxiv_id"], "doi": r["doi"],
            "openreview_id": r.get("openreview_id"),
            "issues": [{"severity": s, "message": m} for s, m in r["issues"]],
            "author_diff": r.get("author_diff"),
            "evidence": list(r["evidence"]),
        })
    return json.dumps(data, indent=2, ensure_ascii=False)


# ============================================================================
# 7. Main
# ============================================================================
def main():
    ap = argparse.ArgumentParser(
        description="Detect hallucinated / incorrect citations in a LaTeX .bib file "
                    "by verifying title, authors, year and unique identifiers against "
                    "DBLP, arXiv, Crossref and OpenReview.")
    ap.add_argument("bibfile", help="path to the .bib file")
    ap.add_argument("--html", metavar="FILE", default="report.html",
                    help="write an HTML report (default: report.html; pass '' to skip)")
    ap.add_argument("--json", metavar="FILE", help="write a JSON report")
    ap.add_argument("--only", nargs="+", metavar="KEY", help="only check these cite keys")
    ap.add_argument("--delay", type=float, default=0.8,
                    help="seconds between web requests (politeness; default 0.8)")
    ap.add_argument("--no-cache", action="store_true", help="do not read/write the local HTTP cache")
    ap.add_argument("--verbose", action="store_true", help="print every HTTP request")
    args = ap.parse_args()

    if not os.path.exists(args.bibfile):
        sys.exit(f"error: file not found: {args.bibfile}")
    with open(args.bibfile, encoding="utf-8") as fh:
        text = fh.read()

    entries = parse_bib(text)
    if args.only:
        keep = set(args.only)
        entries = [e for e in entries if e["key"] in keep]
    if not entries:
        sys.exit("no entries to check")

    net = Net(delay=args.delay, use_cache=not args.no_cache, verbose=args.verbose)
    print(C.bold(f"Checking {len(entries)} citation(s) from {args.bibfile}\n"))

    results = []
    for idx, e in enumerate(entries, 1):
        sys.stdout.write(C.dim(f"[{idx}/{len(entries)}] {e['key']} …\r"))
        sys.stdout.flush()
        try:
            res = verify_entry(net, e)
        except Exception as ex:
            res = {"entry": e, "verdict": WARN,
                   "issues": [(WARN, f"checker error: {ex}")],
                   "evidence": [], "arxiv_id": None, "doi": None, "reference": None}
        results.append(res)
        sys.stdout.write(" " * 60 + "\r")
        print(fmt_console(res))
        net.save()

    # summary
    counts = {}
    for r in results:
        counts[r["verdict"]] = counts.get(r["verdict"], 0) + 1
    print("\n" + C.bold("Summary:"))
    for k in (FAIL, WARN, MINOR, INFO, OK):
        if counts.get(k):
            print(f"  {SEV_ICON[k]} {SEV_COLOR[k](SEV_LABEL[k]):<14} {counts[k]}")
    flagged = [r for r in results if r["verdict"] in (FAIL, WARN)]
    if flagged:
        print("\n" + C.bold("Needs attention:"))
        for r in sorted(flagged, key=lambda r: SEV_ORDER[r["verdict"]], reverse=True):
            print(f"  {SEV_ICON[r['verdict']]} {r['entry']['key']}")

    if args.html:
        with open(args.html, "w", encoding="utf-8") as f:
            f.write(build_html(results, args.bibfile))
        print(C.dim(f"\nHTML report -> {os.path.abspath(args.html)}"))
    if args.json:
        with open(args.json, "w", encoding="utf-8") as f:
            f.write(build_json(results, args.bibfile))
        print(C.dim(f"JSON report -> {os.path.abspath(args.json)}"))

    net.save()
    # exit non-zero if anything looks fabricated, useful for CI
    sys.exit(1 if any(r["verdict"] == FAIL for r in results) else 0)


if __name__ == "__main__":
    main()
