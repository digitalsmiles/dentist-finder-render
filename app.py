import os, re, time, math, json, random, unicodedata, threading, io
from urllib.parse import urljoin, urlparse
from collections import deque
from concurrent.futures import ThreadPoolExecutor, TimeoutError as FuturesTimeout

import requests
import pandas as pd
import googlemaps
from bs4 import BeautifulSoup
from requests.adapters import HTTPAdapter
from urllib3.util.retry import Retry

from dash import Dash, html, dcc, Input, Output, State, dash_table, no_update

# ==========================
# Tunables (stable & safe)
# ==========================
CONNECT_TIMEOUT = 5
READ_TIMEOUT = 25
TIMEOUT = (CONNECT_TIMEOUT, READ_TIMEOUT)
PLACE_TIMEOUT = 120
RETRIES = 3
CRAWL_SLEEP = 0.35
NEARBY_SLEEP = 2.1
JITTER = 0.25
MAX_HTML_BYTES = 1_800_000
MAX_WORKERS = 2

BINARY_EXTS = (
    ".pdf",".doc",".docx",".xls",".xlsx",".ppt",".pptx",".zip",".rar",
    ".png",".jpg",".jpeg",".gif",".svg",".webp",".mp4",".avi",".mov",".wmv",
    ".ics",".csv",".json",".xml",".rss",".atom"
)

HEADERS = {
    "User-Agent": "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 "
                  "(like Gecko) Chrome/124.0 Safari/537.36"
}

EMAIL_RE = re.compile(r"\b[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}\b", re.I)
OBFUSCATED_EMAIL_RE = re.compile(
    r"([A-Z0-9._%+\-]+)\s*(?:@|\s?[\[\(]{0,1}\s*at\s*[\]\)]{0,1}\s?)\s*([A-Z0-9.\-]+)\s*(?:\.|\s?dot\s?)\s*([A-Z]{2,})",
    re.I
)
MOBILE_RE = re.compile(
    r"\b(04\d{2}[-\s]?\d{3}[-\s]?\d{3}|(\+?61[-\s]?)?4\d{2}[-\s]?\d{3}[-\s]?\d{3})\b"
)

ROLE_OK = [
    "principal dentist", "practice owner", "owner",
    "lead dentist", "clinical director", "principal"
]
ROLE_OWNER = [
    "practice owner", "owner", "managing director", "director", "general manager"
]
ROLE_FOUNDER = [
    "founder", "co-founder"
]
ROLE_BLOCK = [
    "associate", "hygienist", "therapist", "oral health therapist",
    "assistant", "reception", "practice manager", "coordinator",
    "nurse", "specialist anaesthetist", "orthodontic therapist"
]

DR_NAME_RE = re.compile(r"(Dr\.?\s+[A-Z][a-z]+(?:\s+[A-Z][a-z]+){0,2})")

def make_session():
    s = requests.Session()
    retry = Retry(
        total=RETRIES, connect=RETRIES, read=RETRIES, status=RETRIES,
        backoff_factor=0.6,
        status_forcelist=[408,409,425,429,500,502,503,504],
        allowed_methods=frozenset(["GET","HEAD","OPTIONS"]),
    )
    adapter = HTTPAdapter(max_retries=retry, pool_connections=32, pool_maxsize=64)
    s.mount("http://", adapter)
    s.mount("https://", adapter)
    s.headers.update(HEADERS)
    return s

SESSION = make_session()

def slugify(s: str):
    s = unicodedata.normalize("NFKD", s).encode("ascii","ignore").decode("ascii")
    s = re.sub(r"[^A-Za-z0-9]+","_", s).strip("_")
    return s.lower() or "output"

def same_site(a, b):
    ua, ub = urlparse(a), urlparse(b)
    return (ua.scheme, ua.netloc) == (ub.scheme, ub.netloc)

def normalize_abs(base, href):
    if not href: return None
    href = href.strip()
    if href.startswith(("#","mailto:","tel:")): return None
    absu = urljoin(base, href)
    u = urlparse(absu)
    if any(u.path.lower().endswith(ext) for ext in BINARY_EXTS): return None
    return u._replace(fragment="").geturl()

def http_get(url: str):
    for i in range(RETRIES + 1):
        try:
            r = SESSION.get(url, timeout=TIMEOUT, allow_redirects=True, stream=True)
            if not r.ok:
                raise requests.RequestException(f"HTTP {r.status_code}")
            ctype = (r.headers.get("Content-Type","") or "").lower()
            if ("text/html" not in ctype) and ("xml" not in ctype):
                return None, url
            clen = r.headers.get("Content-Length")
            if clen and int(clen) > MAX_HTML_BYTES:
                return None, url
            chunks, total = [], 0
            for chunk in r.iter_content(chunk_size=16384, decode_unicode=True):
                if chunk:
                    if isinstance(chunk, bytes):
                        try:
                            chunk = chunk.decode(errors="ignore")
                        except Exception:
                            chunk = ""
                    chunks.append(chunk)
                    total += len(chunk)
                    if total > MAX_HTML_BYTES: break
            return "".join(chunks), r.url
        except requests.RequestException:
            pass
        time.sleep(0.4 * (2 ** i) + random.random() * JITTER)
    return None, url

def extract_emails(soup: BeautifulSoup):
    found = set()
    for a in soup.select("a[href^='mailto:']"):
        addr = a.get("href","").split("mailto:")[-1].split("?")[0].strip()
        if EMAIL_RE.fullmatch(addr): found.add(addr.lower())
    text = soup.get_text(" ", strip=True)
    for m in EMAIL_RE.finditer(text):
        e = m.group(0).lower()
        if any(e.endswith(ext) for ext in [".jpg",".jpeg",".png",".gif",".svg",".webp"]):
            continue
        allowed_tlds = [
            ".com", ".net", ".org", ".edu", ".gov", ".co", ".uk", ".au", ".info", ".io", ".us", ".biz"
        ]
        if not any(e.endswith(tld) for tld in allowed_tlds):
            continue
        found.add(e)
    for m in OBFUSCATED_EMAIL_RE.finditer(text):
        user, domain, tld = m.groups()
        addr = f"{user}@{domain}.{tld}".lower()
        if EMAIL_RE.fullmatch(addr):
            allowed_tlds = [
                ".com", ".net", ".org", ".edu", ".gov", ".co", ".uk", ".au", ".info", ".io", ".us", ".biz"
            ]
            if any(addr.endswith(tld) for tld in allowed_tlds):
                found.add(addr)
    return set(found)

def extract_mobiles(text):
    matches = MOBILE_RE.findall(text)
    cleaned = []
    for m in matches:
        number = re.sub(r"\D", "", m[0])
        if number.startswith("61") and len(number) == 11:
            number = "0" + number[2:]
        if number.startswith("04") and len(number) == 10:
            cleaned.append(number)
    return list(set(cleaned))

def norm_space(s: str) -> str:
    return re.sub(r"\s+", " ", s or "").strip()

def normalize_name(txt: str):
    txt = norm_space(txt)
    if re.match(r"(?i)^dr\.?\s+", txt):
        txt = re.sub(r"(?i)^dr\.?\s*", "Dr ", txt).strip()
    return txt

def dedupe(names):
    return list(dict.fromkeys([normalize_name(x) for x in names if x]))

def role_is(role_text: str, role_list):
    t = role_text.lower()
    for block_word in ROLE_BLOCK:
        if block_word in t:
            return False
    for ok_word in role_list:
        if ok_word in t:
            return True
    return False

def find_people_by_role(soup: BeautifulSoup, role_list):
    people = []
    for tag in soup.find_all(["h1","h2","h3","h4","strong","b","p","li","span","div"]):
        t = norm_space(tag.get_text(" ", strip=True))
        if not t:
            continue
        m = DR_NAME_RE.search(t)
        name = m.group(1) if m else ""
        if name and role_is(t, role_list):
            people.append(name)
        for ok_word in role_list:
            pat = re.compile(rf"{ok_word}\s*[:\-]?\s*([A-Z][a-z]+(?:\s+[A-Z][a-z]+)*)", re.I)
            m2 = pat.search(t)
            if m2:
                people.append(normalize_name(m2.group(1)))
    for tag in soup.find_all("script", type=lambda t: t and "ld+json" in t):
        try:
            data = json.loads(tag.string or "")
        except Exception:
            continue
        items = data if isinstance(data, list) else [data]
        for it in items:
            if not isinstance(it, dict): continue
            graphs = it.get("@graph") if isinstance(it.get("@graph"), list) else [it]
            for obj in graphs:
                if not isinstance(obj, dict): continue
                job = obj.get("jobTitle") or ""
                name = obj.get("name") or ""
                if name and role_is(job, role_list):
                    people.append(normalize_name(name))
    seen = set()
    return [x for x in people if not (x in seen or seen.add(x))]

def find_principal_by_dr_pattern(soup: BeautifulSoup):
    text = soup.get_text(" ", strip=True)
    matches = DR_NAME_RE.findall(text)
    seen = set()
    return [normalize_name(m) for m in matches if m not in seen and not seen.add(m)]

def crawl_site(site_url: str, max_pages: int, max_seconds: int, progress_cb=None, practice_name=None):
    t0 = time.time()
    html, canon = http_get(site_url)
    if not html: return "", set(), "", site_url, "", "", ""
    queue, seen = deque(), set()
    queue.append(canon); seen.add(canon)
    principal_candidates, owners, founders = [], [], []
    emails, email_src = set(), {}
    pages_scanned = 0
    while queue and pages_scanned < max_pages and (time.time() - t0) < max_seconds:
        url = queue.popleft()
        pages_scanned += 1
        html, final_url = http_get(url)
        if not html:
            if progress_cb: progress_cb(pages_scanned, max_pages)
            continue
        soup = BeautifulSoup(html, "lxml")
        found = extract_emails(soup)
        for e in found:
            email_src.setdefault(e, final_url)
        emails |= found
        page_text = soup.get_text(" ", strip=True)
        principal_candidates += find_principal_by_dr_pattern(soup)
        owners += find_people_by_role(soup, ROLE_OWNER)
        founders += find_people_by_role(soup, ROLE_FOUNDER)
        internal = []
        for a in soup.find_all("a", href=True):
            u = normalize_abs(final_url, a["href"])
            if u and same_site(canon, u) and u not in seen:
                internal.append(u)
        for u in internal:
            seen.add(u); queue.append(u)
        if progress_cb: progress_cb(pages_scanned, max_pages)
        time.sleep(CRAWL_SLEEP + random.random() * JITTER)
    principal_candidates = dedupe(principal_candidates)
    owners = dedupe(owners)
    founders = dedupe(founders)
    first_email = next(iter(emails)) if emails else ""
    first_email_source = ""
    if first_email:
        first_email_source = email_src.get(first_email, "")
    return (
        ", ".join(principal_candidates) if principal_candidates else "",
        emails,
        first_email_source,
        site_url,
        ", ".join(owners) if owners else "",
        ", ".join(founders) if founders else ""
    )

# ... rest of Dash app and worker logic unchanged ...
