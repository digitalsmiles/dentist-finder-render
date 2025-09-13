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
# Tunables
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
    "User-Agent": "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (like Gecko) Chrome/124.0 Safari/537.36"
}

EMAIL_RE = re.compile(r"\b[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}\b", re.I)
OBFUSCATED_EMAIL_RE = re.compile(
    r"([A-Z0-9._%+\-]+)\s*(?:@|\s?[\[\(]{0,1}\s*at\s*[\]\)]{0,1}\s?)\s*([A-Z0-9.\-]+)\s*(?:\.|\s?dot\s?)\s*([A-Z]{2,})",
    re.I
)
MOBILE_RE = re.compile(r"\b(04\d{2}[-\s]?\d{3}[-\s]?\d{3}|(\+?61[-\s]?)?4\d{2}[-\s]?\d{3}[-\s]?\d{3})\b")

ROLE_OK = ["principal dentist","practice owner","owner","lead dentist","clinical director","principal"]
ROLE_OWNER = ["practice owner","owner","managing director","director","general manager"]
ROLE_FOUNDER = ["founder","co-founder"]
ROLE_BLOCK = [
    "associate","hygienist","therapist","oral health therapist","assistant","reception",
    "practice manager","coordinator","nurse","specialist anaesthetist","orthodontic therapist"
]

DR_NAME_RE = re.compile(r"(Dr\.?\s+[A-Z][a-z]+(?:\s+[A-Z][a-z]+){0,2})")

# ==========================
# HTTP
# ==========================
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

# ==========================
# Utils
# ==========================
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
    last_url = url
    for i in range(RETRIES + 1):
        try:
            r = SESSION.get(url, timeout=TIMEOUT, allow_redirects=True, stream=True)
            last_url = r.url
            if not r.ok:
                raise requests.RequestException(f"HTTP {r.status_code}")
            ctype = (r.headers.get("Content-Type","") or "").lower()
            if ("text/html" not in ctype) and ("xml" not in ctype):
                return None, last_url
            clen = r.headers.get("Content-Length")
            if clen and int(clen) > MAX_HTML_BYTES:
                return None, last_url
            chunks, total = [], 0
            for chunk in r.iter_content(chunk_size=16384, decode_unicode=True):
                if chunk:
                    if isinstance(chunk, bytes):
                        try: chunk = chunk.decode(errors="ignore")
                        except Exception: chunk = ""
                    chunks.append(chunk)
                    total += len(chunk)
                    if total > MAX_HTML_BYTES: break
            return "".join(chunks), last_url
        except requests.RequestException:
            pass
        time.sleep(0.4 * (2 ** i) + random.random() * JITTER)
    return None, last_url

def norm_space(s: str) -> str:
    return re.sub(r"\s+", " ", s or "").strip()

def normalize_name(txt: str):
    txt = norm_space(txt)
    if re.match(r"(?i)^dr\.?\s+", txt):
        txt = re.sub(r"(?i)^dr\.?\s*", "Dr ", txt).strip()
    return txt

def dedupe(seq):
    seen, out = set(), []
    for x in seq:
        if not x: continue
        if x not in seen:
            seen.add(x)
            out.append(x)
    return out

def role_is(role_text: str, role_list):
    t = role_text.lower()
    for block_word in ROLE_BLOCK:
        if block_word in t: return False
    for ok_word in role_list:
        if ok_word in t: return True
    return False

# ==========================
# Parsers
# ==========================
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
        allowed_tlds = [".com",".net",".org",".edu",".gov",".co",".uk",".au",".info",".io",".us",".biz"]
        if not any(e.endswith(tld) for tld in allowed_tlds):
            continue
        found.add(e)
    for m in OBFUSCATED_EMAIL_RE.finditer(text):
        user, domain, tld = m.groups()
        addr = f"{user}@{domain}.{tld}".lower()
        if EMAIL_RE.fullmatch(addr):
            allowed_tlds = [".com",".net",".org",".edu",".gov",".co",".uk",".au",".info",".io",".us",".biz"]
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

def find_people_by_role(soup: BeautifulSoup, role_list):
    people = []
    for tag in soup.find_all(["h1","h2","h3","h4","strong","b","p","li","span","div"]):
        t = norm_space(tag.get_text(" ", strip=True))
        if not t: continue
        m = DR_NAME_RE.search(t)
        name = m.group(1) if m else ""
        if name and role_is(t, role_list):
            people.append(normalize_name(name))
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
    return dedupe(people)

def find_principal_by_dr_pattern(soup: BeautifulSoup):
    text = soup.get_text(" ", strip=True)
    matches = DR_NAME_RE.findall(text)
    return dedupe([normalize_name(m) for m in matches])

def extract_mobiles_with_context(soup: BeautifulSoup, page_url: str):
    text = soup.get_text(" ", strip=True)
    mobiles = extract_mobiles(text)
    if not mobiles: return []
    names_role = set(find_people_by_role(soup, ROLE_OK) + find_people_by_role(soup, ROLE_OWNER))
    names_dr = set(find_principal_by_dr_pattern(soup))
    names_all = dedupe(list(names_role) + list(names_dr))
    results, seen = [], set()
    for num in mobiles:
        if num in seen: continue
        seen.add(num)
        person = ""
        idx = text.find(num[:4])
        if idx != -1:
            start = max(0, idx - 160)
            end = min(len(text), idx + 160)
            window = text[start:end]
            mwin = DR_NAME_RE.search(window)
            if mwin:
                person = normalize_name(mwin.group(1))
        if not person and names_all:
            person = names_all[0]
        results.append({"mobile": num, "name": person, "source": page_url})
    return results

# ==========================
# Crawl
# ==========================
def crawl_site(site_url: str, max_pages: int, max_seconds: int, progress_cb=None, practice_name=None):
    t0 = time.time()
    html, canon = http_get(site_url)
    if not html: return "", set(), "", site_url, "", "", [],  # 7 items
    queue, seen = deque(), set()
    queue.append(canon); seen.add(canon)
    principal_candidates, owners, founders = [], [], []
    emails, email_src = set(), {}
    mobiles_all = []
    pages_scanned = 0
    while queue and pages_scanned < max_pages and (time.time() - t0) < max_seconds:
        url = queue.popleft()
        pages_scanned += 1
        html, final_url = http_get(url)
        if not html:
            if progress_cb: progress_cb(pages_scanned, max_pages)
            continue
        soup = BeautifulSoup(html, "lxml")
        found_emails = extract_emails(soup)
        for e in found_emails:
            email_src.setdefault(e, final_url)
        emails |= found_emails
        mobiles_all.extend(extract_mobiles_with_context(soup, final_url))
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

    # dedupe mobiles by number keep first pairing
    mob_map = {}
    for m in mobiles_all:
        mob_map.setdefault(m["mobile"], m)
    mobiles_all = list(mob_map.values())

    first_email = next(iter(emails)) if emails else ""
    first_email_source = email_src.get(first_email, "") if first_email else ""

    return (
        ", ".join(principal_candidates) if principal_candidates else "",
        emails,
        first_email_source,
        site_url,
        ", ".join(owners) if owners else "",
        ", ".join(founders) if founders else "",
        mobiles_all
    )

# ==========================
# Geo helpers
# ==========================
def haversine_km(lat1, lon1, lat2, lon2):
    R = 6371.0088
    dlat = math.radians(lat2 - lat1)
    dlon = math.radians(lon2 - lon1)
    a = math.sin(dlat/2)**2 + math.cos(math.radians(lat1))*math.cos(math.radians(lat2))*math.sin(dlon/2)**2
    return 2 * R * math.asin(math.sqrt(a))

def km_to_deg(lat_deg: float, km: float):
    deg_lat = km / 110.574
    deg_lon = km / (111.320 * max(0.000001, math.cos(math.radians(lat_deg))))
    return deg_lat, deg_lon

def geocode_viewport(gmaps_client, place_text: str):
    g = None
    for attempt in range(RETRIES + 1):
        try:
            g = gmaps_client.geocode(place_text, region="au")
            break
        except Exception:
            time.sleep(0.6 * (2 ** attempt) + random.random() * JITTER)
    if not g: return None
    res = g[0]
    geom = res.get("geometry", {})
    vp = geom.get("viewport")
    if vp:
        ne = vp.get("northeast", {}); sw = vp.get("southwest", {})
        north, south = float(ne.get("lat")), float(sw.get("lat"))
        east, west   = float(ne.get("lng")), float(sw.get("lng"))
        # clamp orientation
        north, south = max(north, south), min(north, south)
        east, west   = max(east, west),   min(east, west)
        return north, south, east, west
    loc = geom.get("location")
    if not loc: return None
    lat, lng = float(loc["lat"]), float(loc["lng"])
    # small fallback box ~ 1 km half size
    dlat, dlon = km_to_deg(lat, 1.0)
    return lat + dlat, lat - dlat, lng + dlon, lng - dlon

def make_grid(north, south, east, west, radius_km, step_factor=1.5):
    lat_mid = (north + south) / 2.0
    step_km = max(0.2, radius_km / max(0.1, step_factor))
    dlat, dlon = km_to_deg(lat_mid, step_km)
    lat = south
    while lat <= north:
        lon = west
        while lon <= east:
            yield (lat, lon)
            lon += dlon
        lat += dlat

def sort_center_out(points, center_lat, center_lon):
    return sorted(points, key=lambda p: haversine_km(center_lat, center_lon, p[0], p[1]))

# ==========================
# Google Places
# ==========================
def fetch_nearby_all_pages(gmaps_client, center, radius_m, type_="dentist"):
    out = []
    page_token = None
    tries = 0
    while True:
        try:
            kwargs = {"location": center, "radius": radius_m, "type": type_}
            if page_token: kwargs["page_token"] = page_token
            resp = gmaps_client.places_nearby(**kwargs)
            for pl in resp.get("results", []):
                loc = pl.get("geometry", {}).get("location", {})
                lat, lng = loc.get("lat"), loc.get("lng")
                if lat is None or lng is None:
                    continue
                d_km = haversine_km(center[0], center[1], lat, lng)
                if d_km * 1000.0 <= radius_m + 1.0:
                    out.append(pl)
            page_token = resp.get("next_page_token")
            if not page_token:
                break
            time.sleep(NEARBY_SLEEP + random.random() * JITTER)
        except Exception:
            tries += 1
            if tries > RETRIES: break
            time.sleep(0.8 * (2 ** tries) + random.random() * JITTER)
    dedup = {}
    for pl in out:
        pid = pl.get("place_id")
        if pid and pid not in dedup:
            dedup[pid] = pl
    return list(dedup.values())

def gmaps_place_details(gmaps_client, place_id):
    for attempt in range(RETRIES + 1):
        try:
            return gmaps_client.place(place_id=place_id, fields=["name","formatted_address","website","place_id"])
        except Exception:
            time.sleep(0.6 * (2 ** attempt) + random.random() * JITTER)
    return {"result": {"place_id": place_id}}

# ==========================
# Job state
# ==========================
job = {"running": False, "progress": "Ready", "current": 0, "total": 0,
       "rows": [], "csv_bytes": b"", "error": "", "diag": ""}

job_lock = threading.Lock()
def set_job(**updates):
    with job_lock:
        job.update(updates)
def is_job_running():
    with job_lock:
        return job.get("running", False)
def reset_job():
    with job_lock:
        job.update({"running": False, "progress": "Ready", "current": 0, "total": 0,
                    "rows": [], "csv_bytes": b"", "error": "", "diag": ""})

# ==========================
# Dash app
# ==========================
app = Dash(__name__, title="Dental Finder (Dash)", suppress_callback_exceptions=True)
server = app.server

app.layout = html.Div(
    id="app-root",
    style={"fontFamily":"system-ui,-apple-system,Segoe UI,Arial","maxWidth":"1100px","margin":"0 auto","padding":"18px"},
    children=[
        html.H2("Dental Finder 🦷"),
        html.Label("Place"),
        dcc.Input(id="place_text", value="Brisbane QLD", style={"width":"60%"}),
        html.Div([
            html.Div([html.Label("Nearby radius km"),
                      dcc.Input(id="radius_km", type="number", value=2.5, step=0.5)]),
            html.Div([html.Label("Tile overlap step factor"),
                      dcc.Input(id="step_factor", type="number", value=1.5, step=0.1)]),
            html.Div([html.Label("Max tiles center out"),
                      dcc.Input(id="max_tiles", type="number", value=1, step=1)]),
            html.Div([html.Label("Max clinics to collect"),
                      dcc.Input(id="max_total_places", type="number", value=200, step=50)]),
        ], style={"marginTop":"8px","display":"grid","gridTemplateColumns":"repeat(4, minmax(180px,1fr))","gap":"10px"}),
        html.Div([
            html.Div([html.Label("Max pages per site"),
                      dcc.Input(id="max_pages_per_site", type="number", value=80, step=5)]),
            html.Div([html.Label("Max seconds per site"),
                      dcc.Input(id="max_seconds_per_site", type="number", value=90, step=5)]),
        ], style={"marginTop":"8px","display":"grid","gridTemplateColumns":"repeat(2, minmax(220px,1fr))","gap":"10px"}),
        html.Br(),
        html.Button("Start sweep", id="start", n_clicks=0, style={"padding":"8px 14px"}),
        html.Span(id="status", style={"marginLeft":"12px"}),
        html.Div(id="diag", style={"marginTop":"6px", "fontSize":"12px", "opacity":0.8}),
        html.Div(style={"height":"14px"}),
        html.Div(id="progress-bar", style={"height":"10px","background":"#eee","borderRadius":"6px","overflow":"hidden"}),
        html.Div(id="progress-info", style={"marginTop":"6px"}),
        html.Hr(),
        dash_table.DataTable(
            id="table", page_size=10,
            style_cell={"whiteSpace":"normal","height":"auto"},
            style_table={"maxHeight":"520px","overflowY":"auto"}
        ),
        html.Br(),
        html.Button("Download CSV", id="download-btn"),
        dcc.Download(id="download"),
        dcc.Store(id="kick"),
        dcc.Interval(id="poll", interval=1500, n_intervals=0),
    ]
)

# ==========================
# Worker
# ==========================
def run_job(args):
    try:
        set_job(progress="Starting worker…", running=True, error="", diag="")
        api_key = (os.getenv("GOOGLE_API_KEY") or os.getenv("GMAPS_KEY") or "").strip()
        if not api_key:
            set_job(running=False, error="No Google API key found in env", progress="Stopped")
            return

        gmaps_client = googlemaps.Client(key=api_key)
        place_text = args.get("place_text") or "Brisbane QLD"
        radius_km = float(args.get("radius_km", 2.5))
        step_factor = float(args.get("step_factor", 1.5))
        max_tiles = int(args.get("max_tiles", 1))
        max_total_places = int(args.get("max_total_places", 200))
        max_pages_per_site = int(args.get("max_pages_per_site", 80))
        max_seconds_per_site = int(args.get("max_seconds_per_site", 90))

        vp = geocode_viewport(gmaps_client, place_text)
        if not vp:
            set_job(running=False, error=f"Could not geocode {place_text}", progress="Stopped")
            return
        north, south, east, west = vp

        centers_all = list(make_grid(north, south, east, west, radius_km, step_factor))
        center_lat = (north + south)/2.0
        center_lon = (east + west)/2.0
        centers_sorted = sort_center_out(centers_all, center_lat, center_lon)

        centers = centers_sorted[:max_tiles] if len(centers_sorted) > max_tiles else centers_sorted
        if max_tiles <= 1:
            centers = [(center_lat, center_lon)]

        cover_w_km = haversine_km(center_lat, west, center_lat, east)
        cover_h_km = haversine_km(south, center_lon, north, center_lon)
        set_job(diag=f"Tiles planned {len(centers)} • Viewport about {cover_w_km:.1f} x {cover_h_km:.1f} km • Max clinics {max_total_places}")

        place_ids = {}
        for i, (lat, lon) in enumerate(centers, start=1):
            set_job(progress=f"Discovery {i}/{len(centers)} tiles…")
            nearby = fetch_nearby_all_pages(gmaps_client, (lat, lon), int(radius_km*1000), type_="dentist")
            for pl in nearby:
                pid = pl.get("place_id")
                if pid and pid not in place_ids:
                    place_ids[pid] = pl
                    if len(place_ids) >= max_total_places: break
            if len(place_ids) >= max_total_places: break

        if not place_ids:
            set_job(running=False, error="No clinics found", progress="Stopped")
            return

        ids = list(place_ids.keys())
        rows_buffer = []
        set_job(progress="Scraping details…", current=0, total=len(ids))

        def worker(pid):
            det = gmaps_place_details(gmaps_client, pid)
            r = det.get("result", {})
            practice = r.get("name") or ""
            addr = r.get("formatted_address") or ""
            site = (r.get("website") or "").strip()
            principal = owner = founder = ""
            emails, email_src, principal_src = set(), "", ""
            mobiles = []

            if site:
                principal, emails, email_src, principal_src, owner, founder, mobiles = crawl_site(
                    site,
                    max_pages=max_pages_per_site,
                    max_seconds=max_seconds_per_site,
                    progress_cb=None,
                    practice_name=practice
                )

            return {
                "Practice": practice,
                "Address": addr,
                "Website": site,
                "Principal or Owner guess": principal,
                "Owner(s)": owner,
                "Founder(s)": founder,
                "Emails found": ", ".join(sorted(emails)) if emails else "",
                "First email source": email_src,
                "Principal source": principal_src or site,
                "Mobiles found": ", ".join([m["mobile"] for m in mobiles]) if mobiles else "",
                "Mobile Name(s)": ", ".join([m["name"] for m in mobiles if m.get("name")]) if mobiles else "",
                "Mobile Source(s)": ", ".join([m["source"] for m in mobiles]) if mobiles else "",
                "Place ID": r.get("place_id") or pid
            }

        with ThreadPoolExecutor(max_workers=MAX_WORKERS) as pool:
            idx = 0
            while idx < len(ids):
                batch = ids[idx: min(idx + MAX_WORKERS, len(ids))]
                futures = {pool.submit(worker, pid): pid for pid in batch}
                for fut in futures:
                    try:
                        row = fut.result(timeout=PLACE_TIMEOUT)
                    except FuturesTimeout:
                        row = {"Practice":"","Address":"","Website":"","Principal or Owner guess":"",
                               "Owner(s)":"","Founder(s)":"","Emails found":"","First email source":"",
                               "Principal source":"", "Mobiles found":"","Mobile Name(s)":"","Mobile Source(s)":"",
                               "Place ID": futures[fut], "Error": f"Timeout after {PLACE_TIMEOUT}s"}
                    except Exception as e:
                        row = {"Practice":"","Address":"","Website":"","Principal or Owner guess":"",
                               "Owner(s)":"","Founder(s)":"","Emails found":"","First email source":"",
                               "Principal source":"", "Mobiles found":"","Mobile Name(s)":"","Mobile Source(s)":"",
                               "Place ID": futures[fut], "Error": f"{type(e).__name__}: {e}"}

                    # append all rows so you can see cases with no site
                    rows_buffer.append(row)
                    with job_lock:
                        job["current"] += 1
                idx += len(batch)
                set_job(progress=f"Scraping {job['current']}/{len(ids)}…")

        df = pd.DataFrame(rows_buffer)
        if "Place ID" in df.columns:
            df = df.drop_duplicates(subset=["Place ID"]).reset_index(drop=True)

        buf = io.BytesIO()
        df.to_csv(buf, index=False)
        buf.seek(0)
        set_job(running=False, progress=f"Done. {len(df)} clinics.",
                rows=df.to_dict("records"), csv_bytes=buf.read(), error="")
    except Exception as e:
        set_job(running=False, error=f"Crash: {type(e).__name__}: {e}", progress="Stopped")

# ==========================
# Dash callbacks
# ==========================
@app.callback(
    Output("status","children"),
    Output("diag","children"),
    Output("progress-bar","children"),
    Output("progress-info","children"),
    Output("table","data"),
    Input("poll","n_intervals"),
)
def poll_status(_):
    with job_lock:
        running = job["running"]; prog = job["progress"]; cur = job["current"]
        tot = job["total"]; rows = job["rows"]; err = job["error"]; diag = job["diag"]
    if err:
        return f"❌ {err}", diag, None, "", []
    bar = None
    if tot:
        pct = int(100 * (cur / max(1, tot)))
        bar = html.Div(style={"width":f"{pct}%","height":"100%","background":"#36c","transition":"width .25s"})
        info = f"{cur}/{tot} ({pct}%)"
    else:
        info = prog
    status = ("⏳ " if running else "✅ ") + prog
    return status, diag, bar, info, rows

@app.callback(
    Output("kick","data"),
    Input("start","n_clicks"),
    State("place_text","value"),
    State("radius_km","value"),
    State("step_factor","value"),
    State("max_tiles","value"),
    State("max_total_places","value"),
    State("max_pages_per_site","value"),
    State("max_seconds_per_site","value"),
    prevent_initial_call=True
)
def start(n, place_text, radius_km, step_factor, max_tiles, max_total_places,
          max_pages_per_site, max_seconds_per_site):
    if not n:
        return no_update
    if is_job_running():
        set_job(diag="Job already running, wait for completion.", progress=job.get("progress", "Busy"))
        return {"msg":"already_running", "ts": time.time()}
    reset_job()
    set_job(running=True, progress="Starting…", current=0, total=0, rows=[], error="", diag="launching thread")
    args = {
        "place_text": place_text or "Brisbane QLD",
        "radius_km": float(radius_km) if radius_km is not None else 2.5,
        "step_factor": float(step_factor) if step_factor is not None else 1.5,
        "max_tiles": int(max_tiles) if max_tiles is not None else 1,
        "max_total_places": int(max_total_places) if max_total_places is not None else 200,
        "max_pages_per_site": int(max_pages_per_site) if max_pages_per_site is not None else 80,
        "max_seconds_per_site": int(max_seconds_per_site) if max_seconds_per_site is not None else 90,
    }
    threading.Thread(target=run_job, args=(args,), daemon=True).start()
    return {"msg":"started", "ts": time.time()}

@app.callback(
    Output("download","data"),
    Input("download-btn","n_clicks"),
    prevent_initial_call=True
)
def do_download(n):
    with job_lock:
        data = job["csv_bytes"]
    if not data:
        return no_update
    return dcc.send_bytes(lambda b: b.write(data), "dental_clinics_with_emails_and_mobiles.csv")

if __name__ == "__main__":
    print("GOOGLE_API_KEY set?", bool(os.getenv("GOOGLE_API_KEY")))
    print("GMAPS_KEY set?", bool(os.getenv("GMAPS_KEY")))
    app.run(host="0.0.0.0", port=int(os.getenv("PORT","8050")), debug=False)
