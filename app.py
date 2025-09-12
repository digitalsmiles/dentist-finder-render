# app.py
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
FAST_MODE_DEFAULT = True
CONNECT_TIMEOUT = 5
READ_TIMEOUT = 20
TIMEOUT = (CONNECT_TIMEOUT, READ_TIMEOUT)
PLACE_TIMEOUT = 90
RETRIES = 3
CRAWL_SLEEP = 0.5
NEARBY_SLEEP = 2.1
JITTER = 0.25
MAX_HTML_BYTES = 1_800_000
MAX_WORKERS = 4

BINARY_EXTS = (".pdf",".doc",".docx",".xls",".xlsx",".ppt",".pptx",".zip",".rar",
               ".png",".jpg",".jpeg",".gif",".svg",".webp",".mp4",".avi",".mov",".wmv")

HEADERS = {
    "User-Agent": "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0 Safari/537.36"
}

DEFAULT_LIKELY = ["contact","contact-us","book","appointments",
                  "about","about-us","our-team","team","meet-the-team",
                  "our-doctors","our-dentists","dentists","staff","people"]

EMAIL_RE = re.compile(r"[A-Z0-9._%+\-]+@[A-Z0-9.\-]+\.[A-Z]{2,}", re.I)

# ==========================
# HTTP session with retry
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
    s.mount("http://", adapter); s.mount("https://", adapter)
    s.headers.update(HEADERS)
    return s

SESSION = make_session()

# ==========================
# Utils
# ==========================
def slugify(s: str):
    s = unicodedata.normalize("NFKD", s).encode("ascii","ignore").decode("ascii")
    s = re.sub(r"[^A-Za-z0-9]+","_", s).strip("_")
    return s.lower() or "output"

def http_get(url: str):
    for i in range(RETRIES + 1):
        try:
            r = SESSION.get(url, timeout=TIMEOUT, allow_redirects=True, stream=True)
            if not r.ok:
                raise requests.RequestException(f"HTTP {r.status_code}")
            ctype = (r.headers.get("Content-Type","") or "").lower()
            if "text/html" not in ctype:
                return None, url
            clen = r.headers.get("Content-Length")
            if clen and int(clen) > MAX_HTML_BYTES:
                return None, url
            chunks, total = [], 0
            for chunk in r.iter_content(chunk_size=16384, decode_unicode=True):
                if chunk:
                    if isinstance(chunk, bytes):
                        chunk = chunk.decode(errors="ignore")
                    chunks.append(chunk)
                    total += len(chunk)
                    if total > MAX_HTML_BYTES:
                        break
            return "".join(chunks), r.url
        except requests.RequestException:
            pass
        time.sleep(0.4 * (2 ** i) + random.random() * JITTER)
    return None, url

def clean_url(base, href):
    if not href: return None
    href = href.strip()
    if href.startswith(("#","mailto:","tel:")): return None
    absu = urljoin(base, href)
    u = urlparse(absu)
    if any(u.path.lower().endswith(ext) for ext in BINARY_EXTS): return None
    return u._replace(fragment="").geturl()

def same_site(a, b):
    ua, ub = urlparse(a), urlparse(b)
    return (ua.scheme, ua.netloc) == (ub.scheme, ub.netloc)

def extract_emails(soup: BeautifulSoup):
    found = set()
    for a in soup.select("a[href^='mailto:']"):
        addr = a.get("href","").split("mailto:")[-1].split("?")[0].strip()
        if EMAIL_RE.fullmatch(addr): found.add(addr)
    text = soup.get_text(" ", strip=True)
    for m in EMAIL_RE.finditer(text): found.add(m.group(0))
    return found

def normalize_name(txt: str):
    txt = re.sub(r"\s+"," ", txt).strip(" -:•|")
    txt = re.sub(r"^(Dr\.?\s*)?", "Dr ", txt, flags=re.I).strip()
    return txt

def guess_principal(text: str):
    t = re.sub(r"\s+"," ", text)
    pat1 = re.compile(r"(Dr\.?\s+[A-Z][a-z]+(?:\s+[A-Z][a-z]+){0,2})\s*(?:,|\s|-)?\s*(Principal\s+Dentist|Practice\s+Owner|Owner|Lead\s+Dentist|Clinical\s+Director)", re.I)
    m = pat1.search(t)
    if m: return normalize_name(m.group(1))
    pat2 = re.compile(r"(Principal\s+Dentist|Practice\s+Owner|Owner|Lead\s+Dentist|Clinical\s+Director)\s*[:\-]?\s*(Dr\.?\s+[A-Z][a-z]+(?:\s+[A-Z][a-z]+){0,2})", re.I)
    m = pat2.search(t)
    if m: return normalize_name(m.group(2))
    m = re.search(r"(Dr\.?\s+[A-Z][a-z]+(?:\s+[A-Z][a-z]+){0,2})", t)
    if m: return normalize_name(m.group(1))
    return ""

def path_matches(u: str, tokens: list[str]):
    path = urlparse(u).path.lower().strip("/")
    return any(tok.lower() in path for tok in tokens)

def prioritise(urls, tokens):
    def score(u): return 0 if path_matches(u, tokens) else 1
    return sorted(set(urls), key=score)

# ==========================
# Site crawler (bounded)
# ==========================
def crawl_site(site_url: str, max_pages: int, max_seconds: int, progress_cb=None,
               fast_mode=True, only_paths=False, tokens=None):
    tokens = tokens or DEFAULT_LIKELY
    t0 = time.time()
    html, canon = http_get(site_url)
    if not html: return "", set(), "", site_url

    queue, seen = deque(), set()
    queue.append(canon); seen.add(canon)

    soup0 = BeautifulSoup(html, "lxml")
    internal = []
    for a in soup0.find_all("a", href=True):
        u = clean_url(canon, a["href"])
        if u and same_site(canon, u):
            if (not only_paths) or path_matches(u, tokens):
                internal.append(u)
    for u in prioritise(internal, tokens):
        if u not in seen:
            seen.add(u); queue.append(u)

    principal, principal_src = "", canon
    emails, email_src = set(), {}
    pages_scanned = 0

    while queue and pages_scanned < max_pages and (time.time() - t0) < max_seconds:
        url = queue.pop(); pages_scanned += 1

        if only_paths and url != canon and not path_matches(url, tokens):
            if progress_cb: progress_cb(pages_scanned, max_pages)
            continue

        html, final_url = http_get(url)
        if not html:
            if progress_cb: progress_cb(pages_scanned, max_pages)
            continue

        soup = BeautifulSoup(html, "lxml")

        found = extract_emails(soup)
        for e in found: email_src.setdefault(e, final_url)
        emails |= found

        if not principal:
            g = guess_principal(soup.get_text(" ", strip=True))
            if g: principal, principal_src = g, final_url

        if fast_mode and (emails or principal) and (only_paths or path_matches(final_url, tokens)):
            if progress_cb: progress_cb(pages_scanned, max_pages)
            break

        for a in soup.find_all("a", href=True):
            u = clean_url(final_url, a["href"])
            if u and same_site(canon, u) and u not in seen:
                if (not only_paths) or path_matches(u, tokens):
                    seen.add(u); queue.append(u)

        if progress_cb: progress_cb(pages_scanned, max_pages)
        time.sleep(CRAWL_SLEEP + random.random() * JITTER)

    first_email_source = next(iter(emails)) if emails else ""
    first_email_source = first_email_source and email_src.get(first_email_source, "")
    return principal, emails, first_email_source, principal_src

# ==========================
# Google helpers
# ==========================
def fetch_nearby_all_pages(gmaps_client, center, radius_m, type_="dentist"):
    out = []
    for attempt in range(RETRIES + 1):
        try:
            resp = gmaps_client.places_nearby(location=center, radius=radius_m, type=type_)
            out.extend(resp.get("results", []))
            while "next_page_token" in resp:
                time.sleep(NEARBY_SLEEP + random.random() * JITTER)
                resp = gmaps_client.places_nearby(location=center, radius=radius_m, type=type_, page_token=resp["next_page_token"])
                out.extend(resp.get("results", []))
            return out
        except Exception:
            time.sleep(0.6 * (2 ** attempt) + random.random() * JITTER)
    return out

def gmaps_place_details(gmaps_client, place_id):
    for attempt in range(RETRIES + 1):
        try:
            return gmaps_client.place(place_id=place_id, fields=["name","formatted_address","website"])
        except Exception:
            time.sleep(0.6 * (2 ** attempt) + random.random() * JITTER)
    return {"result": {}}

def km_to_deg(lat_deg: float, km: float):
    deg_lat = km / 111.0
    deg_lon = km / (111.320 * math.cos(math.radians(lat_deg)) or 1e-6)
    return deg_lat, deg_lon

def make_grid(north, south, east, west, radius_km, step_factor=1.6):
    mid_lat = (north + south) / 2.0
    step_km = radius_km * step_factor
    dlat, dlon = km_to_deg(mid_lat, step_km)
    lat = south + dlat/2.0
    while lat < north:
        lon = west + dlon/2.0
        while lon < east:
            yield (lat, lon)
            lon += dlon
        lat += dlat

def sort_center_out(points, center_lat, center_lon):
    def key(pt):
        lat, lon = pt
        dx = (lon - center_lon) * math.cos(math.radians(center_lat))
        dy = (lat - center_lat)
        return dx*dx + dy*dy
    return sorted(points, key=key)

def geocode_viewport(gmaps_client, place_text: str):
    g = None
    for attempt in range(RETRIES + 1):
        try:
            g = gmaps_client.geocode(place_text, region="au")
            break
        except Exception:
            time.sleep(0.6 * (2 ** attempt) + random.random() * JITTER)
    if not g:
        return None
    res = g[0]
    geom = res.get("geometry", {})
    vp = geom.get("viewport")
    if vp:
        ne = vp.get("northeast", {}); sw = vp.get("southwest", {})
        north, south = float(ne.get("lat")), float(sw.get("lat"))
        east, west   = float(ne.get("lng")), float(sw.get("lng"))
        north, south = max(north, south), min(north, south)
        east, west   = max(east, west),   min(east, west)
        return north, south, east, west
    loc = geom.get("location")
    if not loc: return None
    lat, lng = float(loc["lat"]), float(loc["lng"])
    dlat, dlon = km_to_deg(lat, 50.0)
    return lat + dlat, lat - dlat, lng + dlon, lng - dlon

# ==========================
# Background job state
# ==========================
job = {"running": False, "progress": "Idle", "current": 0, "total": 0,
       "rows": [], "csv_bytes": b"", "error": ""}
job_lock = threading.Lock()

def set_job(**updates):
    with job_lock:
        job.update(updates)

# ==========================
# Dash app & layout  (ONLY LABELS ADDED)
# ==========================
app = Dash(__name__, title="Dental Finder (Dash)", suppress_callback_exceptions=True)
server = app.server

app.layout = html.Div(
    style={"fontFamily":"system-ui,-apple-system,Segoe UI,Arial","maxWidth":"1100px","margin":"0 auto","padding":"18px"},
    children=[
        html.H2("Dental Finder 🦷 — Dash (Region Sweep only)"),

        # API key
        html.Label("Google API key (optional if set as env var)"),
        dcc.Input(id="api_key", placeholder="•••••••", type="password", style={"width":"420px"}),
        html.Br(), html.Br(),

        # Place
        html.Label("Place (AU city / suburb / state / postcode)"),
        dcc.Input(id="place_text", value="Brisbane QLD", style={"width":"60%"}),

        # Sweep geometry & caps
        html.Div([
            html.Div([
                html.Label("Nearby radius (km)"),
                dcc.Input(id="radius_km", type="number", value=2.5, step=0.5, placeholder="Radius km"),
            ]),
            html.Div([
                html.Label("Tile overlap (step factor)"),
                dcc.Input(id="step_factor", type="number", value=1.5, step=0.1, placeholder="Step factor", style={"marginLeft":"8px"}),
            ]),
            html.Div([
                html.Label("Max tiles (center-out)"),
                dcc.Input(id="max_tiles", type="number", value=200, step=10, placeholder="Max tiles", style={"marginLeft":"8px"}),
            ]),
            html.Div([
                html.Label("Max clinics to collect"),
                dcc.Input(id="max_total_places", type="number", value=3000, step=100, placeholder="Max clinics", style={"marginLeft":"8px"}),
            ]),
        ], style={"marginTop":"8px","display":"grid","gridTemplateColumns":"repeat(4, minmax(180px,1fr))","gap":"10px"}),

        # Crawler limits & options
        html.Div([
            html.Div([
                html.Label("Max pages per site"),
                dcc.Input(id="max_pages_per_site", type="number", value=20, step=1, placeholder="Max pages/site"),
            ]),
            html.Div([
                html.Label("Max seconds per site"),
                dcc.Input(id="max_seconds_per_site", type="number", value=30, step=5, placeholder="Max seconds/site", style={"marginLeft":"8px"}),
            ]),
            html.Div([
                html.Label("Fast mode"),
                dcc.Checklist(id="fast_mode", options=[{"label":" Stop after first lead on likely pages","value":"on"}], value=["on"]),
            ], style={"paddingTop":"6px"}),
            html.Div([
                html.Label("Only crawl likely paths"),
                dcc.Checklist(id="only_paths", options=[{"label":" contact, about, team, staff…","value":"on"}], value=[]),
            ], style={"paddingTop":"6px"}),
        ], style={"marginTop":"8px","display":"grid","gridTemplateColumns":"repeat(4, minmax(220px,1fr))","gap":"10px"}),

        html.Label("Paths list (comma-separated)"),
        dcc.Input(id="paths_txt", value="contact,about,team,staff", style={"width":"60%","marginTop":"4px"}),

        html.Br(),
        html.Button("Start sweep", id="start", n_clicks=0, style={"padding":"8px 14px"}),
        html.Span(id="status", style={"marginLeft":"12px"}),

        html.Div(style={"height":"14px"}),
        html.Div(id="progress-bar", style={"height":"10px","background":"#eee","borderRadius":"6px","overflow":"hidden"}),
        html.Div(id="progress-info", style={"marginTop":"6px"}),

        html.Hr(),
        dash_table.DataTable(id="table", page_size=10,
            style_cell={"whiteSpace":"normal","height":"auto"},
            style_table={"maxHeight":"520px","overflowY":"auto"}),

        html.Br(),
        html.Button("Download CSV", id="download-btn"),
        dcc.Download(id="download"),

        dcc.Store(id="kick"),
        dcc.Interval(id="poll", interval=1500, n_intervals=0),
    ]
)

# --------------------------
# Job runner (region only)
# --------------------------
def run_job(args):
    set_job(running=True, progress="Starting…", current=0, total=0, rows=[], csv_bytes=b"", error="")

    api_key = (args["api_key"] or os.getenv("GOOGLE_API_KEY") or os.getenv("GMAPS_KEY") or "").strip()
    if not api_key:
        set_job(running=False, error="No API key provided."); return

    gmaps_client = googlemaps.Client(key=api_key)

    vp = geocode_viewport(gmaps_client, args["place_text"])
    if not vp:
        set_job(running=False, error="Could not geocode that place."); return
    north, south, east, west = vp

    radius_km, step_factor = args["radius_km"], args["step_factor"]
    max_tiles, max_total_places = args["max_tiles"], args["max_total_places"]

    centers_all = list(make_grid(north, south, east, west, radius_km, step_factor))
    center_lat = (north + south)/2.0; center_lon = (east + west)/2.0
    centers_sorted = sort_center_out(centers_all, center_lat, center_lon)
    centers = centers_sorted[:max_tiles] if len(centers_sorted) > max_tiles else centers_sorted

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
        set_job(running=False, error="No clinics found."); return

    ids = list(place_ids.keys())
    tokens = [t.strip().strip("/") for t in (args["paths_txt"] or "").split(",") if t.strip()] or DEFAULT_LIKELY
    only_paths = args["only_paths"]
    fast_mode = args["fast_mode"]
    max_pages_per_site = args["max_pages_per_site"]
    max_seconds_per_site = args["max_seconds_per_site"]

    rows_buffer = []
    set_job(progress="Scraping details…", current=0, total=len(ids))

    def worker(pid):
        det = gmaps_place_details(gmaps_client, pid)
        r = det.get("result", {})
        practice = r.get("name"); addr = r.get("formatted_address")
        site = (r.get("website") or "").strip()

        principal, emails, email_src, principal_src = ("", set(), "", "")
        if site:
            principal, emails, email_src, principal_src = crawl_site(
                site, max_pages=max_pages_per_site, max_seconds=max_seconds_per_site,
                progress_cb=None, fast_mode=fast_mode, only_paths=only_paths, tokens=tokens
            )
        return {
            "Practice": practice or "", "Address": addr or "", "Website": site,
            "Principal / Owner (guess)": principal,
            "Emails found": ", ".join(sorted(emails)) if emails else "",
            "First email source": email_src, "Principal source": principal_src or site,
            "Place ID": pid
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
                    row = {"Practice":"","Address":"","Website":"","Principal / Owner (guess)":"",
                           "Emails found":"","First email source":"","Principal source":"",
                           "Place ID": futures[fut], "Error": f"Timeout after {PLACE_TIMEOUT}s"}
                except Exception as e:
                    row = {"Practice":"","Address":"","Website":"","Principal / Owner (guess)":"",
                           "Emails found":"","First email source":"","Principal source":"",
                           "Place ID": futures[fut], "Error": str(e)}
                rows_buffer.append(row)
                with job_lock:
                    job["current"] += 1
            idx += len(batch)
            set_job(progress=f"Scraping {job['current']}/{len(ids)}…")

    df = pd.DataFrame(rows_buffer)
    if "Place ID" in df.columns:
        df = df.drop_duplicates(subset=["Place ID"]).reset_index(drop=True)

    buf = io.BytesIO()
    df.to_csv(buf, index=False); buf.seek(0)

    set_job(running=False, progress=f"Done. {len(df)} clinics.", rows=df.to_dict("records"),
            csv_bytes=buf.read(), error="", total=len(ids))

# --------------------------
# Poll UI for progress
# --------------------------
@app.callback(
    Output("status","children"),
    Output("progress-bar","children"),
    Output("progress-info","children"),
    Output("table","data"),
    Input("poll","n_intervals"),
)
def poll_status(_):
    with job_lock:
        running = job["running"]; prog = job["progress"]; cur = job["current"]
        tot = job["total"]; rows = job["rows"]; err = job["error"]
    if err:
        return f"❌ {err}", None, "", []

    bar = None
    if tot:
        pct = int(100 * (cur / max(1, tot)))
        bar = html.Div(style={"width":f"{pct}%","height":"100%","background":"#36c","transition":"width .4s"})
        info = f"{cur}/{tot} ({pct}%)"
    else:
        info = prog
    status = ("⏳ " if running else "✅ ") + prog
    return status, bar, info, rows

# --------------------------
# Start job
# --------------------------
@app.callback(
    Output("kick","data"),
    Input("start","n_clicks"),
    State("api_key","value"),
    State("place_text","value"),
    State("radius_km","value"),
    State("step_factor","value"),
    State("max_tiles","value"),
    State("max_total_places","value"),
    State("max_pages_per_site","value"),
    State("max_seconds_per_site","value"),
    State("fast_mode","value"),
    State("only_paths","value"),
    State("paths_txt","value"),
    prevent_initial_call=True
)
def start(n, api_key, place_text, radius_km, step_factor, max_tiles, max_total_places,
          max_pages_per_site, max_seconds_per_site, fast_mode, only_paths, paths_txt):
    if not n:
        return no_update
    if job["running"]:
        return {"msg":"already running"}

    args = {
        "api_key": (api_key or "").strip(),
        "place_text": place_text or "Brisbane QLD",
        "radius_km": float(radius_km) if radius_km is not None else 2.5,
        "step_factor": float(step_factor) if step_factor is not None else 1.5,
        "max_tiles": int(max_tiles) if max_tiles is not None else 200,
        "max_total_places": int(max_total_places) if max_total_places is not None else 3000,
        "max_pages_per_site": int(max_pages_per_site) if max_pages_per_site is not None else 20,
        "max_seconds_per_site": int(max_seconds_per_site) if max_seconds_per_site is not None else 30,
        "fast_mode": ("on" in (fast_mode or [])),
        "only_paths": ("on" in (only_paths or [])),
        "paths_txt": paths_txt or "contact,about,team,staff",
    }
    threading.Thread(target=run_job, args=(args,), daemon=True).start()
    return {"msg":"started", "ts": time.time()}

# --------------------------
# Download CSV
# --------------------------
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
    return dcc.send_bytes(lambda b: b.write(data), "dental_clinics_with_emails.csv")

# --------------------------
# Entry
# --------------------------
if __name__ == "__main__":
    app.run(host="0.0.0.0", port=int(os.getenv("PORT","8050")), debug=False)
