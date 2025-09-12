# app.py
import os, re, time, math, json, random, unicodedata, threading, io, traceback, sys
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
# Tunables & constants
# ==========================
CONNECT_TIMEOUT = 5
READ_TIMEOUT = 25
TIMEOUT = (CONNECT_TIMEOUT, READ_TIMEOUT)
PLACE_TIMEOUT = 150                # hard cap per place
RETRIES = 3
CRAWL_SLEEP = 0.35                 # polite pause between page fetches
NEARBY_SLEEP = 2.1
JITTER = 0.25
MAX_HTML_BYTES = 1_800_000
MAX_WORKERS = 2                    # smaller = fewer memory spikes, fewer crashes on small instances
FLUSH_EVERY = 12                   # append to CSV every N processed clinics

BINARY_EXTS = (".pdf",".doc",".docx",".xls",".xlsx",".ppt",".pptx",".zip",".rar",
               ".png",".jpg",".jpeg",".gif",".svg",".webp",".mp4",".avi",".mov",".wmv",
               ".ics",".csv",".json",".xml",".rss",".atom")

HEADERS = {
    "User-Agent": "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 "
                  "(KHTML, like Gecko) Chrome/124.0 Safari/537.36"
}

# Only used to order visits earlier (we still crawl everything)
LIKELY_PATH_HINTS = [
    "contact","contact-us","book","appointments",
    "about","about-us","our-team","team","meet-the-team",
    "our-doctors","our-dentists","dentists","staff","people","providers"
]

EMAIL_RE = re.compile(r"[A-Z0-9._%+\-]+@[A-Z0-9.\-]+\.[A-Z]{2,}", re.I)
AT_VARIANTS = r"(?:@|\s?[\[\(]{0,1}\s*at\s*[\]\)]{0,1}\s?)"
DOT_VARIANTS = r"(?:\.|\s?dot\s?)"
OBFUSCATED_EMAIL_RE = re.compile(
    rf"([A-Z0-9._%+\-]+)\s*{AT_VARIANTS}\s*([A-Z0-9.\-]+)\s*{DOT_VARIANTS}\s*([A-Z]{{2,}})",
    re.I
)

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
def log(*args):
    print(*args, file=sys.stdout, flush=True)

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
            if "text/html" not in ctype and "xml" not in ctype:
                return None, url
            clen = r.headers.get("Content-Length")
            if clen and int(clen) > MAX_HTML_BYTES:
                return None, url
            chunks, total = [], 0
            for chunk in r.iter_content(chunk_size=16384, decode_unicode=True):
                if chunk:
                    if isinstance(chunk, bytes):
                        try: chunk = chunk.decode(errors="ignore")
                        except Exception: chunk = ""
                    chunks.append(chunk)
                    total += len(chunk)
                    if total > MAX_HTML_BYTES: break
            return "".join(chunks), r.url
        except requests.RequestException:
            pass
        time.sleep(0.4 * (2 ** i) + random.random() * JITTER)
    return None, url

# ==========================
# Email / principal extraction
# ==========================
def extract_emails(soup: BeautifulSoup):
    found = set()
    for a in soup.select("a[href^='mailto:']"):
        addr = a.get("href","").split("mailto:")[-1].split("?")[0].strip()
        if EMAIL_RE.fullmatch(addr): found.add(addr.lower())

    text = soup.get_text(" ", strip=True)
    for m in EMAIL_RE.finditer(text):
        found.add(m.group(0).lower())

    for m in OBFUSCATED_EMAIL_RE.finditer(text):
        user, domain, tld = m.groups()
        addr = f"{user}@{domain}.{tld}".lower()
        if EMAIL_RE.fullmatch(addr):
            found.add(addr)
    return found

def normalize_name(txt: str):
    txt = re.sub(r"\s+"," ", txt).strip(" -:•|")
    txt = re.sub(r"^(Dr\.?\s*)?", "Dr ", txt, flags=re.I).strip()
    return txt

def guess_principal(text: str):
    t = re.sub(r"\s+"," ", text)
    pat1 = re.compile(
        r"(Dr\.?\s+[A-Z][a-z]+(?:\s+[A-Z][a-z]+){0,2})\s*(?:,|\s|-)?\s*"
        r"(Principal\s+Dentist|Practice\s+Owner|Owner|Lead\s+Dentist|Clinical\s+Director)",
        re.I
    )
    m = pat1.search(t)
    if m: return normalize_name(m.group(1))
    pat2 = re.compile(
        r"(Principal\s+Dentist|Practice\s+Owner|Owner|Lead\s+Dentist|Clinical\s+Director)"
        r"\s*[:\-]?\s*(Dr\.?\s+[A-Z][a-z]+(?:\s+[A-Z][a-z]+){0,2})",
        re.I
    )
    m = pat2.search(t)
    if m: return normalize_name(m.group(2))
    m = re.search(r"(Dr\.?\s+[A-Z][a-z]+(?:\s+[A-Z][a-z]+){0,2})", t)
    if m: return normalize_name(m.group(1))
    return ""

# ==========================
# Crawl helpers (visit ordering only)
# ==========================
def prioritise(urls):
    def score(u):
        path = urlparse(u).path.lower().strip("/")
        return 0 if any(tok in path for tok in LIKELY_PATH_HINTS) else 1
    return sorted(set(urls), key=score)

def sitemap_urls_from_robots(base_url):
    try:
        robots_url = urljoin(base_url, "/robots.txt")
        txt, _ = http_get(robots_url)
        if not txt: return []
        urls = []
        for line in txt.splitlines():
            if line.lower().startswith("sitemap:"):
                sm = line.split(":",1)[1].strip()
                if sm: urls.append(sm)
        return urls
    except Exception:
        return []

def parse_sitemap(url):
    try:
        xml, _ = http_get(url)
        if not xml: return []
        soup = BeautifulSoup(xml, "xml")
        locs = [loc.get_text(strip=True) for loc in soup.find_all("loc")]
        return [l for l in locs if l]
    except Exception:
        return []

def sitemap_seed(base_url):
    seeds = []
    try:
        for sm in sitemap_urls_from_robots(base_url):
            seeds.extend(parse_sitemap(sm))
        seeds.extend(parse_sitemap(urljoin(base_url, "/sitemap.xml")))
    except Exception:
        pass
    seeds = [u for u in seeds if same_site(base_url, u)]
    return prioritise(seeds)[:2000]

# ==========================
# Full-site crawler (bounded)
# ==========================
def crawl_site(site_url: str, max_pages: int, max_seconds: int, progress_cb=None):
    t0 = time.time()
    html, canon = http_get(site_url)
    if not html: return "", set(), "", site_url

    queue, seen = deque(), set()
    queue.append(canon); seen.add(canon)

    for su in sitemap_seed(canon):
        if su not in seen:
            seen.add(su); queue.append(su)

    principal, principal_src = "", canon
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

        if not principal:
            g = guess_principal(soup.get_text(" ", strip=True))
            if g:
                principal, principal_src = g, final_url

        internal = []
        for a in soup.find_all("a", href=True):
            u = normalize_abs(final_url, a["href"])
            if u and same_site(canon, u) and u not in seen:
                internal.append(u)

        for u in prioritise(internal):
            seen.add(u); queue.append(u)

        if progress_cb: progress_cb(pages_scanned, max_pages)
        time.sleep(CRAWL_SLEEP + random.random() * JITTER)

    first_email = next(iter(emails)) if emails else ""
    first_email_source = email_src.get(first_email, "")
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
    if not g: return None
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
# Persistence (checkpoint & CSV)
# ==========================
def load_checkpoint(path):
    try:
        if os.path.exists(path):
            with open(path, "r") as f:
                return json.load(f)
    except Exception:
        pass
    return {"done_ids": []}

def save_checkpoint(path, done_ids):
    tmp = path + ".tmp"
    with open(tmp, "w") as f:
        json.dump({"done_ids": list(done_ids)}, f)
    os.replace(tmp, path)

def append_rows_csv(path, rows):
    if not rows: return
    header = not os.path.exists(path)
    df = pd.DataFrame(rows)
    df.to_csv(path, mode="a", header=header, index=False)

def load_csv_if_any(path):
    if os.path.exists(path):
        try:
            return pd.read_csv(path)
        except Exception:
            return pd.DataFrame()
    return pd.DataFrame()

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
# Dash app & layout (Region Sweep only, no API field)
# ==========================
app = Dash(__name__, title="Dental Finder (Dash)", suppress_callback_exceptions=True)
server = app.server

app.layout = html.Div(
    id="app-root",
    style={"fontFamily":"system-ui,-apple-system,Segoe UI,Arial","maxWidth":"1100px","margin":"0 auto","padding":"18px"},
    children=[
        html.H2("Dental Finder 🦷"),

        html.Label("Place (AU city / suburb / state / postcode)"),
        dcc.Input(id="place_text", value="Brisbane QLD", style={"width":"60%"}),

        html.Div([
            html.Div([
                html.Label("Nearby radius (km)"),
                dcc.Input(id="radius_km", type="number", value=2.5, step=0.5),
            ]),
            html.Div([
                html.Label("Tile overlap (step factor)"),
                dcc.Input(id="step_factor", type="number", value=1.5, step=0.1),
            ]),
            html.Div([
                html.Label("Max tiles (center-out)"),
                dcc.Input(id="max_tiles", type="number", value=200, step=10),
            ]),
            html.Div([
                html.Label("Max clinics to collect"),
                dcc.Input(id="max_total_places", type="number", value=3000, step=100),
            ]),
        ], style={"marginTop":"8px","display":"grid","gridTemplateColumns":"repeat(4, minmax(180px,1fr))","gap":"10px"}),

        html.Div([
            html.Div([
                html.Label("Max pages per site (crawl deeper = higher)"),
                dcc.Input(id="max_pages_per_site", type="number", value=80, step=5),
            ]),
            html.Div([
                html.Label("Max seconds per site"),
                dcc.Input(id="max_seconds_per_site", type="number", value=90, step=5),
            ]),
        ], style={"marginTop":"8px","display":"grid","gridTemplateColumns":"repeat(2, minmax(220px,1fr))","gap":"10px"}),

        html.Br(),
        html.Button("Start sweep", id="start", n_clicks=0, style={"padding":"8px 14px"}),
        html.Span(id="status", style={"marginLeft":"12px"}),

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

# --------------------------
# Job runner (with crash guard + checkpoint/resume)
# --------------------------
def run_job(args):
    set_job(running=True, progress="Starting…", current=0, total=0, rows=[], csv_bytes=b"", error="")
    try:
        # 1) API key (env only; field hidden)
        api_key = (os.getenv("GOOGLE_API_KEY") or os.getenv("GMAPS_KEY") or "").strip()
        if not api_key:
            set_job(running=False, error="No API key provided in env (set GOOGLE_API_KEY or GMAPS_KEY).")
            return
        gmaps_client = googlemaps.Client(key=api_key)

        # 2) Discovery bounds
        place_text = args["place_text"]
        vp = geocode_viewport(gmaps_client, place_text)
        if not vp:
            set_job(running=False, error="Could not geocode that place.")
            return
        north, south, east, west = vp

        radius_km, step_factor = args["radius_km"], args["step_factor"]
        max_tiles, max_total_places = args["max_tiles"], args["max_total_places"]

        centers_all = list(make_grid(north, south, east, west, radius_km, step_factor))
        center_lat = (north + south)/2.0; center_lon = (east + west)/2.0
        centers_sorted = sort_center_out(centers_all, center_lat, center_lon)
        centers = centers_sorted[:max_tiles] if len(centers_sorted) > max_tiles else centers_sorted

        # 3) Names for persistence
        slug = slugify(place_text or "region")
        out_csv = f"{slug}_dental_clinics_with_emails.csv"
        ckpt = f"ckpt_{slug}.json"

        # Load checkpoint (done_ids) and already-saved CSV
        ck = load_checkpoint(ckpt)
        done_ids = set(ck.get("done_ids", []))
        existing_df = load_csv_if_any(out_csv)
        if not existing_df.empty and "Place ID" in existing_df.columns:
            done_ids |= set(existing_df["Place ID"].astype(str).tolist())

        # 4) Collect places
        place_ids = {}
        for i, (lat, lon) in enumerate(centers, start=1):
            set_job(progress=f"Discovery {i}/{len(centers)} tiles…")
            nearby = fetch_nearby_all_pages(gmaps_client, (lat, lon), int(radius_km*1000), type_="dentist")
            for pl in nearby:
                pid = str(pl.get("place_id"))
                if pid and pid not in place_ids:
                    place_ids[pid] = pl
                    if len(place_ids) >= max_total_places:
                        break
            if len(place_ids) >= max_total_places:
                break

        if not place_ids:
            set_job(running=False, error="No clinics found.")
            return

        ids = list(place_ids.keys())
        # Skip ones already done (from ckpt or CSV)
        ids = [pid for pid in ids if pid not in done_ids]

        total = len(ids)
        set_job(progress="Scraping details…", current=0, total=total)

        rows_buffer = []

        def worker(pid):
            det = gmaps_place_details(gmaps_client, pid)
            r = det.get("result", {})
            practice = r.get("name"); addr = r.get("formatted_address")
            site = (r.get("website") or "").strip()

            principal, emails, email_src, principal_src = ("", set(), "", "")
            if site:
                principal, emails, email_src, principal_src = crawl_site(
                    site, max_pages=args["max_pages_per_site"], max_seconds=args["max_seconds_per_site"], progress_cb=None
                )

            row = {
                "Practice": practice or "", "Address": addr or "", "Website": site,
                "Principal / Owner (guess)": principal,
                "Emails found": ", ".join(sorted(emails)) if emails else "",
                "First email source": email_src, "Principal source": principal_src or site,
                "Place ID": pid
            }
            # if literally nothing, return minimal (we'll still mark done to avoid rework)
            return row

        with ThreadPoolExecutor(max_workers=MAX_WORKERS) as pool:
            idx = 0
            while idx < len(ids):
                batch = ids[idx: min(idx + MAX_WORKERS, len(ids))]
                fut_map = {pool.submit(worker, pid): pid for pid in batch}
                for fut in list(fut_map.keys()):
                    pid = fut_map[fut]
                    try:
                        row = fut.result(timeout=PLACE_TIMEOUT)
                    except FuturesTimeout:
                        row = {"Practice":"","Address":"","Website":"","Principal / Owner (guess)":"",
                               "Emails found":"","First email source":"","Principal source":"",
                               "Place ID": pid, "Error": f"Timeout after {PLACE_TIMEOUT}s"}
                    except Exception as e:
                        row = {"Practice":"","Address":"","Website":"","Principal / Owner (guess)":"",
                               "Emails found":"","First email source":"","Principal source":"",
                               "Place ID": pid, "Error": str(e)}

                    rows_buffer.append(row)
                    done_ids.add(pid)

                    with job_lock:
                        job["current"] += 1

                    # Periodic flush to disk & checkpoint
                    if (job["current"] % FLUSH_EVERY) == 0:
                        try:
                            append_rows_csv(out_csv, rows_buffer)
                            rows_buffer = []
                            save_checkpoint(ckpt, done_ids)
                        except Exception as e:
                            log("Flush error:", e)

                idx += len(batch)
                set_job(progress=f"Scraping {job['current']}/{total}…")

        # Final flush
        append_rows_csv(out_csv, rows_buffer)
        save_checkpoint(ckpt, done_ids)

        # Load final CSV for UI
        df = load_csv_if_any(out_csv)
        if "Place ID" in df.columns:
            df = df.drop_duplicates(subset=["Place ID"]).reset_index(drop=True)

        buf = io.BytesIO()
        df.to_csv(buf, index=False); buf.seek(0)

        set_job(running=False, progress=f"Done. {len(df)} clinics.",
                rows=df.to_dict("records"), csv_bytes=buf.read(), error="", total=total)

    except Exception as e:
        log("RUN_JOB CRASH:\n", traceback.format_exc())
        set_job(running=False, error=f"Crash: {e}", progress="Crashed")

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
        bar = html.Div(style={"width":f"{pct}%","height":"100%","background":"#36c","transition":"width .25s"})
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
    if job["running"]:
        return {"msg":"already running"}

    args = {
        "place_text": place_text or "Brisbane QLD",
        "radius_km": float(radius_km) if radius_km is not None else 2.5,
        "step_factor": float(step_factor) if step_factor is not None else 1.5,
        "max_tiles": int(max_tiles) if max_tiles is not None else 200,
        "max_total_places": int(max_total_places) if max_total_places is not None else 3000,
        "max_pages_per_site": int(max_pages_per_site) if max_pages_per_site is not None else 80,
        "max_seconds_per_site": int(max_seconds_per_site) if max_seconds_per_site is not None else 90,
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
    # For local runs; Render will use gunicorn
    app.run(host="0.0.0.0", port=int(os.getenv("PORT","8050")), debug=False)
