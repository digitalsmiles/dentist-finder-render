import time, re, requests, math, os, json, unicodedata, random, socket
from urllib.parse import urljoin, urlparse
from collections import deque
from concurrent.futures import ThreadPoolExecutor, TimeoutError as FuturesTimeout
import streamlit as st
import googlemaps
import pandas as pd
from bs4 import BeautifulSoup
from requests.adapters import HTTPAdapter
from urllib3.util.retry import Retry

# ==========================
# UI Title
# ==========================
st.title("Dental Finder 🦷 — region sweep + email/principal scraper (center-out & crash-safe, anti-timeout)")

# ==========================
# Tunables (robust defaults)
# ==========================
FAST_MODE_DEFAULT = True

# Network timeouts
CONNECT_TIMEOUT = 5
READ_TIMEOUT = 20
TIMEOUT = (CONNECT_TIMEOUT, READ_TIMEOUT)

# Per-place hard cap
PLACE_TIMEOUT = 90

# Retries / pacing
RETRIES = 3
CRAWL_SLEEP = 0.5
NEARBY_SLEEP = 2.1
JITTER = 0.25
MAX_HTML_BYTES = 1_800_000

# Concurrency (per-place only)
MAX_WORKERS = 4

BINARY_EXTS = (".pdf",".doc",".docx",".xls",".xlsx",".ppt",".pptx",".zip",".rar",
               ".png",".jpg",".jpeg",".gif",".svg",".webp",".mp4",".avi",".mov",".wmv")

HEADERS = {
    "User-Agent": "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 "
                  "(KHTML, like Gecko) Chrome/124.0 Safari/537.36"
}

DEFAULT_LIKELY = ["contact","contact-us","book","appointments",
                  "about","about-us","our-team","team","meet-the-team",
                  "our-doctors","our-dentists","dentists","staff","people"]

EMAIL_RE = re.compile(r"[A-Z0-9._%+\-]+@[A-Z0-9.\-]+\.[A-Z]{2,}", re.I)

# Crash-safe output
FLUSH_EVERY = 20  # write to disk every N clinics

# ==========================
# Utils
# ==========================
def slugify(s: str):
    s = unicodedata.normalize("NFKD", s).encode("ascii", "ignore").decode("ascii")
    s = re.sub(r"[^A-Za-z0-9]+", "_", s).strip("_")
    return s.lower() or "output"

def checkpoint(idx, new_rows, out_csv, ckpt_json):
    if new_rows:
        header = not os.path.exists(out_csv)
        pd.DataFrame(new_rows).to_csv(out_csv, mode="a", header=header, index=False)
    tmp = ckpt_json + ".tmp"
    with open(tmp, "w") as f:
        json.dump({"idx": idx}, f)
    os.replace(tmp, ckpt_json)

def load_resume_index(ckpt_json):
    if os.path.exists(ckpt_json):
        try:
            data = json.load(open(ckpt_json, "r"))
            return int(data.get("idx", 0))
        except Exception:
            return 0
    return 0

# ==========================
# Robust HTTP session (retries/backoff)
# ==========================
def make_session():
    s = requests.Session()
    retry = Retry(
        total=RETRIES,
        connect=RETRIES,
        read=RETRIES,
        status=RETRIES,
        backoff_factor=0.6,
        status_forcelist=[408, 409, 425, 429, 500, 502, 503, 504],
        allowed_methods=frozenset(["GET", "HEAD", "OPTIONS"])
    )
    adapter = HTTPAdapter(max_retries=retry, pool_connections=32, pool_maxsize=64)
    s.mount("http://", adapter)
    s.mount("https://", adapter)
    s.headers.update(HEADERS)
    return s

SESSION = make_session()

# ==========================
# UI Controls
# ==========================
# 🔑 Read key from Render env vars first; fall back to st.secrets; finally to a text box.
api_key = (
    os.getenv("GMAPS_KEY", "")
    or os.getenv("GOOGLE_API_KEY", "")
    or st.secrets.get("GMAPS_KEY", "")
    or st.secrets.get("GOOGLE_API_KEY", "")
).strip()
if not api_key:
    api_key = st.text_input("Google Maps API key", type="password").strip()

mode = st.selectbox("Discovery mode", [
    "Text Search (max 60)",
    "Citywide Sweep (manual bounds)",
    "Region Sweep by place name"
])

if mode == "Text Search (max 60)":
    query = st.text_input("Search for dental practices", value="dentist Brisbane")
elif mode == "Citywide Sweep (manual bounds)":
    st.markdown("**Manual bounds (enter any region you like):**")
    colb = st.columns(4)
    with colb[0]: north = st.number_input("North lat", value=-27.00, format="%.5f")
    with colb[1]: south = st.number_input("South lat", value=-27.75, format="%.5f")
    with colb[2]: east  = st.number_input("East lon",  value=153.30, format="%.5f")
    with colb[3]: west  = st.number_input("West lon",  value=152.60, format="%.5f")
else:
    place_text = st.text_input("Type a place in Australia (city, suburb, postcode, state, or 'Australia')",
                               value="Brisbane QLD")
    st.caption("Examples: Brisbane QLD, Sydney NSW, Melbourne VIC, Gold Coast, Australia")

# Grid controls (sweep modes)
if mode != "Text Search (max 60)":
    colg = st.columns(4)
    with colg[0]: radius_km = st.number_input("Nearby radius (km)", value=2.5, min_value=0.5, max_value=10.0, step=0.5)
    with colg[1]: step_factor = st.slider("Tile overlap (lower = denser)", 1.2, 2.5, 1.5, 0.1)
    with colg[2]: max_tiles = st.number_input("Max tiles (center-out)", value=200, min_value=20, step=10)
    with colg[3]: max_total_places = st.number_input("Max clinics to collect", value=3000, min_value=100, step=100)

# Crawl options
max_pages_per_site = st.slider("Max pages per site (crawler)", 5, 100, 20)
max_seconds_per_site = st.slider("Max seconds per site", 5, 120, 30)
fast_mode = st.checkbox("Fast mode (stop after first email/lead on likely pages)", value=FAST_MODE_DEFAULT)

col1, col2 = st.columns([1,2])
with col1:
    only_paths = st.checkbox("Only crawl these paths", value=False)
with col2:
    paths_txt = st.text_input("Paths (comma-separated)", value="contact,about,team,staff")

run = st.button("Run")

# ==========================
# HTTP helpers
# ==========================
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
            text = "".join(chunks)
            return text, r.url
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

# ==========================
# Extraction helpers
# ==========================
def extract_emails(soup: BeautifulSoup):
    found = set()
    for a in soup.select("a[href^='mailto:']"):
        addr = a.get("href","").split("mailto:")[-1].split("?")[0].strip()
        if EMAIL_RE.fullmatch(addr):
            found.add(addr)
    text = soup.get_text(" ", strip=True)
    for m in EMAIL_RE.finditer(text):
        found.add(m.group(0))
    return found

def normalize_name(txt: str):
    txt = re.sub(r"\s+", " ", txt).strip(" -:•|")
    txt = re.sub(r"^(Dr\.?\s*)?", "Dr ", txt, flags=re.I).strip()
    return txt

def guess_principal(text: str):
    t = re.sub(r"\s+", " ", text)
    pat1 = re.compile(
        r"(Dr\.?\s+[A-Z][a-z]+(?:\s+[A-Z][a-z]+){0,2})\s*(?:,|\s|-)?\s*"
        r"(Principal\s+Dentist|Practice\s+Owner|Owner|Lead\s+Dentist|Clinical\s+Director)", re.I)
    m = pat1.search(t)
    if m: return normalize_name(m.group(1))
    pat2 = re.compile(
        r"(Principal\s+Dentist|Practice\s+Owner|Owner|Lead\s+Dentist|Clinical\s+Director)"
        r"\s*[:\-]?\s*(Dr\.?\s+[A-Z][a-z]+(?:\s+[A-Z][a-z]+){0,2})", re.I)
    m = pat2.search(t)
    if m: return normalize_name(m.group(2))
    m = re.search(r"(Dr\.?\s+[A-Z][a-z]+(?:\s+[A-Z][a-z]+){0,2})", t)
    if m: return normalize_name(m.group(1))
    return ""

def path_tokens_list():
    toks = [p.strip().strip("/") for p in paths_txt.split(",") if p.strip()]
    return toks or DEFAULT_LIKELY

def path_matches(u: str, tokens: list[str]):
    path = urlparse(u).path.lower().strip("/")
    return any(tok.lower() in path for tok in tokens)

def prioritise(urls, tokens):
    def score(u):
        return 0 if path_matches(u, tokens) else 1
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
        url = queue.pop()
        pages_scanned += 1

        if only_paths and url != canon and not path_matches(url, tokens):
            if progress_cb: progress_cb(pages_scanned, max_pages)
            continue

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
# Grid helpers (center-out)
# ==========================
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

# ==========================
# Geocoding helpers
# ==========================
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
        ne = vp.get("northeast", {})
        sw = vp.get("southwest", {})
        north, south = float(ne.get("lat")), float(sw.get("lat"))
        east, west = float(ne.get("lng")), float(sw.get("lng"))
        north, south = max(north, south), min(north, south)
        east, west = max(east, west), min(east, west)
        return north, south, east, west
    loc = geom.get("location")
    if not loc:
        return None
    lat, lng = float(loc["lat"]), float(loc["lng"])
    dlat, dlon = km_to_deg(lat, 50.0)
    return lat + dlat, lat - dlat, lng + dlon, lng - dlon

# ==========================
# Google helpers with retry
# ==========================
def gmaps_text_search_all(gmaps_client, query):
    results = []
    p = None
    for attempt in range(RETRIES + 1):
        try:
            p = gmaps_client.places(query=query)
            break
        except Exception:
            time.sleep(0.6 * (2 ** attempt) + random.random() * JITTER)
    if not p:
        return results
    results += p.get("results", [])
    while "next_page_token" in p:
        time.sleep(NEARBY_SLEEP + random.random() * JITTER)
        for attempt in range(RETRIES + 1):
            try:
                p = gmaps_client.places(query=query, page_token=p["next_page_token"])
                break
            except Exception:
                time.sleep(0.6 * (2 ** attempt) + random.random() * JITTER)
        if not p:
            break
        results += p.get("results", [])
    return results

def gmaps_place_details(gmaps_client, place_id):
    for attempt in range(RETRIES + 1):
        try:
            return gmaps_client.place(place_id=place_id, fields=["name","formatted_address","website"])
        except Exception:
            time.sleep(0.6 * (2 ** attempt) + random.random() * JITTER)
    return {"result": {}}

# ==========================
# Per-clinic worker (bounded)
# ==========================
def process_place(gmaps_client, pid, max_pages_per_site, max_seconds_per_site, fast_mode, only_paths, tokens):
    det = gmaps_place_details(gmaps_client, pid)
    r = det.get("result", {})
    practice = r.get("name")
    addr = r.get("formatted_address")
    site = (r.get("website") or "").strip()

    site_prog = st.progress(0.0)

    def _site_cb(done, cap):
        try:
            site_prog.progress(min(done / max(1, cap), 1.0))
        except Exception:
            pass

    principal, emails, email_src, principal_src = ("", set(), "", "")
    if site:
        principal, emails, email_src, principal_src = crawl_site(
            site,
            max_pages=max_pages_per_site,
            max_seconds=max_seconds_per_site,
            progress_cb=_site_cb,
            fast_mode=fast_mode,
            only_paths=only_paths,
            tokens=tokens
        )
    try:
        site_prog.progress(1.0)
    except Exception:
        pass

    return {
        "Practice": practice or "",
        "Address": addr or "",
        "Website": site,
        "Principal / Owner (guess)": principal,
        "Emails found": ", ".join(sorted(emails)) if emails else "",
        "First email source": email_src,
        "Principal source": principal_src or site,
        "Place ID": pid
    }

# ==========================
# Heartbeat (keeps UI active)
# ==========================
def ui_heartbeat():
    hb = st.empty()
    return hb

def update_heartbeat(hb, i):
    try:
        hb.markdown(f"**Heartbeat:** working… tick {i}")
    except Exception:
        pass

# ==========================
# MAIN
# ==========================
if run and api_key:
    try:
        gmaps_client = googlemaps.Client(key=api_key)

        if mode == "Text Search (max 60)":
            name_hint = slugify(query or "text_search")
        elif mode == "Citywide Sweep (manual bounds)":
            name_hint = "manual_bounds"
        else:
            name_hint = slugify(place_text or "region")

        OUT_CSV   = f"{name_hint}_dental_clinics_with_emails.csv"
        CKPT_JSON = f"{name_hint}_scrape_ckpt.json"

        place_ids = {}
        if mode == "Text Search (max 60)":
            all_places = gmaps_text_search_all(gmaps_client, query)
            for pl in all_places:
                pid = pl.get("place_id")
                if pid: place_ids[pid] = pl
            st.info(f"Collected {len(place_ids)} places (Text Search).")

        else:
            if mode == "Citywide Sweep (manual bounds)":
                bounds = (north, south, east, west)
                st.caption(f"Bounds: N {north:.4f} S {south:.4f} E {east:.4f} W {west:.4f}")
            else:
                vp = geocode_viewport(gmaps_client, place_text)
                if not vp:
                    st.error("Could not geocode that place. Try 'Brisbane QLD' or similar.")
                    st.stop()
                north, south, east, west = vp
                st.caption(f"Viewport for {place_text}: N {north:.4f} S {south:.4f} E {east:.4f} W {west:.4f}")
                bounds = (north, south, east, west)

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

            centers_all = list(make_grid(*bounds, radius_km, step_factor))
            center_lat = (north + south)/2.0
            center_lon = (east + west)/2.0
            centers_sorted = sort_center_out(centers_all, center_lat, center_lon)

            if len(centers_sorted) > max_tiles:
                centers = centers_sorted[:max_tiles]
                st.caption(f"Center-out sampling {max_tiles} of {len(centers_sorted)} tiles.")
            else:
                centers = centers_sorted

            grid_prog = st.progress(0.0)
            for i, (lat, lon) in enumerate(centers, start=1):
                nearby = fetch_nearby_all_pages(gmaps_client, (lat, lon), int(radius_km*1000), type_="dentist")
                for pl in nearby:
                    pid = pl.get("place_id")
                    if pid and pid not in place_ids:
                        place_ids[pid] = pl
                        if len(place_ids) >= max_total_places:
                            break
                grid_prog.progress(min(i/len(centers), 1.0))
                if len(place_ids) >= max_total_places:
                    break
            st.success(f"Collected {len(place_ids)} unique places across {min(i, len(centers))} tiles.")

        if not place_ids:
            st.warning("No clinics found."); st.stop()

        start_idx = load_resume_index(CKPT_JSON)
        ids = list(place_ids.keys())
        if start_idx >= len(ids): start_idx = 0

        tokens = path_tokens_list()
        rows_buffer = []
        overall = st.progress(0.0, text="Processing clinics…")
        hb = ui_heartbeat()

        def process_place_wrapper(pid):
            return process_place(gmaps_client, pid,
                                 max_pages_per_site, max_seconds_per_site,
                                 fast_mode, only_paths, tokens)

        with ThreadPoolExecutor(max_workers=MAX_WORKERS) as pool:
            idx = start_idx
            while idx < len(ids):
                batch = ids[idx : min(idx + MAX_WORKERS, len(ids))]
                futures = {pool.submit(process_place_wrapper, pid): pid for pid in batch}

                for j, (fut, pid) in enumerate(list(futures.items()), start=1):
                    try:
                        row = fut.result(timeout=PLACE_TIMEOUT)
                    except FuturesTimeout:
                        row = {
                            "Practice": "", "Address": "", "Website": "",
                            "Principal / Owner (guess)": "", "Emails found": "",
                            "First email source": "", "Principal source": "",
                            "Place ID": pid, "Error": f"Timeout after {PLACE_TIMEOUT}s"
                        }
                    except Exception as e:
                        row = {
                            "Practice": "", "Address": "", "Website": "",
                            "Principal / Owner (guess)": "", "Emails found": "",
                            "First email source": "", "Principal source": "",
                            "Place ID": pid, "Error": str(e)
                        }

                    rows_buffer.append(row)

                    cur = idx + j
                    overall.progress(cur / len(ids), text=f"{cur}/{len(ids)} processed")
                    update_heartbeat(hb, cur)

                    if cur % FLUSH_EVERY == 0:
                        checkpoint(cur, rows_buffer, OUT_CSV, CKPT_JSON)
                        rows_buffer = []

                    time.sleep(0.05)

                idx += len(batch)

        checkpoint(len(ids), rows_buffer, OUT_CSV, CKPT_JSON)

        if os.path.exists(OUT_CSV):
            df = pd.read_csv(OUT_CSV)
        else:
            df = pd.DataFrame(columns=[
                "Practice","Address","Website","Principal / Owner (guess)",
                "Emails found","First email source","Principal source","Place ID","Error"
            ])

        if "Place ID" in df.columns:
            df = df.drop_duplicates(subset=["Place ID"]).reset_index(drop=True)

        st.success(f"Processed {len(df)} clinics total for {name_hint} (center-out, crash-safe, anti-timeout).")
        safe_view = [c for c in df.columns if c != "Place ID"]
        st.dataframe(df[safe_view], use_container_width=True)
        st.download_button("Download CSV", df.to_csv(index=False).encode("utf-8"),
                           f"{name_hint}_dental_clinics_with_emails.csv", "text/csv")
        st.caption("Center-out scan covers the middle first. If interrupted, press Run again to resume — it won’t re-do finished clinics.")

    except Exception as e:
        st.error(f"Error: {e}")

elif run and not api_key:
    st.info("Add your key in Render → Environment as GMAPS_KEY (or GOOGLE_API_KEY), or paste it above.")
