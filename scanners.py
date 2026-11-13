"""
Unified Lead Scout – platform scanners (v3.6).

Each platform is one adapter function registered with @register_adapter.
Separates Job Leads ('seeker' & 'employer') from Buy & Sell Leads ('buyer' & 'seller')
so product/marketplace results never mix into Jobseeker or Employer Hiring views.
"""
import base64
import email.utils
import hashlib
import html as html_lib
import json
import os
import re
import threading
import time
import urllib.error
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime, timedelta, timezone

from database import (
    ALLOWED_WEB_DOMAINS,
    is_buy_sell_keyword,
    is_valid_lead_url,
    save_lead,
    smart_query_matches,
    utc_now_sql,
)

SCANNER_VERSION = "v3.6"
REDDIT_USER_AGENT = "linux:unified-lead-scout:v3.6 (by /u/unified_lead_scout)"
BROWSER_USER_AGENT = (
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
    "(KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36"
)
APIFY_BASE = "https://api.apify.com/v2"
ATOM = "{http://www.w3.org/2005/Atom}"

_SERVER_TIME_LOCK = threading.Lock()
_LAST_REMOTE_UTC = None
_REDDIT_GLOBAL_LOCK = threading.Lock()
_REDDIT_RSS_CACHE = {}
_SEARCH_GLOBAL_LOCK = threading.Lock()

APIFY_ACTORS = {
    "facebook_groups": "apify/facebook-groups-scraper",
    "facebook_pages": "apify/facebook-posts-scraper",
    "facebook_comments": "apify/facebook-comments-scraper",
    "instagram_hashtags": "apify/instagram-hashtag-scraper",
    "instagram_comments": "apify/instagram-comment-scraper",
    "tiktok_search": "clockworks/tiktok-scraper",
    "tiktok_comments": "clockworks/tiktok-comments-scraper",
}

# 100% Jobseeker keywords (never includes buy/sell words)
DEFAULT_SEEKER_KEYWORDS = [
    "looking for a job", "looking for job", "looking for work",
    "looking for part time", "looking for part-time", "looking for full time",
    "looking for side hustle", "looking for side hustles", "remote gigs",
    "looking for gig", "looking for gigs", "need a job", "need work",
    "need part time", "need extra income", "open for work", "open to work",
    "available for work", "available for any work", "available for any task",
    "for hire", "hire me", "hiring me", "offering remote services", "offering services",
    "offering coaching", "errand runner", "currently unemployed", "unemployed for",
    "nangita kog trabaho", "nangita ug trabaho", "nangita ko trabaho",
    "ngita kog trabaho", "ngita ko trabaho", "ngita trabaho", "pangita trabaho",
    "mangita trabaho", "naghahanap ng trabaho", "naghahanap ako ng trabaho",
    "hanap trabaho", "pwede mo apply", "pwede pa mo apply", "pwede ko mo apply",
    "pwede pa apply", "pwede mag apply", "unsaon pag apply", "paano mag apply",
    "asa dapit mo apply", "how to apply", "where to apply", "interested po",
    "interested ako", "interested here", "interested ko", "interested maam",
    "interested sir", "i'm interested", "im interested", "interested",
    "willing to start asap", "willing to start immediately", "willing to start",
    "can start immediately", "can start asap", "available immediately",
    "naay hiring", "naa bay hiring", "any hiring", "still hiring", "hiring pa",
    "pa apply", "apply ko", "apply ta", "pa refer", "how po", "no experience",
    "mo duty", "pm sir", "pm boss", "pm maam", "nag message ko", "nag pm ko",
    "check message",
]

# 100% Employer Hiring keywords (never includes 'for sale' or buy/sell words)
DEFAULT_EMPLOYER_KEYWORDS = [
    "we are hiring", "we're hiring", "now hiring", "urgent hiring", "urgently hiring",
    "is hiring", "are hiring", "currently hiring", "job hiring", "cebu hiring",
    "hiring", "job vacancy", "job vacancies", "job opening", "job openings",
    "vacancy", "vacancies", "apply now", "send your resume", "send resume",
    "send your cv", "submit your resume", "join our team",
    "looking for staff", "need staff", "need crew", "looking for crew",
    "looking for dishwasher", "looking for service crew", "looking for helper",
    "looking for cook", "looking for cashier", "looking for barista",
    "looking for virtual assistant", "accepting applicants", "walk-in applicants",
    "walk in applicants", "nangita mi", "nangita kami", "nanginahanglan mi",
    "naghahanap kami", "kailangan namin", "hiring staff", "hiring crew",
    "we need staff",
]

# Separate Seller & Buyer keywords (categorized strictly as 'seller' and 'buyer')
DEFAULT_SELLER_KEYWORDS = [
    "for sale", "fs:", "selling", "rush sale", "sale or swap", "fix price",
    "gpu for sale", "graphics card", "video card", "pc set", "system unit",
]

DEFAULT_BUYER_KEYWORDS = [
    "wtb", "want to buy", "lf:", "kuhaon dayon", "pila last price", "last price",
]

DEFAULT_LOCATION_TERMS = {
    "cebu": [
        "cebu", "mandaue", "lapu-lapu", "lapulapu", "lapu lapu", "talisay", "consolacion",
        "liloan", "minglanilla", "carcar", "danao", "toledo", "it park", "banilad", "mabolo",
        "lahug", "guadalupe", "fuente", "mactan", "cordova", "sm seaside", "ayala", "talamban",
    ],
}

NON_CEBU_CITIES = (
    "manila", "metro manila", "ncr", "makati", "quezon city", "qc", "marikina",
    "taguig", "bgc", "pasig", "ortigas", "alabang", "muntinlupa", "cavite",
    "laguna", "bacoor", "imus", "lucena", "pampanga", "bulacan", "davao",
    "iloilo", "bacolod",
)

REMOTE_WORK_TERMS = (
    "remote", "online", "wfh", "work from home", "virtual", "data entry",
    "anywhere", "freelance",
)


class ScanError(Exception):
    pass


# =====================================================================
# SETTINGS & TEXT HELPERS
# =====================================================================

def _as_list(value):
    if isinstance(value, str):
        value = re.split(r"[\n,]", value)
    return [str(v).strip() for v in (value or []) if str(v).strip()]


def get_settings(config):
    config = config or {}
    s = config.get("search_settings", {})
    social = config.get("social", {})
    reddit = config.get("reddit", {})
    # Filter out any buy/sell terms that might have been in config.json seeker/employer lists
    raw_seeker = [k for k in _as_list(s.get("seeker_keywords")) if not is_buy_sell_keyword(k)]
    raw_employer = [k for k in _as_list(s.get("employer_keywords")) if not is_buy_sell_keyword(k)]
    seeker_kw = list(dict.fromkeys(raw_seeker + DEFAULT_SEEKER_KEYWORDS))
    employer_kw = list(dict.fromkeys(raw_employer + DEFAULT_EMPLOYER_KEYWORDS))
    custom_queries = list(dict.fromkeys(
        _as_list(social.get("search_queries"))
        + _as_list(social.get("tiktok_search_queries"))
    ))
    return {
        "location": s.get("location", "Cebu"),
        "max_age_days": int(s.get("max_age_days", 7) or 7),
        "seeker_keywords": seeker_kw,
        "employer_keywords": employer_kw,
        "seller_keywords": list(DEFAULT_SELLER_KEYWORDS),
        "buyer_keywords": list(DEFAULT_BUYER_KEYWORDS),
        "custom_queries": custom_queries,
        "location_terms": {k.lower(): v for k, v in
                           (s.get("location_terms") or DEFAULT_LOCATION_TERMS).items()},
        "subreddits": [re.sub(r"^/?r/", "", x) for x in (_as_list(config.get("subreddits")) or ["Cebu", "phclassifieds", "buhaydigital"])],
        "reddit_client_id": reddit.get("client_id", ""),
        "reddit_client_secret": reddit.get("client_secret", ""),
        "apify_token": os.environ.get("APIFY_TOKEN") or config.get("apify_token", ""),
        "facebook_groups": _as_list(social.get("facebook_groups")),
        "facebook_pages": _as_list(social.get("facebook_pages")),
        "instagram_hashtags": [t.lstrip("#") for t in _as_list(social.get("instagram_hashtags"))],
        "tiktok_search_queries": custom_queries,
        "tiktok_hashtags": [t.lstrip("#") for t in _as_list(social.get("tiktok_hashtags"))],
        "results_per_source": int(social.get("results_per_source", 30) or 30),
        "comment_threads_per_platform": int(social.get("comment_threads_per_platform", 3) or 0),
        "comments_per_thread": int(social.get("comments_per_thread", 50) or 50),
        "rss_feeds": config.get("rss_feeds", []),
    }


def _norm(text):
    text = (text or "").replace("\u2019", "'").replace("\u2018", "'")
    return re.sub(r"\s+", " ", text.lower()).strip()


def phrase_in(text_norm, phrase):
    p = _norm(phrase).strip("[]#:!.,? ")
    if not p:
        return False
    return re.search(r"(?<!\w)" + re.escape(p) + r"(?!\w)", text_norm) is not None


AMBIGUOUS_JOB_PHRASES = {
    "pm sent", "dm sent", "sent you a dm", "sent you a pm",
    "available pa", "naa pa ni", "qualifications", "requirements",
    "interested po", "interested ako", "interested here", "i'm interested", "im interested",
    "interested", "how po", "pm sir", "pm boss", "pm maam", "nag message ko",
    "nag pm ko", "check message",
}

UNAMBIGUOUS_JOB_WORDS = (
    "job", "work", "trabaho", "hiring", "apply", "applicant", "vacancy",
    "resume", "cv", "staff", "crew", "salary", "part time", "part-time",
    "full time", "full-time", "for hire", "hire me", "freelance", "remote",
    "gig", "gigs", "unemployed", "opening", "dishwasher", "barista",
    "cashier", "helper", "cook", "driver", "errand", "coach",
)

MERCH_SALE_INDICATORS = (
    "for sale", "fs:", "sale or swap", "fix price", "rfs:", "reason for selling",
    "decluttering", "reposting until sold", "brand new and sealed",
)


def _classify_query_intent(text_norm, kind, q_str):
    """Determines whether a custom query match belongs to ('seeker'|'employer') or ('buyer'|'seller')."""
    q_low = q_str.strip().lower().rstrip("?")
    if is_buy_sell_keyword(q_low) or any(m in text_norm for m in MERCH_SALE_INDICATORS):
        if kind == "comment" or any(phrase_in(text_norm, w) for w in ("lf", "wtb", "looking for", "buying", "kuhaon dayon")):
            return "buyer"
        return "seller"
    # Otherwise it's a job query
    if kind == "comment":
        return "seeker"
    if any(phrase_in(text_norm, p) for p in DEFAULT_SEEKER_KEYWORDS):
        return "seeker"
    if any(phrase_in(text_norm, p) for p in ("we are hiring", "now hiring", "urgent hiring", "is hiring", "are hiring", "looking for staff", "looking for crew", "job opening", "vacancy")):
        return "employer"
    if any(w in q_low for w in ("interested", "apply", "trabaho", "looking for work", "for hire", "naay hiring")):
        return "seeker"
    return "employer"


def classify_intent(text_norm, kind, settings, query="", full_context="", source_name=""):
    """
    Returns ('seeker'|'employer'|'buyer'|'seller'|None, matched_phrase).
    Strictly separates Jobs ('seeker', 'employer') from Buy & Sell ('buyer', 'seller').
    """
    ctx_check = full_context or text_norm
    src_low = (source_name or "").lower()
    is_merch_group = any(g in src_low for g in ("sales & repairs", "buy and sell", "buy & sell", "marketplace"))
    has_merch_indicator = is_merch_group or any(m in ctx_check for m in MERCH_SALE_INDICATORS)
    has_job_word = any(phrase_in(ctx_check, w) for w in UNAMBIGUOUS_JOB_WORDS)

    # 1. Check pure Jobseeker & Employer Hiring keywords first (unless it's a pure merchandise sale without job words)
    if not (has_merch_indicator and not has_job_word):
        s_hits = [
            p for p in settings["seeker_keywords"]
            if phrase_in(text_norm, p) and (p not in AMBIGUOUS_JOB_PHRASES or has_job_word)
        ]
        e_hits = [
            p for p in settings["employer_keywords"]
            if phrase_in(text_norm, p) and (p not in AMBIGUOUS_JOB_PHRASES or has_job_word)
        ]
        if "hiring me" in text_norm and "hiring" in e_hits and not any(phrase_in(text_norm, w) for w in ("we are hiring", "now hiring", "urgent hiring")):
            e_hits = [p for p in e_hits if p != "hiring"]

        if s_hits or e_hits:
            if kind == "comment":
                # Comments on hiring threads or with seeker phrases are always jobseekers
                return "seeker", (s_hits[0] if s_hits else e_hits[0])
            if s_hits and not e_hits:
                return "seeker", s_hits[0]
            if e_hits and not s_hits:
                return "employer", e_hits[0]
            # Both matched on a post: if seeker phrase is explicit ("nangita kog trabaho", "for hire", "how to apply", "interested po"), pick seeker
            return ("seeker", s_hits[0]) if len(s_hits) >= len(e_hits) else ("employer", e_hits[0])

    # 2. Check active search bar query (if provided)
    if query and smart_query_matches(text_norm, query):
        clean_q = ("ram" if query.strip().lower() == "rame" else query.strip()).rstrip("?")
        return _classify_query_intent(text_norm, kind, clean_q), clean_q

    # 3. Check custom queries configured in Settings
    for cq in settings.get("custom_queries") or []:
        cq_clean = ("ram" if cq.strip().lower() == "rame" else cq.strip()).rstrip("?")
        if not cq_clean:
            continue
        if smart_query_matches(text_norm, cq_clean):
            intent_val = _classify_query_intent(text_norm, kind, cq_clean)
            # Don't let ambiguous phrases like "interested po" match a non-job merchandise post as 'seeker'
            if intent_val in ("seeker", "employer") and has_merch_indicator and not has_job_word:
                continue
            return intent_val, cq_clean

    # 4. Check Buy & Sell keywords ('buyer' and 'seller')
    b_hits = [p for p in settings["buyer_keywords"] if phrase_in(text_norm, p)]
    sel_hits = [p for p in settings["seller_keywords"] if phrase_in(text_norm, p)]
    if b_hits or sel_hits:
        if kind == "comment" or (b_hits and not sel_hits):
            return "buyer", (b_hits[0] if b_hits else sel_hits[0])
        return "seller", (sel_hits[0] if sel_hits else b_hits[0])

    return None, ""


def _location_terms(location, settings):
    loc = (location or "").strip().lower()
    return settings["location_terms"].get(loc, [loc]) if loc else []


def location_matches(text_norm, location, settings):
    if not location or location.lower() == "any":
        return True
    return any(phrase_in(text_norm, t) for t in _location_terms(location, settings))


def location_scoped(name, location, settings):
    if not location or location.lower() == "any":
        return False
    n = (name or "").lower()
    return any(t.replace(" ", "") in n.replace(" ", "") for t in _location_terms(location, settings))


def to_epoch(value):
    if value in (None, "", 0):
        return None
    if isinstance(value, (int, float)):
        v = float(value)
        return v / 1000.0 if v > 1e12 else v
    s = str(value).strip()
    if re.fullmatch(r"\d+(\.\d+)?", s):
        return to_epoch(float(s))
    try:
        iso = s.replace("Z", "+00:00")
        if "T" not in iso and " " in iso:
            iso = iso.replace(" ", "T", 1)
        dt = datetime.fromisoformat(iso)
        if dt.tzinfo is None:
            dt = dt.replace(tzinfo=timezone.utc)
        return dt.timestamp()
    except ValueError:
        pass
    try:
        dt = email.utils.parsedate_to_datetime(s)
        if dt.tzinfo is None:
            dt = dt.replace(tzinfo=timezone.utc)
        return dt.timestamp()
    except (TypeError, ValueError):
        return None


def _record_remote_date(date_hdr):
    global _LAST_REMOTE_UTC
    ts = to_epoch(date_hdr)
    if ts and ts > 1700000000:
        with _SERVER_TIME_LOCK:
            _LAST_REMOTE_UTC = ts


def get_reference_now(fallback_ts=None):
    with _SERVER_TIME_LOCK:
        if _LAST_REMOTE_UTC:
            return _LAST_REMOTE_UTC
    if fallback_ts and fallback_ts > 1700000000:
        return fallback_ts
    return time.time()


def age_adjusted_sql_ts(item_ts):
    if not item_ts:
        return utc_now_sql()
    ref_now = get_reference_now(item_ts)
    age_sec = max(0.0, ref_now - float(item_ts))
    local_age = time.time() - float(item_ts)
    if 0 <= local_age < age_sec:
        age_sec = local_age
    dt = datetime.now(timezone.utc) - timedelta(seconds=age_sec)
    return dt.strftime("%Y-%m-%d %H:%M:%S")


def pick(d, *paths):
    for path in paths:
        cur = d
        for part in path.split("."):
            cur = cur.get(part) if isinstance(cur, dict) else None
            if cur is None:
                break
        if cur not in (None, "", [], {}):
            return cur
    return None


def stable_id(*parts):
    return hashlib.sha1("|".join(str(p) for p in parts).encode("utf-8")).hexdigest()[:16]


def _short(text, n=200):
    text = html_lib.unescape(re.sub(r"<[^>]+>", " ", text or ""))
    text = re.sub(r"\s+", " ", text).strip()
    return text if len(text) <= n else text[: n - 1] + "…"


# =====================================================================
# HTTP / API CLIENTS
# =====================================================================

def http_request(url, method="GET", body=None, headers=None, timeout=20, raw=False):
    host = urllib.parse.urlparse(url).netloc
    ua = REDDIT_USER_AGENT if "reddit.com" in host else BROWSER_USER_AGENT
    h = {"User-Agent": ua, "Accept": "application/json"}
    h.update(headers or {})
    data = None
    if body is not None:
        if isinstance(body, (dict, list)):
            data = json.dumps(body).encode("utf-8")
            h["Content-Type"] = "application/json"
        else:
            data = body
    req = urllib.request.Request(url, data=data, headers=h, method=method)
    try:
        with urllib.request.urlopen(req, timeout=timeout) as resp:
            _record_remote_date(resp.headers.get("Date"))
            payload = resp.read()
    except urllib.error.HTTPError as e:
        _record_remote_date(e.headers.get("Date") if e.headers else None)
        raise ScanError(f"HTTP {e.code} from {host}") from None
    except urllib.error.URLError as e:
        raise ScanError(f"Network error reaching {host}: {e.reason}") from None
    except (TimeoutError, OSError) as e:
        raise ScanError(f"Connection problem with {host}: {e}") from None
    if raw:
        return payload
    try:
        return json.loads(payload.decode("utf-8"))
    except ValueError:
        raise ScanError(f"Unexpected (non-JSON) response from {host}") from None


class RedditClient:
    _token_cache = {}
    _lock = threading.Lock()

    def __init__(self, settings):
        self.cid = settings.get("reddit_client_id", "")
        self.secret = settings.get("reddit_client_secret", "")

    @property
    def has_oauth(self):
        return bool(self.cid and self.secret)

    def _token(self):
        with RedditClient._lock:
            cached = RedditClient._token_cache.get(self.cid)
            if cached and cached[1] > time.time() + 60:
                return cached[0]
            auth = base64.b64encode(f"{self.cid}:{self.secret}".encode()).decode()
            resp = http_request(
                "https://www.reddit.com/api/v1/access_token", "POST",
                body=b"grant_type=client_credentials",
                headers={"Authorization": f"Basic {auth}",
                         "Content-Type": "application/x-www-form-urlencoded"},
            )
            token = resp.get("access_token")
            if not token:
                raise ScanError("Reddit OAuth failed — check the Reddit client id/secret in Settings.")
            RedditClient._token_cache[self.cid] = (token, time.time() + float(resp.get("expires_in", 3600)))
            return token

    def get(self, path, params=None):
        params = dict(params or {})
        params["raw_json"] = 1
        path = "/" + path.strip("/")
        if self.has_oauth:
            url = f"https://oauth.reddit.com{path}?{urllib.parse.urlencode(params)}"
            headers = {"Authorization": f"Bearer {self._token()}"}
        else:
            url = f"https://www.reddit.com{path}.json?{urllib.parse.urlencode(params)}"
            headers = {}
        with _REDDIT_GLOBAL_LOCK:
            try:
                return http_request(url, headers=headers, timeout=20)
            finally:
                time.sleep(0.8)

    def get_rss_entries(self, path, params=None):
        params = dict(params or {})
        clean_path = "/" + path.strip("/") + "/"
        q_str = f"?{urllib.parse.urlencode(sorted(params.items()))}" if params else ""
        cache_key = f"{clean_path}{q_str}"

        with _REDDIT_GLOBAL_LOCK:
            cached = _REDDIT_RSS_CACHE.get(cache_key)
            if cached and (time.time() - cached[0]) < 45:
                return list(cached[1])

            hosts = ["https://www.reddit.com", "https://old.reddit.com"]
            last_err = None
            raw_xml = None
            for host in hosts:
                url = f"{host}{clean_path}.rss{q_str}"
                try:
                    raw_xml = http_request(
                        url,
                        headers={"Accept": "application/atom+xml, application/rss+xml, application/xml, */*"},
                        timeout=20,
                        raw=True,
                    )
                    break
                except ScanError as e:
                    last_err = e
                    time.sleep(1.5)
            time.sleep(1.1)

            if raw_xml is None:
                raise last_err or ScanError("Reddit RSS unavailable")

            parsed = parse_reddit_atom(raw_xml)
            _REDDIT_RSS_CACHE[cache_key] = (time.time(), parsed)
            return list(parsed)


def parse_reddit_atom(raw_xml):
    try:
        root = ET.fromstring(raw_xml)
    except ET.ParseError as e:
        raise ScanError(f"Invalid XML from Reddit RSS: {e}") from None

    entries = []
    for entry in root.findall(f".//{ATOM}entry") or root.findall(".//item"):
        title = entry.findtext(f"{ATOM}title") or entry.findtext("title") or ""
        link = entry.findtext("link") or ""
        if not link:
            el = entry.find(f"{ATOM}link")
            link = el.attrib.get("href", "") if el is not None else ""
        content_html = (
            entry.findtext(f"{ATOM}content")
            or entry.findtext(f"{ATOM}summary")
            or entry.findtext("description")
            or ""
        )
        clean_text = html_lib.unescape(re.sub(r"<[^>]+>", " ", content_html))
        clean_text = re.sub(r"\s*submitted by\s+/u/\S+.*$", "", clean_text, flags=re.I).strip()
        clean_text = re.sub(r"\s+", " ", clean_text).strip()
        author = entry.findtext(f"{ATOM}author/{ATOM}name") or entry.findtext("author") or "u/reddit_user"
        if not author.startswith("u/") and not author.startswith("/u/"):
            author = f"u/{author}"
        author = author.lstrip("/")
        pub_str = entry.findtext(f"{ATOM}updated") or entry.findtext(f"{ATOM}published") or entry.findtext("pubDate")
        cat_el = entry.find(f"{ATOM}category")
        sub = ""
        if cat_el is not None:
            sub = (cat_el.attrib.get("term") or cat_el.attrib.get("label") or "").lstrip("r/")
        if not sub and "/r/" in link:
            m = re.search(r"/r/([^/]+)", link)
            if m:
                sub = m.group(1)
        entry_id = entry.findtext(f"{ATOM}id") or stable_id(link)
        entries.append({
            "id": entry_id.split("_")[-1] if "_" in entry_id else stable_id(link),
            "title": html_lib.unescape(title).strip(),
            "text": clean_text or html_lib.unescape(title).strip(),
            "url": link,
            "author": author,
            "posted_ts": to_epoch(pub_str),
            "subreddit": sub or "Cebu",
        })
    return entries


def apify_fetch_recent_runs(actor_id, token, max_runs=2):
    act = actor_id.replace("/", "~")
    headers = {"Authorization": f"Bearer {token}"}
    try:
        resp = http_request(
            f"{APIFY_BASE}/acts/{act}/runs?limit={max_runs}&desc=1&status=SUCCEEDED",
            headers=headers,
            timeout=20,
        )
        run_list = pick(resp, "data.items") or []
    except ScanError:
        return [], float("inf")

    all_items = []
    latest_age = float("inf")
    for idx, r_info in enumerate(run_list):
        ds_id = r_info.get("defaultDatasetId")
        started_ts = to_epoch(r_info.get("finishedAt") or r_info.get("startedAt"))
        if idx == 0 and started_ts:
            latest_age = max(0.0, get_reference_now(started_ts) - started_ts)
        if not ds_id:
            continue
        try:
            ds_items = http_request(
                f"{APIFY_BASE}/datasets/{ds_id}/items?clean=true&format=json",
                headers=headers,
                timeout=30,
            )
            if isinstance(ds_items, list):
                for i in ds_items:
                    if isinstance(i, dict) and not (i.get("error") and not (i.get("text") or i.get("title"))):
                        all_items.append(i)
        except ScanError:
            continue
    return all_items, latest_age


class ScanCancelled(ScanError):
    pass


def apify_abort_run(run_id, token):
    if not run_id or not token:
        return
    try:
        http_request(
            f"{APIFY_BASE}/actor-runs/{run_id}/abort",
            method="POST",
            headers={"Authorization": f"Bearer {token}"},
            timeout=10,
        )
    except ScanError:
        pass


def apify_run(actor_id, run_input, token, max_wait_s=600, ctx=None):
    if ctx and ctx.is_cancelled():
        raise ScanCancelled("Cancelled by user.")
    act = actor_id.replace("/", "~")
    headers = {"Authorization": f"Bearer {token}"}
    run = http_request(f"{APIFY_BASE}/acts/{act}/runs?waitForFinish=5", "POST",
                       body=run_input, headers=headers, timeout=30).get("data", {})
    run_id = run.get("id")
    if ctx and run_id:
        ctx.register_apify_run(run_id, token)
    deadline = time.time() + max_wait_s
    while run.get("status") in ("READY", "RUNNING", "TIMING-OUT", "ABORTING"):
        if ctx and ctx.is_cancelled():
            apify_abort_run(run_id, token)
            raise ScanCancelled("Cancelled by user.")
        if time.time() > deadline:
            raise ScanError(f"{actor_id} still running after {max_wait_s}s (run {run_id}); skipped.")
        run = http_request(f"{APIFY_BASE}/actor-runs/{run_id}?waitForFinish=5",
                           headers=headers, timeout=30).get("data", {})
    if ctx and ctx.is_cancelled():
        raise ScanCancelled("Cancelled by user.")
    if run.get("status") != "SUCCEEDED":
        raise ScanError(f"{actor_id} finished with status {run.get('status')}: "
                        f"{_short(run.get('statusMessage') or '')}")
    items = http_request(f"{APIFY_BASE}/datasets/{run['defaultDatasetId']}/items?clean=true&format=json",
                         headers=headers, timeout=90)
    return [i for i in items if isinstance(i, dict) and not (i.get("error") and not (i.get("text") or i.get("title")))] \
        if isinstance(items, list) else []


# =====================================================================
# SCAN CONTEXT, RESULTS & CENTRAL EVALUATION
# =====================================================================

class ScanContext:
    def __init__(self, config, query="", location="Cebu", max_age_days=7, intents=None,
                 trigger="manual", cancel_event=None):
        self.settings = get_settings(config)
        self.query = (query or "").strip()
        self.location = location or "Any"
        self.max_age_days = max(1, int(max_age_days or 7))
        self.intents = set(intents or ["seeker", "employer"])
        self.trigger = trigger
        self.cancel_event = cancel_event or threading.Event()
        self._apify_lock = threading.Lock()
        self._apify_runs = []

    def is_cancelled(self):
        return self.cancel_event.is_set()

    def register_apify_run(self, run_id, token):
        with self._apify_lock:
            self._apify_runs.append((run_id, token))

    def abort_active_apify_runs(self):
        with self._apify_lock:
            runs = list(self._apify_runs)
        for run_id, token in runs:
            apify_abort_run(run_id, token)

    def since_phrase(self):
        return "1 day" if self.max_age_days == 1 else f"{self.max_age_days} days"

    def is_recent(self, ts):
        if ts is None:
            return True
        ref_now = get_reference_now(ts)
        age = ref_now - float(ts)
        local_age = time.time() - float(ts)
        effective_age = min(age if age >= -300 else float("inf"),
                            local_age if local_age >= -300 else float("inf"))
        if effective_age == float("inf"):
            return True
        return effective_age <= self.max_age_days * 86400

    def intent_of(self, text, kind="post"):
        return classify_intent(_norm(text), kind, self.settings, query=self.query)[0]


def result(status, message="", items=None, fetched=0):
    return {"status": status, "message": message, "items": items or [], "fetched": fetched}


def _finish(items, fetched, errors, note=""):
    if not errors or items:
        status = "ok" if not errors else "partial"
        msg = note or (f"Checked {fetched} posts/comments." if not errors else "; ".join(errors[:2]))
        return result(status, msg, items, fetched)
    msg = "; ".join(errors[:3]) + (f" (+{len(errors) - 3} more)" if len(errors) > 3 else "")
    return result("partial" if fetched else "error", msg, items, fetched)


def item(platform, kind, source, external_id, text, author, url, posted_ts,
         title="", parent_text="", parent_url="", scoped=False, from_configured_source=False):
    return {
        "platform": platform, "kind": kind, "source": source, "external_id": external_id,
        "text": text or "", "author": author or "unknown", "url": url, "posted_ts": posted_ts,
        "title": title or "", "parent_text": parent_text or "", "parent_url": parent_url or "",
        "scoped": scoped, "from_configured_source": from_configured_source,
    }


def evaluate_item(it, ctx):
    """
    Applies URL domain/path validation, recency, 4-way intent classification
    ('seeker', 'employer', 'buyer', 'seller'), and location filters.
    Never creates fallback 'group post' or 'group comment' tags.
    """
    url = (it.get("url") or "").strip()
    plat = (it.get("platform") or "").strip()
    ext_id = it.get("external_id") or ""
    if not ext_id or not url or not (it.get("text") or it.get("title")):
        return None

    # 1. Strict URL domain AND path verification for the target platform
    if not is_valid_lead_url(plat, url, ext_id):
        return None

    # 2. Recency filter
    ts = it.get("posted_ts")
    if not ctx.is_recent(ts):
        return None

    body = html_lib.unescape(it.get("text") or "").strip()
    title = html_lib.unescape(it.get("title") or _short(body.split("\n")[0], 100)).strip()

    own_text = _norm(body if it["kind"] == "comment" else f"{title} {body}")
    context = _norm(f"{own_text} {it.get('parent_text', '')}")

    # 3. 4-Way Intent Classification ('seeker' | 'employer' | 'buyer' | 'seller')
    intent, keyword = classify_intent(
        own_text, it["kind"], ctx.settings,
        query=ctx.query, full_context=context, source_name=it.get("source", "")
    )
    if intent is None or not keyword or keyword.lower() in ("seeker", "employer", "group post", "group comment"):
        return None

    # 4. Location check
    if ctx.location.lower() != "any":
        is_direct_loc = (
            it.get("scoped")
            or it.get("from_configured_source")
            or location_matches(context, ctx.location, ctx.settings)
        )
        is_remote_ph = (
            plat == "reddit"
            and any(sub in (it.get("source") or "").lower() for sub in ("phclassifieds", "buhaydigital"))
            and (
                any(phrase_in(context, rt) for rt in REMOTE_WORK_TERMS)
                or not any(phrase_in(context, city) for city in NON_CEBU_CITIES)
            )
        )
        if not (is_direct_loc or is_remote_ph):
            return None
        loc = ctx.location if is_direct_loc else f"{ctx.location} / Remote PH"
    else:
        loc = next((name.title() for name in ctx.settings["location_terms"]
                    if location_matches(context, name, ctx.settings)), "Philippines")

    return {
        "source": it["source"], "external_id": ext_id, "title": title,
        "content": body[:3000], "author": it["author"], "url": url, "location": loc,
        "posted_at": age_adjusted_sql_ts(ts), "platform": plat, "kind": it["kind"],
        "intent": intent, "matched_keyword": keyword, "parent_url": it.get("parent_url", ""),
    }


def lead_matches_active_filters(lead, ctx):
    if lead.get("intent") not in ctx.intents:
        return False
    if not ctx.query:
        return True
    hay = _norm(" ".join([
        lead.get("title", ""), lead.get("content", ""), lead.get("author", ""),
        lead.get("source", ""), lead.get("location", ""), lead.get("matched_keyword", ""),
    ]))
    return smart_query_matches(hay, ctx.query)


# =====================================================================
# ADAPTER REGISTRY & PUBLIC SEARCH INDEXERS
# =====================================================================

PLATFORM_ADAPTERS = {}


def register_adapter(key, label, description="", needs=None):
    def decorator(func):
        PLATFORM_ADAPTERS[key] = {"key": key, "label": label, "description": description,
                                  "needs": needs, "handler": func}
        return func
    return decorator


def adapter_readiness(key, settings):
    s = settings
    if key in ("facebook", "instagram", "tiktok"):
        if s["apify_token"]:
            return True, f"Ready ({SCANNER_VERSION} Apify Deep Scraper)"
        return True, f"Ready ({SCANNER_VERSION} Verified Public Index)"
    if key in ("reddit_posts", "reddit_comments") and not s["subreddits"]:
        return False, "Add subreddits (Settings)."
    return True, f"Ready ({SCANNER_VERSION})"


def _unwrap_redirect_url(raw_href):
    href = html_lib.unescape(raw_href or "").strip()
    if href.startswith("//"):
        href = "https:" + href
    if "uddg=" in href:
        qs = urllib.parse.parse_qs(urllib.parse.urlparse(href).query)
        href = qs.get("uddg", [href])[0]
    elif "/RU=" in href:
        m = re.search(r"/RU=([^/]+)/RK=", href)
        if m:
            href = urllib.parse.unquote(m.group(1))
    return href


def _search_duckduckgo_html(dork_query, max_age_days=7, platform=""):
    df = "d" if max_age_days <= 1 else ("w" if max_age_days <= 7 else "m")
    qs = urllib.parse.urlencode({"q": dork_query, "df": df})
    url = f"https://html.duckduckgo.com/html/?{qs}"
    with _SEARCH_GLOBAL_LOCK:
        try:
            raw_html = http_request(
                url,
                method="GET",
                headers={
                    "Accept": "text/html,application/xhtml+xml",
                    "Accept-Language": "en-US,en;q=0.9",
                    "Referer": "https://html.duckduckgo.com/",
                },
                timeout=18,
                raw=True,
            ).decode("utf-8", "replace")
        finally:
            time.sleep(0.6)

    results = []
    seen_urls = set()
    for block in re.split(r'<div[^>]+class="[^"]*\bresult\b[^"]*"[^>]*>', raw_html)[1:]:
        a_match = re.search(r'<a\b([^>]*\bresult__a\b[^>]*)>(.*?)</a>', block, re.S | re.I)
        if not a_match:
            continue
        attrs, raw_title = a_match.group(1), a_match.group(2)
        href_m = re.search(r'href=["\']([^"\']+)["\']', attrs, re.I)
        if not href_m:
            continue
        href = _unwrap_redirect_url(href_m.group(1))
        if not href.startswith(("http://", "https://")) or href in seen_urls:
            continue
        if platform and not is_valid_lead_url(platform, href):
            continue
        snip_m = re.search(r'class=["\'][^"\']*result__snippet[^"\']*["\'][^>]*>(.*?)</(?:a|div|span)>', block, re.S | re.I)
        raw_snip = snip_m.group(1) if snip_m else ""
        title = _short(raw_title, 180)
        snippet = _short(raw_snip, 500)
        if title or snippet:
            seen_urls.add(href)
            results.append({"url": href, "title": title, "snippet": snippet})
    return results


def _search_yahoo_html(dork_query, max_age_days=7, platform=""):
    btf = "d" if max_age_days <= 1 else ("w" if max_age_days <= 7 else "m")
    qs = urllib.parse.urlencode({"p": dork_query, "btf": btf, "ei": "UTF-8"})
    url = f"https://search.yahoo.com/search?{qs}"
    with _SEARCH_GLOBAL_LOCK:
        try:
            raw_html = http_request(
                url,
                method="GET",
                headers={
                    "Accept": "text/html,application/xhtml+xml",
                    "Accept-Language": "en-US,en;q=0.9",
                },
                timeout=18,
                raw=True,
            ).decode("utf-8", "replace")
        finally:
            time.sleep(0.6)

    results = []
    seen_urls = set()
    for block in re.split(r'<div[^>]+class="[^"]*\balgo\b[^"]*"[^>]*>', raw_html)[1:]:
        a_match = re.search(r'<a\b[^>]*href=["\']([^"\']+)["\'][^>]*>(.*?)</a>', block, re.S | re.I)
        if not a_match:
            continue
        href = _unwrap_redirect_url(a_match.group(1))
        if not href.startswith(("http://", "https://")) or href in seen_urls:
            continue
        if platform and not is_valid_lead_url(platform, href):
            continue
        raw_title = a_match.group(2)
        snip_m = re.search(r'<div[^>]+class=["\'][^"\']*compText[^"\']*["\'][^>]*>(.*?)</div>', block, re.S | re.I)
        raw_snip = snip_m.group(1) if snip_m else ""
        title = _short(raw_title, 180)
        snippet = _short(raw_snip, 500)
        if title or snippet:
            seen_urls.add(href)
            results.append({"url": href, "title": title, "snippet": snippet})
    return results


def _search_public_index(dork_query, max_age_days=7, platform=""):
    hits = []
    errors = []
    for fn in (_search_duckduckgo_html, _search_yahoo_html):
        try:
            res = fn(dork_query, max_age_days=max_age_days, platform=platform)
            if res:
                hits.extend(res)
                break
        except ScanError as e:
            errors.append(str(e))
    dedup, seen = [], set()
    for h in hits:
        if h["url"] not in seen and is_valid_lead_url(platform, h["url"]):
            seen.add(h["url"])
            dedup.append(h)
    return dedup, errors


def _scan_public_social(platform, label, dork_prefixes, ctx):
    loc_term = ctx.location if (ctx.location and ctx.location.lower() != "any") else "Philippines"
    is_loc_scoped = bool(ctx.location and ctx.location.lower() != "any")

    queries = []
    custom_qs = ctx.settings.get("custom_queries") or []
    for prefix in dork_prefixes:
        if ctx.query:
            queries.append(f'{prefix} {loc_term} {ctx.query}')
        elif custom_qs:
            q_joined = " OR ".join(f'"{q}"' for q in custom_qs[:4])
            queries.append(f'{prefix} {loc_term} ({q_joined})')
        else:
            if "seeker" in ctx.intents:
                queries.append(f'{prefix} {loc_term} "nangita kog trabaho" OR "looking for work" OR "interested po" OR "for hire"')
            if "employer" in ctx.intents:
                queries.append(f'{prefix} {loc_term} "we are hiring" OR "urgent hiring" OR "job hiring"')

    items, errors, fetched = [], [], 0
    seen_urls = set()
    now_ts = get_reference_now()

    for dork in queries[:3]:
        if ctx.is_cancelled():
            return result("cancelled", "Cancelled by user.", items, fetched)
        hits, errs = _search_public_index(dork, max_age_days=ctx.max_age_days, platform=platform)
        errors.extend(errs)
        for h in hits:
            if h["url"] in seen_urls or not is_valid_lead_url(platform, h["url"]):
                continue
            seen_urls.add(h["url"])
            fetched += 1
            combined = f"{h['title']} {h['snippet']}".lower()
            is_comment = any(k in combined for k in ("interested po", "how to apply", "pwede pa mo apply"))
            kind = "comment" if is_comment else "post"
            src_name = f"{label} {'Comment' if kind == 'comment' else 'Post'}"
            items.append(
                item(
                    platform=platform,
                    kind=kind,
                    source=src_name,
                    external_id=f"{platform}_{stable_id(h['url'])}",
                    text=h["snippet"] or h["title"],
                    author=f"{label} User",
                    url=h["url"],
                    posted_ts=now_ts,
                    title=h["title"],
                    scoped=is_loc_scoped or location_scoped(combined, ctx.location, ctx.settings),
                )
            )

    note = ""
    if not items and not errors:
        note = f"0 public {label} post links indexed for this filter."
    return _finish(items, fetched, errors if not items else [], note=note)


def get_registered_adapters(config=None):
    settings = get_settings(config)
    out = []
    for k, v in PLATFORM_ADAPTERS.items():
        ok, hint = adapter_readiness(k, settings)
        out.append({"key": k, "label": v["label"], "description": v["description"],
                    "configured": ok, "hint": hint, "version": SCANNER_VERSION})
    return out


# =====================================================================
# REDDIT (Direct .rss by default; OAuth JSON if credentials configured)
# =====================================================================

def _listing(data):
    return (data or {}).get("data", {}).get("children", []) if isinstance(data, dict) else []


def _reddit_post_item(d, sub, ctx, force_scoped=False):
    return item(
        "reddit", "post", f"Reddit r/{d.get('subreddit') or sub}", f"reddit_post_{d.get('id')}",
        d.get("selftext", ""), f"u/{d.get('author', 'unknown')}",
        "https://www.reddit.com" + d.get("permalink", ""), to_epoch(d.get("created_utc")),
        title=d.get("title", ""),
        scoped=force_scoped or location_scoped(d.get("subreddit") or sub, ctx.location, ctx.settings),
    )


def _reddit_comment_item(d, sub, ctx, parent_title="", parent_text="", parent_url="", force_scoped=False):
    author = d.get("author", "")
    if not author or author in ("AutoModerator", "[deleted]") or d.get("body") in ("[deleted]", "[removed]"):
        return None
    link_title = d.get("link_title") or parent_title or "Reddit thread"
    return item(
        "reddit", "comment", f"Reddit Comment (r/{d.get('subreddit') or sub})",
        f"reddit_comment_{d.get('id')}", d.get("body", ""), f"u/{author}",
        "https://www.reddit.com" + d.get("permalink", ""), to_epoch(d.get("created_utc")),
        title=f'Comment on "{_short(link_title, 90)}"',
        parent_text=f"{link_title} {parent_text}", parent_url=parent_url,
        scoped=force_scoped or location_scoped(d.get("subreddit") or sub, ctx.location, ctx.settings),
    )


def _reddit_t(days):
    return "day" if days <= 1 else "week" if days <= 7 else "month" if days <= 31 else "year"


@register_adapter("reddit_posts", "Reddit Posts",
                  "Newest posts & targeted search in your subreddits.")
def adapter_reddit_posts(ctx):
    client = RedditClient(ctx.settings)
    items, errors, fetched = [], [], 0
    t_win = _reddit_t(ctx.max_age_days)
    subs = ctx.settings["subreddits"] or ["Cebu", "phclassifieds", "buhaydigital"]
    multi_sub = "+".join(subs)
    loc_prefix = f"{ctx.location} " if ctx.location.lower() != "any" else ""
    if ctx.query:
        search_q = f"{loc_prefix}{ctx.query}".strip()
    else:
        search_q = f"{loc_prefix}(hiring OR trabaho OR job OR work OR apply OR \"for hire\")"

    if client.has_oauth:
        try:
            posts = _listing(client.get(f"/r/{multi_sub}/search", {
                "q": search_q, "restrict_sr": 1, "sort": "new", "t": t_win, "limit": 75
            }))
            for p in posts:
                d = p.get("data", {})
                if d.get("id"):
                    fetched += 1
                    items.append(_reddit_post_item(d, d.get("subreddit") or subs[0], ctx, force_scoped=True))
            return _finish(items, fetched, errors)
        except ScanError as e:
            errors.append(str(e))

    seen_ids = set()
    for path, params, force_scoped in [
        (f"/r/{multi_sub}/new", {"limit": 100}, False),
        (f"/r/{multi_sub}/search", {"q": search_q, "restrict_sr": 1, "sort": "new", "t": t_win, "limit": 75}, True),
    ]:
        try:
            rss_entries = client.get_rss_entries(path, params)
            for e in rss_entries:
                if e["id"] in seen_ids:
                    continue
                seen_ids.add(e["id"])
                fetched += 1
                items.append(
                    item(
                        "reddit", "post", f"Reddit r/{e['subreddit']}", f"reddit_post_{e['id']}",
                        e["text"], e["author"], e["url"], e["posted_ts"],
                        title=e["title"],
                        scoped=force_scoped or location_scoped(e["subreddit"] + " " + e["title"] + " " + e["text"], ctx.location, ctx.settings),
                    )
                )
        except ScanError as rss_err:
            errors.append(f"Reddit Posts: {rss_err}")

    return _finish(items, fetched, errors)


@register_adapter("reddit_comments", "Reddit Comments",
                  "Newest comments + reply trees in your subreddits.")
def adapter_reddit_comments(ctx):
    client = RedditClient(ctx.settings)
    max_threads = ctx.settings["comment_threads_per_platform"]
    subs = ctx.settings["subreddits"] or ["Cebu", "phclassifieds", "buhaydigital"]
    multi_sub = "+".join(subs)
    items, errors, fetched = [], [], 0

    if client.has_oauth:
        try:
            for c in _listing(client.get(f"/r/{multi_sub}/comments", {"limit": 100})):
                if c.get("kind") == "t1":
                    fetched += 1
                    d = c.get("data", {})
                    it = _reddit_comment_item(d, d.get("subreddit") or subs[0], ctx)
                    if it:
                        items.append(it)
            return _finish(items, fetched, errors)
        except ScanError as e:
            errors.append(str(e))

    try:
        comment_entries = client.get_rss_entries(f"/r/{multi_sub}/comments", {"limit": 100})
        for e in comment_entries:
            fetched += 1
            items.append(
                item(
                    "reddit", "comment", f"Reddit Comment (r/{e['subreddit']})",
                    f"reddit_comment_{e['id']}", e["text"], e["author"], e["url"],
                    e["posted_ts"], title=_short(e["title"], 90),
                    parent_text=e["title"],
                    scoped=location_scoped(e["subreddit"] + " " + e["title"] + " " + e["text"], ctx.location, ctx.settings),
                )
            )
    except ScanError as rss_err:
        errors.append(f"Comment stream: {rss_err}")

    try:
        recent_posts = client.get_rss_entries(f"/r/{multi_sub}/new", {"limit": 100})
        job_threads = [
            p for p in recent_posts
            if ctx.intent_of(f"{p['title']} {p['text']}") in ("seeker", "employer")
        ]
        for t_entry in job_threads[:max_threads]:
            t_path = urllib.parse.urlparse(t_entry["url"]).path
            if not t_path or "/comments/" not in t_path:
                continue
            try:
                replies = client.get_rss_entries(t_path, {"limit": 100})
                for idx, r_entry in enumerate(replies):
                    if idx == 0:
                        continue
                    fetched += 1
                    items.append(
                        item(
                            "reddit", "comment", f"Reddit Comment (r/{r_entry['subreddit']})",
                            f"reddit_comment_{r_entry['id']}", r_entry["text"], r_entry["author"],
                            r_entry["url"], r_entry["posted_ts"],
                            title=f'Comment on "{_short(t_entry["title"], 85)}"',
                            parent_text=f"{t_entry['title']} {t_entry['text']}",
                            parent_url=t_entry["url"],
                            scoped=location_scoped(r_entry["subreddit"] + " " + t_entry["title"] + " " + r_entry["text"], ctx.location, ctx.settings),
                        )
                    )
            except ScanError:
                continue
    except ScanError:
        pass

    return _finish(items, fetched, errors)


# =====================================================================
# FACEBOOK (Apify Deep Group/Page/Comment Scraper + Public Index)
# =====================================================================

def _name(v):
    return v.get("name") if isinstance(v, dict) else v


def _extract_fb_post_content(post):
    parts = []
    raw_title = str(pick(post, "title", "postTitle", "marketplaceTitle", "name") or "").strip()
    price = str(pick(post, "formattedPrice", "price", "marketplacePrice") or "").strip()
    if price and price not in raw_title:
        raw_title = f"{raw_title} ({price})".strip()

    main_text = str(pick(post, "text", "message", "postText", "caption", "description") or "").strip()
    if main_text:
        parts.append(main_text)

    for att_key in ("attachments", "media"):
        att_list = post.get(att_key)
        if isinstance(att_list, list):
            for att in att_list:
                if not isinstance(att, dict):
                    continue
                # Skip automatic AI image alt-text ("May be an image of...")
                for f_key in ("title", "name", "description", "text", "caption"):
                    val = str(att.get(f_key) or "").strip()
                    if not val or val.lower().startswith("may be an image of"):
                        continue
                    if val not in raw_title and val not in parts:
                        if not raw_title and f_key in ("title", "name"):
                            raw_title = val
                        else:
                            parts.append(val)

    shared = post.get("sharedPost")
    if isinstance(shared, dict):
        for f_key in ("title", "text", "message", "description"):
            val = str(shared.get(f_key) or "").strip()
            if val and val not in parts:
                parts.append(val)

    body = "\n".join(parts).strip()
    if not raw_title and body:
        raw_title = _short(body.split("\n")[0], 110)
    if not body and raw_title:
        body = raw_title
    return raw_title, body


def _fb_post_item(post, ctx, page_mode=False):
    title, text = _extract_fb_post_content(post)
    url = pick(post, "url", "postUrl", "facebookUrl", "link")
    if not url or not (text or title):
        return None
    if not is_valid_lead_url("facebook", url):
        return None
    pid = pick(post, "postId", "id", "legacyId") or stable_id(url)
    author = _name(pick(post, "user", "author", "authorName", "pageName")) or "Facebook user"
    where = pick(post, "groupTitle", "groupName", "pageName") or ""
    if not where:
        inp = str(pick(post, "inputUrl", "facebookUrl", "groupUrl") or "")
        m = re.search(r"/groups/([^/?#]+)", inp or url)
        if m:
            where = m.group(1)
    source = (f"Facebook Page ({where})" if page_mode else f"Facebook Group ({where})") if where else "Facebook"
    return item(
        "facebook", "post", source, f"fb_post_{pid}", text, author, url,
        to_epoch(pick(post, "time", "timestamp", "date", "creation_time", "publishedAt")),
        title=title,
        scoped=True,
        from_configured_source=True,
    )


def _fb_comment_item(c, parent, ctx):
    text = pick(c, "text", "message", "body") or ""
    url = pick(c, "commentUrl", "url") or (parent or {}).get("url")
    if not text or not url or not is_valid_lead_url("facebook", url):
        return None
    cid = pick(c, "id", "commentId", "legacyId") or stable_id(url, text)
    author = _name(pick(c, "profileName", "commenterName", "author", "user", "name")) or "Facebook user"
    p_title = (parent or {}).get("title") or (parent or {}).get("text") or pick(c, "postTitle") or "Facebook post"
    group = ((parent or {}).get("source") or "").replace("Facebook ", "")
    return item(
        "facebook", "comment", f"Facebook Comment {group}".strip(), f"fb_comment_{cid}",
        text, author, url, to_epoch(pick(c, "date", "timestamp", "created_time", "time")),
        title=f'Comment on "{_short(p_title, 90)}"',
        parent_text=f"{p_title} {(parent or {}).get('text', '')}",
        parent_url=(parent or {}).get("url", ""),
        scoped=True,
        from_configured_source=True,
    )


def _url_group_key(u):
    m = re.search(r"/groups/([^/?#]+)", str(u or "").lower())
    return m.group(1) if m else str(u or "").lower().rstrip("/")


def _post_matches_configured_groups(post, configured_keys):
    if not configured_keys:
        return False
    for field in ("inputUrl", "facebookUrl", "groupUrl", "url", "postUrl"):
        val = pick(post, field)
        if val and _url_group_key(val) in configured_keys:
            return True
    return False


@register_adapter("facebook", "Facebook",
                  "Newest posts + comments in your configured public Facebook groups/pages.",
                  needs="apify")
def adapter_facebook(ctx):
    s = ctx.settings
    if not s["apify_token"] or not (s["facebook_groups"] or s["facebook_pages"]):
        return _scan_public_social(
            "facebook", "Facebook",
            ["site:facebook.com/groups", "site:facebook.com"],
            ctx,
        )
    token, limit = s["apify_token"], s["results_per_source"]
    items, errors, fetched, threads = [], [], 0, []
    seen_post_ids = set()
    configured_keys = {_url_group_key(u) for u in s["facebook_groups"]}

    def ingest_fb_posts(data_list, page_mode=False):
        nonlocal fetched
        for post in data_list:
            post_it = _fb_post_item(post, ctx, page_mode)
            if not post_it or post_it["external_id"] in seen_post_ids:
                continue
            seen_post_ids.add(post_it["external_id"])
            fetched += 1
            items.append(post_it)
            embedded = pick(post, "topComments", "comments", "latestComments")
            for c in embedded if isinstance(embedded, list) else []:
                ci = _fb_comment_item(c, post_it, ctx)
                if ci:
                    fetched += 1
                    items.append(ci)
            n_comments = pick(post, "commentsCount", "comments_count")
            if (isinstance(n_comments, int) and n_comments > 0 and ctx.is_recent(post_it["posted_ts"])
                    and ctx.intent_of(f"{post_it['title']} {post_it['text']}") in ("employer", "seeker", "seller", "buyer")):
                threads.append(post_it)

    # 1. Only pull cached items that belong to the CURRENTLY configured facebook_groups in Settings!
    cached_all, latest_age_s = apify_fetch_recent_runs(APIFY_ACTORS["facebook_groups"], token, max_runs=2)
    cached_matching = [p for p in cached_all if _post_matches_configured_groups(p, configured_keys)]
    if cached_matching:
        ingest_fb_posts(cached_matching, page_mode=False)

    covered_keys = {
        _url_group_key(pick(p, "inputUrl", "facebookUrl", "groupUrl", "url"))
        for p in cached_matching
    }
    missing_groups = [u for u in s["facebook_groups"] if _url_group_key(u) not in covered_keys]

    # 2. Run a fresh Apify scrape for any newly added group or if the last run is >10 minutes old
    jobs = []
    if s["facebook_groups"] and (missing_groups or latest_age_s > 600 or not cached_matching):
        target_groups = missing_groups if (missing_groups and latest_age_s <= 600) else s["facebook_groups"]
        jobs.append((APIFY_ACTORS["facebook_groups"], False, {
            "startUrls": [{"url": u} for u in target_groups], "resultsLimit": limit,
            "viewOption": "CHRONOLOGICAL", "onlyPostsNewerThan": ctx.since_phrase()}))
    if s["facebook_pages"]:
        jobs.append((APIFY_ACTORS["facebook_pages"], True, {
            "startUrls": [{"url": u} for u in s["facebook_pages"]], "resultsLimit": limit,
            "onlyPostsNewerThan": ctx.since_phrase()}))

    for actor, page_mode, run_input in jobs:
        if ctx.is_cancelled():
            return result("cancelled", "Cancelled by user.", items, fetched)
        try:
            data = apify_run(actor, run_input, token, ctx=ctx)
            ingest_fb_posts(data, page_mode=page_mode)
        except ScanCancelled:
            return result("cancelled", "Cancelled by user.", items, fetched)
        except ScanError as e:
            errors.append(str(e))

    if ctx.is_cancelled():
        return result("cancelled", "Cancelled by user.", items, fetched)

    # 3. Only ingest comments whose parent thread is in `threads` (from the currently configured groups)
    by_url = {t["url"]: t for t in threads}
    cached_comments, comment_age_s = apify_fetch_recent_runs(APIFY_ACTORS["facebook_comments"], token, max_runs=2)
    for c in cached_comments:
        parent = by_url.get(pick(c, "inputUrl", "facebookUrl", "postUrl"))
        if not parent:
            continue
        ci = _fb_comment_item(c, parent, ctx)
        if ci:
            fetched += 1
            items.append(ci)

    unscraped_threads = [t for t in threads if t["url"] not in {pick(c, "inputUrl", "facebookUrl", "postUrl") for c in cached_comments}]
    unscraped_threads = unscraped_threads[: s["comment_threads_per_platform"]]
    if unscraped_threads and not ctx.is_cancelled():
        try:
            data = apify_run(APIFY_ACTORS["facebook_comments"], {
                "startUrls": [{"url": t["url"]} for t in unscraped_threads],
                "resultsLimit": s["comments_per_thread"], "includeNestedComments": True,
                "viewOption": "RANKED_UNFILTERED"}, token, ctx=ctx)
            for c in data:
                parent = by_url.get(pick(c, "inputUrl", "facebookUrl", "postUrl")) or \
                    (unscraped_threads[0] if len(unscraped_threads) == 1 else None)
                ci = _fb_comment_item(c, parent, ctx)
                if ci:
                    fetched += 1
                    items.append(ci)
        except ScanCancelled:
            return result("cancelled", "Cancelled by user.", items, fetched)
        except ScanError as e:
            errors.append(f"comments: {e}")

    return _finish(items, fetched, errors)


# =====================================================================
# INSTAGRAM (Apify + Domain/Path-Verified Public Index)
# =====================================================================

def _ig_post_url(post):
    url = pick(post, "url")
    code = pick(post, "shortCode", "shortcode")
    return url or (f"https://www.instagram.com/p/{code}/" if code else None)


def _ig_comment_item(c, parent, ctx):
    text = pick(c, "text") or ""
    cid = pick(c, "id")
    post_url = (parent or {}).get("url") or pick(c, "postUrl", "inputUrl")
    if not text or not post_url or not is_valid_lead_url("instagram", post_url):
        return None
    url = f"{post_url.rstrip('/')}/c/{cid}/" if cid else post_url
    p_text = (parent or {}).get("text", "")
    return item("instagram", "comment", "Instagram Comment", f"ig_comment_{cid or stable_id(post_url, text)}",
                text, "@" + str(pick(c, "ownerUsername", "owner.username") or "unknown"), url,
                to_epoch(pick(c, "timestamp", "created_at")),
                title=f'Comment on "{_short(p_text or "Instagram post", 90)}"', parent_text=p_text,
                parent_url=post_url, scoped=(parent or {}).get("scoped", False))


@register_adapter("instagram", "Instagram",
                  "Newest posts + comments on Instagram (strictly verified instagram.com/p/ & /reel/ links).", needs="apify")
def adapter_instagram(ctx):
    s = ctx.settings
    if not s["apify_token"] or not s["instagram_hashtags"]:
        return _scan_public_social(
            "instagram", "Instagram",
            ["site:instagram.com/p/", "site:instagram.com/reel/"],
            ctx,
        )
    token = s["apify_token"]
    items, errors, fetched, threads = [], [], 0, []
    try:
        data, age_s = apify_fetch_recent_runs(APIFY_ACTORS["instagram_hashtags"], token, max_runs=1)
        if ctx.is_cancelled():
            return result("cancelled", "Cancelled by user.", items, fetched)
        if not data or age_s > 600:
            data = apify_run(APIFY_ACTORS["instagram_hashtags"], {
                "hashtags": s["instagram_hashtags"], "resultsLimit": s["results_per_source"],
                "resultsType": "posts", "onlyPostsNewerThan": ctx.since_phrase()}, token, ctx=ctx)
    except ScanCancelled:
        return result("cancelled", "Cancelled by user.", items, fetched)
    except ScanError as e:
        return result("error", str(e))

    for post in data:
        url = _ig_post_url(post)
        if not url or not is_valid_lead_url("instagram", url):
            continue
        fetched += 1
        tags = " ".join(pick(post, "hashtags") or []) + " " + str(pick(post, "inputUrl", "queryTag") or "")
        post_it = item("instagram", "post", "Instagram Post",
                       f"ig_post_{pick(post, 'id', 'shortCode') or stable_id(url)}",
                       pick(post, "caption") or "", "@" + str(pick(post, "ownerUsername") or "unknown"),
                       url, to_epoch(pick(post, "timestamp")),
                       scoped=location_scoped(tags, ctx.location, ctx.settings) or True,
                       from_configured_source=True)
        items.append(post_it)
        latest = pick(post, "latestComments") or []
        for c in latest if isinstance(latest, list) else []:
            ci = _ig_comment_item(c, post_it, ctx)
            if ci:
                fetched += 1
                items.append(ci)
        n = pick(post, "commentsCount") or 0
        if (isinstance(n, int) and n > len(latest) and ctx.is_recent(post_it["posted_ts"])
                and ctx.intent_of(post_it["text"]) == "employer"):
            threads.append(post_it)

    return _finish(items, fetched, errors)


# =====================================================================
# TIKTOK (Apify + Domain/Path-Verified Public Index)
# =====================================================================

def _tt_comment_item(c, parent, ctx):
    text = pick(c, "text") or ""
    video_url = pick(c, "videoWebUrl") or (parent or {}).get("url")
    if not text or not video_url or not is_valid_lead_url("tiktok", video_url):
        return None
    p_text = (parent or {}).get("text", "")
    return item("tiktok", "comment", "TikTok Comment",
                f"tt_comment_{pick(c, 'cid', 'id') or stable_id(video_url, text)}",
                text, "@" + str(pick(c, "uniqueId", "user.uniqueId") or "unknown"), video_url,
                to_epoch(pick(c, "createTimeISO", "createTime")),
                title=f'Comment on "{_short(p_text or "TikTok video", 90)}"', parent_text=p_text,
                parent_url=video_url, scoped=True, from_configured_source=True)


@register_adapter("tiktok", "TikTok",
                  "Newest videos + comments on TikTok (strictly verified tiktok.com video/tag links).",
                  needs="apify")
def adapter_tiktok(ctx):
    s = ctx.settings
    if not s["apify_token"] or not (s["tiktok_search_queries"] or s["tiktok_hashtags"] or ctx.query):
        return _scan_public_social(
            "tiktok", "TikTok",
            ["site:tiktok.com"],
            ctx,
        )
    token = s["apify_token"]
    queries = [("ram" if q.lower() == "rame" else q) for q in s["tiktok_search_queries"]]
    if ctx.query:
        q_clean = "ram" if ctx.query.lower() == "rame" else ctx.query
        queries.insert(0, q_clean if ctx.location.lower() == "any" else f"{q_clean} {ctx.location}")
    run_input = {"resultsPerPage": s["results_per_source"], "shouldDownloadVideos": False,
                 "shouldDownloadCovers": False, "shouldDownloadSubtitles": False,
                 "shouldDownloadSlideshowImages": False}
    if queries:
        run_input["searchQueries"] = queries
    if s["tiktok_hashtags"]:
        run_input["hashtags"] = s["tiktok_hashtags"]

    items, errors, fetched, threads = [], [], 0, []
    try:
        data, age_s = apify_fetch_recent_runs(APIFY_ACTORS["tiktok_search"], token, max_runs=2)
        if ctx.is_cancelled():
            return result("cancelled", "Cancelled by user.", items, fetched)
        if not data or age_s > 600:
            data = apify_run(APIFY_ACTORS["tiktok_search"], run_input, token, ctx=ctx)
    except ScanCancelled:
        return result("cancelled", "Cancelled by user.", items, fetched)
    except ScanError as e:
        return result("error", str(e))
    for v in data:
        url = pick(v, "webVideoUrl")
        if not url or not is_valid_lead_url("tiktok", url):
            continue
        fetched += 1
        video = item("tiktok", "post", "TikTok Video", f"tt_video_{pick(v, 'id') or stable_id(url)}",
                     pick(v, "text") or "", "@" + str(pick(v, "authorMeta.name") or "unknoown"), url,
                     to_epoch(pick(v, "createTimeISO", "createTime")),
                     scoped=True, from_configured_source=True)
        items.append(video)
        n = pick(v, "commentCount") or 0
        if (isinstance(n, int) and n > 0 and ctx.is_recent(video["posted_ts"])
                and ctx.intent_of(video["text"]) in ("employer", "seeker")):
            threads.append(video)

    cached_comments, _ = apify_fetch_recent_runs(APIFY_ACTORS["tiktok_comments"], token, max_runs=2)
    by_url = {t["url"]: t for t in threads}
    for c in cached_comments:
        ci = _tt_comment_item(c, by_url.get(pick(c, "videoWebUrl")), ctx)
        if ci:
            fetched += 1
            items.append(ci)

    return _finish(items, fetched, errors)


# =====================================================================
# PUBLIC RSS / ATOM FEEDS + JOB BOARD WEB SEARCH (free)
# =====================================================================

@register_adapter("public_web", "Feeds / Web", "RSS/Atom feeds + Philippine job board search (Mynimo, JobStreet, Indeed, OnlineJobs).")
def adapter_public_web(ctx):
    items, errors, fetched = [], [], 0
    client = RedditClient(ctx.settings)

    for feed in ctx.settings["rss_feeds"]:
        url = feed.get("url") if isinstance(feed, dict) else str(feed)
        name = (feed.get("name") if isinstance(feed, dict) else None) or urllib.parse.urlparse(url).netloc
        try:
            if "reddit.com" in url:
                parsed_u = urllib.parse.urlparse(url)
                r_path = re.sub(r"\.rss$", "", parsed_u.path)
                r_params = {k: v[0] for k, v in urllib.parse.parse_qs(parsed_u.query).items()}
                for e in client.get_rss_entries(r_path, r_params):
                    fetched += 1
                    items.append(item("reddit", "post", f"Reddit r/{e['subreddit']}", f"reddit_post_{e['id']}",
                                      e["text"], e["author"], e["url"], e["posted_ts"],
                                      title=e["title"],
                                      scoped=location_scoped(e["subreddit"] + " " + e["title"] + " " + e["text"], ctx.location, ctx.settings)))
            else:
                root = ET.fromstring(http_request(url, headers={"Accept": "application/rss+xml, application/atom+xml, */*"}, raw=True))
                for entry in root.findall(".//item") or root.findall(f".//{ATOM}entry"):
                    link = entry.findtext("link") or ""
                    if not link:
                        el = entry.find(f"{ATOM}link")
                        link = el.attrib.get("href", "") if el is not None else ""
                    title = entry.findtext("title") or entry.findtext(f"{ATOM}title") or ""
                    desc = (entry.findtext("description") or entry.findtext(f"{ATOM}content")
                            or entry.findtext(f"{ATOM}summary") or "")
                    author = entry.findtext("author") or entry.findtext(f"{ATOM}author/{ATOM}name") or name
                    pub_ts = to_epoch(entry.findtext("pubDate") or entry.findtext(f"{ATOM}updated")
                                      or entry.findtext(f"{ATOM}published"))
                    if not link or not is_valid_lead_url("web", link):
                        continue
                    fetched += 1
                    items.append(item("web", "post", name, f"rss_{stable_id(link)}",
                                      re.sub(r"<[^>]+>", " ", desc).strip(), author, link, pub_ts,
                                      title=title, scoped=location_scoped(name, ctx.location, ctx.settings)))
        except (ScanError, ET.ParseError) as e:
            errors.append(f"{name}: {e}")

    loc_q = "Philippines" if ctx.location.lower() == "any" else ctx.location
    q_expr = ctx.query if ctx.query else "hiring OR job"
    for site_domain in ("mynimo.com", "jobstreet.com.ph", "ph.indeed.com", "onlinejobs.ph"):
        if ctx.is_cancelled():
            return result("cancelled", "Cancelled by user.", items, fetched)
        dork = f"site:{site_domain} {loc_q} {q_expr}"
        hits, errs = _search_public_index(dork, max_age_days=ctx.max_age_days, platform="web")
        errors.extend(errs)
        now_ts = get_reference_now()
        for h in hits:
            fetched += 1
            host = urllib.parse.urlparse(h["url"]).netloc.replace("www.", "")
            items.append(item("web", "post", f"Web ({host})", f"web_{stable_id(h['url'])}",
                              h["snippet"] or h["title"], host, h["url"], now_ts,
                              title=h["title"], scoped=(ctx.location.lower() != "any")))

    return _finish(items, fetched, errors if not items else [])


# =====================================================================
# SCAN MANAGER (background scans + progress)
# =====================================================================

class ScanManager:
    def __init__(self):
        self._lock = threading.Lock()
        self._scan_seq = 0
        self._cancel_event = None
        self._active_ctx = None
        self.last_finished_epoch = 0.0
        self.state = {"running": False, "cancelled": False, "finished_at": None, "adapters": {},
                      "new_total": 0, "matched_total": 0}

    def status(self):
        with self._lock:
            return json.loads(json.dumps(self.state))

    def _update(self, key=None, seq=None, **fields):
        with self._lock:
            if seq is not None and seq != self._scan_seq:
                return
            target = self.state["adapters"][key] if key else self.state
            target.update(fields)

    def start(self, config, params, trigger="manual"):
        platforms = [p for p in (params.get("platforms") or list(PLATFORM_ADAPTERS)) if p in PLATFORM_ADAPTERS]
        with self._lock:
            if self.state.get("running"):
                return False
            self._scan_seq += 1
            seq = self._scan_seq
            self._cancel_event = threading.Event()
            cancel_ev = self._cancel_event
            self.state = {
                "running": True, "cancelled": False, "trigger": trigger,
                "started_at": utc_now_sql(), "finished_at": None,
                "params": {k: params.get(k) for k in ("query", "location", "max_age_days", "intents")},
                "adapters": {k: {"label": PLATFORM_ADAPTERS[k]["label"], "status": "queued",
                                 "message": "", "fetched": 0, "matched": 0, "new": 0} for k in platforms},
                "new_total": 0, "matched_total": 0,
            }
        threading.Thread(target=self._run, args=(config, params, platforms, seq, cancel_ev), daemon=True).start()
        return True

    def cancel(self):
        with self._lock:
            if not self.state.get("running"):
                return False
            self._scan_seq += 1
            if self._cancel_event:
                self._cancel_event.set()
            ctx = self._active_ctx
            self.state["running"] = False
            self.state["cancelled"] = True
            self.state["finished_at"] = utc_now_sql()
            for a in self.state["adapters"].values():
                if a.get("status") in ("queued", "running"):
                    a["status"] = "cancelled"
                    a["message"] = "Cancelled by user."
        if ctx:
            threading.Thread(target=ctx.abort_active_apify_runs, daemon=True).start()
        print("[scan] Cancelled by user.")
        return True

    def _run(self, config, params, platforms, seq, cancel_ev):
        ctx = ScanContext(config, params.get("query", ""), params.get("location", "Cebu"),
                          params.get("max_age_days", 7), params.get("intents"),
                          trigger=self.state.get("trigger", "manual"), cancel_event=cancel_ev)
        with self._lock:
            if seq == self._scan_seq:
                self._active_ctx = ctx

        def run_one(key):
            if cancel_ev.is_set():
                return key, result("cancelled", "Cancelled by user.")
            self._update(key, seq=seq, status="running")
            try:
                return key, PLATFORM_ADAPTERS[key]["handler"](ctx)
            except ScanCancelled:
                return key, result("cancelled", "Cancelled by user.")
            except Exception as e:
                return key, result("error", f"Unexpected error: {e}")

        try:
            with ThreadPoolExecutor(max_workers=max(1, len(platforms))) as pool:
                for fut in as_completed([pool.submit(run_one, k) for k in platforms]):
                    key, res = fut.result()
                    if cancel_ev.is_set() or seq != self._scan_seq:
                        continue
                    matched = new = 0
                    seen = set()
                    for raw in res["items"]:
                        if cancel_ev.is_set():
                            break
                        lead = evaluate_item(raw, ctx)
                        if not lead or lead["external_id"] in seen:
                            continue
                        seen.add(lead["external_id"])
                        is_saved = save_lead(**lead)
                        if lead_matches_active_filters(lead, ctx):
                            matched += 1
                            if is_saved:
                                new += 1
                    self._update(key, seq=seq, status=res["status"], message=res["message"],
                                 fetched=res["fetched"], matched=matched, new=new)
                    with self._lock:
                        if seq == self._scan_seq:
                            self.state["new_total"] += new
                            self.state["matched_total"] += matched
                    if res["status"] in ("error", "partial"):
                        print(f"[scan] {key}: {res['message']}")
        finally:
            self.last_finished_epoch = time.time()
            self._update(seq=seq, running=False, finished_at=utc_now_sql())
