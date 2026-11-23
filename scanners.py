"""
Unified Lead Scout – platform scanners (v3.6).

Each platform is one adapter function registered with @register_adapter.
Separates Job Leads ('seeker' & 'employer') from Buy & Sell Leads ('buyer' & 'seller')
so product/marketplace results never mix into Jobseeker or Employer Hiring views.
"""
import base64
import email.utils
import gzip
import hashlib
import html as html_lib
import json
import os
import re
import threading
import time
import unicodedata
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
    parse_search_query,
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
    "mangita trabaho", "ngita unta ko work", "ngita unta kog work", "ngita unta ko trabaho",
    "ngita unta kog trabaho", "nangita unta ko", "nangita unta kog",
    "naghahanap ng trabaho", "naghahanap ako ng trabaho", "naghahanap po ako ng trabaho",
    "naghahanap po ng trabaho", "hanap trabaho", "hanap po ako ng trabaho",
    "pwede mo apply", "pwede pa mo apply", "pwede ko mo apply",
    "pwede pa apply", "pwede mag apply", "unsaon pag apply", "paano mag apply",
    "asa dapit mo apply", "how to apply", "where to apply", "interested po",
    "interested ako", "interested here", "interested ko", "interested maam",
    "interested sir", "i'm interested", "im interested", "interested",
    "willing to start asap", "willing to start immediately", "willing to start",
    "can start immediately", "can start asap", "available immediately",
    "naay hiring", "naa bay hiring", "naa moy nahibaw-an nga hiring",
    "kinsa naay hiring", "kinsay naay hiring", "any hiring", "who is hiring",
    "anyone hiring", "anybody hiring", "still hiring", "hiring pa",
    "pa-aplya ko", "pa aplya ko", "paaplya ko",
    "pa apply", "apply ko", "apply ta", "pa refer", "how po", "no experience",
    "mo duty", "pm sir", "pm boss", "pm maam", "pm sent", "details po",
    "available pa po", "nag message ko", "nag pm ko", "check message",
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
    "walk in applicants", "nangita mi", "nangita kami", "ngita mi", "ngita kami",
    "ngita mig", "nangita mig", "nanginahanglan mi", "nanginahanglan kami",
    "naghahanap kami", "kailangan namin", "hiring staff", "hiring crew",
    "we need staff",
]

# Separate Seller & Buyer keywords (categorized strictly as 'seller' and 'buyer')
DEFAULT_SELLER_KEYWORDS = [
    "for sale", "fs:", "selling", "rush sale", "sale or swap", "fix price",
    "gpu for sale", "graphics card", "video card", "pc set", "system unit",
    "moving out sale", "garage sale", "clearance sale", "decluttering sale",
]

DEFAULT_BUYER_KEYWORDS = [
    "wtb", "want to buy", "lf:", "kuhaon dayon", "pila last price", "last price",
    "buying", "drop offers", "hm", "how much", "pila ni",
    "looking for gaming laptop", "looking for laptop", "looking for gpu",
    "looking for ram", "looking for pc",
]

DEFAULT_LOCATION_TERMS = {
    "cebu": [
        "cebu", "mandaue", "lapu-lapu", "lapulapu", "lapu lapu", "talisay", "consolacion",
        "liloan", "minglanilla", "carcar", "danao", "toledo", "it park", "banilad", "mabolo",
        "lahug", "guadalupe", "fuente", "mactan", "cordova", "sm seaside", "ayala", "talamban",
        "naga", "compostela", "colon", "osmena", "bantayan", "moalboal",
    ],
}

NON_CEBU_CITIES = (
    "manila", "manilam", "metro manila", "ncr", "makati", "quezon city", "qc", "marikina",
    "taguig", "bgc", "pasig", "ortigas", "alabang", "muntinlupa", "paranaque", "pasay",
    "mandaluyong", "caloocan", "valenzuela", "malabon", "navotas", "cavite", "laguna",
    "bacoor", "imus", "dasmarinas", "batangas", "rizal", "antipolo", "bulacan", "pampanga",
    "tarlac", "baguio", "lucena", "davao", "iloilo", "bacolod", "cagayan de oro", "cdo",
    "zamboanga", "gensan", "dlsu", "up diliman", "luxembourg", "south africa", "ballymena", "lautoka",
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

DEFAULT_BLOCKED_KEYWORDS = [
    "networking", "frontrow", "paluwagan", "online casino", "scatter",
    "crypto investment", "forex signal", "binary option", "task scam",
]


def _safe_int(val, default=0):
    try:
        if val in (None, ""):
            return default
        return int(val)
    except (ValueError, TypeError):
        return default


def _as_list(value):
    if isinstance(value, str):
        value = re.split(r"[\n,]", value)
    return [str(v).strip() for v in (value or []) if str(v).strip()]


def get_settings(config):
    config = config if isinstance(config, dict) else {}
    s = config.get("search_settings") if isinstance(config.get("search_settings"), dict) else {}
    social = config.get("social") if isinstance(config.get("social"), dict) else {}
    reddit = config.get("reddit") if isinstance(config.get("reddit"), dict) else {}
    providers = config.get("providers") if isinstance(config.get("providers"), dict) else {}
    raw_mode = str(providers.get("search_mode") or config.get("search_mode") or "auto").strip().lower()
    search_mode = raw_mode if raw_mode in ("auto", "alternative_only", "apify_only") else "auto"
    cache_mins = _safe_int(providers.get("apify_cache_minutes", config.get("apify_cache_minutes", 10)), 10)
    raw_blocked_kw = s.get("blocked_keywords") if "blocked_keywords" in s else config.get("blocked_keywords")
    blocked_keywords = [k.lower() for k in (_as_list(raw_blocked_kw) if raw_blocked_kw is not None else DEFAULT_BLOCKED_KEYWORDS)]
    raw_blocked_authors = s.get("blocked_authors") if "blocked_authors" in s else config.get("blocked_authors")
    blocked_authors = [re.sub(r"^(@|u/)", "", a.lower()) for a in _as_list(raw_blocked_authors)]
    autoscan_minutes = max(0, _safe_int(s.get("autoscan_minutes", config.get("autoscan_minutes", 0)), 0))
    desktop_notifications = bool(s.get("desktop_notifications", config.get("desktop_notifications", True)))
    alert_webhook_url = str(s.get("alert_webhook_url") or config.get("alert_webhook_url") or "").strip()
    # Filter out any buy/sell terms that might have been in config.json seeker/employer lists
    raw_seeker = [k for k in _as_list(s.get("seeker_keywords")) if not is_buy_sell_keyword(k)]
    raw_employer = [k for k in _as_list(s.get("employer_keywords")) if not is_buy_sell_keyword(k)]
    seeker_kw = list(dict.fromkeys(raw_seeker + DEFAULT_SEEKER_KEYWORDS))
    employer_kw = list(dict.fromkeys(raw_employer + DEFAULT_EMPLOYER_KEYWORDS))
    custom_queries = list(dict.fromkeys(
        _as_list(social.get("search_queries"))
        + _as_list(social.get("tiktok_search_queries"))
    ))
    raw_loc_terms = s.get("location_terms") if isinstance(s.get("location_terms"), dict) and s.get("location_terms") else DEFAULT_LOCATION_TERMS
    return {
        "location": str(s.get("location") or "Cebu"),
        "max_age_days": max(1, _safe_int(s.get("max_age_days", 7), 7)),
        "seeker_keywords": seeker_kw,
        "employer_keywords": employer_kw,
        "seller_keywords": list(DEFAULT_SELLER_KEYWORDS),
        "buyer_keywords": list(DEFAULT_BUYER_KEYWORDS),
        "blocked_keywords": blocked_keywords,
        "blocked_authors": blocked_authors,
        "autoscan_minutes": autoscan_minutes,
        "desktop_notifications": desktop_notifications,
        "alert_webhook_url": alert_webhook_url,
        "custom_queries": custom_queries,
        "location_terms": {str(k).lower(): v for k, v in raw_loc_terms.items()},
        "subreddits": [re.sub(r"^/?r/", "", x) for x in (_as_list(config.get("subreddits")) or ["Cebu", "phclassifieds", "buhaydigital"])],
        "reddit_client_id": str(reddit.get("client_id") or ""),
        "reddit_client_secret": str(reddit.get("client_secret") or ""),
        "apify_token": str(os.environ.get("APIFY_TOKEN") or config.get("apify_token") or "").strip(),
        "search_mode": search_mode,
        "apify_cache_seconds": max(60, cache_mins * 60),
        "gemini_api_key": str(os.environ.get("GEMINI_API_KEY") or providers.get("gemini_api_key") or config.get("gemini_api_key") or "").strip(),
        "gemini_model": str(providers.get("gemini_model") or config.get("gemini_model") or "gemini-3.5-flash-lite").strip(),
        "ai_filter_enabled": bool(providers.get("ai_filter_enabled", config.get("ai_filter_enabled", True))),
        "auto_archive_days": max(0, _safe_int(providers.get("auto_archive_days", s.get("auto_archive_days", config.get("auto_archive_days", 14))), 14)),
        "serper_api_key": str(os.environ.get("SERPER_API_KEY") or providers.get("serper_api_key") or config.get("serper_api_key") or "").strip(),
        "tavily_api_key": str(os.environ.get("TAVILY_API_KEY") or providers.get("tavily_api_key") or config.get("tavily_api_key") or "").strip(),
        "brave_api_key": str(os.environ.get("BRAVE_API_KEY") or providers.get("brave_api_key") or config.get("brave_api_key") or "").strip(),
        "custom_api_url": str(providers.get("custom_api_url") or config.get("custom_api_url") or "").strip(),
        "custom_api_key": str(providers.get("custom_api_key") or config.get("custom_api_key") or "").strip(),
        "facebook_groups": _as_list(social.get("facebook_groups")),
        "facebook_pages": _as_list(social.get("facebook_pages")),
        "instagram_hashtags": [t.lstrip("#") for t in _as_list(social.get("instagram_hashtags"))],
        "tiktok_search_queries": custom_queries,
        "tiktok_hashtags": [t.lstrip("#") for t in _as_list(social.get("tiktok_hashtags"))],
        "results_per_source": max(1, _safe_int(social.get("results_per_source", 30), 30)),
        "comment_threads_per_platform": max(0, _safe_int(social.get("comment_threads_per_platform", 3), 3)),
        "comments_per_thread": max(1, _safe_int(social.get("comments_per_thread", 50), 50)),
        "rss_feeds": config.get("rss_feeds") if isinstance(config.get("rss_feeds"), list) else [],
    }


def _norm(text):
    text = unicodedata.normalize("NFKC", text or "")
    text = text.replace("\u2019", "'").replace("\u2018", "'")
    low = text.lower()
    # Collapse dot/dash/space-obfuscated "H.I.R.I.N.G." or "H-I-R-I-N-G" used by recruiters
    low = re.sub(r"\bh[\s.\-_]+i[\s.\-_]+r[\s.\-_]+i[\s.\-_]+n[\s.\-_]+g\.?(?=\W|$)", "hiring", low)
    return re.sub(r"\s+", " ", low).strip()


def phrase_in(text_norm, phrase):
    p = _norm(phrase).strip("[]#:!.,? ")
    if not p:
        return False
    return re.search(r"(?<!\w)" + re.escape(p) + r"(?!\w)", text_norm) is not None


# Short comment-style phrases that ONLY classify as 'seeker' on comments (kind == 'comment').
# On full posts (kind == 'post'), employers frequently write "How to apply: send resume", "Comment 'interested po'", or "No experience required".
COMMENT_ONLY_SEEKER_PHRASES = {
    "interested po", "interested", "interested ako", "interested here",
    "interested ko", "interested maam", "interested sir", "i'm interested", "im interested",
    "how to apply", "paano mag apply", "pwede mo apply", "pwede pa mo apply",
    "pwede ko mo apply", "pwede pa apply", "pwede mag apply", "unsaon pag apply",
    "available pa po", "available pa", "pm sent", "dm sent", "details po",
    "how po", "pm sir", "pm boss", "pm maam", "nag message ko", "nag pm ko", "check message",
    "no experience", "still hiring", "hiring pa",
}

# Phrases that also appear inside employer qualification sections (e.g. "Qualifications: can start ASAP, no experience")
REQUIREMENT_LIKE_SEEKER_PHRASES = {
    "willing to start asap", "willing to start immediately", "willing to start",
    "can start immediately", "can start asap", "available immediately",
    "no experience", "still hiring", "hiring pa",
}

# Strong corporate / employer job-ad fingerprints that lock a post (kind == 'post') as 'employer'
EMPLOYER_VETO_PHRASES = (
    "career opportunity", "career opportunities", "next career",
    "join our team", "be part of our",
    "send your resume", "send resume", "email your cv", "email your resume",
    "send your cv", "submit your resume",
    "walk-in applicants", "walk in applicants",
    "apply now", "apply na", "now accepting applicants", "accepting applicants",
    "open positions", "open position", "job openings", "job opening",
    "job vacancy", "job vacancies",
    "qualifications:", "responsibilities:", "benefits:",
    "competitive salary", "how to apply:",
    "comment interested", "comment 'interested", 'comment "interested',
    "leading distributor", "leading company",
    "we are hiring", "we're hiring", "were hiring",
    "now hiring", "urgent hiring", "urgently hiring", "currently hiring",
    "hiring:", "we're looking for", "were looking for",
    "nangita ka og trabaho", "nangita ka ug trabaho", "naghahanap ka ba ng trabaho",
    "inviting to apply", "still ramping", "batch training",
    "csr position", "csr positions", "nonvoice and voice", "voice and nonvoice",
    "call center career", "one day process", "1 day process", "20k offer",
    "pm me to apply", "dm me to apply", "message us to apply",
)

EMPLOYER_VETO_PATTERNS = (
    re.compile(r"\b(?:careers|hr|hrd|recruitment|recruit|talent|jobs|hiring|apply)[a-z0-9._-]*@[a-z0-9.-]+\.[a-z]{2,}\b"),
    re.compile(r"\bjoin\s+(?:the\s+)?[a-z0-9][a-z0-9&'.-]{1,30}\s+(?:team|family|group|corp|inc|company|cebu|ph|philippines)\b"),
    re.compile(r"\bjoin\s+us\b"),
    re.compile(r"\b[a-z0-9][a-z0-9&'.-]{1,28}\s+(?:cebu|ph|philippines|company|corp|inc)?\s*is\s+(?:now\s+|urgently\s+|currently\s+)?(?:hiring|looking\s+for)\b"),
    re.compile(r"\blooking\s+for\s+(?:part[- ]?time\s+|full[- ]?time\s+)?(?:workers|applicants|candidates|staff|crew|customer\s+service|representatives|csr|tsr|agents|drivers|cashiers|baristas|helpers|cooks|nurses|engineers|technicians|sales\s+in[- ]?charge|person\s+in\s+charge)\b"),
)

CORPORATE_AUTHOR_PHRASES = (
    "group of companies", "talent acquisition",
)

CORPORATE_AUTHOR_WORDS = (
    "careers", "career", "hiring", "recruitment", "recruiting", "recruiter",
    "hr", "hrd", "staffing", "agency", "inc", "corp", "corporation",
    "official", "jobs", "solutions", "hotels", "condotels",
    "enterprise", "enterprises", "manpower",
)

FIRST_PERSON_START_RE = re.compile(
    r"^(?:\[?\s*for hire\s*\]?|hire me|i am looking for|i'm looking for|im looking for|"
    r"looking for (?:a )?(?:(?:part[- ]?time|full[- ]?time)\s+)?(?:job|work|side hustle|gig)s?|"
    r"nangita\s+(?:ko|kog|unta\s+ko)|ngita\s+(?:ko|kog|unta\s+ko)|"
    r"naghahanap(?:\s+po)?\s+ako|hanap(?:\s+po)?\s+ako|currently unemployed|unemployed for|"
    r"fresh grad|need (?:a )?(?:job|work|extra income|part[- ]?time\s+(?:job|work))|"
    r"offering (?:remote )?(?:services|coaching)|desperate to do anything|available for (?:any )?work)\b"
)


def has_employer_veto(text_norm):
    """Returns the matched employer/corporate job-ad fingerprint on a post, or ''."""
    if not text_norm:
        return ""
    for phrase in EMPLOYER_VETO_PHRASES:
        if phrase.endswith(":"):
            if phrase in text_norm:
                return phrase.rstrip(":")
        elif phrase_in(text_norm, phrase):
            return phrase
    for pat in EMPLOYER_VETO_PATTERNS:
        m = pat.search(text_norm)
        if m:
            matched_str = m.group(0).strip()
            # Guard against questions like "who is hiring" or "anyone is hiring"
            if re.search(r"\b(?:who|anyone|anybody|someone|what|which|if\s+you)\s+is\s+(?:hiring|looking\s+for)\b", text_norm):
                continue
            return matched_str[:60]
    return ""


def is_corporate_author(author):
    """Detects corporate/recruiting page names on posts (e.g. 'PCNI Careers', 'HR Zai', 'Cebu Condotels')."""
    a = _norm(author)
    if not a:
        return False
    a_clean = re.sub(r"^(@|u/)", "", a).strip()
    if any(p in a_clean for p in CORPORATE_AUTHOR_PHRASES):
        return True
    if re.match(r"^ta\s+[a-z]", a_clean):
        return True
    for w in CORPORATE_AUTHOR_WORDS:
        if re.search(r"(?<!\w)" + re.escape(w) + r"(?!\w)", a_clean):
            return True
    return False


def starts_with_first_person_seeker(text_norm):
    t = re.sub(r"^[^a-z0-9\[]+", "", (text_norm or "").strip())
    return bool(FIRST_PERSON_START_RE.search(t))


AMBIGUOUS_JOB_PHRASES = {
    "pm sent", "dm sent", "sent you a dm", "sent you a pm",
    "available pa", "available pa po", "naa pa ni", "qualifications", "requirements",
    "interested po", "interested ako", "interested here", "i'm interested", "im interested",
    "interested", "how po", "pm sir", "pm boss", "pm maam", "nag message ko",
    "nag pm ko", "check message", "details po",
}

UNAMBIGUOUS_JOB_WORDS = (
    "job", "work", "trabaho", "hiring", "apply", "applicant", "vacancy",
    "resume", "cv", "staff", "crew", "salary", "part time", "part-time",
    "full time", "full-time", "for hire", "hire me", "freelance", "remote",
    "gig", "gigs", "unemployed", "opening", "dishwasher", "barista",
    "cashier", "helper", "cook", "driver", "errand", "coach",
    "waiter", "waitress", "video editor", "graphic designer", "virtual assistant",
    "bookkeeper", "carpenter", "electrician", "plumber", "welder", "mason",
    "tindera", "yaya", "housekeeper", "caregiver", "encoder", "accountant",
    "career", "careers", "position", "positions",
)

JOB_ROLE_TERMS = (
    "dishwasher", "barista", "cashier", "helper", "cook", "driver", "waiter",
    "waitress", "service crew", "video editor", "graphic designer",
    "virtual assistant", "bookkeeper", "carpenter", "electrician", "plumber",
    "welder", "mason", "tindera", "yaya", "housekeeper", "caregiver",
    "encoder", "accountant", "staff", "crew",
)

MERCH_SALE_INDICATORS = (
    "for sale", "fs:", "sale or swap", "fix price", "rfs:", "reason for selling",
    "decluttering", "reposting until sold", "brand new and sealed",
    "slightly used", "good condition", "moving out sale", "garage sale", "clearance sale",
)


def _is_merch_sale_post(text_norm):
    if any(m in text_norm for m in MERCH_SALE_INDICATORS):
        return True
    if "still available" in text_norm and any(w in text_norm for w in ("size:", "size ", "price", "php", "₱", "pm if interested")):
        return True
    return False


def _classify_query_intent(text_norm, kind, q_str, author=""):
    """Determines whether a custom query match belongs to ('seeker'|'employer') or ('buyer'|'seller')."""
    q_low = q_str.strip().lower().rstrip("?")
    if is_buy_sell_keyword(q_low) or _is_merch_sale_post(text_norm):
        if kind == "comment" or any(phrase_in(text_norm, w) for w in ("lf", "wtb", "looking for", "buying", "kuhaon dayon")):
            return "buyer"
        return "seller"
    # Otherwise it's a job query
    if kind == "comment":
        if (is_corporate_author(author) or has_employer_veto(text_norm)) and not any(phrase_in(text_norm, p) for p in DEFAULT_SEEKER_KEYWORDS):
            return "employer"
        return "seeker"
    if has_employer_veto(text_norm):
        return "employer"
    if is_corporate_author(author) and not starts_with_first_person_seeker(text_norm):
        return "employer"
    if any(phrase_in(text_norm, p) for p in DEFAULT_SEEKER_KEYWORDS if p not in COMMENT_ONLY_SEEKER_PHRASES):
        return "seeker"
    if any(phrase_in(text_norm, p) for p in ("we are hiring", "now hiring", "urgent hiring", "is hiring", "are hiring", "looking for staff", "looking for crew", "job opening", "vacancy")):
        return "employer"
    if any(w in q_low for w in ("trabaho", "looking for work", "for hire", "naay hiring")):
        return "seeker"
    return "employer"


def classify_intent(text_norm, kind, settings, query="", full_context="", source_name="", author=""):
    """
    Returns ('seeker'|'employer'|'buyer'|'seller'|None, matched_phrase).
    Strictly separates Jobs ('seeker', 'employer') from Buy & Sell ('buyer', 'seller').
    Enforces Comment-Only seeker phrase guard, Strong Employer Veto, and Corporate Author Classifier on posts.
    """
    text_norm = _norm(text_norm)
    ctx_check = _norm(full_context) if full_context else text_norm
    src_low = (source_name or "").lower()
    is_merch_group = any(g in src_low for g in ("sales & repairs", "buy and sell", "buy & sell", "marketplace", "pc market"))
    has_merch_indicator = is_merch_group or _is_merch_sale_post(ctx_check)
    has_job_word = any(phrase_in(ctx_check, w) for w in UNAMBIGUOUS_JOB_WORDS)

    applicant_looking_m = re.search(
        r"\blooking\s+for\s+(?:a\s+)?(?:[a-z0-9/-]+(?:\s+(?:or|and)\s+[a-z0-9/-]+)?\s+){1,3}(?:job|work|gig|position)s?\b",
        text_norm,
    )
    # Exclude employer copy like "looking for your next career opportunity" or "looking for a ... position? apply now"
    if applicant_looking_m and re.search(r"\blooking\s+for\s+your\b", applicant_looking_m.group(0)):
        applicant_looking_m = None

    has_first_person_seeker = bool(
        applicant_looking_m
        or re.search(r"\b(?:for hire|hire me|hiring me|fresh grad ko|graduate of|experienced\s+[a-z]+\s+here|if you are hiring|who is hiring|anyone hiring|naa moy nahibaw-an|kinsa naay hiring|ngita unta ko|nangita kog|ngita kog|naghahanap(?:\s+po)?\s+ako)\b", text_norm)
        or (re.search(r"\b(?:po ako|ko po)\b", text_norm) and any(w in text_norm for w in ("looking for", "naghahanap", "apply", "trabaho", "job", "work")))
    )

    is_post = (kind or "post").lower() != "comment"
    veto_match = has_employer_veto(text_norm)
    corp_author = is_corporate_author(author)
    fp_start = starts_with_first_person_seeker(text_norm) if is_post else False

    # 1. Check pure Jobseeker & Employer Hiring keywords first (unless it's a pure merchandise sale without job words)
    if not (has_merch_indicator and not has_job_word):
        # Strong Corporate / Employer Veto Rule (locks posts to 'employer' before any seeker assignment)
        if is_post and veto_match and not fp_start:
            return "employer", veto_match

        s_hits = [
            p for p in settings["seeker_keywords"]
            if phrase_in(text_norm, p)
            and (p not in AMBIGUOUS_JOB_PHRASES or has_job_word)
            and (not is_post or p.lower() not in COMMENT_ONLY_SEEKER_PHRASES)
        ]
        if applicant_looking_m and not veto_match:
            matched_app_phrase = applicant_looking_m.group(0).strip()
            if matched_app_phrase not in s_hits:
                s_hits.insert(0, matched_app_phrase)

        e_hits = [
            p for p in settings["employer_keywords"]
            if phrase_in(text_norm, p) and (p not in AMBIGUOUS_JOB_PHRASES or has_job_word)
        ]

        # Author / Page Name Corporate Classifier (for kind == 'post')
        if is_post and corp_author and not fp_start:
            if e_hits or veto_match or s_hits or has_job_word:
                return "employer", (e_hits[0] if e_hits else (veto_match or (s_hits[0] if s_hits else "hiring")))

        if has_first_person_seeker and not veto_match:
            e_hits = [
                p for p in e_hits
                if not p.startswith("looking for ")
                and p not in ("hiring", "are hiring", "is hiring")
            ]
        else:
            if len(e_hits) > 1 and "hiring" in e_hits and any("hiring" in p and p != "hiring" for p in e_hits):
                e_hits = [p for p in e_hits if p != "hiring"]

        if not s_hits and not e_hits and not has_first_person_seeker:
            for role in JOB_ROLE_TERMS:
                if phrase_in(text_norm, role) and (
                    re.search(r"(?<!\w)lf\s*:?\s*", text_norm)
                    or re.search(r"\b(?:we\s+need|need\s+\d+|looking\s+for)\b", text_norm)
                ):
                    e_hits.append(f"lf: {role}" if "lf" in text_norm else f"looking for {role}")
                    break

        # If a post matched BOTH employer keywords AND only requirement-like seeker phrases (e.g. 'can start asap'),
        # it is an employer job ad, never a jobseeker
        if is_post and e_hits and s_hits and all(p.lower() in REQUIREMENT_LIKE_SEEKER_PHRASES for p in s_hits):
            return "employer", e_hits[0]

        if s_hits or e_hits or (not is_post and veto_match):
            if not is_post:
                # If a comment is from a corporate recruiter or has ONLY employer veto/hiring phrases (e.g. 'Pm me to apply now'), classify as 'employer'
                if not s_hits and (e_hits or veto_match):
                    return "employer", (e_hits[0] if e_hits else veto_match)
                if corp_author and (e_hits or veto_match) and not has_first_person_seeker:
                    return "employer", (e_hits[0] if e_hits else veto_match)
                return "seeker", (s_hits[0] if s_hits else e_hits[0])
            if s_hits and not e_hits:
                return "seeker", s_hits[0]
            if e_hits and not s_hits:
                return "employer", e_hits[0]
            if has_first_person_seeker and not veto_match:
                return "seeker", s_hits[0]
            return ("seeker", s_hits[0]) if len(s_hits) > len(e_hits) else ("employer", e_hits[0])

    # 2. Check active search bar query (if provided)
    pos_query, _ = parse_search_query(query)
    if pos_query and smart_query_matches(text_norm, query):
        clean_q = ("ram" if pos_query.strip().lower() == "rame" else pos_query.strip()).rstrip("?")
        return _classify_query_intent(text_norm, kind, clean_q, author=author), clean_q

    # 3. Check custom queries configured in Settings
    for cq in settings.get("custom_queries") or []:
        cq_clean = ("ram" if cq.strip().lower() == "rame" else cq.strip()).rstrip("?")
        if not cq_clean:
            continue
        if smart_query_matches(text_norm, cq_clean):
            intent_val = _classify_query_intent(text_norm, kind, cq_clean, author=author)
            if intent_val in ("seeker", "employer") and has_merch_indicator and not has_job_word:
                if kind == "comment":
                    return "buyer", cq_clean
                continue
            return intent_val, cq_clean

    # 4. Check Buy & Sell keywords ('buyer' and 'seller')
    b_hits = [p for p in settings["buyer_keywords"] if phrase_in(text_norm, p)]
    sel_hits = [p for p in settings["seller_keywords"] if phrase_in(text_norm, p)]
    if not sel_hits and is_post and _is_merch_sale_post(text_norm):
        sel_hits.append("for sale")
    if not b_hits and kind == "comment" and has_merch_indicator and not has_job_word:
        for merch_c_kw in ("interested po", "interested", "hm", "how much", "available pa", "last price", "pm sent"):
            if phrase_in(text_norm, merch_c_kw):
                b_hits.append(merch_c_kw)
                break
    if b_hits or sel_hits:
        if kind == "comment" or (b_hits and not sel_hits):
            return "buyer", (b_hits[0] if b_hits else sel_hits[0])
        return "seller", (sel_hits[0] if sel_hits else b_hits[0])

    return None, ""


def classify_stored_row(row, settings):
    """
    Re-classifies an existing stored lead row using the upgraded deterministic rules.
    Returns (new_intent, matched_phrase).
    """
    kind = (row.get("kind") or ("comment" if "comment" in (row.get("source") or "").lower() else "post")).lower()
    title = row.get("title") or ""
    body = row.get("content") or ""
    own_text = _norm(body if kind == "comment" else f"{title} {body}")
    full_ctx = _norm(f"{title} {body}")
    author = row.get("author") or ""
    source = row.get("source") or ""

    intent, kw = classify_intent(
        own_text, kind, settings,
        query="", full_context=full_ctx, source_name=source, author=author,
    )
    if intent in ("seeker", "employer", "buyer", "seller"):
        return intent, kw

    if kind == "post":
        if _is_merch_sale_post(own_text):
            return "seller", "for sale"
        veto = has_employer_veto(own_text)
        if veto and not starts_with_first_person_seeker(own_text):
            return "employer", veto
        if is_corporate_author(author) and not starts_with_first_person_seeker(own_text):
            return "employer", (row.get("matched_keyword") or "hiring")
    return row.get("intent") or "", row.get("matched_keyword") or ""


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


def _parse_search_ts(value):
    ts = to_epoch(value)
    if ts:
        return ts
    if not value:
        return None
    s = str(value).strip().lower()
    now_ts = get_reference_now()
    if s == "yesterday":
        return now_ts - 86400
    m = re.match(r"^(\d+)\s*(min|mins|minute|minutes|hr|hrs|hour|hours|day|days|wk|wks|week|weeks|mo|month|months)\s+ago$", s)
    if m:
        qty = int(m.group(1))
        unit = m.group(2)
        mult = 60 if unit.startswith("min") else 3600 if unit.startswith(("hr", "hour")) else 86400 if unit.startswith("day") else 604800 if unit.startswith(("wk", "week")) else 2592000
        return now_ts - qty * mult
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
            if (resp.headers.get("Content-Encoding") or "").lower() == "gzip":
                payload = gzip.decompress(payload)
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

    def _parse_json_entries(self, data):
        """Extracts normalized RSS-style entry dicts from Reddit .json payloads."""
        entries = []
        batches = data if isinstance(data, list) else [data]
        for b in batches:
            for child in _listing(b):
                if not isinstance(child, dict):
                    continue
                d = child.get("data") or {}
                cid = str(d.get("id") or "").strip()
                permalink = str(d.get("permalink") or "").strip()
                if not cid or not permalink:
                    continue
                link = f"https://www.reddit.com{permalink}" if permalink.startswith("/") else permalink
                title = html_lib.unescape(str(d.get("title") or d.get("link_title") or "Reddit thread")).strip()
                text = html_lib.unescape(str(d.get("selftext") or d.get("body") or title)).strip()
                author = str(d.get("author") or "reddit_user").strip()
                if not author.startswith("u/"):
                    author = f"u/{author}"
                entries.append({
                    "id": cid,
                    "title": title,
                    "text": text or title,
                    "url": link,
                    "author": author,
                    "posted_ts": to_epoch(d.get("created_utc")),
                    "subreddit": str(d.get("subreddit") or "Cebu"),
                })
        return entries

    def get_rss_entries(self, path, params=None):
        params = dict(params or {})
        base_path = "/" + path.strip("/")
        q_str = f"?{urllib.parse.urlencode(sorted(params.items()))}" if params else ""
        cache_key = f"{base_path}{q_str}"

        with _REDDIT_GLOBAL_LOCK:
            cached = _REDDIT_RSS_CACHE.get(cache_key)
            if cached and (time.time() - cached[0]) < 45:
                return list(cached[1])

            hosts = ["https://www.reddit.com", "https://old.reddit.com"]
            last_err = None
            parsed = None

            # 1. Try .rss across both Reddit hosts (validating XML inside loop)
            for host in hosts:
                for suffix in (f"{base_path}.rss{q_str}", f"{base_path}/.rss{q_str}"):
                    url = f"{host}{suffix}"
                    try:
                        raw_xml = http_request(
                            url,
                            headers={"Accept": "application/atom+xml, application/rss+xml, application/xml, */*"},
                            timeout=15,
                            raw=True,
                        )
                        parsed = parse_reddit_atom(raw_xml)
                        break
                    except ScanError as e:
                        last_err = e
                if parsed is not None:
                    break

            # 2. If .rss returned an HTML challenge/invalid XML, fall back to .json endpoint
            if parsed is None:
                json_params = dict(params, raw_json=1)
                jq_str = f"?{urllib.parse.urlencode(sorted(json_params.items()))}"
                for host in hosts:
                    j_url = f"{host}{base_path}.json{jq_str}"
                    try:
                        j_data = http_request(j_url, headers={"Accept": "application/json"}, timeout=15)
                        parsed = self._parse_json_entries(j_data)
                        if parsed:
                            break
                    except ScanError as e:
                        last_err = e

            time.sleep(0.5)
            if not parsed:
                raise last_err or ScanError("Reddit RSS/JSON unavailable")

            _REDDIT_RSS_CACHE[cache_key] = (time.time(), parsed)
            return list(parsed)


def parse_reddit_atom(raw_xml):
    if isinstance(raw_xml, bytes):
        head = raw_xml[:300].lstrip().lower()
        if head.startswith((b"<!doctype html", b"<html")):
            raise ScanError("Reddit returned an HTML challenge page instead of RSS XML")
        cleaned_xml = re.sub(rb"&(?!(?:amp|lt|gt|quot|apos|#\d+|#x[0-9a-fA-F]+);)", b"&amp;", raw_xml)
    else:
        head = (raw_xml or "")[:300].lstrip().lower()
        if head.startswith(("<!doctype html", "<html")):
            raise ScanError("Reddit returned an HTML challenge page instead of RSS XML")
        cleaned_xml = re.sub(r"&(?!(?:amp|lt|gt|quot|apos|#\d+|#x[0-9a-fA-F]+);)", "&amp;", raw_xml or "")
    try:
        root = ET.fromstring(cleaned_xml)
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

    def intent_of(self, text, kind="post", author=""):
        return classify_intent(_norm(text), kind, self.settings, query=self.query, author=author)[0]


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

    # 2b. Noise & Spam Blocker (blocked authors + negative keywords)
    author_norm = re.sub(r"^(@|u/)", "", _norm(it.get("author") or ""))
    if author_norm and any(author_norm == ba or ba in author_norm for ba in ctx.settings.get("blocked_authors", []) if ba):
        return None
    if any(phrase_in(context, bw) for bw in ctx.settings.get("blocked_keywords", []) if bw):
        return None

    # 3. 4-Way Intent Classification ('seeker' | 'employer' | 'buyer' | 'seller')
    intent, keyword = classify_intent(
        own_text, it["kind"], ctx.settings,
        query=ctx.query, full_context=context, source_name=it.get("source", ""),
        author=it.get("author", ""),
    )
    if intent is None or not keyword or keyword.lower() in ("seeker", "employer", "group post", "group comment"):
        return None

    # 4. Location check
    if ctx.location.lower() != "any":
        has_target_loc_in_text = location_matches(context, ctx.location, ctx.settings)
        has_non_cebu_city = (
            ctx.location.lower() == "cebu"
            and any(phrase_in(context, city) for city in NON_CEBU_CITIES)
        )
        if has_non_cebu_city and not has_target_loc_in_text:
            return None

        is_direct_loc = (
            has_target_loc_in_text
            or it.get("scoped")
            or it.get("from_configured_source")
        )
        is_remote_ph = (
            plat == "reddit"
            and any(sub in (it.get("source") or "").lower() for sub in ("phclassifieds", "buhaydigital"))
            and (
                any(phrase_in(context, rt) for rt in REMOTE_WORK_TERMS)
                or not has_non_cebu_city
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


def active_alt_provider_labels(settings):
    labels = []
    if settings.get("custom_api_url"):
        labels.append("Custom API")
    if settings.get("serper_api_key"):
        labels.append("Serper")
    if settings.get("tavily_api_key"):
        labels.append("Tavily")
    if settings.get("brave_api_key"):
        labels.append("Brave")
    return labels


def adapter_readiness(key, settings):
    s = settings
    alt_labels = active_alt_provider_labels(s)
    alt_str = " + ".join(alt_labels) if alt_labels else "Free Public Index"
    if key in ("facebook", "instagram", "tiktok"):
        if s.get("search_mode") == "alternative_only":
            return True, f"Ready ({SCANNER_VERSION} {alt_str})"
        if s["apify_token"]:
            if s.get("search_mode") == "apify_only":
                return True, f"Ready ({SCANNER_VERSION} Apify Only)"
            return True, f"Ready ({SCANNER_VERSION} Apify + {alt_str} Fallback)"
        return True, f"Ready ({SCANNER_VERSION} {alt_str})"
    if key == "public_web":
        return True, f"Ready ({SCANNER_VERSION} {alt_str})"
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


def _search_serper(dork_query, api_key, max_age_days=7, platform=""):
    tbs = "qdr:d" if max_age_days <= 1 else ("qdr:w" if max_age_days <= 7 else "qdr:m")
    body = {"q": dork_query, "gl": "ph", "hl": "en", "num": 20, "tbs": tbs}
    data = http_request(
        "https://google.serper.dev/search",
        method="POST",
        body=body,
        headers={"X-API-KEY": api_key},
        timeout=20,
    )
    results = []
    seen = set()
    for row in (data or {}).get("organic", []) or []:
        if not isinstance(row, dict):
            continue
        href = (row.get("link") or "").strip()
        if not href.startswith(("http://", "https://")) or href in seen:
            continue
        if platform and not is_valid_lead_url(platform, href):
            continue
        title = _short(row.get("title") or "", 180)
        snippet = _short(row.get("snippet") or "", 500)
        if title or snippet:
            seen.add(href)
            results.append({
                "url": href,
                "title": title,
                "snippet": snippet,
                "posted_ts": _parse_search_ts(row.get("date")),
                "provider": "Serper.dev",
            })
    return results


def _search_tavily(dork_query, api_key, max_age_days=7, platform=""):
    time_range = "day" if max_age_days <= 1 else ("week" if max_age_days <= 7 else "month")
    body = {
        "api_key": api_key,
        "query": dork_query,
        "search_depth": "basic",
        "time_range": time_range,
        "max_results": 20,
    }
    data = http_request(
        "https://api.tavily.com/search",
        method="POST",
        body=body,
        headers={"Authorization": f"Bearer {api_key}"},
        timeout=20,
    )
    results = []
    seen = set()
    for row in (data or {}).get("results", []) or []:
        if not isinstance(row, dict):
            continue
        href = (row.get("url") or "").strip()
        if not href.startswith(("http://", "https://")) or href in seen:
            continue
        if platform and not is_valid_lead_url(platform, href):
            continue
        title = _short(row.get("title") or "", 180)
        snippet = _short(row.get("content") or row.get("raw_content") or "", 500)
        if title or snippet:
            seen.add(href)
            results.append({
                "url": href,
                "title": title,
                "snippet": snippet,
                "posted_ts": _parse_search_ts(row.get("published_date")),
                "provider": "Tavily",
            })
    return results


def _search_brave(dork_query, api_key, max_age_days=7, platform=""):
    freshness = "pd" if max_age_days <= 1 else ("pw" if max_age_days <= 7 else "pm")
    qs = urllib.parse.urlencode({"q": dork_query, "freshness": freshness, "count": 20})
    url = f"https://api.search.brave.com/res/v1/web/search?{qs}"
    data = http_request(
        url,
        method="GET",
        headers={
            "X-Subscription-Token": api_key,
            "Accept": "application/json",
            "Accept-Encoding": "identity",
        },
        timeout=20,
    )
    results = []
    seen = set()
    rows = ((data or {}).get("web") or {}).get("results", []) or []
    for row in rows:
        if not isinstance(row, dict):
            continue
        href = (row.get("url") or "").strip()
        if not href.startswith(("http://", "https://")) or href in seen:
            continue
        if platform and not is_valid_lead_url(platform, href):
            continue
        title = _short(row.get("title") or "", 180)
        snippet = _short(row.get("description") or "", 500)
        if title or snippet:
            seen.add(href)
            results.append({
                "url": href,
                "title": title,
                "snippet": snippet,
                "posted_ts": _parse_search_ts(row.get("page_age") or row.get("age")),
                "provider": "Brave",
            })
    return results


def _search_custom_api(dork_query, endpoint_url, api_key="", max_age_days=7,
                       platform="", raw_query="", location="", intents=None):
    headers = {"Accept": "application/json"}
    if api_key:
        headers["Authorization"] = f"Bearer {api_key}"
        headers["X-API-Key"] = api_key

    if "{query}" in endpoint_url:
        req_url = endpoint_url.format(
            query=urllib.parse.quote_plus(dork_query),
            raw_query=urllib.parse.quote_plus(raw_query or ""),
            platform=urllib.parse.quote_plus(platform or ""),
            location=urllib.parse.quote_plus(location or ""),
            max_age_days=max_age_days,
        )
        data = http_request(req_url, method="GET", headers=headers, timeout=25)
    else:
        data = http_request(
            endpoint_url,
            method="POST",
            body={
                "query": dork_query,
                "raw_query": raw_query,
                "platform": platform,
                "location": location,
                "max_age_days": max_age_days,
                "intents": list(intents or []),
            },
            headers=headers,
            timeout=25,
        )

    rows = []
    if isinstance(data, list):
        rows = data
    elif isinstance(data, dict):
        for k in ("results", "items", "organic", "leads", "data"):
            if isinstance(data.get(k), list):
                rows = data[k]
                break

    results = []
    seen = set()
    for row in rows:
        if not isinstance(row, dict):
            continue
        href = str(pick(row, "url", "link", "commentUrl", "postUrl", "permalink", "webVideoUrl") or "").strip()
        if not href.startswith(("http://", "https://")) or href in seen:
            continue
        if platform and not is_valid_lead_url(platform, href):
            continue
        title = _short(str(pick(row, "title", "name", "postTitle") or ""), 180)
        snippet = _short(str(pick(row, "snippet", "text", "content", "description", "body", "message") or ""), 500)
        if title or snippet:
            seen.add(href)
            raw_kind = str(row.get("kind") or "").lower()
            results.append({
                "url": href,
                "title": title,
                "snippet": snippet,
                "author": _name(pick(row, "author", "username", "profileName", "authorMeta.name")) or "",
                "posted_ts": _parse_search_ts(pick(row, "posted_at", "published_date", "date", "timestamp", "createTimeISO", "created_at")),
                "kind": raw_kind if raw_kind in ("comment", "post") else "",
                "source": str(row.get("source") or ""),
                "provider": "Custom API",
            })
    return results


def _search_public_index(dork_query, max_age_days=7, platform="", settings=None,
                         raw_query="", location="", intents=None):
    s = settings or {}
    providers = []
    if s.get("custom_api_url"):
        providers.append(("Custom API", lambda: _search_custom_api(
            dork_query, s["custom_api_url"], s.get("custom_api_key", ""),
            max_age_days=max_age_days, platform=platform,
            raw_query=raw_query, location=location, intents=intents,
        )))
    if s.get("serper_api_key"):
        providers.append(("Serper.dev", lambda: _search_serper(
            dork_query, s["serper_api_key"], max_age_days=max_age_days, platform=platform,
        )))
    if s.get("tavily_api_key"):
        providers.append(("Tavily", lambda: _search_tavily(
            dork_query, s["tavily_api_key"], max_age_days=max_age_days, platform=platform,
        )))
    if s.get("brave_api_key"):
        providers.append(("Brave", lambda: _search_brave(
            dork_query, s["brave_api_key"], max_age_days=max_age_days, platform=platform,
        )))
    providers.append(("DuckDuckGo", lambda: _search_duckduckgo_html(dork_query, max_age_days=max_age_days, platform=platform)))
    providers.append(("Yahoo", lambda: _search_yahoo_html(dork_query, max_age_days=max_age_days, platform=platform)))

    hits = []
    errors = []
    any_provider_ok = False
    for pname, fn in providers:
        try:
            res = fn()
            any_provider_ok = True
            if res:
                hits.extend(res)
                break
        except ScanError as e:
            errors.append(f"{pname}: {e}")
    if any_provider_ok:
        errors = []
    dedup, seen = [], set()
    for h in hits:
        if h["url"] not in seen and (not platform or is_valid_lead_url(platform, h["url"])):
            seen.add(h["url"])
            dedup.append(h)
    return dedup, errors


def _scan_public_social(platform, label, dork_prefixes, ctx, extra_note=""):
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
    used_providers = []
    now_ts = get_reference_now()

    for dork in queries[:3]:
        if ctx.is_cancelled():
            return result("cancelled", "Cancelled by user.", items, fetched)
        hits, errs = _search_public_index(
            dork, max_age_days=ctx.max_age_days, platform=platform,
            settings=ctx.settings, raw_query=ctx.query, location=ctx.location, intents=ctx.intents,
        )
        errors.extend(errs)
        for h in hits:
            if h.get("provider") and h["provider"] not in used_providers:
                used_providers.append(h["provider"])
            if h["url"] in seen_urls or not is_valid_lead_url(platform, h["url"]):
                continue
            seen_urls.add(h["url"])
            fetched += 1
            combined = f"{h['title']} {h['snippet']}".lower()
            combined_norm = _norm(combined)
            is_comment = (
                any(k in combined_norm for k in ("interested po", "how to apply", "pwede pa mo apply"))
                and not has_employer_veto(combined_norm)
                and not is_corporate_author(h.get("author") or "")
            )
            kind = h.get("kind") or ("comment" if is_comment else "post")
            src_name = h.get("source") or f"{label} {'Comment' if kind == 'comment' else 'Post'}"
            items.append(
                item(
                    platform=platform,
                    kind=kind,
                    source=src_name,
                    external_id=f"{platform}_{stable_id(h['url'])}",
                    text=h["snippet"] or h["title"],
                    author=h.get("author") or f"{label} User",
                    url=h["url"],
                    posted_ts=h.get("posted_ts") or now_ts,
                    title=h["title"],
                    scoped=is_loc_scoped or location_scoped(combined, ctx.location, ctx.settings),
                )
            )

    notes = []
    if used_providers:
        notes.append(f"via {', '.join(used_providers)}")
    if extra_note:
        notes.append(extra_note)
    if not items and not errors:
        notes.append(f"0 public {label} post links indexed for this filter.")
    return _finish(items, fetched, errors if not items else [], note=" · ".join(notes))


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

    if not items and errors:
        return _scan_public_social(
            "reddit", "Reddit",
            ["site:reddit.com/r/Cebu/comments", "site:reddit.com/r/phclassifieds/comments", "site:reddit.com/r/buhaydigital/comments"],
            ctx,
            extra_note="Public Index fallback",
        )

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

    if not items and errors:
        return _scan_public_social(
            "reddit", "Reddit",
            [f"site:reddit.com/r/{s}/comments" for s in subs[:3]],
            ctx,
            extra_note="Public Index fallback",
        )

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


def _fb_public_prefixes(settings):
    prefixes = []
    for g in (settings.get("facebook_groups") or [])[:2]:
        key = _url_group_key(g)
        if key and not key.startswith("http"):
            prefixes.append(f"site:facebook.com/groups/{key}")
    for p in ("site:facebook.com/groups", "site:facebook.com"):
        if p not in prefixes:
            prefixes.append(p)
    return prefixes


@register_adapter("facebook", "Facebook",
                  "Newest posts + comments in your configured public Facebook groups/pages.",
                  needs="apify")
def adapter_facebook(ctx):
    s = ctx.settings
    if ctx.trigger == "auto" or s.get("search_mode") == "alternative_only" or not s["apify_token"] or not (s["facebook_groups"] or s["facebook_pages"]):
        return _scan_public_social(
            "facebook", "Facebook",
            _fb_public_prefixes(s),
            ctx,
        )
    token, limit = s["apify_token"], s["results_per_source"]
    cache_s = s["apify_cache_seconds"]
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

    # 2. Run a fresh Apify scrape for any newly added group or if the last run exceeds cache window
    jobs = []
    if s["facebook_groups"] and (missing_groups or latest_age_s > cache_s or not cached_matching):
        target_groups = missing_groups if (missing_groups and latest_age_s <= cache_s) else s["facebook_groups"]
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

    if not items and errors and s.get("search_mode") == "auto":
        return _scan_public_social(
            "facebook", "Facebook",
            _fb_public_prefixes(s),
            ctx,
            extra_note=f"Apify fallback ({errors[0]})",
        )

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
    if ctx.trigger == "auto" or s.get("search_mode") == "alternative_only" or not s["apify_token"] or not s["instagram_hashtags"]:
        return _scan_public_social(
            "instagram", "Instagram",
            ["site:instagram.com/p/", "site:instagram.com/reel/"],
            ctx,
        )
    token = s["apify_token"]
    cache_s = s["apify_cache_seconds"]
    items, errors, fetched, threads = [], [], 0, []
    try:
        data, age_s = apify_fetch_recent_runs(APIFY_ACTORS["instagram_hashtags"], token, max_runs=1)
        if ctx.is_cancelled():
            return result("cancelled", "Cancelled by user.", items, fetched)
        cache_matches_query = not ctx.query or any(
            smart_query_matches(f"{pick(p, 'caption') or ''} {' '.join(pick(p, 'hashtags') or [])}".lower(), ctx.query)
            for p in (data or [])
        )
        if not data or age_s > cache_s or not cache_matches_query:
            data = apify_run(APIFY_ACTORS["instagram_hashtags"], {
                "hashtags": s["instagram_hashtags"], "resultsLimit": s["results_per_source"],
                "resultsType": "posts", "onlyPostsNewerThan": ctx.since_phrase()}, token, ctx=ctx)
    except ScanCancelled:
        return result("cancelled", "Cancelled by user.", items, fetched)
    except ScanError as e:
        if s.get("search_mode") == "auto":
            return _scan_public_social(
                "instagram", "Instagram",
                ["site:instagram.com/p/", "site:instagram.com/reel/"],
                ctx,
                extra_note=f"Apify fallback ({e})",
            )
        return result("error", str(e))

    for post in data:
        url = _ig_post_url(post)
        if not url or not is_valid_lead_url("instagram", url):
            continue
        fetched += 1
        tags = " ".join(pick(post, "hashtags") or []) + " " + str(pick(post, "inputUrl", "queryTag") or "")
        caption = pick(post, "caption") or ""
        post_it = item("instagram", "post", "Instagram Post",
                       f"ig_post_{pick(post, 'id', 'shortCode') or stable_id(url)}",
                       caption, "@" + str(pick(post, "ownerUsername") or "unknown"),
                       url, to_epoch(pick(post, "timestamp")),
                       scoped=location_scoped(f"{tags} {caption}", ctx.location, ctx.settings),
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
    if ctx.trigger == "auto" or s.get("search_mode") == "alternative_only" or not s["apify_token"] or not (s["tiktok_search_queries"] or s["tiktok_hashtags"] or ctx.query):
        return _scan_public_social(
            "tiktok", "TikTok",
            ["site:tiktok.com"],
            ctx,
        )
    token = s["apify_token"]
    cache_s = s["apify_cache_seconds"]
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
        cache_matches_query = not ctx.query or any(
            smart_query_matches(str(pick(v, "text") or "").lower(), ctx.query)
            for v in (data or [])
        )
        if not data or age_s > cache_s or not cache_matches_query:
            data = apify_run(APIFY_ACTORS["tiktok_search"], run_input, token, ctx=ctx)
    except ScanCancelled:
        return result("cancelled", "Cancelled by user.", items, fetched)
    except ScanError as e:
        if s.get("search_mode") == "auto":
            return _scan_public_social(
                "tiktok", "TikTok",
                ["site:tiktok.com"],
                ctx,
                extra_note=f"Apify fallback ({e})",
            )
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
        hits, errs = _search_public_index(
            dork, max_age_days=ctx.max_age_days, platform="web",
            settings=ctx.settings, raw_query=ctx.query, location=ctx.location, intents=ctx.intents,
        )
        errors.extend(errs)
        now_ts = get_reference_now()
        for h in hits:
            fetched += 1
            host = urllib.parse.urlparse(h["url"]).netloc.replace("www.", "")
            items.append(item("web", "post", h.get("source") or f"Web ({host})", f"web_{stable_id(h['url'])}",
                              h["snippet"] or h["title"], h.get("author") or host, h["url"],
                              h.get("posted_ts") or now_ts,
                              title=h["title"], scoped=(ctx.location.lower() != "any")))

    return _finish(items, fetched, errors if not items else [])


# =====================================================================
# SCAN MANAGER (background scans + progress)
# =====================================================================

def detect_rant_or_misaligned_heuristic(lead):
    """
    Fast contextual check for posts that matched a keyword like 'need work' or 'hiring'
    but are actually rants, workplace venting, repair requests, or general discussions.
    Returns (is_aligned: bool, reason: str).
    """
    title = (lead.get("title") or "").strip()
    body = (lead.get("content") or "").strip()
    text = _norm(f"{title} {body}")
    kw = _norm(lead.get("matched_keyword") or "")

    # 1. Misaligned "need work" / "looking for work" uses (repairs, work-life balance, relationship/self work)
    misaligned_work_patterns = (
        r"\bneed(?:s)?\s+work[- ]life\b",
        r"\bneed(?:s)?\s+work\s+(?:done|on\s+my|on\s+the)\b",
        r"\b(?:car|motor|motorcycle|bike|laptop|phone|aircon|house|roof|brake|engine)\s+needs?\s+work\b",
        r"\bi\s+just\s+need\s+to\s+vent\b",
        r"\brant\s*[:\-]\b",
        r"\bjust\s+ranting\b",
        r"\bventing\s+about\b",
    )
    for pat in misaligned_work_patterns:
        if re.search(pat, text):
            return False, f"Matched '{kw}', but context is a rant, personal vent, or repair phrase rather than job-seeking."

    # 2. Workplace rants / complaints that mention work/hiring without seeking or offering a job
    rant_markers = (
        "hate my job", "tired of my job", "toxic workplace", "toxic boss",
        "toxic management", "kapoy kaayo sa work", "kapoy na sa trabaho",
        "burnout", "burned out", "worst company", "delayed sweldo",
        "walay klaro nga management", "resign na ba ko", "should i resign",
        "why is hiring so", "fake hiring", "ghost job",
    )
    actionable_markers = (
        "hire me", "for hire", "looking for a job", "looking for part time",
        "willing to start", "send resume", "send your resume", "apply now",
        "dm me", "pm me", "interested po", "pwede mo apply", "how to apply",
    )
    if any(rm in text for rm in rant_markers) and not any(am in text for am in actionable_markers):
        return False, "Detected workplace rant/complaint rather than an actionable jobseeker or hiring post."

    return True, "Context aligns with target lead category."


def _extract_interaction_text(resp):
    if not isinstance(resp, dict):
        return ""
    if isinstance(resp.get("output_text"), str) and resp["output_text"].strip():
        return resp["output_text"].strip()
    for step in reversed(resp.get("steps") or []):
        if isinstance(step, dict) and step.get("type") == "model_output":
            parts = []
            for c in step.get("content") or []:
                if isinstance(c, dict) and c.get("type") == "text" and c.get("text"):
                    parts.append(str(c["text"]))
            if parts:
                return "".join(parts).strip()
    for out in reversed(resp.get("outputs") or []):
        if isinstance(out, dict) and out.get("text"):
            return str(out["text"]).strip()
    return ""


def gemini_screen_leads_batch(leads_batch, api_key, model="gemini-3.5-flash-lite"):
    """
    Calls the Gemini Interactions API with structured JSON output to verify whether
    each scraped post/comment is genuinely an actionable lead AND return its true category:
    {"id": "...", "keep": true, "intent": "employer|seeker|buyer|seller", "reason": "..."}.
    """
    if not api_key or not leads_batch:
        return {}
    chosen_model = model if model in ("gemini-3.5-flash-lite", "gemini-4-hydrogen", "gemini-4-argon", "gemini-3.1-flash-lite") else "gemini-3.5-flash-lite"

    compact_input = []
    idx_to_key = {}
    for idx, ld in enumerate(leads_batch):
        orig_key = str(ld.get("external_id") or ld.get("id") or idx)
        short_id = str(idx)
        idx_to_key[short_id] = orig_key
        idx_to_key[orig_key] = orig_key
        compact_input.append({
            "id": short_id,
            "kind": ld.get("kind", "post"),
            "author": _short(ld.get("author") or "", 80),
            "source": ld.get("source", ""),
            "detected_intent": ld.get("intent", "seeker"),
            "matched_keyword": ld.get("matched_keyword", ""),
            "title": _short(ld.get("title") or "", 140),
            "text": _short(ld.get("content") or "", 360),
        })

    prompt = (
        "Evaluate each social media post/comment below for a Cebu/Philippines lead finder.\n"
        "For EACH item return {id, keep, intent, reason}.\n"
        "1. Determine the TRUE `intent` strictly from who is speaking:\n"
        "- 'employer': company, HR/Careers/Recruitment page, agency, or manager advertising job openings, career opportunities, or hiring staff "
        "(IMPORTANT: posts saying 'How to apply: send resume', 'Comment interested po below', 'Looking for your next career opportunity?', or posted by a Careers/HR page are ALWAYS 'employer', NEVER 'seeker').\n"
        "- 'seeker': an individual looking for work/gigs/side hustle, offering freelance services, OR commenting on a thread to apply ('interested po', 'how to apply', 'nangita kog trabaho').\n"
        "- 'seller': selling PC parts/electronics/items ('for sale', 'fs', 'rfs').\n"
        "- 'buyer': looking to buy items ('lf', 'wtb', 'looking for gpu/ram').\n\n"
        "2. Set `keep=true` ONLY if it is genuinely an actionable lead. Set `keep=false` if it is just ranting/venting about work/boss/life, "
        "asking general career advice without seeking/offering a job, talking about needing repair work on an object ('my car needs work'), or unrelated discussion.\n"
        "3. Provide a concise 1-sentence `reason` for each item.\n\n"
        f"ITEMS_JSON:\n{json.dumps(compact_input, ensure_ascii=False)}"
    )

    body = {
        "model": chosen_model,
        "store": False,
        "input": prompt,
        "response_format": {
            "type": "text",
            "mime_type": "application/json",
            "schema": {
                "type": "object",
                "properties": {
                    "decisions": {
                        "type": "array",
                        "items": {
                            "type": "object",
                            "properties": {
                                "id": {"type": "string"},
                                "keep": {"type": "boolean"},
                                "intent": {"type": "string", "enum": ["employer", "seeker", "buyer", "seller"]},
                                "reason": {"type": "string"},
                            },
                            "required": ["id", "keep", "intent", "reason"],
                        },
                    }
                },
                "required": ["decisions"],
            },
        },
    }

    url = "https://generativelanguage.googleapis.com/v1beta/interactions"
    resp = http_request(
        url,
        method="POST",
        body=body,
        headers={
            "x-goog-api-key": api_key,
            "Api-Revision": "2026-05-20",
        },
        timeout=30,
    )
    raw_txt = _extract_interaction_text(resp)
    if not raw_txt:
        return {}
    parsed = json.loads(raw_txt)
    decisions = parsed.get("decisions") if isinstance(parsed, dict) else (parsed if isinstance(parsed, list) else [])
    out = {}
    for pos, d in enumerate(decisions or []):
        if isinstance(d, dict):
            raw_id = str(d.get("id") if d.get("id") is not None else pos).strip()
            mapped_key = idx_to_key.get(raw_id) or idx_to_key.get(str(pos)) or raw_id
            keep_val = d["keep"] if "keep" in d else d.get("aligned", True)
            out[mapped_key] = {
                "keep": bool(keep_val),
                "aligned": bool(keep_val),
                "intent": str(d.get("intent") or "").lower().strip(),
                "reason": _short(str(d.get("reason") or ""), 200),
            }
    return out


def screen_leads_with_ai(leads_list, settings, skip_already_approved=False):
    """
    Screens a list of lead dicts in-place:
    1. Runs deterministic intent check (Comment-Only Guard, Employer Veto, Corporate Author) on non-manual leads.
    2. Runs contextual rant/misaligned heuristic check.
    3. If ai_filter_enabled and gemini_api_key is configured, batches remaining leads to Gemini
       and applies BOTH keep/filter verdict AND Gemini's corrected intent category.
    """
    if not leads_list:
        return leads_list
    s = settings or {}
    ai_enabled = bool(s.get("ai_filter_enabled", True))
    api_key = (s.get("gemini_api_key") or "").strip()
    model = (s.get("gemini_model") or "gemini-3.5-flash-lite").strip()

    to_gemini = []
    for ld in leads_list:
        if not str(ld.get("external_id") or "").startswith("manual_"):
            det_intent, det_kw = classify_stored_row(ld, s)
            if det_intent in ("seeker", "employer", "buyer", "seller") and det_intent != ld.get("intent"):
                ld["intent"] = det_intent
                if det_kw and not ld.get("matched_keyword"):
                    ld["matched_keyword"] = det_kw

        if skip_already_approved and ld.get("ai_verdict") == "approved" and str(ld.get("ai_reason") or "").startswith("Gemini AI:"):
            continue
        aligned, reason = detect_rant_or_misaligned_heuristic(ld)
        if not aligned and ai_enabled:
            ld["ai_verdict"] = "filtered"
            ld["ai_reason"] = reason
            ld["status"] = "ai_filtered"
        else:
            ld["ai_verdict"] = ld.get("ai_verdict") or "approved"
            ld["ai_reason"] = ld.get("ai_reason") or reason
            to_gemini.append(ld)

    if ai_enabled and api_key and to_gemini:
        for i in range(0, len(to_gemini), 15):
            chunk = to_gemini[i : i + 15]
            try:
                verdicts = gemini_screen_leads_batch(chunk, api_key, model=model)
                for ld in chunk:
                    key = str(ld.get("external_id") or ld.get("id") or "")
                    v = verdicts.get(key)
                    if not v:
                        continue
                    keep = v["keep"] if "keep" in v else v.get("aligned", True)
                    corrected_intent = str(v.get("intent") or "").lower().strip()
                    if corrected_intent in ("seeker", "employer", "buyer", "seller"):
                        ld["intent"] = corrected_intent
                    if not keep:
                        ld["ai_verdict"] = "filtered"
                        ld["ai_reason"] = f"Gemini AI: {v['reason']}"
                        ld["status"] = "ai_filtered"
                    else:
                        ld["ai_verdict"] = "approved"
                        ld["ai_reason"] = f"Gemini AI: {v['reason']}"
            except Exception as e:
                print(f"[gemini-ai] Batch screening fallback: {e}")

    return leads_list


def send_webhook_notification(webhook_url, new_leads, trigger="auto"):
    webhook_url = (webhook_url or "").strip()
    if not webhook_url or not new_leads:
        return False
    lines = [f"🔔 Unified Lead Scout ({trigger}): {len(new_leads)} new lead(s) found!"]
    for ld in new_leads[:5]:
        lines.append(f"• [{ld.get('source', 'Lead')}] {_short(ld.get('title') or ld.get('content'), 90)} -> {ld.get('url')}")
    summary = "\n".join(lines)
    try:
        http_request(
            webhook_url,
            method="POST",
            body={"content": summary, "text": summary, "new_count": len(new_leads), "leads": new_leads[:5]},
            timeout=10,
        )
        return True
    except Exception as e:
        print(f"[webhook] Notification failed: {e}")
        return False


class ScanManager:
    def __init__(self):
        self._lock = threading.Lock()
        self._scan_seq = 0
        self._cancel_event = None
        self._active_ctx = None
        self.last_finished_epoch = 0.0
        self.state = {"running": False, "cancelled": False, "finished_at": None, "adapters": {},
                      "new_total": 0, "matched_total": 0, "latest_new": []}

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
                "new_total": 0, "matched_total": 0, "latest_new": [],
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

        newly_saved_leads = []
        try:
            with ThreadPoolExecutor(max_workers=max(1, len(platforms))) as pool:
                for fut in as_completed([pool.submit(run_one, k) for k in platforms]):
                    key, res = fut.result()
                    if cancel_ev.is_set() or seq != self._scan_seq:
                        continue
                    matched = new = 0
                    seen = set()
                    candidates = []
                    for raw in res["items"]:
                        if cancel_ev.is_set():
                            break
                        lead = evaluate_item(raw, ctx)
                        if not lead or lead["external_id"] in seen:
                            continue
                        seen.add(lead["external_id"])
                        candidates.append(lead)

                    if candidates and not cancel_ev.is_set():
                        screen_leads_with_ai(candidates, ctx.settings)

                    for lead in candidates:
                        if cancel_ev.is_set():
                            break
                        is_saved = save_lead(**lead)
                        if lead.get("status") != "ai_filtered" and lead_matches_active_filters(lead, ctx):
                            matched += 1
                            if is_saved:
                                new += 1
                                if len(newly_saved_leads) < 5:
                                    newly_saved_leads.append({
                                        "title": lead.get("title", ""),
                                        "source": lead.get("source", ""),
                                        "url": lead.get("url", ""),
                                        "intent": lead.get("intent", ""),
                                    })
                    self._update(key, seq=seq, status=res["status"], message=res["message"],
                                 fetched=res["fetched"], matched=matched, new=new)
                    with self._lock:
                        if seq == self._scan_seq:
                            self.state["new_total"] += new
                            self.state["matched_total"] += matched
                            self.state["latest_new"] = list(newly_saved_leads)
                    if res["status"] in ("error", "partial"):
                        print(f"[scan] {key}: {res['message']}")
        finally:
            self.last_finished_epoch = time.time()
            self._update(seq=seq, running=False, finished_at=utc_now_sql())
            if newly_saved_leads and not cancel_ev.is_set() and ctx.settings.get("alert_webhook_url"):
                threading.Thread(
                    target=send_webhook_notification,
                    args=(ctx.settings["alert_webhook_url"], newly_saved_leads, ctx.trigger),
                    daemon=True,
                ).start()
