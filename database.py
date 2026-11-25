import os
import re
import sqlite3
import urllib.parse
from datetime import datetime, timezone

DB_PATH = os.path.join(os.path.dirname(__file__), "leads.db")

# Columns added after v1. Missing ones are added automatically on startup.
EXTRA_COLUMNS = {
    "posted_at": "TIMESTAMP",
    "platform": "TEXT DEFAULT ''",
    "kind": "TEXT DEFAULT 'post'",
    "intent": "TEXT DEFAULT ''",
    "matched_keyword": "TEXT DEFAULT ''",
    "parent_url": "TEXT DEFAULT ''",
    "ai_verdict": "TEXT DEFAULT ''",
    "ai_reason": "TEXT DEFAULT ''",
    "updated_at": "TIMESTAMP",
    "followup_at": "TIMESTAMP",
    "comments_count": "INTEGER DEFAULT NULL",
}

ALLOWED_WEB_DOMAINS = (
    "mynimo.com",
    "jobstreet.com.ph",
    "indeed.com",
    "bossjob.ph",
    "onlinejobs.ph",
    "kalibrr.com",
    "philjobnet.gov.ph",
    "foundit.ph",
    "jora.com",
    "linkedin.com",
    "craigslist.org",
)

QUERY_FILLER_WORDS = {
    "for", "sale", "selling", "fs", "lf", "wtb", "wts", "looking",
    "in", "sa", "cebu", "po", "ang", "ng", "ug", "ko", "kog", "a", "the",
}

# Strict hardware synonyms (no '16gb'/'32gb'/'128gb' phone storage or '1 pc' piece false positives)
QUERY_SYNONYMS = {
    "gpu": ("gpu", "graphics card", "video card", "videocard", "rtx", "gtx", "radeon", "rx 5", "rx 6", "rx 7"),
    "ram": ("ram", "ddr3", "ddr4", "ddr5", "sodimm", "dimm"),
    "rame": ("ram", "ddr3", "ddr4", "ddr5", "sodimm", "dimm"),
    "laptop": ("laptop", "notebook", "macbook", "thinkpad", "ideapad", "vivobook", "tuf gaming", "rog", "acer nitro", "lenovo legion"),
}

BUY_SELL_KEYWORDS = {
    "for sale", "fs:", "selling", "rush sale", "sale or swap", "fix price", "rfs",
    "gpu for sale", "gpu", "graphics card", "video card", "rtx", "gtx",
    "ram", "ddr4", "ddr5", "pc set", "system unit", "gaming pc", "laptop",
    "wtb", "lf:", "buying", "hm", "how much", "last price", "pilay",
}


def get_db():
    conn = sqlite3.connect(DB_PATH, timeout=30)
    conn.row_factory = sqlite3.Row
    return conn


def utc_now_sql():
    return datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M:%S")


def infer_platform(source):
    s = (source or "").lower()
    for p in ("reddit", "facebook", "instagram", "tiktok"):
        if p in s:
            return p
    return "web"


def is_buy_sell_keyword(kw):
    k = re.sub(r"\s+", " ", (kw or "").strip().lower()).rstrip("?")
    if not k:
        return False
    if k in BUY_SELL_KEYWORDS:
        return True
    # Any job keyword is NOT buy/sell
    job_Indicators = (
        "hiring", "trabaho", "job", "work", "apply", "for hire", "hire me",
        "hiring me", "interested", "resume", "cv", "vacancy", "vacancies",
        "opening", "staff", "crew", "dishwasher", "barista", "cashier",
        "helper", "cook", "unemployed", "remote", "coaching", "errand",
        "qualifications", "requirements", "applicants", "nangita mi", "nangita kami",
        "start asap", "start immediately", "available immediately",
    )
    if any(j in k for j in job_Indicators):
        return False
    return False


def parse_search_query(query):
    """
    Splits a user search string into (positive_query, negative_terms).
    Supports -word and -"multi word" exclusion syntax (e.g. 'dishwasher -agency -bpo').
    """
    raw = (query or "").strip()
    if not raw:
        return "", []
    neg_terms = []

    def _collect_neg(match):
        term = (match.group(1) or match.group(2) or "").strip().lower()
        if term:
            neg_terms.append(term)
        return " "

    # Match -word or -"phrase" preceded by start-of-string or whitespace
    cleaned = re.sub(
        r'(?:^|\s)-(?:"([^"]+)"|([^\s]+))',
        _collect_neg,
        raw,
    )
    pos = re.sub(r"\s+", " ", cleaned).strip()
    return pos, neg_terms


def _term_in_text(hay, term):
    t = re.sub(r"\s+", " ", (term or "").strip().lower()).rstrip("?")
    if not t:
        return False
    return re.search(r"(?<!\w)" + re.escape(t) + r"(?!\w)", hay) is not None


def _single_query_matches(hay, q_part):
    q = re.sub(r"\s+", " ", (q_part or "").strip().lower()).rstrip("?")
    if not q:
        return True

    # Exact phrase check with word boundaries
    if _term_in_text(hay, q):
        return True

    if q in ("pc set", "system unit"):
        return any(
            _term_in_text(hay, term)
            for term in ("pc set", "system unit", "gaming pc", "desktop pc", "full set pc", "ryzen")
        )

    if q in ("for sale", "fs", "selling"):
        return any(
            _term_in_text(hay, t)
            for t in ("for sale", "selling", "fs", "sale or swap", "fix price", "rush sale", "rfs")
        )

    raw_words = [w for w in re.split(r"\W+", q) if w]
    if not raw_words:
        return True

    core_words = [w for w in raw_words if w not in QUERY_FILLER_WORDS]
    if not core_words:
        core_words = raw_words

    for w in core_words:
        syns = QUERY_SYNONYMS.get(w, (w,))
        if not any(_term_in_text(hay, s) for s in syns):
            return False
    return True


def smart_query_matches(haystack, query):
    """
    Matches user search queries accurately without false positives on phone storage ('128gb')
    or piece count ('1 pc'). Supports negative -exclude terms (e.g. 'barista -manila -agency')
    and uppercase OR / | branches (e.g. 'dishwasher OR cook OR service crew').
    """
    pos_raw, neg_terms = parse_search_query(query)
    hay = (haystack or "").lower()

    # 1. Negative exclusions always veto a match
    for neg in neg_terms:
        syns = QUERY_SYNONYMS.get(neg, (neg,))
        if any(_term_in_text(hay, s) for s in syns):
            return False

    pos_raw = (pos_raw or "").strip()
    if not pos_raw:
        return True

    branches = [b.strip() for b in re.split(r"\s+(?:OR|\|)\s+", pos_raw) if b.strip()]
    if not branches:
        return True
    return any(_single_query_matches(hay, b) for b in branches)


def score_query_relevance(row, pos_query):
    """
    Ranks exact matches in title or comment body above weak/secondary matches.
    """
    raw_q = (pos_query or "").strip()
    if not raw_q:
        return 0
    branches = [b.strip() for b in re.split(r"\s+(?:OR|\|)\s+", raw_q) if b.strip()]
    title = (row.get("title") or "").lower()
    content = (row.get("content") or "").lower()
    kind = (row.get("kind") or ("comment" if "comment" in (row.get("source") or "").lower() else "post")).lower()
    primary_text = content if kind == "comment" else title
    secondary_text = title if kind == "comment" else content
    meta_text = " ".join(str(row.get(k) or "") for k in ("matched_keyword", "author", "source", "notes", "ai_reason")).lower()

    best = 0
    for b in branches:
        q = re.sub(r"\s+", " ", b.lower()).rstrip("?")
        if not q:
            continue
        raw_words = [w for w in re.split(r"\W+", q) if w]
        core_words = [w for w in raw_words if w not in QUERY_FILLER_WORDS] or raw_words
        score = 0
        if _term_in_text(primary_text, q):
            score += 100
        elif core_words and all(any(_term_in_text(primary_text, s) for s in QUERY_SYNONYMS.get(w, (w,))) for w in core_words):
            score += 65
        if _term_in_text(secondary_text, q):
            score += 45
        elif core_words and all(any(_term_in_text(secondary_text, s) for s in QUERY_SYNONYMS.get(w, (w,))) for w in core_words):
            score += 25
        if _term_in_text(meta_text, q):
            score += 10
        if score > best:
            best = score
    return best


def is_valid_lead_url(platform, url, external_id=""):
    """
    Strictly verifies that `url` is a real post, comment, video, group thread, commerce listing,
    or job listing belonging to `platform` (never an unrelated site, login page, or generic homepage).
    """
    if str(external_id or "").startswith("manual_"):
        return bool(url and url.startswith(("http://", "https://")))

    if not url or not isinstance(url, str):
        return False
    try:
        parsed = urllib.parse.urlparse(url.strip())
    except Exception:
        return False

    if parsed.scheme not in ("http", "https"):
        return False

    host = (parsed.netloc or "").lower().split(":")[0]
    path = (parsed.path or "").lower()
    full = f"{path}?{parsed.query.lower()}" if parsed.query else path
    plat = (platform or "").lower().strip()

    if plat == "facebook":
        valid_hosts = {
            "facebook.com", "www.facebook.com", "m.facebook.com",
            "web.facebook.com", "mbasic.facebook.com", "fb.com", "www.fb.com",
        }
        if host not in valid_hosts:
            return False
        banned = (
            "/login", "/recover", "/help", "/policies", "/privacy", "/terms",
            "/marketplace/category", "/business", "/ads", "/gaming", "/directory", "/public/",
        )
        if any(b in full for b in banned):
            return False
        required = (
            "/groups/", "/posts/", "/permalink", "story_fbid=", "fbid=",
            "/reel/", "/videos/", "/watch", "/share/", "/photo", "pfbid",
            "/commerce/", "/marketplace/item/",
        )
        return any(r in full for r in required)

    if plat == "tiktok":
        if not (host == "tiktok.com" or host.endswith(".tiktok.com")):
            return False
        banned = ("/login", "/signup", "/foryou", "/help", "/legal", "/about", "/business")
        if path in ("", "/", "/en") or any(b in full for b in banned):
            return False
        return bool(
            re.search(r"/@[^/]+/(video|photo)/\d+", path)
            or re.search(r"/(v|t)/[a-z0-9_-]+", path)
            or path.startswith(("/tag/", "/discover/"))
        )

    if plat == "instagram":
        if not (host == "instagram.com" or host.endswith(".instagram.com")):
            return False
        banned = ("/accounts/", "/login", "/about", "/legal", "/help", "/developer", "/directory")
        if path in ("", "/") or any(b in full for b in banned):
            return False
        return bool(
            re.search(r"/(p|reel|reels|tv)/[a-z0-9_-]+", path)
            or path.startswith("/explore/tags/")
        )

    if plat == "reddit":
        if not (host == "reddit.com" or host.endswith(".reddit.com") or host == "redd.it"):
            return False
        return "/comments/" in path

    # 'web' / public_web
    if not any(host == d or host.endswith("." + d) for d in ALLOWED_WEB_DOMAINS):
        return False
    if host == "linkedin.com" or host.endswith(".linkedin.com"):
        return "/jobs/" in path
    return True


def init_db():
    conn = get_db()
    with conn:
        conn.execute("""
            CREATE TABLE IF NOT EXISTS leads (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                source TEXT NOT NULL,
                external_id TEXT UNIQUE NOT NULL,
                title TEXT NOT NULL,
                content TEXT,
                author TEXT,
                url TEXT NOT NULL,
                location TEXT,
                status TEXT DEFAULT 'new',
                notes TEXT DEFAULT '',
                found_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
            )
        """)
        cols = {r["name"] for r in conn.execute("PRAGMA table_info(leads)").fetchall()}
        for name, ddl in EXTRA_COLUMNS.items():
            if name not in cols:
                conn.execute(f"ALTER TABLE leads ADD COLUMN {name} {ddl}")

        # Backfill platform/kind for rows created by older versions
        for row in conn.execute(
            "SELECT id, source FROM leads WHERE platform IS NULL OR platform = ''"
        ).fetchall():
            kind = "comment" if "comment" in (row["source"] or "").lower() else "post"
            conn.execute(
                "UPDATE leads SET platform = ?, kind = ? WHERE id = ?",
                (infer_platform(row["source"]), kind, row["id"]),
            )

        # Install SQLite BEFORE INSERT trigger to block fallback/empty keywords and invalid URLs
        conn.execute("DROP TRIGGER IF EXISTS trg_validate_lead_before_insert")
        conn.execute("""
            CREATE TRIGGER trg_validate_lead_before_insert
            BEFORE INSERT ON leads
            FOR EACH ROW
            WHEN (
                NEW.external_id NOT LIKE 'manual_%'
                AND (
                    NEW.matched_keyword IN ('seeker', 'employer', 'group post', 'group comment', '')
                    OR (
                        NEW.platform = 'facebook' AND NOT (
                            (
                                LOWER(NEW.url) LIKE 'https://www.facebook.com/%'
                                OR LOWER(NEW.url) LIKE 'https://facebook.com/%'
                                OR LOWER(NEW.url) LIKE 'https://m.facebook.com/%'
                                OR LOWER(NEW.url) LIKE 'https://web.facebook.com/%'
                                OR LOWER(NEW.url) LIKE 'https://mbasic.facebook.com/%'
                                OR LOWER(NEW.url) LIKE 'https://fb.com/%'
                                OR LOWER(NEW.url) LIKE 'https://www.fb.com/%'
                                OR LOWER(NEW.url) LIKE 'http://www.facebook.com/%'
                                OR LOWER(NEW.url) LIKE 'http://facebook.com/%'
                                OR LOWER(NEW.url) LIKE 'http://m.facebook.com/%'
                                OR LOWER(NEW.url) LIKE 'http://web.facebook.com/%'
                                OR LOWER(NEW.url) LIKE 'http://mbasic.facebook.com/%'
                                OR LOWER(NEW.url) LIKE 'http://fb.com/%'
                                OR LOWER(NEW.url) LIKE 'http://www.fb.com/%'
                            )
                            AND (
                                LOWER(NEW.url) LIKE '%/groups/%'
                                OR LOWER(NEW.url) LIKE '%/posts/%'
                                OR LOWER(NEW.url) LIKE '%/permalink%'
                                OR LOWER(NEW.url) LIKE '%story_fbid=%'
                                OR LOWER(NEW.url) LIKE '%fbid=%'
                                OR LOWER(NEW.url) LIKE '%/reel/%'
                                OR LOWER(NEW.url) LIKE '%/videos/%'
                                OR LOWER(NEW.url) LIKE '%/watch%'
                                OR LOWER(NEW.url) LIKE '%/share/%'
                                OR LOWER(NEW.url) LIKE '%/photo%'
                                OR LOWER(NEW.url) LIKE '%pfbid%'
                                OR LOWER(NEW.url) LIKE '%/commerce/%'
                                OR LOWER(NEW.url) LIKE '%/marketplace/item/%'
                            )
                            AND LOWER(NEW.url) NOT LIKE '%/login%'
                            AND LOWER(NEW.url) NOT LIKE '%/help%'
                            AND LOWER(NEW.url) NOT LIKE '%/marketplace/category%'
                        )
                    )
                    OR (
                        NEW.platform = 'tiktok' AND NOT (
                            (LOWER(NEW.url) LIKE 'https://%tiktok.com/%' OR LOWER(NEW.url) LIKE 'http://%tiktok.com/%')
                            AND (
                                LOWER(NEW.url) LIKE '%/@%/video/%'
                                OR LOWER(NEW.url) LIKE '%/@%/photo/%'
                                OR LOWER(NEW.url) LIKE '%/v/%'
                                OR LOWER(NEW.url) LIKE '%/t/%'
                                OR LOWER(NEW.url) LIKE '%/tag/%'
                                OR LOWER(NEW.url) LIKE '%/discover/%'
                            )
                            AND LOWER(NEW.url) NOT LIKE '%/login%'
                            AND LOWER(NEW.url) NOT LIKE '%/signup%'
                            AND LOWER(NEW.url) NOT LIKE '%/foryou%'
                        )
                    )
                    OR (
                        NEW.platform = 'instagram' AND NOT (
                            (LOWER(NEW.url) LIKE 'https://%instagram.com/%' OR LOWER(NEW.url) LIKE 'http://%instagram.com/%')
                            AND (
                                LOWER(NEW.url) LIKE '%/p/%'
                                OR LOWER(NEW.url) LIKE '%/reel/%'
                                OR LOWER(NEW.url) LIKE '%/reels/%'
                                OR LOWER(NEW.url) LIKE '%/tv/%'
                                OR LOWER(NEW.url) LIKE '%/explore/tags/%'
                            )
                            AND LOWER(NEW.url) NOT LIKE '%/login%'
                            AND LOWER(NEW.url) NOT LIKE '%/accounts/%'
                        )
                    )
                    OR (
                        NEW.platform = 'reddit' AND NOT (
                            LOWER(NEW.url) LIKE 'https://%reddit.com/%/comments/%'
                            OR LOWER(NEW.url) LIKE 'https://%reddit.com/comments/%'
                            OR LOWER(NEW.url) LIKE 'http://%reddit.com/%/comments/%'
                            OR LOWER(NEW.url) LIKE 'http://%reddit.com/comments/%'
                        )
                    )
                    OR (
                        NEW.platform = 'web' AND NOT (
                            LOWER(NEW.url) LIKE 'http%://%mynimo.com/%'
                            OR LOWER(NEW.url) LIKE 'http%://%jobstreet.com.ph/%'
                            OR LOWER(NEW.url) LIKE 'http%://%indeed.com/%'
                            OR LOWER(NEW.url) LIKE 'http%://%bossjob.ph/%'
                            OR LOWER(NEW.url) LIKE 'http%://%onlinejobs.ph/%'
                            OR LOWER(NEW.url) LIKE 'http%://%kalibrr.com/%'
                            OR LOWER(NEW.url) LIKE 'http%://%philjobnet.gov.ph/%'
                            OR LOWER(NEW.url) LIKE 'http%://%foundit.ph/%'
                            OR LOWER(NEW.url) LIKE 'http%://%jora.com/%'
                            OR LOWER(NEW.url) LIKE 'http%://%linkedin.com/jobs/%'
                            OR LOWER(NEW.url) LIKE 'http%://%craigslist.org/%'
                        )
                    )
                )
            )
            BEGIN
                SELECT RAISE(IGNORE);
            END;
        """)

        # Clean up fallback rows ('group post', 'group comment', 'seeker', 'employer') and
        # migrate any existing Buy & Sell rows ('for sale', 'ram', 'pc set', 'system unit', 'gpu for sale', 'laptop')
        # into the separate 'seller' / 'buyer' intent categories so they never mix with 'seeker' / 'employer'!
        all_rows = conn.execute(
            "SELECT id, platform, kind, source, external_id, title, content, url, intent, matched_keyword FROM leads"
        ).fetchall()
        bad_ids = []
        for r in all_rows:
            plat = r["platform"] or infer_platform(r["source"])
            ext_id = r["external_id"] or ""
            kw = (r["matched_keyword"] or "").strip()
            kw_low = kw.lower()
            kind = r["kind"] or "post"
            src_low = (r["source"] or "").lower()
            text_all = f"{r['title'] or ''} {r['content'] or ''}".lower()

            if ext_id.startswith(("seed_", "fallback_")):
                bad_ids.append(r["id"])
                continue
            if not is_valid_lead_url(plat, r["url"], ext_id):
                bad_ids.append(r["id"])
                continue
            if not ext_id.startswith("manual_") and kw_low in ("seeker", "employer", "group post", "group comment", ""):
                bad_ids.append(r["id"])
                continue

            # If this row was matched by a Buy & Sell keyword (or came from a Phone/PC Sales group),
            # move it to 'seller' / 'buyer' (or delete if it was a false-positive 'ram'/'pc set' on an iPhone/iPad)
            if is_buy_sell_keyword(kw_low) or "sales & repairs" in src_low or "buy and sell" in src_low:
                if kw_low in ("ram", "pc set", "system unit") and not smart_query_matches(text_all, kw_low):
                    bad_ids.append(r["id"])
                    continue
                new_intent = "buyer" if (kind == "comment" or any(w in text_all for w in ("lf ", "lf:", "wtb", "looking for", "buying"))) else "seller"
                if r["intent"] != new_intent:
                    conn.execute("UPDATE leads SET intent = ? WHERE id = ?", (new_intent, r["id"]))
                continue

            # Only force comment-style seeker phrases to 'seeker' when kind == 'comment'
            # (employer posts frequently contain 'How to apply:' or 'Comment interested po')
            if kind == "comment" and kw_low in ("interested po", "how to apply", "pwede pa mo apply", "naay hiring", "naay hiring?", "naa bay hiring", "apply ko", "nangita kog trabaho", "ngita kog trabaho", "ngita ko trabaho"):
                if r["intent"] != "seeker":
                    conn.execute("UPDATE leads SET intent = 'seeker' WHERE id = ?", (r["id"],))

            # Clean up comments that were saved by an older version with an employer parent-post keyword
            if kind == "comment" and kw_low in ("we are hiring", "urgently hiring", "is hiring", "urgent hiring", "hiring", "requirements", "qualifications"):
                c_low = (r["content"] or "").lower()
                real_comment_kw = next(
                    (p for p in ("interested po", "interested", "how to apply", "how po", "pa refer", "apply ta", "apply", "no experience", "mo duty", "pm sir", "pm boss", "pm maam", "nag message ko", "nag pm ko", "check message", "pm kay") if p in c_low),
                    None,
                )
                if real_comment_kw:
                    conn.execute("UPDATE leads SET intent = 'seeker', matched_keyword = ? WHERE id = ?", (real_comment_kw, r["id"]))
                else:
                    bad_ids.append(r["id"])
                    continue

            # Clean Facebook AI image alt-text ("May be an image of...") from existing content/titles
            raw_content = r["content"] or ""
            if "May be an image of" in raw_content or "May be a meme of" in raw_content:
                cleaned_content = re.sub(r"\s*May be an? (?:image|meme|photo|illustration) of[^\n.]*", "", raw_content, flags=re.I).strip()
                if cleaned_content != raw_content:
                    conn.execute("UPDATE leads SET content = ? WHERE id = ?", (cleaned_content, r["id"]))

        if bad_ids:
            placeholders = ",".join("?" for _ in bad_ids)
            conn.execute(f"DELETE FROM leads WHERE id IN ({placeholders})", bad_ids)

        conn.execute("CREATE INDEX IF NOT EXISTS idx_leads_status ON leads(status)")
        conn.execute("CREATE INDEX IF NOT EXISTS idx_leads_found ON leads(found_at)")
        conn.execute("CREATE INDEX IF NOT EXISTS idx_leads_posted ON leads(posted_at)")
        conn.execute(
            """
            CREATE TABLE IF NOT EXISTS api_usage_daily (
                date TEXT NOT NULL,
                provider TEXT NOT NULL,
                calls INTEGER NOT NULL DEFAULT 0,
                PRIMARY KEY (date, provider)
            )
            """
        )
    conn.close()


LOCATION_MATCH_TERMS = {
    "cebu": (
        "cebu", "mandaue", "lapu-lapu", "lapulapu", "lapu lapu", "talisay", "consolacion",
        "liloan", "minglanilla", "carcar", "danao", "toledo", "it park", "banilad", "mabolo",
        "lahug", "guadalupe", "fuente", "mactan", "cordova", "sm seaside", "ayala", "talamban",
        "naga", "compostela", "consoloacion", "colon", "osmena", "bantayan", "moalboal",
    ),
}

NON_CEBU_LOCATION_TERMS = (
    "manila", "manilam", "metro manila", "ncr", "makati", "quezon city", "qc", "marikina",
    "taguig", "bgc", "pasig", "ortigas", "alabang", "muntinlupa", "paranaque", "pasay",
    "mandaluyong", "caloocan", "valenzuela", "malabon", "navotas", "cavite", "laguna",
    "bacoor", "imus", "dasmarinas", "batangas", "rizal", "antipolo", "bulacan", "pampanga",
    "tarlac", "baguio", "lucena", "davao", "iloilo", "bacolod", "cagayan de oro", "cdo",
    "zamboanga", "gensan", "dlsu", "up diliman", "luxembourg", "south africa", "ballymena", "lautoka",
)


def lead_content_fingerprint(author, title, content, kind="post"):
    """
    Computes a normalized fingerprint for deduplicating identical cross-posted ads
    by the same author across multiple groups or runs.
    """
    a_norm = re.sub(r"[^a-z0-9]+", "", (author or "").lower())
    raw_text = f"{title or ''} {(content or '')[:240]}".lower()
    t_norm = re.sub(r"https?://\S+", "", raw_text)
    t_norm = re.sub(r"[^a-z0-9]+", " ", t_norm).strip()
    if len(t_norm) < 18:
        return ""
    return f"{(kind or 'post').lower()}|{a_norm}|{t_norm[:140]}"


def filter_unseen_leads(candidates):
    """
    Pre-Gemini credit saver (zero accuracy loss):
    Checks `leads.db` for existing `external_id` and `lead_content_fingerprint` (for non-manual posts),
    plus deduplicates identical cross-posts within `candidates` itself.
    If an already-stored row has a fresh `comments_count` in `candidates`, updates `comments_count`
    in SQLite without re-sending the lead to Gemini.
    Returns only genuinely unseen candidate dicts in original order.
    """
    if not candidates:
        return []

    ext_ids = [str(c.get("external_id") or "") for c in candidates if c.get("external_id")]
    existing_ext_ids = set()
    existing_fps = set()

    conn = get_db()
    try:
        for i in range(0, len(ext_ids), 500):
            chunk = ext_ids[i : i + 500]
            if not chunk:
                continue
            placeholders = ",".join("?" for _ in chunk)
            rows = conn.execute(
                f"SELECT external_id FROM leads WHERE external_id IN ({placeholders})",
                chunk,
            ).fetchall()
            for r in rows:
                existing_ext_ids.add(str(r["external_id"]))

        # Refresh comments_count on already-stored posts when fresh count is available
        count_updates = []
        for c in candidates:
            eid = str(c.get("external_id") or "")
            cc = c.get("comments_count")
            if eid in existing_ext_ids and cc is not None and not isinstance(cc, bool):
                try:
                    cc_int = int(cc)
                    if cc_int >= 0:
                        count_updates.append((cc_int, eid, cc_int))
                except (ValueError, TypeError):
                    pass
        if count_updates:
            with conn:
                conn.executemany(
                    "UPDATE leads SET comments_count = ? WHERE external_id = ? AND (comments_count IS NULL OR comments_count != ?)",
                    count_updates,
                )

        post_authors = list({
            str(c.get("author") or "")
            for c in candidates
            if str(c.get("external_id") or "") not in existing_ext_ids
            and not str(c.get("external_id") or "").startswith("manual_")
            and (c.get("kind") or "post") == "post"
            and c.get("author")
        })
        for i in range(0, len(post_authors), 400):
            chunk = post_authors[i : i + 400]
            placeholders = ",".join("?" for _ in chunk)
            rows = conn.execute(
                f"SELECT author, title, content, kind FROM leads WHERE kind = 'post' AND author IN ({placeholders})",
                chunk,
            ).fetchall()
            for r in rows:
                fp = lead_content_fingerprint(r["author"], r["title"], r["content"], r["kind"])
                if fp:
                    existing_fps.add(fp)
    finally:
        conn.close()

    unseen = []
    batch_ext = set()
    batch_fps = set()
    for c in candidates:
        eid = str(c.get("external_id") or "")
        if not eid or eid in existing_ext_ids or eid in batch_ext:
            continue
        is_post = not eid.startswith("manual_") and (c.get("kind") or "post") == "post"
        if is_post:
            fp = lead_content_fingerprint(c.get("author"), c.get("title"), c.get("content"), kind="post")
            if fp and (fp in existing_fps or fp in batch_fps):
                continue
            if fp:
                batch_fps.add(fp)
        batch_ext.add(eid)
        unseen.append(c)
    return unseen


def get_latest_fb_posted_at(target_urls, page_mode=False):
    """
    Returns `{target_key: newest_posted_at_sql_str}` for each configured Facebook group or page URL
    in `target_urls` based on leads already stored in `leads.db`. Missing targets are omitted so
    callers know if any target has never been scraped yet.
    """
    if not target_urls:
        return {}
    keys = []
    for raw_u in target_urls:
        u_str = str(raw_u or "").strip()
        if not u_str:
            continue
        if page_mode:
            k = u_str.lower().rstrip("/").split("/")[-1]
        else:
            m = re.search(r"/groups/([^/?#]+)", u_str, re.I)
            k = m.group(1).strip().lower() if m else u_str.lower().rstrip("/").split("/")[-1]
        if k:
            keys.append(k)
    if not keys:
        return {}

    target_set = set(keys)
    latest_by_key = {}
    conn = get_db()
    try:
        rows = conn.execute(
            """
            SELECT source, url, parent_url, posted_at
            FROM leads
            WHERE posted_at IS NOT NULL AND posted_at != ''
              AND (platform = 'facebook' OR lower(source) LIKE '%facebook%')
            ORDER BY posted_at DESC
            LIMIT 1000
            """
        ).fetchall()
    except Exception:
        rows = []
    finally:
        conn.close()

    for r in rows:
        if len(latest_by_key) == len(target_set):
            break
        src = str(r["source"] or "")
        url = str(r["url"] or "")
        purl = str(r["parent_url"] or "")
        pts = str(r["posted_at"] or "").strip()
        if not pts:
            continue
        if page_mode:
            low_blob = f"{src} {url} {purl}".lower()
            for tk in target_set:
                if tk not in latest_by_key and tk in low_blob:
                    latest_by_key[tk] = pts
        else:
            r_key, r_name = extract_fb_group_key_and_name(src, url, purl)
            for tk in target_set:
                if tk in latest_by_key:
                    continue
                if r_key == tk or r_name.lower() == tk or f"/groups/{tk}" in url.lower() or f"/groups/{tk}" in purl.lower():
                    latest_by_key[tk] = pts
    return latest_by_key


def save_lead(source, external_id, title, content, author, url, location="",
              posted_at=None, platform="", kind="post", intent="",
              matched_keyword="", parent_url="", status="new",
              ai_verdict="", ai_reason="", comments_count=None):
    """Insert a lead after strict domain and URL structure verification."""
    plat = platform or infer_platform(source)
    if not is_valid_lead_url(plat, url, external_id):
        return False
    if not str(external_id or "").startswith("manual_"):
        if not matched_keyword or matched_keyword.lower() in ("seeker", "employer", "group post", "group comment"):
            return False

    c_cnt = None
    if comments_count is not None and not isinstance(comments_count, bool):
        try:
            parsed_cc = int(comments_count)
            if parsed_cc >= 0:
                c_cnt = parsed_cc
        except (ValueError, TypeError):
            c_cnt = None

    conn = get_db()
    try:
        with conn:
            # Content-hash deduplication for non-manual posts (prevents 2-6x cross-post spam)
            if not str(external_id or "").startswith("manual_") and (kind or "post") == "post":
                fp = lead_content_fingerprint(author, title, content, kind="post")
                if fp:
                    existing_rows = conn.execute(
                        "SELECT external_id, author, title, content, kind FROM leads WHERE external_id != ? AND kind = 'post' AND author = ?",
                        (external_id, author),
                    ).fetchall()
                    for ex in existing_rows:
                        if lead_content_fingerprint(ex["author"], ex["title"], ex["content"], ex["kind"]) == fp:
                            return False

            cur = conn.execute(
                """
                INSERT OR IGNORE INTO leads
                (source, external_id, title, content, author, url, location, posted_at,
                 platform, kind, intent, matched_keyword, parent_url, status, ai_verdict, ai_reason, comments_count, updated_at)
                VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, CURRENT_TIMESTAMP)
                """,
                (source, external_id, title, content, author, url, location, posted_at,
                 plat, kind or "post", intent or "seeker",
                 matched_keyword or "", parent_url or "", status or "new",
                 ai_verdict or "", ai_reason or "", c_cnt),
            )
            if cur.rowcount == 0 and (ai_verdict or status == "ai_filtered" or intent in ("seeker", "employer", "buyer", "seller") or c_cnt is not None):
                valid_intent = intent if intent in ("seeker", "employer", "buyer", "seller") else ""
                conn.execute(
                    """
                    UPDATE leads
                    SET ai_verdict = CASE WHEN status = 'new' AND ? != '' THEN ? ELSE ai_verdict END,
                        ai_reason = CASE WHEN status = 'new' AND ? != '' THEN ? ELSE ai_reason END,
                        intent = CASE WHEN external_id NOT LIKE 'manual_%' AND ? != '' THEN ? ELSE intent END,
                        status = CASE WHEN status = 'new' AND (? = 'ai_filtered' OR ? = 'filtered') THEN 'ai_filtered' ELSE status END,
                        comments_count = COALESCE(?, comments_count),
                        updated_at = CURRENT_TIMESTAMP
                    WHERE external_id = ?
                    """,
                    (
                        ai_verdict or "", ai_verdict or "",
                        ai_reason or "", ai_reason or "",
                        valid_intent, valid_intent,
                        status or "", ai_verdict or "",
                        c_cnt,
                        external_id,
                    ),
                )
            return cur.rowcount > 0
    finally:
        conn.close()


def platform_key(row):
    """Maps a stored lead to the dashboard platform checkbox keys."""
    platform = row.get("platform") or infer_platform(row.get("source"))
    kind = row.get("kind") or ("comment" if "comment" in (row.get("source") or "").lower() else "post")
    if platform == "reddit":
        return "reddit_comments" if kind == "comment" else "reddit_posts"
    if platform in ("facebook", "instagram", "tiktok"):
        return platform
    return "public_web"


def extract_fb_group_key_and_name(source, url, parent_url=""):
    """
    Extracts `(group_key, human_group_name)` from a Facebook group lead row.
    Returns `("", "")` if the lead is not from a Facebook group.
    """
    src = str(source or "").strip()
    u = str(url or "").strip()
    pu = str(parent_url or "").strip()
    if "facebook" not in src.lower() and "facebook.com" not in u.lower() and "facebook.com" not in pu.lower():
        return "", ""
    m_key = re.search(r"/groups/([^/?#]+)", u, re.I) or re.search(r"/groups/([^/?#]+)", pu, re.I)
    m_name = re.search(r"Facebook\s+(?:Comment\s+)?Group\s*\((.+)\)", src, re.I)
    url_key = m_key.group(1).strip().lower() if m_key else ""
    src_name = m_name.group(1).strip() if m_name else ""
    if not url_key and not src_name:
        return "", ""
    key = url_key or re.sub(r"\s+", "-", src_name.lower())
    if src_name:
        name = src_name
    elif url_key.isdigit():
        name = f"FB Group ({url_key})"
    else:
        name = url_key
    return key, name


def row_matches_fb_group(row, fb_group_filter):
    target = str(fb_group_filter or "").strip().lower()
    if not target:
        return True
    r_key, r_name = extract_fb_group_key_and_name(
        row.get("source"), row.get("url"), row.get("parent_url")
    )
    if not r_key and not r_name:
        return False
    return (
        r_key == target
        or r_name.lower() == target
        or f"/groups/{target}" in str(row.get("url") or "").lower()
        or f"/groups/{target}" in str(row.get("parent_url") or "").lower()
    )


def get_facebook_groups_summary(configured_urls=None, hidden_keys=None):
    """
    Returns a unified list of Facebook Groups synced from `config.json` (`social.facebook_groups`)
    and all scraped Facebook Group leads in `leads.db`, with human names and active lead counts.
    Respects `social.hidden_fb_groups` so groups removed by the user stay removed.
    """
    if configured_urls is None or hidden_keys is None:
        cfg_path = os.path.join(os.path.dirname(__file__), "config.json")
        try:
            import json as _json
            with open(cfg_path, "r", encoding="utf-8") as f:
                raw_cfg = _json.load(f)
            social_cfg = (raw_cfg.get("social") or {}) if isinstance(raw_cfg, dict) else {}
            if configured_urls is None:
                configured_urls = social_cfg.get("facebook_groups") or []
            if hidden_keys is None:
                hidden_keys = social_cfg.get("hidden_fb_groups") or []
        except Exception:
            if configured_urls is None:
                configured_urls = []
            if hidden_keys is None:
                hidden_keys = []

    hidden_set = {str(k).strip().lower() for k in (hidden_keys or []) if str(k).strip()}

    groups = {}
    for raw_u in (configured_urls or []):
        u_str = str(raw_u or "").strip()
        if not u_str:
            continue
        m = re.search(r"/groups/([^/?#]+)", u_str, re.I)
        slug = m.group(1).strip() if m else u_str.rstrip("/").split("/")[-1]
        key = slug.lower()
        if not key:
            continue
        clean_url = f"https://www.facebook.com/groups/{slug}/" if m else u_str
        default_name = f"FB Group ({slug})" if slug.isdigit() else slug
        groups[key] = {
            "key": key,
            "name": default_name,
            "url": clean_url,
            "count": 0,
            "configured": True,
            "intents": {},
        }

    conn = get_db()
    try:
        rows = conn.execute(
            """
            SELECT source, url, parent_url, intent
            FROM leads
            WHERE status NOT IN ('ai_filtered', 'archived')
              AND (lower(source) LIKE '%facebook%' OR lower(url) LIKE '%facebook.com/groups/%')
            """
        ).fetchall()
    except Exception:
        rows = []
    finally:
        conn.close()

    for r in rows:
        key, name = extract_fb_group_key_and_name(r["source"], r["url"], r["parent_url"])
        if not key:
            continue
        g = groups.get(key)
        if g is None:
            if key in hidden_set:
                continue
            g = {
                "key": key,
                "name": name,
                "url": f"https://www.facebook.com/groups/{key}/",
                "count": 0,
                "configured": False,
                "intents": {},
            }
            groups[key] = g
        elif name and not name.startswith("FB Group (") and (g["name"].startswith("FB Group (") or g["name"].lower() == key):
            g["name"] = name
        g["count"] += 1
        intent_val = str(r["intent"] or "").strip().lower()
        if intent_val:
            g["intents"][intent_val] = g["intents"].get(intent_val, 0) + 1

    out = []
    for g in groups.values():
        intents_map = g.pop("intents", {})
        primary_intent = max(intents_map.items(), key=lambda kv: kv[1])[0] if intents_map else "seeker"
        g["primary_intent"] = primary_intent
        g["all_intents"] = sorted(intents_map.keys())
        out.append(g)

    out.sort(key=lambda g: (-int(g["count"]), 0 if g["configured"] else 1, g["name"].lower()))
    return out


def search_leads(query="", platforms=None, intents=None, location="Any", status_filter="all",
                 max_age_days=7, since=None, limit=300, kind="all", fb_group=""):
    sql = "SELECT * FROM leads WHERE 1=1"
    params = []
    if not status_filter or status_filter == "all":
        sql += " AND status NOT IN ('ai_filtered', 'archived')"
    elif status_filter == "followup":
        sql += (
            " AND (status = 'followup'"
            " OR (followup_at IS NOT NULL AND followup_at <= datetime('now') AND status NOT IN ('closed', 'archived', 'ai_filtered'))"
            " OR (status = 'contacted' AND COALESCE(updated_at, found_at) <= datetime('now', '-2 days')))"
        )
    else:
        sql += " AND status = ?"
        params.append(status_filter)
    if max_age_days and int(max_age_days) > 0:
        sql += " AND COALESCE(posted_at, found_at) >= datetime('now', ?)"
        params.append(f"-{int(max_age_days)} days")
    if since:
        sql += " AND found_at > ?"
        params.append(since)
    sql += " ORDER BY COALESCE(posted_at, found_at) DESC, id DESC"

    conn = get_db()
    try:
        rows = [dict(r) for r in conn.execute(sql, params).fetchall()]
    finally:
        conn.close()

    q = (query or "").strip()
    pos_query, _ = parse_search_query(q)
    loc = (location or "Any").strip().lower()
    intents = set(intents) if intents else None
    kind_filter = (kind or "all").strip().lower()
    fb_group_filter = (fb_group or "").strip().lower()

    out = []
    for row in rows:
        plat = row.get("platform") or infer_platform(row.get("source"))
        if not is_valid_lead_url(plat, row.get("url"), row.get("external_id", "")):
            continue
        if fb_group_filter and not row_matches_fb_group(row, fb_group_filter):
            continue
        if platforms is not None and platform_key(row) not in platforms:
            continue
        row_kind = (row.get("kind") or ("comment" if "comment" in (row.get("source") or "").lower() else "post")).lower()
        if kind_filter in ("post", "comment") and row_kind != kind_filter:
            continue
        if intents is not None and status_filter != "ai_filtered" and (row.get("intent") or "") not in intents:
            continue
        haystack = " ".join(str(row.get(k) or "") for k in
                            ("title", "content", "author", "source", "location", "matched_keyword", "notes", "ai_reason")).lower()
        body_hay = " ".join(str(row.get(k) or "") for k in ("title", "content")).lower()
        if loc and loc != "any":
            loc_terms = LOCATION_MATCH_TERMS.get(loc, (loc,))
            has_target_loc = any(_term_in_text(body_hay, t) for t in loc_terms) or any(t in (row.get("location") or "").lower() for t in loc_terms)
            if loc == "cebu":
                has_explicit_cebu_in_body = any(_term_in_text(body_hay, t) for t in loc_terms)
                has_non_cebu = any(_term_in_text(body_hay, c) for c in NON_CEBU_LOCATION_TERMS)
                if has_non_cebu and not has_explicit_cebu_in_body:
                    continue
            if not has_target_loc and "remote" not in haystack:
                continue
        if q and not smart_query_matches(haystack, q):
            continue
        if pos_query:
            row["_relevance"] = score_query_relevance(row, pos_query)
        out.append(row)

    if pos_query:
        out.sort(key=lambda r: (r.get("_relevance", 0), r.get("posted_at") or r.get("found_at") or "", r.get("id") or 0), reverse=True)
        for r in out:
            r.pop("_relevance", None)
    return out[:limit]


def get_lead_by_id(lead_id):
    conn = get_db()
    try:
        row = conn.execute("SELECT * FROM leads WHERE id = ?", (lead_id,)).fetchone()
        return dict(row) if row else None
    finally:
        conn.close()


def update_lead_status(lead_id, new_status):
    conn = get_db()
    try:
        with conn:
            if new_status == "new":
                conn.execute(
                    "UPDATE leads SET status = ?, ai_verdict = CASE WHEN ai_verdict = 'filtered' THEN 'approved' ELSE ai_verdict END, updated_at = CURRENT_TIMESTAMP WHERE id = ?",
                    (new_status, lead_id),
                )
            elif new_status in ("closed", "archived", "ai_filtered"):
                conn.execute(
                    "UPDATE leads SET status = ?, followup_at = NULL, updated_at = CURRENT_TIMESTAMP WHERE id = ?",
                    (new_status, lead_id),
                )
            else:
                conn.execute(
                    "UPDATE leads SET status = ?, updated_at = CURRENT_TIMESTAMP WHERE id = ?",
                    (new_status, lead_id),
                )
    finally:
        conn.close()


def update_lead_followup(lead_id, followup_at=None):
    """Sets or clears the follow-up reminder timestamp (`followup_at`) for a lead."""
    val = (str(followup_at).strip() if followup_at is not None else "") or None
    conn = get_db()
    try:
        with conn:
            if val:
                conn.execute(
                    """
                    UPDATE leads
                    SET followup_at = ?,
                        status = CASE WHEN status IN ('new', 'contacted', 'followup') THEN 'followup' ELSE status END,
                        updated_at = CURRENT_TIMESTAMP
                    WHERE id = ?
                    """,
                    (val, lead_id),
                )
            else:
                conn.execute(
                    "UPDATE leads SET followup_at = NULL, updated_at = CURRENT_TIMESTAMP WHERE id = ?",
                    (lead_id,),
                )
    finally:
        conn.close()


def update_lead_ai_verdict(lead_id, verdict, reason, new_status=None, new_intent=None):
    valid_intent = new_intent if new_intent in ("seeker", "employer", "buyer", "seller") else None
    conn = get_db()
    try:
        with conn:
            if new_status and valid_intent:
                conn.execute(
                    "UPDATE leads SET ai_verdict = ?, ai_reason = ?, status = ?, intent = ?, updated_at = CURRENT_TIMESTAMP WHERE id = ?",
                    (verdict or "", reason or "", new_status, valid_intent, lead_id),
                )
            elif new_status:
                conn.execute(
                    "UPDATE leads SET ai_verdict = ?, ai_reason = ?, status = ?, updated_at = CURRENT_TIMESTAMP WHERE id = ?",
                    (verdict or "", reason or "", new_status, lead_id),
                )
            elif valid_intent:
                conn.execute(
                    "UPDATE leads SET ai_verdict = ?, ai_reason = ?, intent = ?, updated_at = CURRENT_TIMESTAMP WHERE id = ?",
                    (verdict or "", reason or "", valid_intent, lead_id),
                )
            else:
                conn.execute(
                    "UPDATE leads SET ai_verdict = ?, ai_reason = ? WHERE id = ?",
                    (verdict or "", reason or "", lead_id),
                )
    finally:
        conn.close()


def deduplicate_stored_leads(conn=None):
    """
    Removes duplicate cross-posted leads (same author + normalized title/body fingerprint),
    keeping the most recent or highest-priority row (preferring contacted/followup over new).
    """
    own_conn = conn is None
    if own_conn:
        conn = get_db()
    removed_ids = []
    try:
        rows = [
            dict(r)
            for r in conn.execute(
                """
                SELECT id, external_id, author, title, content, kind, status, posted_at, found_at
                FROM leads
                WHERE external_id NOT LIKE 'manual_%'
                ORDER BY
                    CASE WHEN status IN ('contacted', 'followup', 'closed') THEN 0 ELSE 1 END ASC,
                    COALESCE(posted_at, found_at) DESC,
                    id DESC
                """
            ).fetchall()
        ]
        seen_fps = set()
        for r in rows:
            fp = lead_content_fingerprint(r.get("author"), r.get("title"), r.get("content"), r.get("kind"))
            if not fp:
                continue
            if fp in seen_fps:
                removed_ids.append(r["id"])
            else:
                seen_fps.add(fp)
        if removed_ids:
            with conn:
                placeholders = ",".join("?" for _ in removed_ids)
                conn.execute(f"DELETE FROM leads WHERE id IN ({placeholders})", removed_ids)
    finally:
        if own_conn:
            conn.close()
    return len(removed_ids)


def reclassify_stored_leads(classifier_fn=None, platforms=None):
    """
    Re-evaluates existing non-manual leads in SQLite using the upgraded deterministic rules
    (Comment-Only Guard, Employer Veto, Corporate Author Classifier), rescues falsely AI-filtered
    employer job ads, and deduplicates cross-posted ads in place.
    """
    if classifier_fn is None:
        import scanners
        settings = scanners.get_settings({})
        classifier_fn = lambda row: scanners.classify_stored_row(row, settings)

    allowed_plats = set(platforms) if platforms else None
    conn = get_db()
    checked = 0
    updated = 0
    seeker_to_employer = 0
    rescued_from_ai_filtered = 0
    transitions = {}
    try:
        dedup_removed = deduplicate_stored_leads(conn)
        rows = [
            dict(r)
            for r in conn.execute(
                "SELECT id, source, external_id, title, content, author, platform, kind, intent, matched_keyword, status, ai_verdict, ai_reason FROM leads WHERE external_id NOT LIKE 'manual_%'"
            ).fetchall()
        ]
        with conn:
            for row in rows:
                if allowed_plats is not None and platform_key(row) not in allowed_plats:
                    continue
                checked += 1
                old_intent = (row.get("intent") or "").strip().lower()
                new_intent, new_kw = classifier_fn(row)
                if new_intent not in ("seeker", "employer", "buyer", "seller"):
                    continue
                old_kw = (row.get("matched_keyword") or "").strip()
                final_kw = new_kw or old_kw or new_intent

                # Rescue leads like #1241 ("Zark's Burgers is Hiring!!") that were only ai_filtered
                # because their old detected_intent was 'seeker' while the post was an employer job ad
                ai_rsn_low = (row.get("ai_reason") or "").lower()
                should_rescue = (
                    row.get("status") == "ai_filtered"
                    and new_intent == "employer"
                    and ("promotional job opening" in ai_rsn_low or "detected intent" in ai_rsn_low)
                )

                if new_intent != old_intent or final_kw != old_kw or should_rescue:
                    if should_rescue:
                        conn.execute(
                            "UPDATE leads SET intent = ?, matched_keyword = ?, status = 'new', ai_verdict = 'approved', updated_at = CURRENT_TIMESTAMP WHERE id = ?",
                            (new_intent, final_kw, row["id"]),
                        )
                        rescued_from_ai_filtered += 1
                    else:
                        conn.execute(
                            "UPDATE leads SET intent = ?, matched_keyword = ?, updated_at = CURRENT_TIMESTAMP WHERE id = ?",
                            (new_intent, final_kw, row["id"]),
                        )
                    if new_intent != old_intent:
                        updated += 1
                        key = f"{old_intent or 'unknown'}->{new_intent}"
                        transitions[key] = transitions.get(key, 0) + 1
                        if old_intent == "seeker" and new_intent == "employer":
                            seeker_to_employer += 1
    finally:
        conn.close()
    return {
        "checked": checked,
        "updated": updated,
        "seeker_to_employer": seeker_to_employer,
        "rescued_from_ai_filtered": rescued_from_ai_filtered,
        "deduplicated": dedup_removed,
        "transitions": transitions,
    }


def auto_archive_old_leads(days=14):
    days = int(days or 0)
    if days <= 0:
        return 0
    conn = get_db()
    try:
        with conn:
            cur = conn.execute(
                "UPDATE leads SET status = 'archived', updated_at = CURRENT_TIMESTAMP WHERE status = 'new' AND COALESCE(posted_at, found_at) < datetime('now', ?)",
                (f"-{days} days",),
            )
            return cur.rowcount
    finally:
        conn.close()


def update_lead_notes(lead_id, notes):
    conn = get_db()
    try:
        with conn:
            conn.execute("UPDATE leads SET notes = ?, updated_at = CURRENT_TIMESTAMP WHERE id = ?", (notes, lead_id))
    finally:
        conn.close()


def delete_lead(lead_id):
    conn = get_db()
    try:
        with conn:
            conn.execute("DELETE FROM leads WHERE id = ?", (lead_id,))
    finally:
        conn.close()


VALID_BULK_STATUSES = {"new", "contacted", "followup", "closed", "archived", "ai_filtered"}
VALID_BULK_ACTIONS = VALID_BULK_STATUSES | {"approve", "delete"}


def bulk_update_leads(ids, action):
    """
    Executes a bulk triage action ('new', 'contacted', 'followup', 'closed',
    'archived', 'ai_filtered', 'approve', or 'delete') across positive integer `ids`
    in a single SQLite transaction. Raises ValueError on empty valid IDs or invalid action.
    """
    act = str(action or "").strip().lower()
    if act not in VALID_BULK_ACTIONS:
        raise ValueError(f"Invalid bulk action: {action!r}")
    if not isinstance(ids, (list, tuple, set)):
        raise ValueError("ids must be a list of positive integers")

    clean_ids = []
    seen = set()
    for raw in ids:
        if isinstance(raw, bool):
            continue
        val = None
        if isinstance(raw, int):
            val = raw
        elif isinstance(raw, str) and raw.strip().isdigit():
            val = int(raw.strip())
        if val is not None and val > 0 and val not in seen:
            seen.add(val)
            clean_ids.append(val)

    if not clean_ids:
        raise ValueError("No valid positive lead IDs provided")

    conn = get_db()
    affected = 0
    try:
        with conn:
            for i in range(0, len(clean_ids), 500):
                chunk = clean_ids[i : i + 500]
                placeholders = ",".join("?" for _ in chunk)
                if act in VALID_BULK_STATUSES:
                    cur = conn.execute(
                        f"UPDATE leads SET status = ?, updated_at = CURRENT_TIMESTAMP WHERE id IN ({placeholders})",
                        [act, *chunk],
                    )
                elif act == "approve":
                    cur = conn.execute(
                        f"UPDATE leads SET status = 'new', ai_verdict = 'approved', ai_reason = 'Approved by user', updated_at = CURRENT_TIMESTAMP WHERE id IN ({placeholders})",
                        chunk,
                    )
                else:  # 'delete'
                    cur = conn.execute(
                        f"DELETE FROM leads WHERE id IN ({placeholders})",
                        chunk,
                    )
                affected += max(0, cur.rowcount or 0)
    finally:
        conn.close()
    return affected


def get_stats(platforms=None):
    conn = get_db()
    try:
        if platforms is None:
            one = lambda sql: conn.execute(sql).fetchone()[0]
            active_where = "status NOT IN ('ai_filtered', 'archived')"
            return {
                "total": one(f"SELECT COUNT(*) FROM leads WHERE {active_where}"),
                "new": one("SELECT COUNT(*) FROM leads WHERE status = 'new'"),
                "contacted": one("SELECT COUNT(*) FROM leads WHERE status IN ('contacted', 'followup', 'closed')"),
                "followup": one(
                    "SELECT COUNT(*) FROM leads WHERE status = 'followup'"
                    " OR (followup_at IS NOT NULL AND followup_at <= datetime('now') AND status NOT IN ('closed', 'archived', 'ai_filtered'))"
                    " OR (status = 'contacted' AND COALESCE(updated_at, found_at) <= datetime('now', '-2 days'))"
                ),
                "closed": one("SELECT COUNT(*) FROM leads WHERE status = 'closed'"),
                "archived": one("SELECT COUNT(*) FROM leads WHERE status = 'archived'"),
                "ai_filtered": one("SELECT COUNT(*) FROM leads WHERE status = 'ai_filtered'"),
                "seekers": one(f"SELECT COUNT(*) FROM leads WHERE {active_where} AND intent = 'seeker'"),
                "employers": one(f"SELECT COUNT(*) FROM leads WHERE {active_where} AND intent = 'employer'"),
                "buyers": one(f"SELECT COUNT(*) FROM leads WHERE {active_where} AND intent = 'buyer'"),
                "sellers": one(f"SELECT COUNT(*) FROM leads WHERE {active_where} AND intent = 'seller'"),
                "market": one(f"SELECT COUNT(*) FROM leads WHERE {active_where} AND intent IN ('buyer', 'seller')"),
                "comments": one(f"SELECT COUNT(*) FROM leads WHERE {active_where} AND kind = 'comment'"),
                "fb_groups": get_facebook_groups_summary(),
            }

        allowed = set(platforms)
        rows = [
            dict(r)
            for r in conn.execute(
                """
                SELECT platform, source, kind, intent, status, url, external_id, followup_at,
                       (COALESCE(updated_at, found_at) <= datetime('now', '-2 days')) AS is_stale,
                       (followup_at IS NOT NULL AND followup_at <= datetime('now')) AS is_followup_due
                FROM leads
                """
            ).fetchall()
        ]
        counts = {
            "total": 0, "new": 0, "contacted": 0, "followup": 0,
            "closed": 0, "archived": 0, "ai_filtered": 0,
            "seekers": 0, "employers": 0, "buyers": 0, "sellers": 0,
            "market": 0, "comments": 0,
        }
        for row in rows:
            plat = row.get("platform") or infer_platform(row.get("source"))
            if not is_valid_lead_url(plat, row.get("url"), row.get("external_id", "")):
                continue
            if platform_key(row) not in allowed:
                continue
            st = row.get("status") or "new"
            intent = row.get("intent") or ""
            kind = row.get("kind") or "post"
            if st == "new":
                counts["new"] += 1
            elif st == "ai_filtered":
                counts["ai_filtered"] += 1
            elif st == "archived":
                counts["archived"] += 1
            elif st == "closed":
                counts["closed"] += 1
            if st in ("contacted", "followup", "closed"):
                counts["contacted"] += 1
            if st == "followup" or (row.get("is_followup_due") and st not in ("closed", "archived", "ai_filtered")) or (st == "contacted" and row.get("is_stale")):
                counts["followup"] += 1
            if st not in ("ai_filtered", "archived"):
                counts["total"] += 1
                if intent == "seeker":
                    counts["seekers"] += 1
                elif intent == "employer":
                    counts["employers"] += 1
                elif intent == "buyer":
                    counts["buyers"] += 1
                    counts["market"] += 1
                elif intent == "seller":
                    counts["sellers"] += 1
                    counts["market"] += 1
                if kind == "comment":
                    counts["comments"] += 1
        counts["fb_groups"] = get_facebook_groups_summary()
        return counts
    finally:
        conn.close()


def utc_today_sql():
    return datetime.now(timezone.utc).strftime("%Y-%m-%d")


def record_api_usage(provider, count=1):
    """Increments the daily external API call counter for `provider` (never called on cache hits)."""
    prov = str(provider or "").strip().lower()
    inc = int(count or 0)
    if not prov or inc <= 0:
        return
    day = utc_today_sql()
    conn = get_db()
    try:
        with conn:
            conn.execute(
                """
                CREATE TABLE IF NOT EXISTS api_usage_daily (
                    date TEXT NOT NULL,
                    provider TEXT NOT NULL,
                    calls INTEGER NOT NULL DEFAULT 0,
                    PRIMARY KEY (date, provider)
                )
                """
            )
            conn.execute(
                """
                INSERT INTO api_usage_daily (date, provider, calls)
                VALUES (?, ?, ?)
                ON CONFLICT(date, provider) DO UPDATE SET calls = calls + excluded.calls
                """,
                (day, prov, inc),
            )
    except Exception:
        pass
    finally:
        conn.close()


def get_api_usage_today(date_str=None):
    """Returns `{provider: calls_int}` for the specified UTC date (defaults to today)."""
    day = str(date_str or utc_today_sql()).strip()
    conn = get_db()
    try:
        conn.execute(
            """
            CREATE TABLE IF NOT EXISTS api_usage_daily (
                date TEXT NOT NULL,
                provider TEXT NOT NULL,
                calls INTEGER NOT NULL DEFAULT 0,
                PRIMARY KEY (date, provider)
            )
            """
        )
        rows = conn.execute(
            "SELECT provider, calls FROM api_usage_daily WHERE date = ?",
            (day,),
        ).fetchall()
        return {str(r["provider"]): int(r["calls"] or 0) for r in rows}
    except Exception:
        return {}
    finally:
        conn.close()
