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


def smart_query_matches(haystack, query):
    """
    Matches user search queries accurately without false positives on phone storage ('128gb')
    or piece count ('1 pc').
    """
    q = re.sub(r"\s+", " ", (query or "").strip().lower()).rstrip("?")
    if not q:
        return True
    hay = (haystack or "").lower()

    # Exact phrase check with word boundaries
    if re.search(r"(?<!\w)" + re.escape(q) + r"(?!\w)", hay):
        return True

    if q in ("pc set", "system unit"):
        return any(
            re.search(r"(?<!\w)" + re.escape(term) + r"(?!\w)", hay)
            for term in ("pc set", "system unit", "gaming pc", "desktop pc", "full set pc", "ryzen")
        )

    if q in ("for sale", "fs", "selling"):
        return any(
            re.search(r"(?<!\w)" + re.escape(t) + r"(?!\w)", hay)
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
        matched_this_word = False
        for s in syns:
            if re.search(r"(?<!\w)" + re.escape(s) + r"(?!\w)", hay):
                matched_this_word = True
                break
        if not matched_this_word:
            return False
    return True


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

            # Ensure jobseeker phrases like 'interested po', 'how to apply', 'pwede pa mo apply', 'naay hiring'
            # are always categorized as 'seeker', never 'employer'
            if kw_low in ("interested po", "how to apply", "pwede pa mo apply", "naay hiring", "naay hiring?", "naa bay hiring", "apply ko", "nangita kog trabaho", "ngita kog trabaho", "ngita ko trabaho"):
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
    conn.close()


LOCATION_MATCH_TERMS = {
    "cebu": (
        "cebu", "mandaue", "lapu-lapu", "lapulapu", "lapu lapu", "talisay", "consolacion",
        "liloan", "minglanilla", "carcar", "danao", "toledo", "it park", "banilad", "mabolo",
        "lahug", "guadalupe", "fuente", "mactan", "cordova", "sm seaside", "ayala", "talamban",
    ),
}


def save_lead(source, external_id, title, content, author, url, location="",
              posted_at=None, platform="", kind="post", intent="",
              matched_keyword="", parent_url="", status="new",
              ai_verdict="", ai_reason=""):
    """Insert a lead after strict domain and URL structure verification."""
    plat = platform or infer_platform(source)
    if not is_valid_lead_url(plat, url, external_id):
        return False
    if not str(external_id or "").startswith("manual_"):
        if not matched_keyword or matched_keyword.lower() in ("seeker", "employer", "group post", "group comment"):
            return False

    conn = get_db()
    try:
        with conn:
            cur = conn.execute(
                """
                INSERT OR IGNORE INTO leads
                (source, external_id, title, content, author, url, location, posted_at,
                 platform, kind, intent, matched_keyword, parent_url, status, ai_verdict, ai_reason, updated_at)
                VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, CURRENT_TIMESTAMP)
                """,
                (source, external_id, title, content, author, url, location, posted_at,
                 plat, kind or "post", intent or "seeker",
                 matched_keyword or "", parent_url or "", status or "new",
                 ai_verdict or "", ai_reason or ""),
            )
            if cur.rowcount == 0 and (ai_verdict or status == "ai_filtered"):
                conn.execute(
                    """
                    UPDATE leads
                    SET ai_verdict = CASE WHEN status = 'new' THEN ? ELSE ai_verdict END,
                        ai_reason = CASE WHEN status = 'new' THEN ? ELSE ai_reason END,
                        status = CASE WHEN status = 'new' AND (? = 'ai_filtered' OR ? = 'filtered') THEN 'ai_filtered' ELSE status END,
                        updated_at = CURRENT_TIMESTAMP
                    WHERE external_id = ?
                    """,
                    (ai_verdict or "filtered", ai_reason or "", status or "", ai_verdict or "", external_id),
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


def search_leads(query="", platforms=None, intents=None, location="Any", status_filter="all",
                 max_age_days=7, since=None, limit=300):
    sql = "SELECT * FROM leads WHERE 1=1"
    params = []
    if not status_filter or status_filter == "all":
        sql += " AND status NOT IN ('ai_filtered', 'archived')"
    elif status_filter == "followup":
        sql += " AND (status = 'followup' OR (status = 'contacted' AND COALESCE(updated_at, found_at) <= datetime('now', '-2 days')))"
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
    loc = (location or "Any").strip().lower()
    intents = set(intents) if intents else None

    out = []
    for row in rows:
        plat = row.get("platform") or infer_platform(row.get("source"))
        if not is_valid_lead_url(plat, row.get("url"), row.get("external_id", "")):
            continue
        if platforms is not None and platform_key(row) not in platforms:
            continue
        if intents is not None and status_filter != "ai_filtered" and (row.get("intent") or "") not in intents:
            continue
        haystack = " ".join(str(row.get(k) or "") for k in
                            ("title", "content", "author", "source", "location", "matched_keyword", "notes", "ai_reason")).lower()
        if loc and loc != "any":
            loc_terms = LOCATION_MATCH_TERMS.get(loc, (loc,))
            if not any(t in haystack for t in loc_terms) and "remote" not in haystack:
                continue
        if q and not smart_query_matches(haystack, q):
            continue
        out.append(row)
        if len(out) >= limit:
            break
    return out


def update_lead_status(lead_id, new_status):
    conn = get_db()
    try:
        with conn:
            if new_status == "new":
                conn.execute(
                    "UPDATE leads SET status = ?, ai_verdict = CASE WHEN ai_verdict = 'filtered' THEN 'approved' ELSE ai_verdict END, updated_at = CURRENT_TIMESTAMP WHERE id = ?",
                    (new_status, lead_id),
                )
            else:
                conn.execute(
                    "UPDATE leads SET status = ?, updated_at = CURRENT_TIMESTAMP WHERE id = ?",
                    (new_status, lead_id),
                )
    finally:
        conn.close()


def update_lead_ai_verdict(lead_id, verdict, reason, new_status=None):
    conn = get_db()
    try:
        with conn:
            if new_status:
                conn.execute(
                    "UPDATE leads SET ai_verdict = ?, ai_reason = ?, status = ?, updated_at = CURRENT_TIMESTAMP WHERE id = ?",
                    (verdict or "", reason or "", new_status, lead_id),
                )
            else:
                conn.execute(
                    "UPDATE leads SET ai_verdict = ?, ai_reason = ? WHERE id = ?",
                    (verdict or "", reason or "", lead_id),
                )
    finally:
        conn.close()


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
                "followup": one("SELECT COUNT(*) FROM leads WHERE status = 'followup' OR (status = 'contacted' AND COALESCE(updated_at, found_at) <= datetime('now', '-2 days'))"),
                "closed": one("SELECT COUNT(*) FROM leads WHERE status = 'closed'"),
                "archived": one("SELECT COUNT(*) FROM leads WHERE status = 'archived'"),
                "ai_filtered": one("SELECT COUNT(*) FROM leads WHERE status = 'ai_filtered'"),
                "seekers": one(f"SELECT COUNT(*) FROM leads WHERE {active_where} AND intent = 'seeker'"),
                "employers": one(f"SELECT COUNT(*) FROM leads WHERE {active_where} AND intent = 'employer'"),
                "buyers": one(f"SELECT COUNT(*) FROM leads WHERE {active_where} AND intent = 'buyer'"),
                "sellers": one(f"SELECT COUNT(*) FROM leads WHERE {active_where} AND intent = 'seller'"),
                "market": one(f"SELECT COUNT(*) FROM leads WHERE {active_where} AND intent IN ('buyer', 'seller')"),
                "comments": one(f"SELECT COUNT(*) FROM leads WHERE {active_where} AND kind = 'comment'"),
            }

        allowed = set(platforms)
        rows = [
            dict(r)
            for r in conn.execute(
                """
                SELECT platform, source, kind, intent, status, url, external_id,
                       (COALESCE(updated_at, found_at) <= datetime('now', '-2 days')) AS is_stale
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
            if st == "followup" or (st == "contacted" and row.get("is_stale")):
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
        return counts
    finally:
        conn.close()
