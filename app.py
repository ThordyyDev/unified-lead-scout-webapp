import csv
import errno
import http.server
import importlib
import io
import json
import os
import re
import signal
import socketserver
import sys
import threading
import time
import urllib.parse
from datetime import datetime, timedelta, timezone

import database
import scanners

PORT = 5050
BASE_DIR = os.path.dirname(__file__)
CONFIG_FILE = os.path.join(BASE_DIR, "config.json")
TEMPLATE_DIR = os.path.join(BASE_DIR, "templates")

SCAN_MANAGER = scanners.ScanManager()
_RELOAD_LOCK = threading.Lock()
_MODULE_MTIMES = {
    "database": os.path.getmtime(database.__file__),
    "scanners": os.path.getmtime(scanners.__file__),
    "app": os.path.getmtime(__file__),
}


def ensure_fresh_modules():
    """
    Hot-reloads `database.py`, `scanners.py`, and `LeadScoutHandler` methods if modified on disk
    while the server is running, so code updates take effect without restarting `python3 app.py`.
    """
    global SCAN_MANAGER
    with _RELOAD_LOCK:
        if SCAN_MANAGER.status().get("running"):
            return
        db_mtime = os.path.getmtime(database.__file__)
        sc_mtime = os.path.getmtime(scanners.__file__)
        app_mtime = os.path.getmtime(__file__)
        if db_mtime != _MODULE_MTIMES["database"] or sc_mtime != _MODULE_MTIMES["scanners"]:
            importlib.reload(database)
            database.init_db()
            importlib.reload(scanners)
            SCAN_MANAGER = scanners.ScanManager()
            _MODULE_MTIMES["database"] = db_mtime
            _MODULE_MTIMES["scanners"] = sc_mtime
            print(f"[hot-reload] Reloaded database.py & scanners.py ({getattr(scanners, 'SCANNER_VERSION', 'latest')})")
        if app_mtime != _MODULE_MTIMES.get("app"):
            _MODULE_MTIMES["app"] = app_mtime
            try:
                ns = {
                    "__file__": __file__,
                    "__name__": "_app_hot_reload",
                }
                with open(__file__, "r", encoding="utf-8") as f:
                    src = f.read()
                # Preserve singleton SCAN_MANAGER, locks, and mtimes across handler hot-reload
                src_patched = re.sub(
                    r"^SCAN_MANAGER\s*=\s*scanners\.ScanManager\(\)",
                    "SCAN_MANAGER = _SHARED_SCAN_MANAGER",
                    src,
                    count=1,
                    flags=re.M,
                )
                ns["_SHARED_SCAN_MANAGER"] = SCAN_MANAGER
                code = compile(src_patched, __file__, "exec")
                exec(code, ns)
                ns["_RELOAD_LOCK"] = _RELOAD_LOCK
                ns["_MODULE_MTIMES"] = _MODULE_MTIMES
                new_cls = ns.get("LeadScoutHandler")
                if new_cls:
                    LeadScoutHandler.do_GET = new_cls.do_GET
                    LeadScoutHandler.do_POST = new_cls.do_POST
                    print("[hot-reload] Reloaded app.py request handlers")
            except Exception as e:
                print(f"[hot-reload] app.py handler reload skipped: {e}")


def _safe_int(val, default=0):
    try:
        if val in (None, ""):
            return default
        return int(val)
    except (ValueError, TypeError):
        return default


def _safe_float(val, default=0.0):
    try:
        if val in (None, ""):
            return default
        return float(val)
    except (ValueError, TypeError):
        return default


def load_config():
    if os.path.exists(CONFIG_FILE):
        try:
            with open(CONFIG_FILE, "r", encoding="utf-8") as f:
                data = json.load(f)
                return data if isinstance(data, dict) else {}
        except Exception:
            return {}
    return {}


def save_config(cfg):
    with open(CONFIG_FILE, "w", encoding="utf-8") as f:
        json.dump(cfg, f, indent=2)


class ReusableTCPServer(socketserver.ThreadingMixIn, socketserver.TCPServer):
    allow_reuse_address = True
    daemon_threads = True
    block_on_close = False


class LeadScoutHandler(http.server.BaseHTTPRequestHandler):
    def log_message(self, fmt, *args):
        sys.stderr.write("%s - [%s] %s\n" % (self.address_string(), self.log_date_time_string(), fmt % args))

    def send_json(self, data, status=200):
        body = json.dumps(data).encode("utf-8")
        self.send_response(status)
        self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Access-Control-Allow-Origin", "*")
        self.send_header("Access-Control-Allow-Methods", "GET, POST, OPTIONS")
        self.send_header("Access-Control-Allow-Headers", "Content-Type")
        self.end_headers()
        self.wfile.write(body)

    def do_OPTIONS(self):
        self.send_response(200)
        self.send_header("Access-Control-Allow-Origin", "*")
        self.send_header("Access-Control-Allow-Methods", "GET, POST, OPTIONS")
        self.send_header("Access-Control-Allow-Headers", "Content-Type")
        self.end_headers()

    def do_GET(self):
        ensure_fresh_modules()
        parsed = urllib.parse.urlparse(self.path)
        path = parsed.path
        query = urllib.parse.parse_qs(parsed.query)

        if path in ("/", "/index.html"):
            html_path = os.path.join(TEMPLATE_DIR, "index.html")
            if os.path.exists(html_path):
                with open(html_path, "rb") as f:
                    content = f.read()
                self.send_response(200)
                self.send_header("Content-Type", "text/html; charset=utf-8")
                self.send_header("Cache-Control", "no-store, no-cache, must-revalidate, max-age=0")
                self.send_header("Content-Length", str(len(content)))
                self.end_headers()
                self.wfile.write(content)
            else:
                self.send_response(404)
                self.end_headers()
                self.wfile.write(b"index.html not found")
            return

        if path == "/api/leads":
            cfg = load_config()
            settings = scanners.get_settings(cfg)
            if settings.get("auto_archive_days", 0) > 0:
                database.auto_archive_old_leads(settings["auto_archive_days"])
            status_filter = query.get("status", ["all"])[0]
            q_kw = query.get("q", [""])[0]
            location = query.get("location", ["Any"])[0]
            max_age_days = _safe_int(query.get("max_age_days", ["7"])[0], 7)
            platforms_raw = query.get("platforms", [""])[0]
            platforms = [p.strip() for p in platforms_raw.split(",") if p.strip()] if platforms_raw else None
            intents_raw = query.get("intents", [""])[0]
            intents = [i.strip() for i in intents_raw.split(",") if i.strip()] if intents_raw else None
            kind_filter = query.get("kind", ["all"])[0]
            fb_group = query.get("fb_group", [""])[0].strip()

            leads = database.search_leads(
                query=q_kw,
                platforms=platforms,
                intents=intents,
                location=location,
                status_filter=status_filter,
                max_age_days=max_age_days,
                kind=kind_filter,
                fb_group=fb_group,
            )
            social_cfg = (cfg.get("social") or {}) if isinstance(cfg.get("social"), dict) else {}
            fb_cfg_urls = social_cfg.get("facebook_groups") or []
            fb_hidden = social_cfg.get("hidden_fb_groups") or []
            self.send_json({
                "leads": leads,
                "stats": database.get_stats(platforms=platforms),
                "scan": SCAN_MANAGER.status(),
                "adapters": scanners.get_registered_adapters(cfg),
                "fb_groups": database.get_facebook_groups_summary(fb_cfg_urls, fb_hidden),
            })
            return

        if path == "/api/leads/export":
            status_filter = query.get("status", ["all"])[0]
            q_kw = query.get("q", [""])[0]
            location = query.get("location", ["Any"])[0]
            max_age_days = _safe_int(query.get("max_age_days", ["365"])[0], 365)
            platforms_raw = query.get("platforms", [""])[0]
            platforms = [p.strip() for p in platforms_raw.split(",") if p.strip()] if platforms_raw else None
            intents_raw = query.get("intents", [""])[0]
            intents = [i.strip() for i in intents_raw.split(",") if i.strip()] if intents_raw else None
            kind_filter = query.get("kind", ["all"])[0]
            fb_group = query.get("fb_group", [""])[0].strip()

            leads = database.search_leads(
                query=q_kw,
                platforms=platforms,
                intents=intents,
                location=location,
                status_filter=status_filter,
                max_age_days=max_age_days,
                kind=kind_filter,
                fb_group=fb_group,
                limit=2000,
            )
            buf = io.StringIO()
            writer = csv.writer(buf)
            writer.writerow([
                "ID", "Status", "Intent", "AI_Verdict", "AI_Reason",
                "Source", "Author", "Location", "Posted_At",
                "Matched_Keyword", "Title", "Content", "Notes", "URL"
            ])
            for ld in leads:
                writer.writerow([
                    ld.get("id", ""),
                    ld.get("status", ""),
                    ld.get("intent", ""),
                    ld.get("ai_verdict", ""),
                    ld.get("ai_reason", ""),
                    ld.get("source", ""),
                    ld.get("author", ""),
                    ld.get("location", ""),
                    ld.get("posted_at") or ld.get("found_at") or "",
                    ld.get("matched_keyword", ""),
                    ld.get("title", ""),
                    ld.get("content", ""),
                    ld.get("notes", ""),
                    ld.get("url", ""),
                ])
            csv_bytes = buf.getvalue().encode("utf-8-sig")
            self.send_response(200)
            self.send_header("Content-Type", "text/csv; charset=utf-8")
            self.send_header("Content-Disposition", 'attachment; filename="unified_leads_export.csv"')
            self.send_header("Content-Length", str(len(csv_bytes)))
            self.end_headers()
            self.wfile.write(csv_bytes)
            return

        if path == "/api/scan/status":
            platforms_raw = query.get("platforms", [""])[0]
            platforms = [p.strip() for p in platforms_raw.split(",") if p.strip()] if platforms_raw else None
            self.send_json({
                "scan": SCAN_MANAGER.status(),
                "stats": database.get_stats(platforms=platforms),
            })
            return

        if path == "/api/adapters":
            self.send_json({"adapters": scanners.get_registered_adapters(load_config())})
            return

        if path == "/api/config":
            self.send_json(load_config())
            return

        if path == "/api/credits":
            force = query.get("refresh", ["0"])[0] in ("1", "true", "yes")
            cfg = load_config()
            try:
                self.send_json(scanners.get_api_credits_status(cfg, force=force))
            except Exception:
                self.send_json({
                    "success": True,
                    "date": datetime.now(timezone.utc).strftime("%Y-%m-%d"),
                    "total_calls_today": 0,
                    "providers": [],
                })
            return

        if path.startswith("/api/"):
            self.send_json({"error": "Endpoint not found"}, 404)
            return

        self.send_response(404)
        self.end_headers()

    def do_POST(self):
        ensure_fresh_modules()
        parsed = urllib.parse.urlparse(self.path)
        path = parsed.path
        length = max(0, _safe_int(self.headers.get("Content-Length", 0), 0))
        body = self.rfile.read(length) if length > 0 else b"{}"

        try:
            payload = json.loads(body.decode("utf-8")) if body else {}
        except Exception:
            payload = {}
        if not isinstance(payload, dict):
            payload = {}

        if path in ("/api/search", "/api/scan"):
            cfg = load_config()
            s_cfg = cfg.get("search_settings") if isinstance(cfg.get("search_settings"), dict) else {}
            query_kw = str(payload.get("query") or "").strip()
            raw_plats = payload.get("platforms")
            platforms = [str(p).strip() for p in raw_plats if str(p).strip()] if isinstance(raw_plats, list) and raw_plats else [
                "reddit_posts", "reddit_comments", "facebook", "tiktok", "instagram", "public_web"
            ]
            raw_intents = payload.get("intents")
            intents = [str(i).strip() for i in raw_intents if str(i).strip()] if isinstance(raw_intents, list) and raw_intents else ["seeker", "employer"]
            location = str(payload.get("location") or s_cfg.get("location", "Cebu"))
            status_filter = str(payload.get("status") or "all")
            kind_filter = str(payload.get("kind") or "all").strip().lower()
            max_age_days = _safe_int(payload.get("max_age_days", s_cfg.get("max_age_days", 7)), 7)
            fb_group = str(payload.get("fb_group") or "").strip()

            params = {
                "query": query_kw,
                "platforms": platforms,
                "intents": intents,
                "location": location,
                "max_age_days": max_age_days,
                "fb_group": fb_group,
            }
            req_trigger = payload.get("trigger") or ("search" if path == "/api/search" else "scan")
            with _RELOAD_LOCK:
                started = SCAN_MANAGER.start(cfg, params, trigger=req_trigger)

            wait_sec = min(15.0, max(0.0, _safe_float(payload.get("wait_seconds", 2), 2.0)))
            wait_deadline = time.time() + wait_sec
            while SCAN_MANAGER.status().get("running") and time.time() < wait_deadline:
                time.sleep(0.25)

            scan_state = SCAN_MANAGER.status()
            is_audit_status = status_filter in ("ai_filtered", "archived")
            leads = database.search_leads(
                query=query_kw,
                platforms=platforms,
                intents=intents,
                location="Any" if (is_audit_status or fb_group) else location,
                status_filter=status_filter,
                max_age_days=365 if (is_audit_status or fb_group) else max_age_days,
                kind=kind_filter,
                fb_group=fb_group,
            )
            fb_cfg_urls = ((cfg.get("social") or {}).get("facebook_groups") or []) if isinstance(cfg.get("social"), dict) else []
            self.send_json({
                "success": True,
                "started": started,
                "query": query_kw,
                "location": location,
                "max_age_days": max_age_days,
                "platforms": platforms,
                "intents": intents,
                "scan": scan_state,
                "live_found_count": scan_state.get("new_total", 0),
                "match_count": len(leads),
                "leads": leads,
                "stats": database.get_stats(platforms=platforms),
                "fb_groups": database.get_facebook_groups_summary(fb_cfg_urls),
            })
            return

        if path == "/api/scan/cancel":
            cancelled = SCAN_MANAGER.cancel()
            raw_plats = payload.get("platforms")
            platforms = [str(p).strip() for p in raw_plats if str(p).strip()] if isinstance(raw_plats, list) and raw_plats else None
            self.send_json({
                "success": True,
                "cancelled": cancelled,
                "scan": SCAN_MANAGER.status(),
                "stats": database.get_stats(platforms=platforms),
            })
            return

        if path == "/api/lead/status":
            lead_id = payload.get("id")
            new_status = str(payload.get("status") or "").strip()
            valid_statuses = {"new", "contacted", "followup", "closed", "archived", "ai_filtered"}
            if lead_id and new_status in valid_statuses:
                database.update_lead_status(lead_id, new_status)
                self.send_json({"success": True, "stats": database.get_stats()})
            else:
                self.send_json({"error": "Missing or invalid id or status"}, 400)
            return

        if path == "/api/lead/notes":
            lead_id = payload.get("id")
            notes = str(payload.get("notes") or "")
            if lead_id:
                database.update_lead_notes(lead_id, notes)
                self.send_json({"success": True})
            else:
                self.send_json({"error": "Missing id"}, 400)
            return

        if path == "/api/lead/followup":
            lead_id = payload.get("id")
            if not lead_id:
                self.send_json({"error": "Missing id"}, 400)
                return
            days = payload.get("days")
            raw_at = payload.get("followup_at")
            if raw_at is not None and str(raw_at).strip():
                target_ts = str(raw_at).strip()
            elif days not in (None, "", 0, "0"):
                n_days = max(1, min(90, _safe_int(days, 1)))
                target_ts = (datetime.now(timezone.utc) + timedelta(days=n_days)).strftime("%Y-%m-%d %H:%M:%S")
            else:
                target_ts = None
            database.update_lead_followup(lead_id, target_ts)
            self.send_json({"success": True, "followup_at": target_ts, "stats": database.get_stats()})
            return

        if path == "/api/lead/mine-comments":
            lead_id = payload.get("id")
            if not lead_id:
                self.send_json({"error": "Missing id"}, 400)
                return
            lead_row = database.get_lead_by_id(lead_id)
            if not lead_row:
                self.send_json({"error": "Lead not found"}, 404)
                return
            cfg = load_config()
            max_comments = max(5, min(100, _safe_int(payload.get("max_comments", 35), 35)))
            res = scanners.mine_facebook_post_comments(lead_row, cfg, max_comments=max_comments)
            if not res.get("success"):
                self.send_json(res, 400)
                return
            raw_plats = payload.get("platforms")
            platforms = [str(p).strip() for p in raw_plats if str(p).strip()] if isinstance(raw_plats, list) and raw_plats else None
            res["stats"] = database.get_stats(platforms=platforms)
            self.send_json(res)
            return

        if path == "/api/lead/ai-draft":
            lead_id = payload.get("id")
            tone = str(payload.get("tone") or "friendly").strip().lower()
            if not lead_id:
                self.send_json({"error": "Missing id"}, 400)
                return
            lead_row = database.get_lead_by_id(lead_id)
            if not lead_row:
                self.send_json({"error": "Lead not found"}, 404)
                return
            cfg = load_config()
            settings = scanners.get_settings(cfg)
            res = scanners.generate_ai_reply_draft(lead_row, tone=tone, settings=settings)
            if not res.get("success"):
                self.send_json(res, 400)
                return
            self.send_json(res)
            return

        if path == "/api/lead/delete":
            lead_id = payload.get("id")
            if lead_id:
                database.delete_lead(lead_id)
                self.send_json({"success": True, "stats": database.get_stats()})
            else:
                self.send_json({"error": "Missing id"}, 400)
            return

        if path == "/api/leads/bulk":
            raw_ids = payload.get("ids")
            action = str(payload.get("action") or "").strip().lower()
            raw_plats = payload.get("platforms")
            platforms = [str(p).strip() for p in raw_plats if str(p).strip()] if isinstance(raw_plats, list) and raw_plats else None
            if not isinstance(raw_ids, list) or not action:
                self.send_json({"error": "Missing or invalid ids or action"}, 400)
                return
            try:
                affected = database.bulk_update_leads(raw_ids, action)
            except ValueError as ve:
                self.send_json({"error": str(ve)}, 400)
                return
            self.send_json({
                "success": True,
                "affected": affected,
                "action": action,
                "stats": database.get_stats(platforms=platforms),
            })
            return

        if path == "/api/lead/add":
            title = str(payload.get("title") or "").strip()
            url = str(payload.get("url") or "").strip()
            source = str(payload.get("source") or "Manual / Facebook")
            content = str(payload.get("content") or "")
            author = str(payload.get("author") or "User")
            location = str(payload.get("location") or "Cebu")
            intent = str(payload.get("intent") or "seeker")
            kind = "comment" if "comment" in source.lower() else "post"

            if not title or not url:
                self.send_json({"error": "Title and URL are required"}, 400)
                return
            if not url.lower().startswith(("http://", "https://")):
                self.send_json({"error": "URL must start with http:// or https://"}, 400)
                return

            ext_id = f"manual_{abs(hash(url + title))}"
            saved = database.save_lead(
                source=source,
                external_id=ext_id,
                title=title,
                content=content,
                author=author,
                url=url,
                location=location,
                posted_at=database.utc_now_sql(),
                kind=kind,
                intent=intent,
                matched_keyword="manual",
            )
            self.send_json({"success": True, "is_new": saved, "stats": database.get_stats()})
            return

        if path == "/api/config":
            save_config(payload)
            social_cfg = (payload.get("social") or {}) if isinstance(payload.get("social"), dict) else {}
            fb_cfg_urls = social_cfg.get("facebook_groups") or []
            fb_hidden = social_cfg.get("hidden_fb_groups") or []
            self.send_json({
                "success": True,
                "config": payload,
                "adapters": scanners.get_registered_adapters(payload),
                "fb_groups": database.get_facebook_groups_summary(fb_cfg_urls, fb_hidden),
            })
            return

        if path == "/api/credits":
            force = bool(payload.get("refresh", False))
            cfg = load_config()
            # Allow checking unsaved key edits typed into Settings -> API Keys without persisting them yet
            overrides = payload.get("overrides") if isinstance(payload.get("overrides"), dict) else {}
            if overrides:
                cfg = json.loads(json.dumps(cfg or {}))
                cfg["providers"] = dict(cfg.get("providers") or {})
                if "apify_token" in overrides:
                    cfg["apify_token"] = str(overrides.get("apify_token") or "").strip()
                for pk in ("gemini_api_key", "gemini_model", "serper_api_key", "tavily_api_key", "brave_api_key", "custom_api_url", "custom_api_key"):
                    if pk in overrides:
                        cfg["providers"][pk] = str(overrides.get(pk) or "").strip()
            try:
                self.send_json(scanners.get_api_credits_status(cfg, force=force))
            except Exception:
                self.send_json({
                    "success": True,
                    "date": datetime.now(timezone.utc).strftime("%Y-%m-%d"),
                    "total_calls_today": 0,
                    "providers": [],
                })
            return

        if path == "/api/alerts/test":
            cfg = load_config()
            settings = scanners.get_settings(cfg)
            wh_url = str(payload.get("webhook_url") or settings.get("alert_webhook_url") or "").strip()
            tg_token = str(payload.get("telegram_bot_token") or settings.get("telegram_bot_token") or "").strip()
            tg_chat = str(payload.get("telegram_chat_id") or settings.get("telegram_chat_id") or "").strip()
            sample = [{
                "title": "Test Alert: Cebu Jobseeker ready to start ASAP",
                "content": "Looking for kitchen helper / dishwasher work in Mandaue, Cebu.",
                "source": "Unified Lead Scout (Test)",
                "url": "http://localhost:5050",
                "intent": "seeker",
            }]
            wh_sent = scanners.send_webhook_notification(wh_url, sample, trigger="test") if wh_url else False
            tg_sent = scanners.send_telegram_notification(tg_token, tg_chat, sample, trigger="test") if (tg_token and tg_chat) else False
            self.send_json({
                "success": True,
                "webhook_configured": bool(wh_url),
                "webhook_sent": wh_sent,
                "telegram_configured": bool(tg_token and tg_chat),
                "telegram_sent": tg_sent,
            })
            return

        if path == "/api/leads/reclassify":
            cfg = load_config()
            settings = scanners.get_settings(cfg)
            raw_plats = payload.get("platforms")
            if isinstance(raw_plats, str):
                platforms = [p.strip() for p in raw_plats.split(",") if p.strip()] or None
            elif isinstance(raw_plats, list):
                platforms = [str(p).strip() for p in raw_plats if str(p).strip()] or None
            else:
                platforms = None
            summary = database.reclassify_stored_leads(
                classifier_fn=lambda row: scanners.classify_stored_row(row, settings),
                platforms=platforms,
            )
            self.send_json({
                "success": True,
                "platforms": platforms or [],
                **summary,
                "stats": database.get_stats(platforms=platforms),
            })
            return

        if path == "/api/leads/ai-audit":
            cfg = load_config()
            settings = scanners.get_settings(cfg)
            raw_plats = payload.get("platforms")
            if isinstance(raw_plats, str):
                platforms = [p.strip() for p in raw_plats.split(",") if p.strip()] or None
            elif isinstance(raw_plats, list):
                platforms = [str(p).strip() for p in raw_plats if str(p).strip()] or None
            else:
                platforms = None
            force = bool(payload.get("force", False))
            reclass_summary = database.reclassify_stored_leads(
                classifier_fn=lambda row: scanners.classify_stored_row(row, settings),
                platforms=platforms,
            )
            active_leads = database.search_leads(
                status_filter="all",
                platforms=platforms,
                max_age_days=365,
                limit=300,
            )
            prev_intents = {ld["id"]: ld.get("intent") for ld in active_leads}
            scanners.screen_leads_with_ai(active_leads, settings, skip_already_approved=not force)
            filtered_count = 0
            ai_reclassified = 0
            for ld in active_leads:
                verdict = ld.get("ai_verdict", "approved")
                reason = ld.get("ai_reason", "")
                new_intent = ld.get("intent")
                if new_intent and new_intent != prev_intents.get(ld["id"]):
                    ai_reclassified += 1
                if verdict == "filtered":
                    filtered_count += 1
                    database.update_lead_ai_verdict(ld["id"], verdict, reason, new_status="ai_filtered", new_intent=new_intent)
                else:
                    database.update_lead_ai_verdict(ld["id"], verdict, reason, new_intent=new_intent)
            self.send_json({
                "success": True,
                "platforms": platforms or [],
                "checked_count": len(active_leads),
                "filtered_count": filtered_count,
                "reclassified_count": reclass_summary.get("updated", 0) + ai_reclassified,
                "seeker_to_employer": reclass_summary.get("seeker_to_employer", 0),
                "stats": database.get_stats(platforms=platforms),
            })
            return

        self.send_response(404)
        self.end_headers()


def _autoscan_loop():
    last_auto_ts = time.time()
    while True:
        time.sleep(15)
        try:
            ensure_fresh_modules()
            cfg = load_config()
            s_cfg = cfg.get("search_settings", {})
            mins = int(s_cfg.get("autoscan_minutes", cfg.get("autoscan_minutes", 0)) or 0)
            if mins <= 0:
                continue
            if SCAN_MANAGER.status().get("running"):
                continue
            now = time.time()
            last_done = max(last_auto_ts, getattr(SCAN_MANAGER, "last_finished_epoch", 0.0))
            if (now - last_done) >= mins * 60:
                last_auto_ts = now
                platforms = ["reddit_posts", "reddit_comments", "public_web", "facebook", "tiktok", "instagram"]
                params = {
                    "query": "",
                    "platforms": platforms,
                    "intents": ["seeker", "employer", "buyer", "seller"],
                    "location": s_cfg.get("location", "Cebu"),
                    "max_age_days": int(s_cfg.get("max_age_days", 7) or 7),
                }
                print(f"[autoscan] Running scheduled credit-safe scan (every {mins}m)...")
                SCAN_MANAGER.start(cfg, params, trigger="auto")
        except Exception as e:
            print(f"[autoscan] Error: {e}")


def run_server():
    database.init_db()
    threading.Thread(target=_autoscan_loop, daemon=True).start()
    server_address = ("127.0.0.1", PORT)
    try:
        httpd = ReusableTCPServer(server_address, LeadScoutHandler)
    except OSError as e:
        if e.errno == errno.EADDRINUSE:
            print(f"\n[ERROR] Port {PORT} is already in use by an existing server process.")
            print(f"Stop the old process and restart with:\n  fuser -k {PORT}/tcp && python3 app.py\n")
            sys.exit(1)
        raise

    def _sigterm_handler(signum, frame):
        raise KeyboardInterrupt()

    signal.signal(signal.SIGTERM, _sigterm_handler)

    print("=====================================================")
    print(f"🚀 Unified Lead Scout {scanners.SCANNER_VERSION} is LIVE at http://localhost:{PORT}")
    print("Strict Domain & URL Verifier: ENABLED (SQLite Trigger + Scanner Guard)")
    print("Targets: Jobseekers & Employers | Posts & Comment Trees")
    print("Platforms: Reddit, Facebook, TikTok, Instagram, Web RSS")
    print("Press Ctrl+C to stop.")
    print("=====================================================")
    try:
        httpd.serve_forever(poll_interval=0.25)
    except KeyboardInterrupt:
        print("\nShutting down server...", flush=True)
        try:
            httpd.server_close()
        except Exception:
            pass
        try:
            SCAN_MANAGER.cancel()
        except Exception:
            pass
        os._exit(0)


if __name__ == "__main__":
    run_server()
