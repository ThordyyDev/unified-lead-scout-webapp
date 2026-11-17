import csv
import http.server
import importlib
import io
import json
import os
import re
import socketserver
import sys
import threading
import time
import urllib.parse

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
}


def ensure_fresh_modules():
    """
    Hot-reloads `database.py` and `scanners.py` if they were modified on disk while the
    server is running, so code updates take effect without needing to restart `python3 app.py`.
    """
    global SCAN_MANAGER
    with _RELOAD_LOCK:
        if SCAN_MANAGER.status().get("running"):
            return
        db_mtime = os.path.getmtime(database.__file__)
        sc_mtime = os.path.getmtime(scanners.__file__)
        if db_mtime != _MODULE_MTIMES["database"] or sc_mtime != _MODULE_MTIMES["scanners"]:
            importlib.reload(database)
            database.init_db()
            importlib.reload(scanners)
            SCAN_MANAGER = scanners.ScanManager()
            _MODULE_MTIMES["database"] = db_mtime
            _MODULE_MTIMES["scanners"] = sc_mtime
            print(f"[hot-reload] Reloaded database.py & scanners.py ({getattr(scanners, 'SCANNER_VERSION', 'latest')})")


def load_config():
    if os.path.exists(CONFIG_FILE):
        with open(CONFIG_FILE, "r", encoding="utf-8") as f:
            return json.load(f)
    return {}


def save_config(cfg):
    with open(CONFIG_FILE, "w", encoding="utf-8") as f:
        json.dump(cfg, f, indent=2)


class ReusableTCPServer(socketserver.ThreadingMixIn, socketserver.TCPServer):
    allow_reuse_address = True
    daemon_threads = True


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
            max_age_days = int(query.get("max_age_days", ["7"])[0] or 7)
            platforms_raw = query.get("platforms", [""])[0]
            platforms = [p.strip() for p in platforms_raw.split(",") if p.strip()] if platforms_raw else None
            intents_raw = query.get("intents", [""])[0]
            intents = [i.strip() for i in intents_raw.split(",") if i.strip()] if intents_raw else None

            leads = database.search_leads(
                query=q_kw,
                platforms=platforms,
                intents=intents,
                location=location,
                status_filter=status_filter,
                max_age_days=max_age_days,
            )
            self.send_json({
                "leads": leads,
                "stats": database.get_stats(),
                "scan": SCAN_MANAGER.status(),
                "adapters": scanners.get_registered_adapters(cfg),
            })
            return

        if path == "/api/leads/export":
            status_filter = query.get("status", ["all"])[0]
            q_kw = query.get("q", [""])[0]
            location = query.get("location", ["Any"])[0]
            max_age_days = int(query.get("max_age_days", ["365"])[0] or 365)
            platforms_raw = query.get("platforms", [""])[0]
            platforms = [p.strip() for p in platforms_raw.split(",") if p.strip()] if platforms_raw else None
            intents_raw = query.get("intents", [""])[0]
            intents = [i.strip() for i in intents_raw.split(",") if i.strip()] if intents_raw else None

            leads = database.search_leads(
                query=q_kw,
                platforms=platforms,
                intents=intents,
                location=location,
                status_filter=status_filter,
                max_age_days=max_age_days,
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
            self.send_json({
                "scan": SCAN_MANAGER.status(),
                "stats": database.get_stats(),
            })
            return

        if path == "/api/adapters":
            self.send_json({"adapters": scanners.get_registered_adapters(load_config())})
            return

        if path == "/api/config":
            self.send_json(load_config())
            return

        self.send_response(404)
        self.end_headers()

    def do_POST(self):
        ensure_fresh_modules()
        parsed = urllib.parse.urlparse(self.path)
        path = parsed.path
        length = int(self.headers.get("Content-Length", 0))
        body = self.rfile.read(length) if length > 0 else b"{}"

        try:
            payload = json.loads(body.decode("utf-8")) if body else {}
        except Exception:
            payload = {}

        if path in ("/api/search", "/api/scan"):
            cfg = load_config()
            s_cfg = cfg.get("search_settings", {})
            query_kw = payload.get("query", "").strip()
            platforms = payload.get("platforms") or [
                "reddit_posts", "reddit_comments", "facebook", "tiktok", "instagram", "public_web"
            ]
            intents = payload.get("intents") or ["seeker", "employer"]
            location = payload.get("location") or s_cfg.get("location", "Cebu")
            status_filter = payload.get("status", "all")
            max_age_days = int(payload.get("max_age_days", s_cfg.get("max_age_days", 7)) or 7)

            params = {
                "query": query_kw,
                "platforms": platforms,
                "intents": intents,
                "location": location,
                "max_age_days": max_age_days,
            }
            req_trigger = payload.get("trigger") or ("search" if path == "/api/search" else "scan")
            started = SCAN_MANAGER.start(cfg, params, trigger=req_trigger)

            wait_deadline = time.time() + float(payload.get("wait_seconds", 2))
            while SCAN_MANAGER.status().get("running") and time.time() < wait_deadline:
                time.sleep(0.25)

            scan_state = SCAN_MANAGER.status()
            leads = database.search_leads(
                query=query_kw,
                platforms=platforms,
                intents=intents,
                location=location,
                status_filter=status_filter,
                max_age_days=max_age_days,
            )
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
                "stats": database.get_stats(),
            })
            return

        if path == "/api/scan/cancel":
            cancelled = SCAN_MANAGER.cancel()
            self.send_json({
                "success": True,
                "cancelled": cancelled,
                "scan": SCAN_MANAGER.status(),
                "stats": database.get_stats(),
            })
            return

        if path == "/api/lead/status":
            lead_id = payload.get("id")
            new_status = payload.get("status")
            if lead_id and new_status:
                database.update_lead_status(lead_id, new_status)
                self.send_json({"success": True, "stats": database.get_stats()})
            else:
                self.send_json({"error": "Missing id or status"}, 400)
            return

        if path == "/api/lead/notes":
            lead_id = payload.get("id")
            notes = payload.get("notes", "")
            if lead_id:
                database.update_lead_notes(lead_id, notes)
                self.send_json({"success": True})
            else:
                self.send_json({"error": "Missing id"}, 400)
            return

        if path == "/api/lead/delete":
            lead_id = payload.get("id")
            if lead_id:
                database.delete_lead(lead_id)
                self.send_json({"success": True, "stats": database.get_stats()})
            else:
                self.send_json({"error": "Missing id"}, 400)
            return

        if path == "/api/lead/add":
            title = payload.get("title", "").strip()
            url = payload.get("url", "").strip()
            source = payload.get("source", "Manual / Facebook")
            content = payload.get("content", "")
            author = payload.get("author", "User")
            location = payload.get("location", "Cebu")
            intent = payload.get("intent", "seeker")
            kind = "comment" if "comment" in source.lower() else "post"

            if not title or not url:
                self.send_json({"error": "Title and URL are required"}, 400)
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
            self.send_json({
                "success": True,
                "config": payload,
                "adapters": scanners.get_registered_adapters(payload),
            })
            return

        if path == "/api/alerts/test":
            cfg = load_config()
            s_cfg = cfg.get("search_settings", {})
            wh_url = (payload.get("webhook_url") or s_cfg.get("alert_webhook_url") or cfg.get("alert_webhook_url") or "").strip()
            sample = [{
                "title": "Test Alert: Urgent hiring barista / jobseeker lead in Cebu",
                "source": "Unified Lead Scout (Test)",
                "url": "http://localhost:5050",
                "intent": "seeker",
            }]
            sent = scanners.send_webhook_notification(wh_url, sample, trigger="test") if wh_url else False
            self.send_json({"success": True, "webhook_configured": bool(wh_url), "webhook_sent": sent})
            return

        if path == "/api/leads/ai-audit":
            cfg = load_config()
            settings = scanners.get_settings(cfg)
            active_leads = database.search_leads(status_filter="all", max_age_days=365, limit=300)
            scanners.screen_leads_with_ai(active_leads, settings)
            filtered_count = 0
            for ld in active_leads:
                verdict = ld.get("ai_verdict", "approved")
                reason = ld.get("ai_reason", "")
                if verdict == "filtered":
                    filtered_count += 1
                    database.update_lead_ai_verdict(ld["id"], verdict, reason, new_status="ai_filtered")
                else:
                    database.update_lead_ai_verdict(ld["id"], verdict, reason)
            self.send_json({
                "success": True,
                "checked_count": len(active_leads),
                "filtered_count": filtered_count,
                "stats": database.get_stats(),
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
    httpd = ReusableTCPServer(server_address, LeadScoutHandler)
    print("=====================================================")
    print(f"🚀 Unified Lead Scout {scanners.SCANNER_VERSION} is LIVE at http://localhost:{PORT}")
    print("Strict Domain & URL Verifier: ENABLED (SQLite Trigger + Scanner Guard)")
    print("Targets: Jobseekers & Employers | Posts & Comment Trees")
    print("Platforms: Reddit, Facebook, TikTok, Instagram, Web RSS")
    print("=====================================================")
    try:
        httpd.serve_forever()
    except KeyboardInterrupt:
        print("\nShutting down server.")
        httpd.server_close()


if __name__ == "__main__":
    run_server()
