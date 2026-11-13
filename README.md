# 🎯 Unified Lead Scout v2.0 (Posts + Comment-Tree Scanner + Modular Adapters)

A modular, lightweight lead-generation and social monitoring web tool built to find **jobseekers and candidates** across both **POSTS** and individual **COMMENTS** across multiple platforms (Reddit Posts, Reddit Comment Trees/Replies, Public Feeds/Web, and Facebook/TikTok manual ingest).

---

## 🚀 Quick Start

1. Open this project directory:
   ```bash
   cd /home/kebin/.gemini/antigravity/scratch/unified-lead-scout
   ```

2. Start the server:
   ```bash
   python3 app.py
   ```

3. Open your browser to:
   ```
   http://localhost:5050
   ```

---

## 🛠️ Key Features

1. **Comment-Level Scanning (`scan_reddit_comments` in `scanners.py`)**:
   - Inspects subreddit comment streams and recursively walks nested post comment trees/replies (`t1` nodes + `replies`).
   - Detects jobseeker reply phrases such as `"interested po"`, `"how to apply"`, `"pwede pa mo apply"`, `"nangita kog trabaho"`, and `"willing to start ASAP"`.
   - Saves matching comments with `source` (e.g. `"Reddit Comment (r/Cebu)"`), `author` (commenter's username), `content` (exact comment text), and `url` (direct permalink to the comment).
2. **On-Demand Multi-Platform Search Bar (`templates/index.html` & `app.py`)**:
   - Search any keyword (`"dishwasher"`, `"service crew"`, `"looking for work"`, etc.) or comment phrase.
   - Toggle platform checkboxes: `[x] Reddit Posts`, `[x] Reddit Comments`, `[x] Public Feeds / Web`.
   - Select target location: `Cebu` or `Any`.
   - Instant live search & filtering via `POST /api/search` and `GET /api/leads`.
3. **Modular Platform Adapters (`scanners.py`)**:
   - Clean `@register_adapter(key, label, description)` registry pattern.
   - Add new platforms (e.g., TikTok comment API, YouTube comments, or Google Search scrapers) by writing and decorating a single function.
4. **Recent-Only Scanning**: The "Posted" selector on the dashboard (24h / 3 days / **week** / month) filters both live scans and stored leads by the original post or comment date. You can change the default with `search_settings.max_age_days` in `config.json`.
5. **Facebook / TikTok / Instagram (public index)**: These adapters run `site:` searches through Bing's RSS output, so they need no login. They only find **public** content that Bing has already indexed, and the date filter uses Bing's index date. Private FB groups, most comments, and Stories won't show up.
6. **Demo data**: A new, empty database is filled with fictional sample leads tagged **DEMO**. Click **Clear Demo Leads** to remove them.
