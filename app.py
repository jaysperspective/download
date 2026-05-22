import hmac
import json
import os
import subprocess
import threading
import time
import uuid
import ipaddress
import socket
from collections import deque
from datetime import datetime, timedelta
from pathlib import Path
from urllib.parse import urlparse, parse_qs, quote
from flask import Flask, request, jsonify, send_from_directory, send_file, render_template_string, abort, after_this_request, make_response, redirect, Response
import sys
import zipfile
import base64
import re
import urllib.request
import urllib.error
import tempfile
import shutil
import sqlite3
import smtplib
from email.mime.text import MIMEText
from werkzeug.utils import secure_filename

app = Flask(__name__)

DOWNLOAD_DIR = os.environ.get("DOWNLOAD_DIR") or os.path.expanduser("~/Downloads/YT")
os.makedirs(DOWNLOAD_DIR, exist_ok=True)
SOUNDCLOUD_DIR = os.path.join(DOWNLOAD_DIR, "SoundCloud")
os.makedirs(SOUNDCLOUD_DIR, exist_ok=True)
SPOTIFY_DIR = os.path.join(DOWNLOAD_DIR, "Spotify")
SPOTIFY_TRACKS_DIR = os.path.join(SPOTIFY_DIR, "Tracks")
os.makedirs(SPOTIFY_TRACKS_DIR, exist_ok=True)
APPLE_MUSIC_DIR = os.path.join(DOWNLOAD_DIR, "AppleMusic")
APPLE_MUSIC_TRACKS_DIR = os.path.join(APPLE_MUSIC_DIR, "Tracks")
os.makedirs(APPLE_MUSIC_TRACKS_DIR, exist_ok=True)
_data_dir = Path(os.environ.get("YT_UI_STATE_DIR") or Path(__file__).parent)
_data_dir.mkdir(parents=True, exist_ok=True)

HISTORY_PATH = _data_dir / "history.json"
JOBS_PATH    = _data_dir / "jobs.json"
PAUSE_PATH   = _data_dir / "pause.json"
LOG_DIR      = _data_dir / "job-logs"
LOG_DIR.mkdir(exist_ok=True)

# First-party page-view analytics. Server-side counts only — no cookies, no IP
# storage — so it stays compatible with the "no user-tracking" privacy policy.
ANALYTICS_DB = _data_dir / "analytics.db"
_analytics_lock = threading.Lock()
_TRACKED_PAGES = {"/", "/desktop/buy", "/desktop/redeem", "/trial", "/privacy", "/terms"}
PAGEVIEW_RETENTION_DAYS = 90

def _analytics_conn():
    return sqlite3.connect(ANALYTICS_DB, timeout=5)

def _init_analytics_db():
    with _analytics_lock, _analytics_conn() as conn:
        conn.execute(
            "CREATE TABLE IF NOT EXISTS pageviews ("
            "id INTEGER PRIMARY KEY AUTOINCREMENT, "
            "path TEXT NOT NULL, created_at INTEGER NOT NULL)"
        )
        conn.execute("CREATE INDEX IF NOT EXISTS idx_pageviews_created ON pageviews(created_at)")

_init_analytics_db()

def _record_pageview(path: str):
    try:
        with _analytics_lock, _analytics_conn() as conn:
            conn.execute(
                "INSERT INTO pageviews (path, created_at) VALUES (?, ?)",
                (path, int(time.time())),
            )
    except Exception:
        pass

def _prune_pageviews():
    try:
        cutoff = int(time.time()) - PAGEVIEW_RETENTION_DAYS * 86400
        with _analytics_lock, _analytics_conn() as conn:
            conn.execute("DELETE FROM pageviews WHERE created_at < ?", (cutoff,))
    except Exception:
        pass

def _pageview_analytics() -> dict:
    """Aggregate page-view counts for the admin dashboard."""
    now = int(time.time())
    today_start = now - (now % 86400)          # UTC midnight today
    week_start = today_start - 6 * 86400       # last 7 days, inclusive
    month_start = today_start - 29 * 86400     # last 30 days, inclusive
    out = {"total": 0, "today": 0, "week": 0, "month": 0, "daily": [], "by_path": [], "recent": []}
    try:
        conn = _analytics_conn()
        try:
            cur = conn.cursor()
            out["total"] = cur.execute("SELECT COUNT(*) FROM pageviews").fetchone()[0]
            out["today"] = cur.execute("SELECT COUNT(*) FROM pageviews WHERE created_at >= ?", (today_start,)).fetchone()[0]
            out["week"] = cur.execute("SELECT COUNT(*) FROM pageviews WHERE created_at >= ?", (week_start,)).fetchone()[0]
            out["month"] = cur.execute("SELECT COUNT(*) FROM pageviews WHERE created_at >= ?", (month_start,)).fetchone()[0]
            rows = cur.execute(
                "SELECT created_at - (created_at % 86400) AS day, COUNT(*) "
                "FROM pageviews WHERE created_at >= ? GROUP BY day", (month_start,)
            ).fetchall()
            day_counts = {int(d): c for d, c in rows}
            for i in range(29, -1, -1):
                d = today_start - i * 86400
                out["daily"].append({
                    "date": time.strftime("%Y-%m-%d", time.gmtime(d)),
                    "count": day_counts.get(d, 0),
                })
            out["by_path"] = [
                {"path": p, "count": c}
                for p, c in cur.execute(
                    "SELECT path, COUNT(*) AS c FROM pageviews WHERE created_at >= ? "
                    "GROUP BY path ORDER BY c DESC", (month_start,)
                ).fetchall()
            ]
            out["recent"] = [
                {"path": p, "ts": t}
                for p, t in cur.execute(
                    "SELECT path, created_at FROM pageviews ORDER BY id DESC LIMIT 50"
                ).fetchall()
            ]
        finally:
            conn.close()
    except Exception:
        pass
    return out

MAX_CONCURRENT_JOBS = int(os.environ.get("YT_UI_MAX_CONCURRENT", "3"))
JOB_TTL_SECONDS = int(os.environ.get("YT_UI_JOB_TTL_SECONDS", str(60 * 60)))
FILE_TTL_DAYS = float(os.environ.get("YT_UI_FILE_TTL_DAYS", "0"))  # 0 = disabled
VERSION = "1.3"
COOKIES_PATH = os.environ.get("YT_UI_COOKIES") or ""
COOKIES_PASSWORD = os.environ.get("YT_UI_COOKIES_PASSWORD") or ""
MAX_QUEUE_DEPTH = int(os.environ.get("YT_UI_MAX_QUEUE", "10"))
PER_IP_CONCURRENT = int(os.environ.get("YT_UI_PER_IP_CONCURRENT", "2"))
PER_IP_HOURLY = int(os.environ.get("YT_UI_PER_IP_HOURLY", "20"))
MAX_PLAYLIST_TRACKS = int(os.environ.get("YT_UI_MAX_PLAYLIST_TRACKS", "50"))
DISK_CAP_GB = float(os.environ.get("YT_UI_DISK_CAP_GB", "20"))
GLOBAL_RATE_PER_MIN = int(os.environ.get("YT_UI_GLOBAL_RATE_PER_MIN", "120"))
SMTP_USER = os.environ.get("YT_UI_SMTP_USER", "")
SMTP_PASS = os.environ.get("YT_UI_SMTP_PASS", "")
ALERT_EMAIL = os.environ.get("YT_UI_ALERT_EMAIL", "")
PROXY_URL = os.environ.get("YT_UI_PROXY", "")
_ip_jobs_active: dict = {}
_ip_recent: dict = {}
_ip_lock = threading.Lock()
_global_rate: dict = {}
_global_rate_lock = threading.Lock()
_last_cookie_alert: float = 0
_cookie_alert_lock = threading.Lock()
SPOTIFY_CLIENT_ID = os.environ.get("SPOTIFY_CLIENT_ID", "")
SPOTIFY_CLIENT_SECRET = os.environ.get("SPOTIFY_CLIENT_SECRET", "")
_spotify_token_cache: dict = {}
_spotify_token_lock = threading.Lock()

# Token gate — access control via payment app
PAYMENT_APP_URL = os.environ.get("PAYMENT_APP_URL", "http://localhost:4001")
TOKEN_INTERNAL_SECRET = os.environ.get("TOKEN_INTERNAL_SECRET", "")
ACCESS_PAYMENT_URL = os.environ.get("ACCESS_PAYMENT_URL", "http://localhost:4001/payment/access")
DESKTOP_PAYMENT_URL = os.environ.get("DESKTOP_PAYMENT_URL", f"{ACCESS_PAYMENT_URL}?product=desktop")
DESKTOP_BUILDS_DIR = Path(os.environ.get("DESKTOP_BUILDS_DIR") or (_data_dir / "desktop-builds"))
DESKTOP_BUILDS_DIR.mkdir(parents=True, exist_ok=True)
# Free-trial edition installers live in their own folder — never mixed with the
# paid builds above. Same manifest shape, served token-less from /trial.
DESKTOP_BUILDS_TRIAL_DIR = Path(os.environ.get("DESKTOP_BUILDS_TRIAL_DIR") or (_data_dir / "desktop-builds-trial"))
DESKTOP_BUILDS_TRIAL_DIR.mkdir(parents=True, exist_ok=True)

# Free-trial email gate. /trial reveals the download only after the visitor
# submits an email, which is added to the Kit "desktop-trial" tag. Soft gate:
# a signed cookie remembers the unlock so return visits skip the form. If the
# Kit call fails the email is appended to a local fallback file so no lead is
# lost and the download still unlocks.
KIT_API_KEY = os.environ.get("KIT_API_KEY", "")
KIT_TRIAL_TAG_ID = os.environ.get("KIT_TRIAL_TAG_ID", "")
_TRIAL_COOKIE = "trial_unlocked"
_TRIAL_COOKIE_SIG = hmac.new(
    (TOKEN_INTERNAL_SECRET or "trial-gate").encode(), b"trial-unlocked-v1", "sha256"
).hexdigest()
_TRIAL_SIGNUPS_FALLBACK = _data_dir / "trial-signups-fallback.jsonl"
_trial_lock = threading.Lock()
_EMAIL_RE = re.compile(r"^[^@\s]+@[^@\s]+\.[^@\s]+$")

def _load_paused() -> bool:
    try:
        return bool(json.loads(PAUSE_PATH.read_text()).get("paused", False))
    except Exception:
        return False

def _save_paused(val: bool):
    PAUSE_PATH.write_text(json.dumps({"paused": val}))

_service_paused: bool = _load_paused()
_pause_lock = threading.Lock()
_PAUSE_CACHE_TTL = 5.0  # seconds — how often to re-read pause.json from disk
_pause_cache_at: float = 0.0

def _is_paused() -> bool:
    """Read pause state with a short TTL so file edits take effect without restart."""
    global _service_paused, _pause_cache_at
    now = time.time()
    with _pause_lock:
        if now - _pause_cache_at > _PAUSE_CACHE_TTL:
            _service_paused = _load_paused()
            _pause_cache_at = now
        return _service_paused

# Cache of tokens that have been validated recently, so /start can bypass pause without
# calling the payment API on every request.
_TOKEN_CACHE_TTL = 60.0  # seconds
_valid_token_cache: dict = {}  # token -> expires_at epoch
_valid_token_cache_lock = threading.Lock()

def _remember_valid_token(token: str):
    if not token:
        return
    with _valid_token_cache_lock:
        _valid_token_cache[token] = time.time() + _TOKEN_CACHE_TTL

def _is_token_valid(token: str) -> bool:
    """Return True if token passes the payment-app check. Short-lived in-memory cache."""
    if not token or not TOKEN_INTERNAL_SECRET:
        return False
    now = time.time()
    with _valid_token_cache_lock:
        exp = _valid_token_cache.get(token)
        if exp and exp > now:
            return True
    try:
        body = json.dumps({"token": token}).encode()
        req = urllib.request.Request(
            f"{PAYMENT_APP_URL}/payment/api/access/internal/token/check",
            data=body,
            headers={
                "Content-Type": "application/json",
                "x-internal-secret": TOKEN_INTERNAL_SECRET,
                "x-forwarded-proto": "https",
            },
            method="POST",
        )
        with urllib.request.urlopen(req, timeout=3) as resp:
            result = json.loads(resp.read())
    except Exception:
        return False
    if result.get("valid"):
        _remember_valid_token(token)
        return True
    return False

def _consume_token(token: str) -> dict:
    """Atomically validate and decrement a token. Returns payment-app JSON (valid, remaining, ...) or {} on error."""
    if not token or not TOKEN_INTERNAL_SECRET:
        return {}
    try:
        body = json.dumps({"token": token}).encode()
        req = urllib.request.Request(
            f"{PAYMENT_APP_URL}/payment/api/access/internal/token/use",
            data=body,
            headers={
                "Content-Type": "application/json",
                "x-internal-secret": TOKEN_INTERNAL_SECRET,
                "x-forwarded-proto": "https",
            },
            method="POST",
        )
        with urllib.request.urlopen(req, timeout=3) as resp:
            result = json.loads(resp.read())
    except Exception:
        return {}
    # Invalidate cached 'check' result so subsequent checks reflect new remaining.
    with _valid_token_cache_lock:
        _valid_token_cache.pop(token, None)
    return result if isinstance(result, dict) else {}

def _check_token_status(token: str) -> dict:
    """Call the payment-app check endpoint and return the full JSON (valid, remaining, product, reason).

    Unlike _is_token_valid this exposes 'product' and 'reason', which the desktop
    redeem flow needs. Not cached — the redeem page polls this to clear the
    Stripe-redirect/webhook race, so it must see fresh state every call.
    """
    if not token or not TOKEN_INTERNAL_SECRET:
        return {}
    try:
        body = json.dumps({"token": token}).encode()
        req = urllib.request.Request(
            f"{PAYMENT_APP_URL}/payment/api/access/internal/token/check",
            data=body,
            headers={
                "Content-Type": "application/json",
                "x-internal-secret": TOKEN_INTERNAL_SECRET,
                "x-forwarded-proto": "https",
            },
            method="POST",
        )
        with urllib.request.urlopen(req, timeout=3) as resp:
            result = json.loads(resp.read())
    except Exception:
        return {}
    return result if isinstance(result, dict) else {}

# Desktop installer builds — manifest maps each OS slot to a filename in a
# builds dir. The paid app uses DESKTOP_BUILDS_DIR; the free trial uses
# DESKTOP_BUILDS_TRIAL_DIR. Every helper takes the dir so the two channels
# share code but never share files or manifests.
_OS_ORDER = ("mac", "win", "linux")
_OS_LABELS = {"mac": "macOS", "win": "Windows", "linux": "Linux"}

def _builds_dir_for(edition: str) -> Path:
    """Map an edition name ('full' | 'trial') to its builds directory."""
    return DESKTOP_BUILDS_TRIAL_DIR if edition == "trial" else DESKTOP_BUILDS_DIR

def _builds_manifest_path(builds_dir: Path = DESKTOP_BUILDS_DIR) -> Path:
    return builds_dir / "manifest.json"

def _load_builds_manifest(builds_dir: Path = DESKTOP_BUILDS_DIR) -> dict:
    try:
        m = json.loads(_builds_manifest_path(builds_dir).read_text())
        if isinstance(m, dict):
            return m
    except Exception:
        pass
    return {}

def _save_builds_manifest(m: dict, builds_dir: Path = DESKTOP_BUILDS_DIR):
    builds_dir.mkdir(parents=True, exist_ok=True)
    _builds_manifest_path(builds_dir).write_text(json.dumps(m, indent=2))

def _list_desktop_builds(builds_dir: Path = DESKTOP_BUILDS_DIR) -> dict:
    """Per-OS build slots for the admin page: {os: {filename, size} or None}."""
    m = _load_builds_manifest(builds_dir)
    slots = {}
    for os_key in _OS_ORDER:
        fn = m.get(os_key) or ""
        info = None
        if fn:
            p = builds_dir / fn
            if p.exists():
                info = {"filename": fn, "size": p.stat().st_size}
        slots[os_key] = info
    return slots

def _maybe_delete_build_file(filename: str, manifest: dict, builds_dir: Path = DESKTOP_BUILDS_DIR):
    """Delete a build file once no manifest slot still references it."""
    if not filename or filename in {manifest.get(k) for k in _OS_ORDER}:
        return
    try:
        p = builds_dir / filename
        if p.exists() and p.parent == builds_dir:
            p.unlink()
    except Exception:
        pass

def _detect_os(ua: str) -> str:
    """Best-effort desktop OS from a User-Agent string. Empty for mobile/unknown."""
    ua = (ua or "").lower()
    if "windows" in ua:
        return "win"
    if "android" in ua or "iphone" in ua or "ipad" in ua:
        return ""
    if "mac" in ua:
        return "mac"
    if "linux" in ua or "x11" in ua:
        return "linux"
    return ""

def _redeem_build_options(detected: str, builds_dir: Path = DESKTOP_BUILDS_DIR) -> list:
    """Available download options for the redeem page, detected OS listed first."""
    slots = _list_desktop_builds(builds_dir)
    avail = [k for k in _OS_ORDER if slots.get(k)]
    if detected in avail:
        avail = [detected] + [k for k in avail if k != detected]
    return [{"os": k, "label": _OS_LABELS[k]} for k in avail]


def _trial_unlocked(req) -> bool:
    """True once the visitor has cleared the /trial email gate (signed cookie)."""
    return req.cookies.get(_TRIAL_COOKIE) == _TRIAL_COOKIE_SIG


def _kit_subscribe_trial(email: str) -> bool:
    """Add an email to the Kit 'desktop-trial' tag. Returns True on a 2xx."""
    if not KIT_API_KEY or not KIT_TRIAL_TAG_ID:
        return False
    try:
        body = json.dumps({"api_key": KIT_API_KEY, "email": email}).encode()
        req = urllib.request.Request(
            f"https://api.convertkit.com/v3/tags/{KIT_TRIAL_TAG_ID}/subscribe",
            data=body,
            headers={"Content-Type": "application/json"},
            method="POST",
        )
        with urllib.request.urlopen(req, timeout=6) as resp:
            return 200 <= resp.status < 300
    except Exception:
        return False


def _record_trial_signup_fallback(email: str):
    """Persist a signup locally when the Kit call fails — no lead is lost."""
    try:
        line = json.dumps({"email": email, "ts": datetime.utcnow().isoformat()})
        with _trial_lock:
            with open(_TRIAL_SIGNUPS_FALLBACK, "a") as f:
                f.write(line + "\n")
    except Exception:
        pass

YT_DLP_BIN = shutil.which("yt-dlp") or "yt-dlp"
FFMPEG_BIN = shutil.which("ffmpeg") or "ffmpeg"

jobs = {}  # job_id -> {"status": "...", "log": "...", "file": "...", timestamps}
jobs_lock = threading.RLock()
job_sema = threading.Semaphore(MAX_CONCURRENT_JOBS)
history_lock = threading.Lock()
job_queue = deque()
queue_cv = threading.Condition()


def _client_ip() -> str:
    real_ip = request.headers.get("X-Real-IP", "")
    if real_ip:
        return real_ip.strip()
    return request.remote_addr or "unknown"


def _disk_usage_gb(path: str) -> float:
    total = 0
    for root, _dirs, files in os.walk(path):
        for name in files:
            fp = os.path.join(root, name)
            try:
                total += os.path.getsize(fp)
            except OSError:
                pass
    return total / (1024 ** 3)


def _check_ip_limits(ip: str):
    """Returns (error_message, status_code) tuple or (None, None) if OK.
    On success, increments the active counter and records the request timestamp."""
    now = time.time()
    hour_ago = now - 3600
    with _ip_lock:
        recent = _ip_recent.setdefault(ip, deque())
        while recent and recent[0] < hour_ago:
            recent.popleft()
        if len(recent) >= PER_IP_HOURLY:
            return (f"Hourly request limit reached ({PER_IP_HOURLY}/hr). Try again later.", 429)
        if _ip_jobs_active.get(ip, 0) >= PER_IP_CONCURRENT:
            return (f"Too many active jobs for your IP (max {PER_IP_CONCURRENT}). Wait for one to finish.", 429)
        _ip_jobs_active[ip] = _ip_jobs_active.get(ip, 0) + 1
        recent.append(now)
    return (None, None)


def _release_ip(ip: str):
    if not ip:
        return
    with _ip_lock:
        current = _ip_jobs_active.get(ip, 0)
        if current <= 1:
            _ip_jobs_active.pop(ip, None)
        else:
            _ip_jobs_active[ip] = current - 1


_COOKIE_ERROR_PATTERNS = [
    "Sign in to confirm you're not a bot",
    "Sign in to confirm you",
    "cookies expired",
    "does not look like a Netscape format cookies file",
    "Use --cookies-from-browser or --cookies",
]


def _check_cookie_alert(log_output: str):
    global _last_cookie_alert
    if not SMTP_USER or not SMTP_PASS or not ALERT_EMAIL:
        return
    if not any(pattern in log_output for pattern in _COOKIE_ERROR_PATTERNS):
        return
    with _cookie_alert_lock:
        if time.time() - _last_cookie_alert < 86400:
            return
        _last_cookie_alert = time.time()
    try:
        msg = MIMEText(
            "+downloads: YouTube cookies have expired or are invalid.\n\n"
            "Downloads that rely on YouTube (including Spotify/Apple Music) will fail "
            "until you upload fresh cookies.\n\n"
            "To fix:\n"
            "1. Open Chrome, go to youtube.com (make sure you're logged in)\n"
            "2. Use the 'Get cookies.txt LOCALLY' extension to export cookies\n"
            "3. Upload at https://digitaldownloads.space/admin\n\n"
            f"Error detected:\n{log_output[-500:]}"
        )
        msg["Subject"] = "[+downloads] YouTube cookies expired — action needed"
        msg["From"] = SMTP_USER
        msg["To"] = ALERT_EMAIL
        with smtplib.SMTP_SSL("smtp.gmail.com", 465) as smtp:
            smtp.login(SMTP_USER, SMTP_PASS)
            smtp.send_message(msg)
    except Exception:
        pass


def _is_safe_path(path: str) -> bool:
    try:
        return os.path.realpath(path).startswith(os.path.realpath(DOWNLOAD_DIR))
    except (ValueError, OSError):
        return False


ADMIN_HTML = """
<!doctype html>
<html>
<head>
  <meta charset="utf-8">
  <title>+downloads / admin</title>
  <link rel="icon" type="image/svg+xml" href="/static/favicon.svg">
  <link rel="icon" type="image/png" sizes="64x64" href="/static/favicon.png">
  <link rel="apple-touch-icon" href="/static/icon-192.png">
  <style>
    *, *::before, *::after { box-sizing: border-box; margin: 0; padding: 0; }
    body {
      font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', sans-serif;
      background: #1a1818;
      color: #f0eef0;
      min-height: 100vh;
      padding: 32px 16px 64px;
    }
    .wrap { max-width: 860px; margin: 0 auto; }
    h1 {
      font-size: 22px; font-weight: 800; color: #db52a6;
      letter-spacing: -0.5px; margin-bottom: 24px;
    }
    .card {
      background: #242222; border: 1px solid #2e2c2c;
      border-radius: 16px; padding: 24px 28px; margin-bottom: 20px;
    }
    .card-title {
      font-size: 12px; font-weight: 700; text-transform: uppercase;
      letter-spacing: 0.08em; color: #666; margin-bottom: 16px;
    }
    label {
      display: block; font-size: 13px; font-weight: 600;
      color: #888; margin-bottom: 6px; margin-top: 14px;
    }
    label:first-of-type { margin-top: 0; }
    input[type=password], input[type=file] {
      width: 100%; background: #1a1818; border: 1.5px solid #353333;
      color: #f0eef0; padding: 11px 14px; border-radius: 10px;
      font-size: 14px; outline: none; transition: border-color 0.2s;
    }
    input[type=password]:focus { border-color: #db52a6; }
    input[type=file] { cursor: pointer; }
    input::placeholder { color: #464444; }
    .btn-row { display: flex; gap: 10px; margin-top: 18px; }
    .btn {
      flex: 1; background: #db52a6; color: #fff; border: none;
      padding: 12px; border-radius: 10px; font-size: 14px; font-weight: 700;
      cursor: pointer; transition: background 0.15s, transform 0.1s;
    }
    .btn:hover { background: #c9479a; }
    .btn:active { transform: scale(0.97); }
    .btn:disabled { opacity: 0.5; cursor: default; transform: none; }
    .btn-outline {
      flex: 1; background: #1a1818; color: #db52a6;
      border: 1.5px solid #db52a6; padding: 12px; border-radius: 10px;
      font-size: 14px; font-weight: 700; cursor: pointer;
      transition: background 0.15s;
    }
    .btn-outline:hover { background: rgba(219,82,166,0.08); }
    #upload-msg {
      margin-top: 12px; font-size: 13px; font-weight: 600;
      min-height: 18px; text-align: center;
    }
    .ok  { color: #4caf7d; }
    .err { color: #e05c5c; }

    /* Summary cards */
    .stat-grid {
      display: grid; grid-template-columns: repeat(4, 1fr); gap: 12px;
      margin-bottom: 20px;
    }
    .stat-card {
      background: #242222; border: 1px solid #2e2c2c;
      border-radius: 14px; padding: 18px 20px;
    }
    .stat-label { font-size: 11px; font-weight: 700; text-transform: uppercase;
      letter-spacing: 0.07em; color: #555; margin-bottom: 6px; }
    .stat-val { font-size: 32px; font-weight: 800; line-height: 1; }
    .stat-sub { font-size: 12px; color: #666; margin-top: 4px; }
    .c-pink  { color: #db52a6; }
    .c-green { color: #4caf7d; }
    .c-red   { color: #e05c5c; }
    .c-blue  { color: #5b9cf6; }

    /* Type breakdown */
    .type-row { display: flex; flex-wrap: wrap; gap: 10px; }
    .type-pill {
      display: flex; align-items: center; gap: 8px;
      background: #1a1818; border: 1px solid #2e2c2c;
      border-radius: 99px; padding: 7px 14px; font-size: 13px; font-weight: 600;
    }
    .type-dot { width: 8px; height: 8px; border-radius: 50%; flex-shrink: 0; }
    .type-count { color: #888; font-size: 12px; margin-left: 2px; }

    /* Table */
    .tbl { width: 100%; border-collapse: collapse; font-size: 13px; }
    .tbl th {
      text-align: left; font-size: 11px; font-weight: 700;
      text-transform: uppercase; letter-spacing: 0.07em;
      color: #555; padding: 0 10px 10px 0; border-bottom: 1px solid #2e2c2c;
    }
    .tbl td {
      padding: 10px 10px 10px 0; border-bottom: 1px solid #222;
      vertical-align: middle;
    }
    .tbl tr:last-child td { border-bottom: none; }
    .tbl tr:hover td { background: rgba(255,255,255,0.02); }
    .badge {
      display: inline-block; padding: 3px 9px; border-radius: 99px;
      font-size: 11px; font-weight: 700; text-transform: uppercase;
      letter-spacing: 0.05em; white-space: nowrap;
    }
    .badge-done     { background: rgba(76,175,125,0.15); color: #4caf7d; }
    .badge-error    { background: rgba(224,92,92,0.15);  color: #e05c5c; }
    .badge-cancelled{ background: rgba(100,100,100,0.15);color: #777; }
    .badge-running  { background: rgba(91,156,246,0.15); color: #5b9cf6; }
    .badge-queued   { background: rgba(255,200,80,0.15); color: #f0b429; }
    .url-cell { max-width: 320px; overflow: hidden; text-overflow: ellipsis;
      white-space: nowrap; color: #aaa; font-size: 12px; }
    .time-cell { color: #555; font-size: 12px; white-space: nowrap; }
    #stats-section { display: none; }
    .refresh-row { display: flex; justify-content: flex-end; margin-bottom: 12px; }
    .refresh-btn {
      background: none; border: 1px solid #353333; color: #666;
      padding: 6px 14px; border-radius: 8px; font-size: 12px;
      cursor: pointer; transition: color 0.15s, border-color 0.15s;
    }
    .refresh-btn:hover { color: #f0eef0; border-color: #555; }
    .c-amber { color: #bf9b3a; }

    /* Installer builds */
    .build-row { padding: 14px 0; border-bottom: 1px solid #222; }
    .build-row:first-of-type { padding-top: 2px; }
    .build-row:last-of-type { border-bottom: none; padding-bottom: 2px; }
    .build-top { display: flex; align-items: baseline; gap: 10px; margin-bottom: 9px; }
    .build-os { font-size: 14px; font-weight: 700; color: #f0eef0; }
    .build-cur { font-size: 12px; word-break: break-all; }
    .build-cur.ok { color: #4caf7d; }
    .build-cur.none { color: #555; }
    .build-actions { display: flex; gap: 8px; align-items: center; flex-wrap: wrap; }
    .build-actions input[type=file] { flex: 1; min-width: 170px; padding: 8px 10px; font-size: 13px; }
    .build-btn { padding: 9px 16px; border-radius: 8px; font-size: 12px; font-weight: 700; cursor: pointer; border: none; }
    .build-btn.up { background: #db52a6; color: #fff; }
    .build-btn.up:hover { background: #c9479a; }
    .build-btn.del { background: #1a1818; color: #e05c5c; border: 1px solid #e05c5c; }
    .build-btn.del:hover { background: rgba(224,92,92,0.08); }
    #build-msg { margin-top: 12px; font-size: 13px; font-weight: 600; min-height: 16px; }

    /* Page-view analytics */
    .section-head { font-size: 15px; font-weight: 800; color: #f0eef0; margin: 30px 0 14px; }
    .section-head:first-of-type { margin-top: 4px; }
    .chart { display: flex; align-items: flex-end; gap: 3px; height: 150px; }
    .chart-col { flex: 1; display: flex; flex-direction: column; align-items: center;
      justify-content: flex-end; gap: 5px; height: 100%; }
    .chart-bar { width: 100%; background: #db52a6; border-radius: 3px 3px 0 0; }
    .chart-lbl { font-size: 9px; color: #555; white-space: nowrap; line-height: 1; }
    .pv-row { display: grid; grid-template-columns: 1fr 1fr; gap: 20px; }
    .bar-row { margin-bottom: 13px; }
    .bar-row:last-child { margin-bottom: 0; }
    .bar-head { display: flex; justify-content: space-between; align-items: baseline;
      font-size: 13px; margin-bottom: 5px; }
    .bar-head .bp { color: #f0eef0; font-weight: 600; word-break: break-all; }
    .bar-head .bc { color: #888; font-size: 12px; padding-left: 10px; }
    .bar-track { height: 8px; background: #1a1818; border-radius: 99px; overflow: hidden; }
    .bar-fill { height: 100%; background: #db52a6; border-radius: 99px; }
    @media (max-width: 600px) {
      .stat-grid { grid-template-columns: repeat(2, 1fr); }
      .url-cell { max-width: 140px; }
      .pv-row { grid-template-columns: 1fr; }
    }
  </style>
</head>
<body>
  <div class="wrap">
    <h1>+downloads admin</h1>

    <div class="card">
      <div class="card-title">Upload Cookies</div>
      <label for="pw">Password</label>
      <input type="password" id="pw" placeholder="YT_UI_COOKIES_PASSWORD">
      <label for="cfile">cookies.txt</label>
      <input type="file" id="cfile" accept=".txt">
      <div class="btn-row">
        <button class="btn" id="upload-btn" onclick="uploadCookies()">Upload</button>
        <button class="btn-outline" onclick="loadStats()">Load Stats</button>
        <button class="btn-outline" onclick="clearHistory()" style="border-color:#e74c3c;color:#e74c3c">Clear History</button>
      </div>
      <div id="upload-msg"></div>
    </div>

    <div class="card">
      <div class="card-title">Service Control</div>
      <div style="display:flex;align-items:center;gap:16px;flex-wrap:wrap">
        <div id="pause-status" style="font-size:14px;font-weight:600;color:#888">Status: unknown</div>
        <button class="btn" id="pause-btn" onclick="togglePause()" style="flex:none;padding:10px 22px">Toggle Pause</button>
      </div>
      <div id="pause-msg" style="margin-top:10px;font-size:13px;font-weight:600;min-height:16px"></div>
    </div>

    <div id="stats-section">
      <div class="refresh-row">
        <button class="refresh-btn" onclick="loadStats()">&#8635; Refresh</button>
      </div>

      <div class="card">
        <div class="card-title">Installer Builds</div>
        <div class="build-row">
          <div class="build-top">
            <span class="build-os">macOS</span>
            <span class="build-cur none" id="build-cur-mac">Load stats to view</span>
          </div>
          <div class="build-actions">
            <input type="file" id="bf-mac">
            <button class="build-btn up" onclick="uploadBuild('mac')">Upload</button>
            <button class="build-btn del" id="build-del-mac" onclick="deleteBuild('mac')" style="display:none">Delete</button>
          </div>
        </div>
        <div class="build-row">
          <div class="build-top">
            <span class="build-os">Windows</span>
            <span class="build-cur none" id="build-cur-win">Load stats to view</span>
          </div>
          <div class="build-actions">
            <input type="file" id="bf-win">
            <button class="build-btn up" onclick="uploadBuild('win')">Upload</button>
            <button class="build-btn del" id="build-del-win" onclick="deleteBuild('win')" style="display:none">Delete</button>
          </div>
        </div>
        <div class="build-row">
          <div class="build-top">
            <span class="build-os">Linux</span>
            <span class="build-cur none" id="build-cur-linux">Load stats to view</span>
          </div>
          <div class="build-actions">
            <input type="file" id="bf-linux">
            <button class="build-btn up" onclick="uploadBuild('linux')">Upload</button>
            <button class="build-btn del" id="build-del-linux" onclick="deleteBuild('linux')" style="display:none">Delete</button>
          </div>
        </div>
        <div id="build-msg"></div>
      </div>

      <div class="card">
        <div class="card-title">Trial Installer Builds</div>
        <div class="build-row">
          <div class="build-top">
            <span class="build-os">macOS</span>
            <span class="build-cur none" id="build-cur-trial-mac">Load stats to view</span>
          </div>
          <div class="build-actions">
            <input type="file" id="bf-trial-mac">
            <button class="build-btn up" onclick="uploadBuild('mac', 'trial')">Upload</button>
            <button class="build-btn del" id="build-del-trial-mac" onclick="deleteBuild('mac', 'trial')" style="display:none">Delete</button>
          </div>
        </div>
        <div class="build-row">
          <div class="build-top">
            <span class="build-os">Windows</span>
            <span class="build-cur none" id="build-cur-trial-win">Load stats to view</span>
          </div>
          <div class="build-actions">
            <input type="file" id="bf-trial-win">
            <button class="build-btn up" onclick="uploadBuild('win', 'trial')">Upload</button>
            <button class="build-btn del" id="build-del-trial-win" onclick="deleteBuild('win', 'trial')" style="display:none">Delete</button>
          </div>
        </div>
        <div class="build-row">
          <div class="build-top">
            <span class="build-os">Linux</span>
            <span class="build-cur none" id="build-cur-trial-linux">Load stats to view</span>
          </div>
          <div class="build-actions">
            <input type="file" id="bf-trial-linux">
            <button class="build-btn up" onclick="uploadBuild('linux', 'trial')">Upload</button>
            <button class="build-btn del" id="build-del-trial-linux" onclick="deleteBuild('linux', 'trial')" style="display:none">Delete</button>
          </div>
        </div>
        <div id="build-msg-trial"></div>
      </div>

      <div class="section-head">Page Views</div>
      <div class="stat-grid" id="pv-grid"></div>
      <div class="card">
        <div class="card-title">Daily Views &middot; Last 30 Days</div>
        <div class="chart" id="pv-chart"></div>
      </div>
      <div class="pv-row">
        <div class="card">
          <div class="card-title">Top Pages &middot; Last 30 Days</div>
          <div id="pv-paths"></div>
        </div>
        <div class="card">
          <div class="card-title">Recent Views</div>
          <table class="tbl">
            <thead><tr><th>Time</th><th>Page</th></tr></thead>
            <tbody id="pv-recent"></tbody>
          </table>
        </div>
      </div>

      <div class="section-head">Downloads</div>
      <div class="stat-grid" id="stat-grid"></div>

      <div class="card">
        <div class="card-title">Downloads by Type</div>
        <div class="type-row" id="type-row"></div>
      </div>

      <div class="card" id="active-card" style="display:none">
        <div class="card-title">Active Jobs</div>
        <table class="tbl" id="active-tbl">
          <thead><tr>
            <th>Type</th><th>URL</th><th>Progress</th><th>Status</th>
          </tr></thead>
          <tbody id="active-body"></tbody>
        </table>
      </div>

      <div class="card">
        <div class="card-title">Recent Downloads <span id="recent-count" style="color:#555;font-weight:400;font-size:11px;margin-left:6px"></span></div>
        <table class="tbl" id="recent-tbl">
          <thead><tr>
            <th>Time</th><th>Type</th><th>URL</th><th>Status</th>
          </tr></thead>
          <tbody id="recent-body"></tbody>
        </table>
      </div>
    </div>
  </div>

  <script>
    const TYPE_COLORS = {
      video: '#db52a6', audio: '#4caf7d', soundcloud: '#ff5500',
      spotify: '#1db954', apple_music: '#fc3c44'
    };

    function pw() { return document.getElementById('pw').value; }

    function relTime(iso) {
      if (!iso) return '—';
      const diff = Math.floor((Date.now() - new Date(iso + (iso.endsWith('Z') ? '' : 'Z'))) / 1000);
      if (diff < 60)   return diff + 's ago';
      if (diff < 3600) return Math.floor(diff/60) + 'm ago';
      if (diff < 86400)return Math.floor(diff/3600) + 'h ago';
      return Math.floor(diff/86400) + 'd ago';
    }

    function statusBadge(s) {
      const cls = {done:'badge-done',error:'badge-error',cancelled:'badge-cancelled',
                   running:'badge-running',queued:'badge-queued'}[s] || 'badge-cancelled';
      return '<span class="badge ' + cls + '">' + s + '</span>';
    }

    function typePill(t, count) {
      const color = TYPE_COLORS[t] || '#888';
      return '<div class="type-pill">'
        + '<span class="type-dot" style="background:' + color + '"></span>'
        + '<span>' + t + '</span>'
        + '<span class="type-count">' + count + '</span>'
        + '</div>';
    }

    async function uploadCookies() {
      const file = document.getElementById('cfile').files[0];
      const msg  = document.getElementById('upload-msg');
      const btn  = document.getElementById('upload-btn');
      msg.textContent = ''; msg.className = '';
      if (!pw())   { msg.textContent = 'Password required.';   msg.className = 'err'; return; }
      if (!file)   { msg.textContent = 'Select a file first.'; msg.className = 'err'; return; }
      btn.disabled = true; btn.textContent = 'Uploading…';
      try {
        const fd = new FormData();
        fd.append('password', pw());
        fd.append('cookies', file);
        const r = await fetch('/upload-cookies', { method: 'POST', body: fd });
        const j = await r.json();
        if (r.ok) {
          msg.textContent = 'Uploaded successfully.'; msg.className = 'ok';
          document.getElementById('cfile').value = '';
        } else {
          msg.textContent = j.error || 'Upload failed.'; msg.className = 'err';
        }
      } catch (e) { msg.textContent = 'Network error.'; msg.className = 'err'; }
      finally { btn.disabled = false; btn.textContent = 'Upload'; }
    }

    async function loadStats() {
      const msg = document.getElementById('upload-msg');
      if (!pw()) { msg.textContent = 'Enter password first.'; msg.className = 'err'; return; }
      msg.textContent = 'Loading…'; msg.className = '';
      try {
        const r = await fetch('/admin/stats', {
          method: 'POST',
          headers: {'Content-Type': 'application/json'},
          body: JSON.stringify({password: pw()})
        });
        const d = await r.json();
        if (!r.ok) { msg.textContent = d.error || 'Error loading stats.'; msg.className = 'err'; return; }
        msg.textContent = ''; renderStats(d);
      } catch (e) { msg.textContent = 'Network error.'; msg.className = 'err'; }
    }

    async function loadPauseStatus() {
      try {
        const r = await fetch('/service-status');
        const d = await r.json();
        const el = document.getElementById('pause-status');
        if (d.paused) {
          el.textContent = 'Status: PAUSED'; el.style.color = '#e05c5c';
        } else {
          el.textContent = 'Status: ACTIVE'; el.style.color = '#4caf7d';
        }
      } catch (e) {}
    }

    async function togglePause() {
      const msg = document.getElementById('pause-msg');
      if (!pw()) { msg.textContent = 'Enter password first.'; msg.className = 'err'; return; }
      const cur = document.getElementById('pause-status').textContent;
      const newPaused = !cur.includes('PAUSED');
      try {
        const r = await fetch('/admin/pause', {
          method: 'POST',
          headers: {'Content-Type': 'application/json'},
          body: JSON.stringify({password: pw(), paused: newPaused})
        });
        const d = await r.json();
        if (!r.ok) { msg.textContent = d.error || 'Error.'; msg.className = 'err'; return; }
        msg.textContent = d.paused ? 'Service paused.' : 'Service resumed.';
        msg.className = d.paused ? 'err' : 'ok';
        loadPauseStatus();
      } catch (e) { msg.textContent = 'Network error.'; msg.className = 'err'; }
    }

    loadPauseStatus();

    async function clearHistory() {
      const msg = document.getElementById('upload-msg');
      if (!pw()) { msg.textContent = 'Enter password first.'; msg.className = 'err'; return; }
      if (!confirm('Clear all download history? This cannot be undone.')) return;
      msg.textContent = 'Clearing…'; msg.className = '';
      try {
        const r = await fetch('/admin/clear-history', {
          method: 'POST',
          headers: {'Content-Type': 'application/json'},
          body: JSON.stringify({password: pw()})
        });
        const j = await r.json();
        if (!r.ok) { msg.textContent = j.error || 'Error clearing history.'; msg.className = 'err'; return; }
        msg.textContent = 'History cleared.'; msg.className = 'ok';
        loadStats();
      } catch (e) { msg.textContent = 'Network error.'; msg.className = 'err'; }
    }

    function renderStats(d) {
      document.getElementById('stats-section').style.display = 'block';
      renderPageviews(d.pageviews);
      renderBuilds(d.builds, d.trial_builds);

      // Summary cards
      const total    = d.total_history;
      const done     = (d.by_status.done || 0);
      const errors   = (d.by_status.error || 0);
      const succRate = total ? Math.round(done / total * 100) : 0;
      document.getElementById('stat-grid').innerHTML =
        '<div class="stat-card"><div class="stat-label">Total Downloads</div>'
          +'<div class="stat-val c-pink">'+total+'</div>'
          +'<div class="stat-sub">all time (last 500)</div></div>'
        +'<div class="stat-card"><div class="stat-label">Successful</div>'
          +'<div class="stat-val c-green">'+done+'</div>'
          +'<div class="stat-sub">'+succRate+'% success rate</div></div>'
        +'<div class="stat-card"><div class="stat-label">Errors</div>'
          +'<div class="stat-val c-red">'+errors+'</div>'
          +'<div class="stat-sub">'+(d.by_status.cancelled||0)+' cancelled</div></div>'
        +'<div class="stat-card"><div class="stat-label">Running Now</div>'
          +'<div class="stat-val c-blue">'+d.running+'</div>'
          +'<div class="stat-sub">'+d.queue_length+' queued &middot; v'+d.version+'</div></div>';

      // Type pills
      const typeHtml = Object.entries(d.by_type)
        .sort((a,b) => b[1]-a[1])
        .map(([t,c]) => typePill(t, c)).join('');
      document.getElementById('type-row').innerHTML = typeHtml || '<span style="color:#555">No data</span>';

      // Active jobs
      const activeCard = document.getElementById('active-card');
      if (d.active_jobs && d.active_jobs.length) {
        activeCard.style.display = '';
        document.getElementById('active-body').innerHTML = d.active_jobs.map(j =>
          '<tr>'
          +'<td><span class="badge" style="background:rgba(219,82,166,0.15);color:'+
              (TYPE_COLORS[j.type]||'#888')+'">'+j.type+'</span></td>'
          +'<td class="url-cell" title="'+escHtml(j.url||'')+'">'+escHtml(truncUrl(j.url))+'</td>'
          +'<td style="color:#5b9cf6;font-weight:700">'+(j.progress_pct||0)+'%</td>'
          +'<td>'+statusBadge(j.status)+'</td>'
          +'</tr>'
        ).join('');
      } else {
        activeCard.style.display = 'none';
      }

      // Recent table
      document.getElementById('recent-count').textContent =
        '(' + d.recent.length + ' shown)';
      document.getElementById('recent-body').innerHTML = d.recent.map(item =>
        '<tr>'
        +'<td class="time-cell">'+relTime(item.timestamp)+'</td>'
        +'<td><span class="badge" style="background:rgba(219,82,166,0.12);color:'
            +(TYPE_COLORS[item.type]||'#888')+'">'+escHtml(item.type||'?')+'</span></td>'
        +'<td class="url-cell" title="'+escHtml(item.url||'')+'">'+escHtml(truncUrl(item.url))+'</td>'
        +'<td>'+statusBadge(item.final_status||'unknown')+'</td>'
        +'</tr>'
      ).join('') || '<tr><td colspan="4" style="color:#555;padding:16px 0">No history yet</td></tr>';
    }

    function truncUrl(url) {
      if (!url) return '—';
      try { url = decodeURIComponent(url); } catch(e) {}
      return url.length > 60 ? url.slice(0, 57) + '…' : url;
    }
    function escHtml(s) {
      return String(s||'').replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;').replace(/"/g,'&quot;');
    }

    function pvCard(label, val, cls, sub) {
      return '<div class="stat-card"><div class="stat-label">' + label + '</div>'
        + '<div class="stat-val ' + cls + '">' + val + '</div>'
        + '<div class="stat-sub">' + (sub || '&nbsp;') + '</div></div>';
    }

    function relTimeTs(ts) {
      if (!ts) return '—';
      var diff = Math.floor(Date.now() / 1000 - ts);
      if (diff < 60)    return diff + 's ago';
      if (diff < 3600)  return Math.floor(diff / 60) + 'm ago';
      if (diff < 86400) return Math.floor(diff / 3600) + 'h ago';
      return Math.floor(diff / 86400) + 'd ago';
    }

    function renderPageviews(pv) {
      if (!pv) return;
      document.getElementById('pv-grid').innerHTML =
          pvCard('Total Views', pv.total, 'c-pink', 'all time')
        + pvCard('Today', pv.today, 'c-green', '')
        + pvCard('This Week', pv.week, 'c-blue', 'last 7 days')
        + pvCard('This Month', pv.month, 'c-amber', 'last 30 days');

      var daily = pv.daily || [];
      var dmax = 1;
      daily.forEach(function (d) { if (d.count > dmax) dmax = d.count; });
      document.getElementById('pv-chart').innerHTML = daily.map(function (d, i) {
        var h = Math.round((d.count / dmax) * 100);
        var lbl = (i % 5 === 0) ? d.date.slice(5) : '&nbsp;';
        var bar = '<div class="chart-bar" style="height:' + h + '%' + (d.count > 0 ? ';min-height:2px' : '') + '"></div>';
        return '<div class="chart-col" title="' + d.date + ': ' + d.count + ' views">'
          + bar + '<div class="chart-lbl">' + lbl + '</div></div>';
      }).join('');

      var paths = pv.by_path || [];
      var pmax = 1;
      paths.forEach(function (p) { if (p.count > pmax) pmax = p.count; });
      document.getElementById('pv-paths').innerHTML = paths.length
        ? paths.map(function (p) {
            var w = Math.round((p.count / pmax) * 100);
            return '<div class="bar-row"><div class="bar-head">'
              + '<span class="bp">' + escHtml(p.path) + '</span>'
              + '<span class="bc">' + p.count + '</span></div>'
              + '<div class="bar-track"><div class="bar-fill" style="width:' + w + '%"></div></div></div>';
          }).join('')
        : '<span style="color:#555;font-size:13px">No views yet</span>';

      var recent = pv.recent || [];
      document.getElementById('pv-recent').innerHTML = recent.length
        ? recent.map(function (r) {
            return '<tr><td class="time-cell">' + relTimeTs(r.ts) + '</td>'
              + '<td class="url-cell" style="color:#f0eef0">' + escHtml(r.path) + '</td></tr>';
          }).join('')
        : '<tr><td colspan="2" style="color:#555;padding:16px 0">No views yet</td></tr>';
    }

    function fmtBytes(n) {
      if (!n) return '0 B';
      var u = ['B', 'KB', 'MB', 'GB'], i = 0;
      while (n >= 1024 && i < u.length - 1) { n /= 1024; i++; }
      return n.toFixed(i ? 1 : 0) + ' ' + u[i];
    }

    function buildKey(os, edition) {
      return (edition === 'trial' ? 'trial-' : '') + os;
    }

    function renderBuildSet(builds, edition) {
      builds = builds || {};
      ['mac', 'win', 'linux'].forEach(function (os) {
        var k = buildKey(os, edition);
        var cur = document.getElementById('build-cur-' + k);
        var del = document.getElementById('build-del-' + k);
        if (!cur) return;
        var slot = builds[os];
        if (slot) {
          cur.textContent = slot.filename + ' · ' + fmtBytes(slot.size);
          cur.className = 'build-cur ok';
          del.style.display = '';
        } else {
          cur.textContent = 'No build uploaded';
          cur.className = 'build-cur none';
          del.style.display = 'none';
        }
      });
    }

    function renderBuilds(builds, trialBuilds) {
      renderBuildSet(builds, 'full');
      renderBuildSet(trialBuilds, 'trial');
    }

    async function uploadBuild(os, edition) {
      edition = edition || 'full';
      var k = buildKey(os, edition);
      var msg = document.getElementById(edition === 'trial' ? 'build-msg-trial' : 'build-msg');
      var file = document.getElementById('bf-' + k).files[0];
      if (!pw()) { msg.textContent = 'Enter password first.'; msg.className = 'err'; return; }
      if (!file) { msg.textContent = 'Choose a ' + os + ' file first.'; msg.className = 'err'; return; }
      msg.textContent = 'Uploading ' + file.name + '…'; msg.className = '';
      try {
        var fd = new FormData();
        fd.append('password', pw());
        fd.append('os', os);
        fd.append('edition', edition);
        fd.append('build', file);
        var r = await fetch('/admin/builds/upload', { method: 'POST', body: fd });
        var j = await r.json();
        if (!r.ok) { msg.textContent = j.error || 'Upload failed.'; msg.className = 'err'; return; }
        msg.textContent = 'Uploaded ' + j.filename; msg.className = 'ok';
        document.getElementById('bf-' + k).value = '';
        loadStats();
      } catch (e) { msg.textContent = 'Network error.'; msg.className = 'err'; }
    }

    async function deleteBuild(os, edition) {
      edition = edition || 'full';
      var msg = document.getElementById(edition === 'trial' ? 'build-msg-trial' : 'build-msg');
      if (!pw()) { msg.textContent = 'Enter password first.'; msg.className = 'err'; return; }
      if (!confirm('Remove the ' + os + ' ' + edition + ' build?')) return;
      msg.textContent = 'Removing…'; msg.className = '';
      try {
        var r = await fetch('/admin/builds/delete', {
          method: 'POST',
          headers: { 'Content-Type': 'application/json' },
          body: JSON.stringify({ password: pw(), os: os, edition: edition })
        });
        var j = await r.json();
        if (!r.ok) { msg.textContent = j.error || 'Delete failed.'; msg.className = 'err'; return; }
        msg.textContent = 'Removed ' + os + ' ' + edition + ' build.'; msg.className = 'ok';
        loadStats();
      } catch (e) { msg.textContent = 'Network error.'; msg.className = 'err'; }
    }
  </script>
</body>
</html>
"""

HTML = r"""
<!doctype html>
<html lang="en">
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width, initial-scale=1">
  <meta name="theme-color" content="#1a1818">
  <meta name="apple-mobile-web-app-capable" content="yes">
  <meta name="apple-mobile-web-app-status-bar-style" content="black-translucent">
  <meta name="apple-mobile-web-app-title" content="+downloads">
  <meta name="description" content="Download any audio or video from YouTube, Spotify, Apple Music, SoundCloud and more. Use it online or get the desktop app for unlimited downloads — $1.99 one-time, free updates forever. macOS, Windows and Linux.">
  <link rel="manifest" href="/static/manifest.json">
  <title>+downloads — Save anything you can stream</title>
  <link rel="icon" type="image/svg+xml" href="/static/favicon.svg">
  <link rel="icon" type="image/png" sizes="64x64" href="/static/favicon.png">
  <link rel="apple-touch-icon" href="/static/icon-192.png">
  <link rel="canonical" href="https://digitaldownloads.space/">
  <meta name="robots" content="index, follow, max-image-preview:large">
  <meta name="author" content="+downloads">
  <!-- Open Graph -->
  <meta property="og:type" content="website">
  <meta property="og:site_name" content="+downloads">
  <meta property="og:title" content="+downloads — Save anything you can stream">
  <meta property="og:description" content="Download any audio or video from YouTube, Spotify, Apple Music, SoundCloud and 1000+ more sites. Online tool or a $1.99 one-time desktop app — free updates forever, macOS, Windows and Linux.">
  <meta property="og:url" content="https://digitaldownloads.space/">
  <meta property="og:image" content="https://digitaldownloads.space/static/og-image.png">
  <meta property="og:image:width" content="1200">
  <meta property="og:image:height" content="630">
  <meta property="og:image:alt" content="digital +downloads — save anything you can stream">
  <!-- Twitter Card -->
  <meta name="twitter:card" content="summary_large_image">
  <meta name="twitter:title" content="+downloads — Save anything you can stream">
  <meta name="twitter:description" content="Download audio or video from YouTube, Spotify, Apple Music, SoundCloud and 1000+ more. $1.99 one-time desktop app, free updates forever.">
  <meta name="twitter:image" content="https://digitaldownloads.space/static/og-image.png">
  <script type="application/ld+json">
  {
    "@context": "https://schema.org",
    "@graph": [
      {
        "@type": "WebSite",
        "@id": "https://digitaldownloads.space/#website",
        "url": "https://digitaldownloads.space/",
        "name": "+downloads",
        "description": "Download any audio or video from YouTube, Spotify, Apple Music, SoundCloud and 1000+ more sites.",
        "publisher": { "@id": "https://digitaldownloads.space/#org" }
      },
      {
        "@type": "Organization",
        "@id": "https://digitaldownloads.space/#org",
        "name": "+downloads",
        "url": "https://digitaldownloads.space/",
        "logo": "https://digitaldownloads.space/static/icon-512.png"
      },
      {
        "@type": "SoftwareApplication",
        "name": "+downloads for Desktop",
        "operatingSystem": "macOS, Windows, Linux",
        "applicationCategory": "MultimediaApplication",
        "description": "A media downloader for YouTube, Spotify, Apple Music, SoundCloud and 1000+ more sites. Runs locally — files never pass through a server. One-time purchase, free updates forever.",
        "url": "https://digitaldownloads.space/",
        "downloadUrl": "https://digitaldownloads.space/desktop/buy",
        "softwareVersion": "latest",
        "screenshot": "https://digitaldownloads.space/static/og-image.png",
        "offers": {
          "@type": "Offer",
          "price": "1.99",
          "priceCurrency": "USD",
          "url": "https://digitaldownloads.space/desktop/buy",
          "availability": "https://schema.org/InStock"
        }
      },
      {
        "@type": "FAQPage",
        "mainEntity": [
          {
            "@type": "Question",
            "name": "What's the difference between the online tool and the desktop app?",
            "acceptedAnswer": { "@type": "Answer", "text": "The online tool is metered — each token gives you a few downloads, billed instantly. The desktop app is unlimited: one $1.99 purchase, every download you want, forever. Plus it runs locally, so files never pass through our server." }
          },
          {
            "@type": "Question",
            "name": "Are updates really free forever?",
            "acceptedAnswer": { "@type": "Answer", "text": "Yes. You buy once and every future version is included — new site support, new formats, new UI. No subscriptions, no upgrade fees." }
          },
          {
            "@type": "Question",
            "name": "What happens after I buy the desktop app?",
            "acceptedAnswer": { "@type": "Answer", "text": "The moment payment confirms, the installer for your operating system (macOS, Windows or Linux) starts downloading directly from digitaldownloads.space. No email link, no waiting room." }
          },
          {
            "@type": "Question",
            "name": "Which sites are supported?",
            "acceptedAnswer": { "@type": "Answer", "text": "YouTube, Spotify, Apple Music, SoundCloud, Vimeo, Twitter/X, Facebook, TikTok, Twitch, Bandcamp, Mixcloud, Dailymotion, plus ~1000 others. If a site streams audio or video, there's a good chance we support it." }
          },
          {
            "@type": "Question",
            "name": "Is it legal?",
            "acceptedAnswer": { "@type": "Answer", "text": "+downloads is a tool — what you do with it is on you. We expect downloads only for content you own, content licensed under permissive terms, or content where the source platform permits download." }
          },
          {
            "@type": "Question",
            "name": "Do you collect my data?",
            "acceptedAnswer": { "@type": "Answer", "text": "No third-party analytics, no tracking SDKs. The desktop app runs entirely on your machine — we never see your URLs, files, or activity." }
          }
        ]
      }
    ]
  }
  </script>
  <script async src="https://pagead2.googlesyndication.com/pagead/js/adsbygoogle.js?client=ca-pub-5597587878564683"
     crossorigin="anonymous"></script>
  <style>
    *, *::before, *::after { box-sizing: border-box; margin: 0; padding: 0; }
    html { scroll-behavior: smooth; }
    body {
      font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', sans-serif;
      background: #1a1818;
      color: #f0eef0;
      min-height: 100vh;
      overflow-x: hidden;
    }
    a { color: inherit; }

    /* ── HEADER ───────────────────────────────────────────── */
    .header {
      background: rgba(26,24,24,0.85);
      backdrop-filter: blur(12px);
      -webkit-backdrop-filter: blur(12px);
      border-bottom: 1px solid #2e2c2c;
      padding: 0 32px;
      height: 64px;
      display: flex; align-items: center; gap: 14px;
      position: sticky; top: 0; z-index: 50;
    }
    .logo { font-size: 24px; font-weight: 800; color: #db52a6; letter-spacing: -0.5px; text-decoration: none; white-space: nowrap; }
    .logo .lo-prefix { color: #f0eef0; font-weight: 700; margin-right: 4px; }
    .nav { margin-left: auto; display: flex; align-items: center; gap: 10px; }
    .nav a, .nav .nav-link {
      font-size: 13px; font-weight: 600; color: #888; text-decoration: none;
      padding: 8px 12px; border-radius: 8px; transition: color 0.15s, background 0.15s;
      cursor: pointer; background: transparent; border: none;
    }
    .nav a:hover, .nav .nav-link:hover { color: #f0eef0; background: #242222; }
    .nav .pill {
      color: #1a1818; background: #bf9b3a; font-weight: 700;
      padding: 8px 14px;
    }
    .nav .pill:hover { background: #d4ad42; color: #1a1818; }
    .nav .buy-pill {
      color: #fff; background: #db52a6; font-weight: 700;
      padding: 8px 14px;
    }
    .nav .buy-pill:hover { background: #c9479a; color: #fff; }

    /* ── HERO ─────────────────────────────────────────────── */
    .hero {
      position: relative;
      padding: 56px 20px 48px;
      text-align: center;
      overflow: hidden;
    }
    .hero::before {
      content: ''; position: absolute; inset: 0;
      background:
        radial-gradient(circle at 25% 15%, rgba(219,82,166,0.18), transparent 45%),
        radial-gradient(circle at 80% 35%, rgba(155,58,219,0.14), transparent 50%),
        radial-gradient(circle at 50% 90%, rgba(191,155,58,0.10), transparent 55%);
      pointer-events: none;
      z-index: 0;
    }
    .hero-inner { position: relative; z-index: 1; max-width: 720px; margin: 0 auto; }
    .hero-eyebrow {
      display: inline-block; font-size: 12px; font-weight: 700;
      color: #db52a6; letter-spacing: 0.12em; text-transform: uppercase;
      background: rgba(219,82,166,0.10); border: 1px solid rgba(219,82,166,0.25);
      padding: 5px 12px; border-radius: 999px; margin-bottom: 18px;
    }
    .hero-title {
      font-size: clamp(34px, 5.2vw, 52px);
      font-weight: 800; letter-spacing: -1.2px; line-height: 1.05;
      color: #f0eef0; margin-bottom: 14px;
    }
    .hero-title .grad {
      background: linear-gradient(95deg, #db52a6 0%, #c44e9a 40%, #bf9b3a 100%);
      -webkit-background-clip: text; background-clip: text;
      color: transparent;
    }
    .hero-sub {
      font-size: clamp(15px, 1.8vw, 17px); color: #aaa6aa;
      line-height: 1.55; margin: 0 auto 28px; max-width: 520px;
    }

    /* ── DOWNLOADER (in hero) ─────────────────────────────── */
    .downloader {
      max-width: 640px; margin: 0 auto;
      background: #242222; border: 1px solid #2e2c2c;
      border-radius: 18px; padding: 22px;
      box-shadow: 0 18px 48px rgba(0,0,0,0.45), 0 0 0 1px rgba(219,82,166,0.05);
      text-align: left;
    }
    .url-row { display: flex; gap: 10px; }
    input[type=text] {
      background: #1a1818; border: 1.5px solid #353333; color: #f0eef0;
      padding: 14px 16px; border-radius: 11px; font-size: 15px;
      flex: 1; min-width: 0; outline: none;
      transition: border-color 0.2s, box-shadow 0.2s;
    }
    input[type=text]:focus { border-color: #db52a6; box-shadow: 0 0 0 3px rgba(219,82,166,0.12); }
    input::placeholder { color: #555; }
    .btn-primary {
      background: #db52a6; color: #fff; border: none;
      padding: 14px 24px; border-radius: 11px; font-size: 15px; font-weight: 700;
      cursor: pointer; white-space: nowrap; flex-shrink: 0;
      transition: background 0.15s, transform 0.1s, box-shadow 0.15s;
      display: inline-flex; align-items: center; gap: 8px;
    }
    .btn-primary:hover { background: #c9479a; box-shadow: 0 6px 18px rgba(219,82,166,0.32); }
    .btn-primary:active { transform: scale(0.97); }
    .btn-primary:disabled { opacity: 0.55; cursor: default; transform: none; box-shadow: none; }
    .btn-token {
      background: #2a2828; color: #f0eef0; border: 1.5px solid #353333;
    }
    .btn-token:hover { background: #2e2c2c; border-color: #db52a6; color: #db52a6; box-shadow: none; }
    .btn-cancel {
      background: transparent; color: #666; border: 1px solid #353333;
      padding: 5px 14px; border-radius: 8px; font-size: 13px; cursor: pointer;
      transition: color 0.15s, border-color 0.15s;
    }
    .btn-cancel:hover { color: #ff6b6b; border-color: #ff6b6b; }
    .type-row { display: flex; gap: 10px; margin-top: 12px; }
    select {
      background: #1a1818; border: 1.5px solid #353333; color: #f0eef0;
      padding: 12px 36px 12px 14px; border-radius: 10px; font-size: 14px;
      flex: 1; min-width: 0; outline: none; cursor: pointer;
      appearance: none; -webkit-appearance: none;
      background-image: url("data:image/svg+xml,%3Csvg xmlns='http://www.w3.org/2000/svg' width='12' height='7' viewBox='0 0 12 7'%3E%3Cpath d='M1 1l5 5 5-5' stroke='%23666' stroke-width='1.5' fill='none' stroke-linecap='round' stroke-linejoin='round'/%3E%3C/svg%3E");
      background-repeat: no-repeat; background-position: right 13px center;
      transition: border-color 0.2s;
    }
    select:focus { border-color: #db52a6; }
    #scOptions { display: none; margin-top: 12px; gap: 14px; align-items: center; flex-wrap: wrap; }
    #scOptions label { font-size: 13px; color: #888; display: flex; align-items: center; gap: 7px; cursor: pointer; }
    #scOptions select { padding: 8px 32px 8px 12px; font-size: 13px; flex: none; width: auto; }
    .note-pill {
      display: none; margin-top: 10px;
      background: rgba(191,155,58,0.07); border: 1px solid rgba(191,155,58,0.18);
      border-radius: 8px; padding: 9px 14px; font-size: 13px; color: #bf9b3a; line-height: 1.5;
    }

    /* ── Token entry (collapsible) ─────────────────────────── */
    .token-area { margin-top: 12px; }
    #token-input-row {
      display: none; gap: 8px; align-items: center; margin-top: 4px;
      animation: tokenSlide 0.25s ease-out;
    }
    #token-input-row.open { display: flex; }
    @keyframes tokenSlide {
      from { opacity: 0; transform: translateY(-4px); }
      to   { opacity: 1; transform: translateY(0); }
    }
    #token-field {
      flex: 1; background: #1a1818; border: 1.5px solid #2e2c2c;
      border-radius: 10px; padding: 11px 14px; font-size: 13px;
      font-family: 'SF Mono', monospace; color: #f0eef0; outline: none;
      transition: border-color 0.15s;
    }
    #token-field:focus { border-color: #db52a6; }
    #token-submit-btn {
      background: #db52a6; color: #fff; border: none;
      border-radius: 10px; padding: 11px 18px; font-size: 13px; font-weight: 700;
      cursor: pointer; white-space: nowrap; transition: background 0.15s;
    }
    #token-submit-btn:hover { background: #c9479a; }
    #token-submit-btn:disabled { opacity: 0.55; cursor: default; }
    #token-error { display: none; font-size: 12px; color: #ff6b6b; margin-top: 8px; }
    #token-unlocked {
      display: none; align-items: center; gap: 10px;
      background: rgba(72,199,142,0.07); border: 1px solid rgba(72,199,142,0.22);
      border-radius: 10px; padding: 9px 14px; margin-top: 4px;
    }
    #token-unlocked span.lab {
      font-size: 13px; color: #48c78e; font-weight: 600;
    }
    #token-unlocked span#token-remaining { font-size: 12px; color: #888; }
    #token-unlocked button {
      margin-left: auto; background: transparent; border: none; color: #666;
      font-size: 11px; cursor: pointer; padding: 4px 8px; border-radius: 6px;
    }
    #token-unlocked button:hover { color: #e05c5c; }

    /* ── Status / progress (collapsible) ───────────────────── */
    .status-block { display: none; margin-top: 18px; padding-top: 18px; border-top: 1px solid #2a2828; }
    .status-block.active { display: block; }
    .status-row { display: flex; align-items: center; gap: 10px; margin-bottom: 14px; }
    #statusPill {
      padding: 5px 14px; border-radius: 999px;
      font-size: 11px; font-weight: 700; text-transform: uppercase; letter-spacing: 0.7px;
      background: #252323; color: #555; transition: background 0.2s, color 0.2s;
    }
    #queuePos { font-size: 13px; color: #bf9b3a; }
    #progressWrap { display: none; margin-bottom: 14px; }
    #progressTrack {
      background: #1a1818; border-radius: 10px; height: 22px; overflow: hidden;
      position: relative; border: 1px solid #242222;
    }
    #progressBar {
      height: 100%; width: 0%; border-radius: 10px;
      background: linear-gradient(90deg, #db52a6, #c44e9a, #bf9b3a);
      background-size: 200% 100%;
      animation: shimmer 2s linear infinite;
      transition: width 0.4s ease;
      box-shadow: 0 0 12px rgba(219,82,166,0.3);
    }
    @keyframes shimmer { 0%{background-position:200% 0} 100%{background-position:-200% 0} }
    #progressBar.indeterminate {
      width: 30%; background: linear-gradient(90deg, transparent, #db52a6, transparent);
      background-size: 200% 100%;
      animation: barslide 1.5s infinite ease-in-out;
      box-shadow: 0 0 12px rgba(219,82,166,0.3);
    }
    @keyframes barslide { 0%{transform:translateX(-200%)} 100%{transform:translateX(500%)} }
    #progressLabel {
      position: absolute; inset: 0; display: flex; align-items: center; justify-content: center;
      font-size: 11px; font-weight: 600; color: #f0eef0; text-shadow: 0 1px 3px rgba(0,0,0,0.5);
      pointer-events: none; z-index: 1;
    }
    #progressText { font-size: 12px; color: #777; margin-top: 8px; display: block; }
    .phase-label { font-size: 14px; font-weight: 600; color: #f0eef0; margin: 6px 0 2px; }
    .phase-note { font-size: 12px; color: #9a8f9a; margin-bottom: 8px; }
    .phase-note.err { color: #ff8f8f; }
    pre#log {
      background: #141212; border: 1px solid #242222; border-radius: 10px;
      color: #776f77; padding: 10px 14px;
      font-size: 11px; font-family: 'SF Mono', 'Fira Code', monospace;
      max-height: 120px; overflow-y: auto;
      white-space: pre-wrap; word-break: break-all; line-height: 1.55; margin: 0;
      display: none;
    }
    pre#log.visible { display: block; }
    #meta { font-size: 13px; color: #777; margin-top: 10px; }
    #meta a { color: #db52a6; text-decoration: none; }
    #meta a:hover { text-decoration: underline; }

    /* Paused banner */
    .paused-banner {
      display: none; background: #2a1a1a; border: 1.5px solid #e05c5c;
      border-radius: 14px; padding: 18px 22px; margin-bottom: 14px; text-align: center;
    }
    .paused-banner h2 { font-size: 16px; font-weight: 800; color: #e05c5c; margin-bottom: 6px; }
    .paused-banner p { font-size: 13px; color: #aaa; margin-bottom: 14px; line-height: 1.5; }
    .btn-get-app {
      display: inline-block; background: #db52a6; color: #fff;
      padding: 11px 24px; border-radius: 10px; font-size: 14px; font-weight: 700;
      text-decoration: none; transition: background 0.15s;
    }
    .btn-get-app:hover { background: #c9479a; }

    /* ── Token purchase cards (under URL box) ──────────────── */
    .token-buy-wrap { max-width: 640px; margin: 22px auto 0; }
    .token-buy-label {
      text-align: center; font-size: 12px; font-weight: 700;
      color: #555; letter-spacing: 0.12em; text-transform: uppercase; margin-bottom: 12px;
    }
    .token-buy-grid {
      display: grid; grid-template-columns: 1fr 1fr; gap: 12px;
    }
    .token-buy {
      display: flex; flex-direction: column; align-items: flex-start;
      background: #242222; border: 1.5px solid #2e2c2c; border-radius: 14px;
      padding: 18px 22px; text-decoration: none; color: #f0eef0;
      transition: transform 0.15s, border-color 0.15s, box-shadow 0.15s;
      position: relative;
    }
    .token-buy:hover {
      transform: translateY(-2px); border-color: #db52a6;
      box-shadow: 0 10px 28px rgba(219,82,166,0.18);
    }
    .token-buy.alt:hover { border-color: #9b3adb; box-shadow: 0 10px 28px rgba(155,58,219,0.20); }
    .token-buy .tag {
      position: absolute; top: 10px; right: 10px;
      font-size: 10px; font-weight: 700; letter-spacing: 0.06em;
      color: #1a1818; background: #bf9b3a; padding: 3px 9px; border-radius: 999px;
    }
    .token-buy .price {
      font-size: 28px; font-weight: 800; letter-spacing: -0.5px;
      color: #db52a6; line-height: 1; margin-bottom: 4px;
    }
    .token-buy.alt .price { color: #9b3adb; }
    .token-buy .qty { font-size: 14px; font-weight: 700; color: #f0eef0; }
    .token-buy .sub { font-size: 12px; color: #888; margin-top: 6px; line-height: 1.4; }
    .token-buy .arrow {
      align-self: flex-end; margin-top: 10px; font-size: 13px; font-weight: 700;
      color: #db52a6; display: inline-flex; align-items: center; gap: 4px;
    }
    .token-buy.alt .arrow { color: #9b3adb; }

    /* ── PRODUCT SECTION ──────────────────────────────────── */
    .product {
      background: linear-gradient(180deg, #1a1818 0%, #1e1c1e 100%);
      padding: 80px 20px 60px;
      border-top: 1px solid #242222;
      position: relative;
    }
    .container { max-width: 1080px; margin: 0 auto; }
    .product-hero { text-align: center; max-width: 720px; margin: 0 auto 56px; }
    .product-eyebrow {
      display: inline-block; font-size: 12px; font-weight: 700;
      color: #bf9b3a; letter-spacing: 0.12em; text-transform: uppercase;
      background: rgba(191,155,58,0.10); border: 1px solid rgba(191,155,58,0.25);
      padding: 5px 12px; border-radius: 999px; margin-bottom: 18px;
    }
    .product-hero h2 {
      font-size: clamp(30px, 4.4vw, 44px); font-weight: 800; letter-spacing: -1px;
      line-height: 1.1; margin-bottom: 14px;
    }
    .product-hero h2 .grad {
      background: linear-gradient(95deg, #db52a6 0%, #bf9b3a 100%);
      -webkit-background-clip: text; background-clip: text; color: transparent;
    }
    .product-hero p {
      font-size: 17px; color: #aaa6aa; line-height: 1.6; margin: 0 auto 24px; max-width: 580px;
    }
    .trust-row {
      display: flex; gap: 18px; justify-content: center; flex-wrap: wrap;
      font-size: 13px; color: #888; margin-top: 18px;
    }
    .trust-row .trust { display: inline-flex; align-items: center; gap: 6px; }
    .trust-row .trust svg { color: #48c78e; }
    .trial-cta { margin-top: 16px; }
    .btn-trial {
      display: inline-flex; align-items: center; gap: 10px;
      background: linear-gradient(95deg, #c9a53e 0%, #ad8c30 100%);
      color: #1a1818; padding: 16px 32px; border-radius: 12px;
      font-size: 16px; font-weight: 800; text-decoration: none;
      box-shadow: 0 10px 28px rgba(191,155,58,0.26);
      transition: transform 0.15s, box-shadow 0.15s;
      border: none;
    }
    .btn-trial:hover { transform: translateY(-2px); box-shadow: 0 16px 36px rgba(191,155,58,0.40); }
    .btn-trial:active { transform: translateY(0); }
    .btn-buy {
      display: inline-flex; align-items: center; gap: 10px;
      background: linear-gradient(95deg, #db52a6 0%, #c44e9a 100%);
      color: #fff; padding: 16px 32px; border-radius: 12px;
      font-size: 16px; font-weight: 800; text-decoration: none;
      box-shadow: 0 10px 28px rgba(219,82,166,0.28);
      transition: transform 0.15s, box-shadow 0.15s;
      border: none; cursor: pointer;
    }
    .btn-buy:hover { transform: translateY(-2px); box-shadow: 0 16px 36px rgba(219,82,166,0.40); }
    .btn-buy:active { transform: translateY(0); }
    .btn-buy.large { padding: 18px 38px; font-size: 17px; }

    /* Feature grid */
    .features {
      display: grid; grid-template-columns: repeat(3, 1fr); gap: 14px;
      margin-bottom: 64px;
    }
    .feature {
      background: #242222; border: 1px solid #2e2c2c; border-radius: 14px;
      padding: 22px 22px; transition: border-color 0.15s, transform 0.15s;
    }
    .feature:hover { border-color: #353333; transform: translateY(-2px); }
    .feature-icon {
      width: 38px; height: 38px; border-radius: 10px;
      background: rgba(219,82,166,0.12);
      display: inline-flex; align-items: center; justify-content: center;
      color: #db52a6; margin-bottom: 14px;
    }
    .feature h3 { font-size: 16px; font-weight: 800; color: #f0eef0; margin-bottom: 6px; letter-spacing: -0.2px; }
    .feature p { font-size: 13.5px; color: #999; line-height: 1.55; }

    /* Screenshot gallery */
    .shots { margin-bottom: 64px; }
    .shots-label {
      display: block; text-align: center; font-size: 12px; font-weight: 700;
      color: #bf9b3a; letter-spacing: 0.12em; text-transform: uppercase; margin-bottom: 20px;
    }
    .shot-hero {
      background: #1c1a1c; border: 1px solid #2e2c2c; border-radius: 16px;
      overflow: hidden; margin-bottom: 14px;
    }
    .shot-hero img { display: block; width: 100%; height: auto; }
    .shot-grid { display: grid; grid-template-columns: repeat(3, 1fr); gap: 14px; }
    .shot { margin: 0; }
    .shot-frame {
      background: #1c1a1c; border: 1px solid #2e2c2c; border-radius: 14px;
      aspect-ratio: 4 / 3; display: flex; align-items: center; justify-content: center;
      overflow: hidden; padding: 10px;
    }
    .shot-frame img { max-width: 100%; max-height: 100%; object-fit: contain; display: block; }
    .shot figcaption {
      text-align: center; font-size: 13px; color: #999; font-weight: 600; margin-top: 10px;
    }

    /* iOS companion promo */
    .ios-promo {
      display: flex; align-items: center; gap: 22px;
      background: #242222; border: 1px solid #2e2c2c; border-radius: 16px;
      padding: 22px 26px; margin: 0 auto 56px; max-width: 620px;
    }
    .ios-qr {
      flex-shrink: 0; width: 116px; height: 116px; background: #fff;
      border-radius: 12px; padding: 9px;
    }
    .ios-qr img { width: 100%; height: 100%; image-rendering: pixelated; }
    .ios-copy { flex: 1; }
    .ios-eyebrow {
      display: inline-block; font-size: 11px; font-weight: 700; color: #bf9b3a;
      letter-spacing: 0.1em; text-transform: uppercase; margin-bottom: 5px;
    }
    .ios-copy h3 { font-size: 19px; font-weight: 800; color: #f0eef0; margin-bottom: 6px; }
    .ios-copy p { font-size: 13.5px; color: #999; line-height: 1.55; margin-bottom: 13px; }
    .ios-btn {
      display: inline-block; font-size: 13px; font-weight: 700; color: #f0eef0;
      text-decoration: none; background: #1a1818; border: 1px solid #353333;
      padding: 9px 16px; border-radius: 10px; transition: border-color 0.15s, color 0.15s;
    }
    .ios-btn:hover { border-color: #db52a6; color: #db52a6; }
    @media (max-width: 600px) {
      .shot-grid { grid-template-columns: 1fr; }
      .ios-promo { flex-direction: column; text-align: center; }
    }

    /* Supported sites */
    .sites { text-align: center; padding: 40px 0 60px; }
    .sites-label {
      font-size: 12px; font-weight: 700; color: #555;
      letter-spacing: 0.14em; text-transform: uppercase; margin-bottom: 18px;
    }
    .sites-pills {
      display: flex; flex-wrap: wrap; gap: 8px; justify-content: center;
      max-width: 820px; margin: 0 auto;
    }
    .site-pill {
      background: #242222; border: 1px solid #2e2c2c;
      padding: 8px 14px; border-radius: 999px;
      font-size: 13px; font-weight: 600; color: #c8c4c8;
      transition: border-color 0.15s, color 0.15s;
    }
    .site-pill:hover { border-color: #db52a6; color: #db52a6; }

    /* How it works */
    .how { padding: 40px 0; }
    .how-title {
      text-align: center; font-size: 28px; font-weight: 800; letter-spacing: -0.6px;
      margin-bottom: 36px;
    }
    .how-steps {
      display: grid; grid-template-columns: repeat(3, 1fr); gap: 14px;
    }
    .how-step {
      background: #242222; border: 1px solid #2e2c2c; border-radius: 14px;
      padding: 26px 22px; position: relative;
    }
    .how-num {
      position: absolute; top: 18px; right: 22px;
      font-size: 44px; font-weight: 800; color: rgba(219,82,166,0.18);
      letter-spacing: -2px; line-height: 1;
    }
    .how-step h3 { font-size: 17px; font-weight: 800; margin-bottom: 6px; color: #f0eef0; }
    .how-step p { font-size: 13.5px; color: #999; line-height: 1.55; }

    /* FAQ */
    .faq { padding: 60px 0 40px; max-width: 760px; margin: 0 auto; }
    .faq-title {
      text-align: center; font-size: 28px; font-weight: 800; letter-spacing: -0.6px;
      margin-bottom: 32px;
    }
    .faq details {
      background: #242222; border: 1px solid #2e2c2c; border-radius: 12px;
      padding: 0; margin-bottom: 10px; overflow: hidden;
    }
    .faq summary {
      cursor: pointer; padding: 18px 22px; font-size: 15px; font-weight: 700;
      color: #f0eef0; list-style: none; display: flex; align-items: center; gap: 12px;
      transition: background 0.15s;
    }
    .faq summary:hover { background: #2a2828; }
    .faq summary::-webkit-details-marker { display: none; }
    .faq summary::before {
      content: '+'; color: #db52a6; font-size: 22px; font-weight: 400; line-height: 1;
      width: 16px; text-align: center; transition: transform 0.2s;
    }
    .faq details[open] summary::before { content: '−'; }
    .faq-body { padding: 0 22px 18px 50px; font-size: 14px; color: #aaa6aa; line-height: 1.65; }

    /* Final CTA */
    .final-cta {
      text-align: center; padding: 60px 24px 40px;
      background: radial-gradient(circle at 50% 50%, rgba(219,82,166,0.12), transparent 60%);
      margin-top: 30px; border-radius: 18px;
    }
    .final-cta h3 {
      font-size: clamp(24px, 3.4vw, 34px); font-weight: 800; letter-spacing: -0.6px;
      margin-bottom: 10px;
    }
    .final-cta p { font-size: 15px; color: #aaa6aa; margin-bottom: 24px; }

    /* Modal */
    #dlModal {
      display: none; position: fixed; inset: 0; z-index: 999;
      background: rgba(0,0,0,0.55); backdrop-filter: blur(4px);
      align-items: center; justify-content: center;
    }
    .modal-inner {
      background: #1e1c1c; border: 1px solid #333; border-radius: 14px;
      padding: 28px 32px; max-width: 420px; width: 90%; text-align: center;
    }
    /* Footer */
    .site-footer {
      text-align: center; padding: 36px 16px 28px;
      font-size: 12px; color: #555; border-top: 1px solid #242222; margin-top: 40px;
    }
    .site-footer a { color: #888; text-decoration: none; }
    .site-footer a:hover { color: #db52a6; }
    .site-footer .sep { margin: 0 8px; color: #3a3838; }

    ::-webkit-scrollbar { width: 6px; }
    ::-webkit-scrollbar-track { background: transparent; }
    ::-webkit-scrollbar-thumb { background: #353333; border-radius: 3px; }

    /* ── Responsive ────────────────────────────────────────── */
    @media (max-width: 800px) {
      .features, .how-steps { grid-template-columns: 1fr 1fr; }
    }
    @media (max-width: 600px) {
      .header { padding: 0 14px; height: 56px; gap: 8px; }
      .nav a, .nav .nav-link { padding: 7px 10px; font-size: 12px; }
      .nav .pill, .nav .buy-pill { padding: 7px 12px; }
      .logo { font-size: 20px; }
      .hero { padding: 36px 14px 32px; }
      .downloader { padding: 16px; border-radius: 14px; }
      .url-row { flex-wrap: wrap; }
      .url-row .btn-primary { width: 100%; padding: 13px; font-size: 15px; justify-content: center; }
      .token-buy-grid { grid-template-columns: 1fr; }
      .product { padding: 56px 16px 40px; }
      .features, .how-steps { grid-template-columns: 1fr; }
      .how-num { font-size: 36px; }
    }
  </style>
</head>
<body>

  <header class="header">
    <a class="logo" href="/"><span class="lo-prefix">digital</span>+downloads</a>
    <nav class="nav">
      <button class="nav-link" onclick="document.getElementById('downloader').scrollIntoView({behavior:'smooth',block:'center'})">Online</button>
      <a href="#features">Features</a>
      <a href="#faq">FAQ</a>
      <a class="pill" href="/desktop/buy">Buy Desktop · $1.99</a>
    </nav>
  </header>

  <!-- ─── PRODUCT SECTION (Desktop) ────────────────────── -->
  <section class="product" id="features">
    <div class="container">
      <div class="product-hero">
        <span class="product-eyebrow">+downloads for Desktop</span>
        <h2>Own the tool. <span class="grad">No subscriptions.</span></h2>
        <p>Unlimited downloads, batch jobs, 4K video and lossless audio — all running locally on your Mac or PC. No tokens, no waits, no limits.</p>
        <div>
          <a class="btn-buy large" href="/desktop/buy">
            <svg width="18" height="18" viewBox="0 0 24 24" fill="none"><path d="M12 4v12m0 0l-4-4m4 4l4-4M4 20h16" stroke="#fff" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"/></svg>
            Buy +downloads — $1.99
          </a>
        </div>
        <div class="trust-row">
          <span class="trust"><svg width="14" height="14" viewBox="0 0 24 24" fill="none"><path d="M5 12l5 5L20 7" stroke="currentColor" stroke-width="2.5" stroke-linecap="round" stroke-linejoin="round"/></svg>Free updates forever</span>
          <span class="trust"><svg width="14" height="14" viewBox="0 0 24 24" fill="none"><path d="M5 12l5 5L20 7" stroke="currentColor" stroke-width="2.5" stroke-linecap="round" stroke-linejoin="round"/></svg>macOS, Windows &amp; Linux</span>
          <span class="trust"><svg width="14" height="14" viewBox="0 0 24 24" fill="none"><path d="M5 12l5 5L20 7" stroke="currentColor" stroke-width="2.5" stroke-linecap="round" stroke-linejoin="round"/></svg>Auto-download after checkout</span>
        </div>
        <div class="trial-cta">
          <a class="btn-trial" href="/trial">
            <svg width="18" height="18" viewBox="0 0 24 24" fill="none"><path d="M12 4v12m0 0l-4-4m4 4l4-4M4 20h16" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"/></svg>
            Try the <span class="tg">free trial</span> &mdash; no payment
          </a>
        </div>
      </div>

      <!-- Screenshots -->
      <div class="shots">
        <span class="shots-label">See it in action</span>
        <div class="shot-hero">
          <img src="/static/shot-app.png" alt="The +downloads desktop app — downloader, music player and video library in one window" width="2000" height="1193" loading="lazy">
        </div>
        <div class="shot-grid">
          <figure class="shot">
            <div class="shot-frame"><img src="/static/shot-sources.png" alt="Source picker — YouTube, SoundCloud, Spotify, Apple Music" width="680" height="438" loading="lazy"></div>
            <figcaption>Download from any source</figcaption>
          </figure>
          <figure class="shot">
            <div class="shot-frame"><img src="/static/shot-video.jpg" alt="Built-in video player and searchable library" width="1100" height="992" loading="lazy"></div>
            <figcaption>Watch &amp; organize your library</figcaption>
          </figure>
          <figure class="shot">
            <div class="shot-frame"><img src="/static/shot-music.png" alt="Music player with Burn-a-CD queue" width="688" height="1128" loading="lazy"></div>
            <figcaption>Music player &amp; CD burning</figcaption>
          </figure>
        </div>
      </div>

      <div class="features">
        <div class="feature">
          <div class="feature-icon"><svg width="20" height="20" viewBox="0 0 24 24" fill="none"><path d="M12 4v12m0 0l-4-4m4 4l4-4M4 20h16" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"/></svg></div>
          <h3>Unlimited downloads</h3>
          <p>No queue, no per-day cap, no token counter. Run as many jobs as your bandwidth can handle.</p>
        </div>
        <div class="feature">
          <div class="feature-icon"><svg width="20" height="20" viewBox="0 0 24 24" fill="none"><path d="M3 7h18M3 12h18M3 17h12" stroke="currentColor" stroke-width="2" stroke-linecap="round"/></svg></div>
          <h3>Batch queue</h3>
          <p>Paste a list, hit go. Channel rips, playlists, and albums process in parallel in the background.</p>
        </div>
        <div class="feature">
          <div class="feature-icon"><svg width="20" height="20" viewBox="0 0 24 24" fill="none"><rect x="3" y="5" width="18" height="14" rx="2" stroke="currentColor" stroke-width="2"/><path d="M10 9l5 3-5 3V9z" fill="currentColor"/></svg></div>
          <h3>4K + lossless audio</h3>
          <p>Highest available video resolution and best-source audio. m4a, flac, mp3 — pick what you want.</p>
        </div>
        <div class="feature">
          <div class="feature-icon"><svg width="20" height="20" viewBox="0 0 24 24" fill="none"><path d="M12 22s8-4 8-12V5l-8-3-8 3v5c0 8 8 12 8 12z" stroke="currentColor" stroke-width="2" stroke-linejoin="round"/></svg></div>
          <h3>Runs locally</h3>
          <p>Files never touch our server. Nothing logged, nothing uploaded, nothing tracked.</p>
        </div>
        <div class="feature">
          <div class="feature-icon"><svg width="20" height="20" viewBox="0 0 24 24" fill="none"><circle cx="12" cy="12" r="9" stroke="currentColor" stroke-width="2"/><path d="M12 7v5l3 2" stroke="currentColor" stroke-width="2" stroke-linecap="round"/></svg></div>
          <h3>Resume + retry</h3>
          <p>Interrupted downloads pick up where they left off. Flaky network? No re-pay, no re-queue.</p>
        </div>
        <div class="feature">
          <div class="feature-icon"><svg width="20" height="20" viewBox="0 0 24 24" fill="none"><path d="M20 6L9 17l-5-5" stroke="currentColor" stroke-width="2.5" stroke-linecap="round" stroke-linejoin="round"/></svg></div>
          <h3>Updates free forever</h3>
          <p>One purchase, every future version. New site support, new formats, new features — all included.</p>
        </div>
      </div>

      <!-- Supported sites -->
      <div class="sites">
        <div class="sites-label">Works with</div>
        <div class="sites-pills">
          <span class="site-pill">YouTube</span>
          <span class="site-pill">Spotify</span>
          <span class="site-pill">Apple Music</span>
          <span class="site-pill">SoundCloud</span>
          <span class="site-pill">Vimeo</span>
          <span class="site-pill">Twitter / X</span>
          <span class="site-pill">Facebook</span>
          <span class="site-pill">TikTok</span>
          <span class="site-pill">Twitch</span>
          <span class="site-pill">Bandcamp</span>
          <span class="site-pill">Mixcloud</span>
          <span class="site-pill">Dailymotion</span>
          <span class="site-pill">+1000 more</span>
        </div>
      </div>

      <!-- How it works -->
      <div class="how">
        <h2 class="how-title">How it works</h2>
        <div class="how-steps">
          <div class="how-step">
            <span class="how-num">1</span>
            <h3>Buy &amp; download</h3>
            <p>Hit Buy, complete checkout, and the installer downloads automatically — no email links, no waiting.</p>
          </div>
          <div class="how-step">
            <span class="how-num">2</span>
            <h3>Paste a URL</h3>
            <p>Drop any video or track link into the app. It auto-detects the site and picks the best format.</p>
          </div>
          <div class="how-step">
            <span class="how-num">3</span>
            <h3>Save the file</h3>
            <p>Files land in your Downloads folder. Keep them, send them, archive them. They're yours.</p>
          </div>
        </div>
      </div>

      <!-- FAQ -->
      <div class="faq" id="faq">
        <h2 class="faq-title">Common questions</h2>
        <details>
          <summary>What's the difference between the online tool and the desktop app?</summary>
          <div class="faq-body">The online tool is metered — each token gives you a few downloads, billed instantly. The desktop app is unlimited: one $1.99 purchase, every download you want, forever. Plus it runs locally, so files never pass through our server.</div>
        </details>
        <details>
          <summary>Are updates really free forever?</summary>
          <div class="faq-body">Yes. You buy once and every future version is included — new site support, new formats, new UI. No subscriptions, no upgrade fees.</div>
        </details>
        <details>
          <summary>What happens after I buy the desktop app?</summary>
          <div class="faq-body">The moment payment confirms, the installer for your operating system (macOS, Windows or Linux) starts downloading directly from digitaldownloads.space. No email link, no waiting room.</div>
        </details>
        <details>
          <summary>Which sites are supported?</summary>
          <div class="faq-body">YouTube, Spotify, Apple Music, SoundCloud, Vimeo, Twitter/X, Facebook, TikTok, Twitch, Bandcamp, Mixcloud, Dailymotion, plus ~1000 others. If a site streams audio or video, there's a good chance we support it.</div>
        </details>
        <details>
          <summary>Is it legal?</summary>
          <div class="faq-body">+downloads is a tool — what you do with it is on you. We expect downloads only for content you own, content licensed under permissive terms, or content where the source platform permits download. See our <a href="/terms" style="color:#bf9b3a;">Terms</a>.</div>
        </details>
        <details>
          <summary>Do you collect my data?</summary>
          <div class="faq-body">No third-party analytics, no tracking SDKs. The desktop app runs entirely on your machine — we never see your URLs, files, or activity. See our <a href="/privacy" style="color:#bf9b3a;">Privacy policy</a>.</div>
        </details>
      </div>

      <!-- iOS companion -->
      <div class="ios-promo">
        <div class="ios-qr">
          <img src="/static/ios-app-qr.png" alt="Scan to get + Media Player on the App Store" width="330" height="330">
        </div>
        <div class="ios-copy">
          <span class="ios-eyebrow">New iOS companion</span>
          <h3>+ Media Player</h3>
          <p>Scan with your iPhone to play your synced +downloads library on the go — pairs with the desktop app over Wi-Fi.</p>
          <a class="ios-btn" href="https://urapages.com/r/ios-qr?s=digitaldownloads-home" target="_blank" rel="noopener noreferrer">Open in App Store &rsaquo;</a>
        </div>
      </div>

      <!-- Final CTA -->
      <div class="final-cta">
        <h3>Two bucks. Every future update. Done.</h3>
        <p>Stop fighting with free-trial walls and per-download tokens.</p>
        <a class="btn-buy large" href="/desktop/buy">
          <svg width="18" height="18" viewBox="0 0 24 24" fill="none"><path d="M12 4v12m0 0l-4-4m4 4l4-4M4 20h16" stroke="#fff" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"/></svg>
          Get +downloads — $1.99
        </a>
      </div>
    </div>
  </section>

  <!-- ─── HERO ─────────────────────────────────────────── -->
  <section class="hero">
    <div class="hero-inner">
      <span class="hero-eyebrow">Online · Free for token-holders</span>
      <h1 class="hero-title">Save anything you can <span class="grad">stream</span>.</h1>
      <p class="hero-sub">YouTube, Spotify, Apple Music, SoundCloud and more. Paste a link, get the file — right here, or grab the desktop app for unlimited downloads.</p>

      <!-- Downloader card -->
      <div id="downloader" class="downloader">
        <div class="paused-banner" id="paused-banner">
          <h2>Free Service Paused</h2>
          <p>The free web service is no longer available. Buy a token below to use the online tool, or get the desktop app for unlimited downloads.</p>
          <a class="btn-get-app" href="/desktop/buy">Get the Desktop App</a>
        </div>

        <div class="url-row">
          <input id="url" type="text" placeholder="Paste a YouTube, Spotify, Apple Music or SoundCloud URL" autocomplete="off" spellcheck="false" />
          <button id="btnInsertToken" class="btn-primary btn-token" onclick="onInsertToken()">
            <svg width="16" height="16" viewBox="0 0 24 24" fill="none" aria-hidden="true"><path d="M7 11V8a5 5 0 0110 0v3M5 11h14v9H5v-9z" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"/></svg>
            Insert Token
          </button>
          <button id="btnDownload" class="btn-primary" onclick="start()" style="display:none;">
            <svg width="16" height="16" viewBox="0 0 24 24" fill="none" aria-hidden="true"><path d="M12 4v12m0 0l-4-4m4 4l4-4M4 20h16" stroke="#fff" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"/></svg>
            Download
          </button>
        </div>
        <div class="type-row">
          <select id="type">
            <option value="video">Video (MP4)</option>
            <option value="audio">Audio (MP3)</option>
            <option value="soundcloud">SoundCloud</option>
            <option value="spotify">Spotify</option>
            <option value="apple_music">Apple Music</option>
          </select>
        </div>
        <div id="scOptions">
          <label>Format:
            <select id="scQuality">
              <option value="m4a">m4a (Best, default)</option>
              <option value="mp3">mp3 (Compatible)</option>
            </select>
          </label>
          <label><input type="checkbox" id="scPlaylist" checked> Download playlists/sets</label>
        </div>
        <div id="spNote" class="note-pill">Spotify tracks are matched to YouTube and downloaded as MP3.</div>
        <div id="amNote" class="note-pill">Apple Music songs and albums are matched to YouTube and downloaded as MP3. Playlists are not supported.</div>

        <div class="token-area">
          <div id="token-input-row">
            <input id="token-field" type="text" placeholder="Paste your access token" autocomplete="off" spellcheck="false"
              onkeydown="if(event.key==='Enter')unlockWithToken()" />
            <button id="token-submit-btn" onclick="unlockWithToken()">Unlock</button>
          </div>
          <div id="token-error"></div>
          <div id="token-unlocked">
            <svg width="18" height="18" viewBox="0 0 24 24" fill="none" aria-hidden="true"><circle cx="12" cy="12" r="10" fill="rgba(72,199,142,0.15)"/><path d="M8 12l3 3 5-6" stroke="#48c78e" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"/></svg>
            <span class="lab">Access token active</span>
            <span id="token-remaining"></span>
            <button onclick="clearToken()">Remove</button>
          </div>
        </div>

        <!-- status / progress -->
        <div id="statusBlock" class="status-block">
          <div class="status-row">
            <span id="statusPill">idle</span>
            <span id="queuePos"></span>
            <button onclick="cancel()" id="cancelBtn" class="btn-cancel" style="display:none;">Cancel</button>
          </div>
          <div id="progressWrap">
            <div id="progressTrack"><div id="progressBar"></div><div id="progressLabel"></div></div>
            <small id="progressText"></small>
          </div>
          <div id="phase" class="phase-label">Idle…</div>
          <div id="phaseNote" class="phase-note"></div>
          <pre id="log"></pre>
          <div id="meta"></div>
        </div>
      </div>

      <!-- Token purchase options under the URL box -->
      <div class="token-buy-wrap">
        <div class="token-buy-label">Buy a token to use it online</div>
        <div class="token-buy-grid">
          <a class="token-buy" href="https://joshuaisaiah.art/payment/access" target="_blank" rel="noopener noreferrer">
            <div class="price">$1</div>
            <div class="qty">3 downloads</div>
            <div class="sub">Delivered instantly via email. Try it once, no account needed.</div>
            <div class="arrow">Buy 3-pack →</div>
          </a>
          <a class="token-buy alt" href="https://joshuaisaiah.art/payment/access" target="_blank" rel="noopener noreferrer">
            <span class="tag">Best value</span>
            <div class="price">$5</div>
            <div class="qty">10 downloads</div>
            <div class="sub">Save 33% vs the 3-pack. Same instant delivery.</div>
            <div class="arrow">Buy 10-pack →</div>
          </a>
        </div>
      </div>
    </div>
  </section>

  <!-- download-complete modal -->
  <div id="dlModal">
    <div class="modal-inner">
      <svg width="48" height="48" viewBox="0 0 24 24" fill="none" style="margin-bottom:12px;">
        <circle cx="12" cy="12" r="10" fill="rgba(72,199,142,0.15)"/>
        <path d="M8 12l3 3 5-6" stroke="#48c78e" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"/>
      </svg>
      <div id="dlModalTitle" style="font-size:15px; font-weight:600; color:#f0eef0; margin-bottom:6px;"></div>
      <div id="dlModalSub" style="font-size:12px; color:#777; margin-bottom:20px;"></div>
      <div style="display:flex; gap:10px; justify-content:center;">
        <a id="dlModalBtn" href="#" style="display:inline-flex; align-items:center; gap:6px; padding:10px 28px; background:#db52a6; color:#fff; font-size:14px; font-weight:600; border-radius:8px; text-decoration:none;">
          <svg width="16" height="16" viewBox="0 0 24 24" fill="none"><path d="M12 4v12m0 0l-4-4m4 4l4-4M4 18h16" stroke="#fff" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"/></svg>
          Download
        </a>
        <button onclick="closeDlModal()" style="padding:10px 20px; background:transparent; border:1px solid #333; color:#999; font-size:13px; border-radius:8px; cursor:pointer;">Close</button>
      </div>
    </div>
  </div>

  <footer class="site-footer">
    <a href="/terms">Terms of Service</a>
    <span class="sep">·</span>
    <a href="/privacy">Privacy Policy</a>
    <span class="sep">·</span>
    <a href="mailto:digitalsov2026@gmail.com?subject=+downloads%20Bug%20Report">Bug Report</a>
    <span class="sep">·</span>
    <a href="https://joshuaisaiah.art/payment/tip/573083b1f69f451c903db55d1a22ef2b" target="_blank" rel="noopener noreferrer">Tip Jar</a>
  </footer>

<script>
let currentJob = null;
let _tokenUnlocked = false;

function showStatusBlock() {
  document.getElementById('statusBlock').classList.add('active');
}
function hideStatusBlock() {
  document.getElementById('statusBlock').classList.remove('active');
}

function onInsertToken() {
  const row = document.getElementById('token-input-row');
  row.classList.add('open');
  const f = document.getElementById('token-field');
  f.focus();
  // small pulse to draw attention
  f.style.boxShadow = '0 0 0 3px rgba(219,82,166,0.18)';
  setTimeout(() => { f.style.boxShadow = ''; }, 600);
}

function setPrimaryToDownload() {
  document.getElementById('btnInsertToken').style.display = 'none';
  document.getElementById('btnDownload').style.display = 'inline-flex';
}
function setPrimaryToInsertToken() {
  document.getElementById('btnInsertToken').style.display = 'inline-flex';
  document.getElementById('btnDownload').style.display = 'none';
}

async function validateStoredToken() {
  const token = localStorage.getItem('access_token');
  if (!token) return false;
  try {
    const r = await fetch('/token-unlock', {
      method: 'POST',
      headers: {'Content-Type': 'application/json'},
      body: JSON.stringify({token})
    });
    const d = await r.json();
    if (d.valid) {
      _tokenUnlocked = true;
      showTokenUnlocked(d.remaining);
      return true;
    } else {
      localStorage.removeItem('access_token');
      return false;
    }
  } catch (e) { return false; }
}

function showTokenUnlocked(remaining) {
  document.getElementById('token-input-row').classList.remove('open');
  document.getElementById('token-error').style.display = 'none';
  const row = document.getElementById('token-unlocked');
  row.style.display = 'flex';
  if (remaining !== undefined) {
    document.getElementById('token-remaining').textContent = `(${remaining} download${remaining !== 1 ? 's' : ''} remaining)`;
  }
  setPrimaryToDownload();
}

function clearToken() {
  localStorage.removeItem('access_token');
  _tokenUnlocked = false;
  document.getElementById('token-unlocked').style.display = 'none';
  setPrimaryToInsertToken();
  checkPaused();
}

async function unlockWithToken() {
  const token = document.getElementById('token-field').value.trim();
  const errEl = document.getElementById('token-error');
  const btn = document.getElementById('token-submit-btn');
  if (!token) return;
  errEl.style.display = 'none';
  btn.textContent = 'Checking…';
  btn.disabled = true;
  try {
    const r = await fetch('/token-unlock', {
      method: 'POST',
      headers: {'Content-Type': 'application/json'},
      body: JSON.stringify({token})
    });
    const d = await r.json();
    if (d.valid) {
      localStorage.setItem('access_token', token);
      _tokenUnlocked = true;
      showTokenUnlocked(d.remaining);
      document.getElementById('paused-banner').style.display = 'none';
      document.getElementById('url').disabled = false;
    } else {
      errEl.textContent = d.reason === 'exhausted'
        ? 'This token has no downloads remaining.'
        : 'Token not recognised. Please check and try again.';
      errEl.style.display = 'block';
    }
  } catch (e) {
    errEl.textContent = 'Could not validate token. Please try again.';
    errEl.style.display = 'block';
  } finally {
    btn.textContent = 'Unlock';
    btn.disabled = false;
  }
}

async function checkPaused() {
  try {
    const r = await fetch('/service-status');
    const d = await r.json();
    const banner = document.getElementById('paused-banner');
    if (d.paused && !_tokenUnlocked) {
      banner.style.display = 'block';
      document.getElementById('url').disabled = true;
      document.getElementById('btnDownload').disabled = true;
      document.getElementById('btnInsertToken').disabled = false;
    } else {
      banner.style.display = 'none';
      document.getElementById('url').disabled = false;
      document.getElementById('btnDownload').disabled = false;
      document.getElementById('btnInsertToken').disabled = false;
    }
  } catch (e) {}
}

validateStoredToken().then(() => checkPaused());

function escHtml(s) {
  return String(s == null ? '' : s)
    .replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;')
    .replace(/"/g,'&quot;').replace(/'/g,'&#39;');
}

function syncScOptions() {
  const t = document.getElementById('type').value;
  document.getElementById('scOptions').style.display = t === 'soundcloud' ? 'flex' : 'none';
  document.getElementById('spNote').style.display = t === 'spotify' ? 'block' : 'none';
  document.getElementById('amNote').style.display = t === 'apple_music' ? 'block' : 'none';
}
document.getElementById('type').addEventListener('change', syncScOptions);
syncScOptions();

function renderPhase(phase, note, tail) {
  const phEl = document.getElementById('phase');
  const noteEl = document.getElementById('phaseNote');
  const logEl = document.getElementById('log');
  phEl.textContent = phase || '';
  noteEl.textContent = note || '';
  noteEl.className = 'phase-note' + ((phase && /fail|error|timed out|lost/i.test(phase)) ? ' err' : '');
  if (tail && tail.length) {
    logEl.textContent = tail;
    logEl.classList.add('visible');
  } else {
    logEl.textContent = '';
    logEl.classList.remove('visible');
  }
}

function lastMeaningfulLines(log, n) {
  if (!log) return '';
  const lines = log.split('\n').map(s => s.trimEnd()).filter(s => s.length > 0);
  return lines.slice(-n).join('\n');
}

async function start() {
  const url = document.getElementById('url').value.trim();
  if (!url) return;
  showStatusBlock();
  if (url.includes('open.spotify.com') || url.includes('spotify.com/')) {
    document.getElementById('type').value = 'spotify';
    syncScOptions();
  }
  if (url.includes('music.apple.com/')) {
    document.getElementById('type').value = 'apple_music';
    syncScOptions();
  }
  const type = document.getElementById('type').value;
  const scQuality = document.getElementById('scQuality').value;
  const scPlaylist = document.getElementById('scPlaylist').checked;
  renderPhase('Starting…', '', '');
  document.getElementById('meta').textContent = '';
  setStatus('queued');
  let res;
  try {
    res = await fetch('/start', {
      method: 'POST',
      headers: {'Content-Type':'application/json'},
      body: JSON.stringify({
        url, type,
        sc_quality: scQuality, sc_playlist: scPlaylist,
        token: localStorage.getItem('access_token') || undefined
      })
    });
  } catch (e) {
    renderPhase('Could not reach server', '', 'Check your internet connection and try again.');
    setStatus('error');
    return;
  }
  if (!res.ok) {
    const err = await res.json().catch(() => ({}));
    if (err.paused) {
      checkPaused();
      renderPhase('Service paused', '', 'The downloader is paused for maintenance. Purchase or enter an access token to continue.');
      setStatus('error');
      return;
    }
    renderPhase('Couldn’t start download', '', err.error || ('Server returned HTTP ' + res.status));
    setStatus('error');
    return;
  }
  const data = await res.json();
  if (data.token_remaining !== undefined) {
    showTokenUnlocked(data.token_remaining);
    if (data.token_remaining <= 0) {
      localStorage.removeItem('access_token');
      _tokenUnlocked = false;
    }
  }
  currentJob = data.job_id;
  _pollFailCount = 0;
  document.getElementById('cancelBtn').style.display = 'inline-block';
  poll();
}

let _pollFailCount = 0;

async function poll() {
  if (!currentJob) return;
  const jobAtRequest = currentJob;
  let data;
  try {
    const res = await fetch('/status/' + currentJob);
    if (!res.ok) throw new Error('HTTP ' + res.status);
    data = await res.json();
    _pollFailCount = 0;
  } catch (e) {
    _pollFailCount++;
    if (jobAtRequest !== currentJob) return;
    if (_pollFailCount >= 5) {
      renderPhase('Lost connection', '', 'We couldn’t reach the server after several tries. Refresh the page to check the job.');
      setStatus('error');
      return;
    }
    renderPhase('Reconnecting…', 'Attempt ' + _pollFailCount + '/5', '');
    const backoff = Math.min(5000, 500 * Math.pow(2, _pollFailCount));
    setTimeout(poll, backoff);
    return;
  }
  const phase = data.phase || (data.status === 'queued' ? 'Queued' : (data.status === 'running' ? 'Working…' : (data.status || '')));
  const note = data.phase_note || '';
  const errMsg = (data.status === 'error') ? (data.error_message || '') : '';
  const rawTail = lastMeaningfulLines(data.log || '', 3);
  renderPhase(phase, note || errMsg, rawTail);
  setStatus(data.status);
  updateProgress(data.status, data.log || '', data);
  if ((data.type === 'spotify' || data.type === 'apple_music') && data.total_items > 0) {
    const done = data.current_index || 0;
    const tot = data.total_items;
    const n = (data.output_paths || []).length;
    let meta = done + '/' + tot + ' tracks';
    if (data.status === 'done' && n > 0) {
      meta += ' — <a href="/download/' + currentJob + '" target="_blank">Download ZIP</a>';
    }
    meta += ' | <a href="/job-log/' + currentJob + '?tail=200" target="_blank">View log</a>';
    document.getElementById('meta').innerHTML = meta;
  } else if (data.output_paths && data.output_paths.length > 1) {
    const n = data.output_paths.length;
    document.getElementById('meta').innerHTML =
      n + ' files — <a href="/download/' + currentJob + '" target="_blank">Download ZIP</a>'
      + ' | <a href="/job-log/' + currentJob + '?tail=200" target="_blank">View full log</a>';
  } else if (data.file || data.output_path) {
    const name = data.file || data.output_path.split('/').pop();
    document.getElementById('meta').innerHTML =
      'File: <a href="/download/' + currentJob + '" target="_blank">' + escHtml(name) + '</a>'
      + ' | <a href="/job-log/' + currentJob + '?tail=200" target="_blank">View full log</a>';
  }
  if (data.status === 'done') {
    document.getElementById('cancelBtn').style.display = 'none';
    showDlModal(data);
    setTimeout(resetUI, 1500);
    return;
  }
  if (data.status === 'error' || data.status === 'cancelled') {
    document.getElementById('cancelBtn').style.display = 'none';
    return;
  }
  setTimeout(poll, 700);
}

function extractPercent(log) {
  const lines = log.split('\n');
  for (let i = lines.length - 1; i >= 0; i--) {
    const m = lines[i].match(/\[download\]\s+([\d.]+)%/);
    if (m) return parseFloat(m[1]);
  }
  return null;
}

function updateProgress(status, log, data) {
  data = data || {};
  const wrap = document.getElementById('progressWrap');
  const bar = document.getElementById('progressBar');
  const text = document.getElementById('progressText');
  const label = document.getElementById('progressLabel');
  if (status === 'queued') {
    wrap.style.display = 'block';
    bar.className = 'indeterminate';
    bar.style.width = '';
    label.textContent = '';
    const pos = data.queue_position != null ? data.queue_position + 1 : null;
    const qLen = data.queue_length || 0;
    let qText = 'Waiting in queue…';
    if (pos != null) qText = 'Queue position: ' + pos + ' of ' + qLen;
    if (data.active_count > 0) qText += ' · ' + data.active_count + ' downloading now';
    text.textContent = qText;
  } else if (status === 'running') {
    wrap.style.display = 'block';
    if (data && (data.type === 'spotify' || data.type === 'apple_music') && data.total_items > 0) {
      const pct = data.progress_pct || 0;
      const cur = (data.current_index || 0) + 1;
      const tot = data.total_items;
      bar.className = '';
      bar.style.width = pct + '%';
      label.textContent = pct > 8 ? Math.round(pct) + '%' : '';
      text.textContent = cur + ' / ' + tot + ' tracks';
    } else {
      const pct = extractPercent(log);
      if (pct !== null) {
        bar.className = '';
        bar.style.width = pct + '%';
        label.textContent = pct > 8 ? pct.toFixed(1) + '%' : '';
        text.textContent = pct.toFixed(1) + '% downloaded';
      } else {
        bar.className = 'indeterminate';
        bar.style.width = '';
        label.textContent = '';
        text.textContent = 'Processing…';
      }
    }
  } else if (status === 'done') {
    wrap.style.display = 'block';
    bar.className = '';
    bar.style.width = '100%';
    label.textContent = '100%';
    bar.style.boxShadow = '0 0 16px rgba(72,199,142,0.4)';
    bar.style.background = 'linear-gradient(90deg, #48c78e, #3ab882)';
    text.textContent = 'Complete';
  } else {
    wrap.style.display = 'none';
    bar.className = '';
    bar.style.width = '0%';
    bar.style.boxShadow = '';
    bar.style.background = '';
    label.textContent = '';
    text.textContent = '';
  }
}

function showDlModal(data) {
  const modal = document.getElementById('dlModal');
  const title = document.getElementById('dlModalTitle');
  const sub = document.getElementById('dlModalSub');
  const btn = document.getElementById('dlModalBtn');
  const multi = data.output_paths && data.output_paths.length > 1;
  if (multi) {
    const paths = data.output_paths;
    const stem = (paths[0].split('/').pop() || '').replace(/\.[^.]+$/, '').trim();
    title.textContent = stem + (paths.length > 1 ? ' + ' + (paths.length - 1) + ' more' : '');
    sub.textContent = paths.length + ' files — zipped together';
    btn.textContent = ' Download ZIP';
    btn.href = '/download/' + currentJob;
  } else {
    const name = data.file || (data.output_path ? data.output_path.split('/').pop() : 'file');
    title.textContent = name;
    sub.textContent = (data.type || 'video').toUpperCase();
    btn.innerHTML = '<svg width="16" height="16" viewBox="0 0 24 24" fill="none"><path d="M12 4v12m0 0l-4-4m4 4l4-4M4 18h16" stroke="#fff" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"/></svg> Download';
    btn.href = '/download/' + currentJob;
  }
  modal.style.display = 'flex';
}

function closeDlModal() {
  document.getElementById('dlModal').style.display = 'none';
}
document.getElementById('dlModal').addEventListener('click', function(e) {
  if (e.target === this) closeDlModal();
});

function resetUI() {
  currentJob = null;
  _pollFailCount = 0;
  document.getElementById('url').value = '';
  renderPhase('Idle…', '', '');
  document.getElementById('meta').innerHTML = '';
  document.getElementById('progressWrap').style.display = 'none';
  const rBar = document.getElementById('progressBar');
  rBar.style.width = '0%';
  rBar.style.boxShadow = '';
  rBar.style.background = '';
  rBar.className = '';
  document.getElementById('progressLabel').textContent = '';
  document.getElementById('progressText').textContent = '';
  setStatus('idle');
  hideStatusBlock();
}

function setStatus(status) {
  const pill = document.getElementById('statusPill');
  const pos = document.getElementById('queuePos');
  pill.textContent = status || 'idle';
  const colors = {
    queued:    ['rgba(191,155,58,0.15)',  '#bf9b3a'],
    running:   ['rgba(219,82,166,0.15)',  '#db52a6'],
    done:      ['rgba(72,199,142,0.15)',  '#48c78e'],
    error:     ['rgba(255,107,107,0.15)', '#ff6b6b'],
    cancelled: ['#252323',               '#555'],
  };
  const [bg, color] = colors[status] || ['#252323', '#555'];
  pill.style.background = bg;
  pill.style.color = color;
  pos.textContent = '';
}

async function cancel() {
  if (!currentJob) return;
  await fetch('/cancel', {
    method: 'POST',
    headers: {'Content-Type':'application/json'},
    body: JSON.stringify({job_id: currentJob})
  });
  poll();
}
</script>
</body>
</html>
"""

_LEGAL_PAGE_TEMPLATE = """<!doctype html>
<html lang="en">
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width, initial-scale=1">
  <meta name="theme-color" content="#1a1818">
  <title>{{ page_title }} · +downloads</title>
  <meta name="description" content="{{ meta_desc }}">
  <link rel="canonical" href="{{ canonical }}">
  <meta name="robots" content="index, follow">
  <meta property="og:type" content="website">
  <meta property="og:site_name" content="+downloads">
  <meta property="og:title" content="{{ page_title }} · +downloads">
  <meta property="og:description" content="{{ meta_desc }}">
  <meta property="og:url" content="{{ canonical }}">
  <meta property="og:image" content="https://digitaldownloads.space/static/og-image.png">
  <link rel="icon" type="image/svg+xml" href="/static/favicon.svg">
  <link rel="icon" type="image/png" sizes="64x64" href="/static/favicon.png">
  <link rel="apple-touch-icon" href="/static/icon-192.png">
  <style>
    *, *::before, *::after { box-sizing: border-box; margin: 0; padding: 0; }
    body {
      font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', sans-serif;
      background: #1a1818; color: #f0eef0; min-height: 100vh; line-height: 1.6;
    }
    .header {
      background: #242222; border-bottom: 1px solid #2e2c2c;
      padding: 0 32px; height: 62px; display: flex; align-items: center; gap: 12px;
    }
    .logo { font-size: 24px; font-weight: 800; color: #db52a6; letter-spacing: -0.5px; text-decoration: none; white-space: nowrap; }
    .logo .lo-prefix { color: #f0eef0; font-weight: 700; margin-right: 4px; }
    .header a.logo:hover { color: #c9479a; }
    .header a.logo:hover .lo-prefix { color: #f0eef0; }
    .legal-wrap { max-width: 720px; margin: 0 auto; padding: 36px 24px 80px; }
    h1 { font-size: 28px; font-weight: 800; color: #f0eef0; margin-bottom: 6px; letter-spacing: -0.4px; }
    .updated { font-size: 12px; color: #666; margin-bottom: 28px;
      text-transform: uppercase; letter-spacing: 0.08em; }
    h2 { font-size: 17px; font-weight: 700; color: #db52a6; margin: 28px 0 8px; }
    h3 { font-size: 14px; font-weight: 700; color: #bf9b3a; margin: 18px 0 4px; }
    p, li { font-size: 14px; color: #c8c4c8; margin-bottom: 12px; }
    ul, ol { padding-left: 22px; margin-bottom: 12px; }
    li { margin-bottom: 6px; }
    strong { color: #f0eef0; font-weight: 600; }
    a { color: #bf9b3a; }
    a:hover { color: #d6b34d; }
    .callout {
      background: rgba(191,155,58,0.07); border: 1px solid rgba(191,155,58,0.18);
      border-radius: 10px; padding: 14px 16px; font-size: 13px; color: #c8c4c8;
      margin: 16px 0;
    }
    .nav-back {
      display: inline-block; margin-top: 36px; padding: 10px 18px;
      background: #242222; border: 1px solid #353333; border-radius: 10px;
      color: #f0eef0; text-decoration: none; font-size: 13px;
    }
    .nav-back:hover { background: #2e2c2c; color: #db52a6; border-color: #db52a6; }
    footer { text-align: center; padding: 22px 16px; font-size: 12px; color: #555; }
    footer a { color: #555; text-decoration: underline; text-underline-offset: 3px; }
    footer .sep { margin: 0 8px; color: #3a3838; }
  </style>
</head>
<body>
  <div class="header">
    <a class="logo" href="/"><span class="lo-prefix">digital</span>+downloads</a>
  </div>
  <main class="legal-wrap">
    <h1>{{ page_title }}</h1>
    <div class="updated">Last updated: {{ updated }}</div>
    {{ body|safe }}
    <a class="nav-back" href="/">← Back to +downloads</a>
  </main>
  <footer>
    <a href="/terms">Terms of Service</a>
    <span class="sep">·</span>
    <a href="/privacy">Privacy Policy</a>
  </footer>
</body>
</html>
"""

_PRIVACY_BODY = """
<p><strong>+downloads</strong> is operated as a personal-use service at <a href="https://digitaldownloads.space">digitaldownloads.space</a>, with a companion iOS app distributed through the Apple App Store. This Privacy Policy describes what information we receive, how it is used, and the choices you have.</p>

<div class="callout">We do not sell, rent, or share personal information with advertisers or data brokers. We do not run user-tracking analytics. Aside from anonymous server logs and standard ad serving, the service is designed to operate without collecting identifying data.</div>

<h2>1. Information We Collect</h2>

<h3>Web service (digitaldownloads.space)</h3>
<ul>
  <li><strong>Submitted URLs.</strong> When you paste a URL to download, that URL is processed by the server and the corresponding media is fetched on your behalf. URLs are kept in a short-lived job queue and recent-history list while a download is active.</li>
  <li><strong>Generated files.</strong> Audio and video files produced by your downloads are stored temporarily on the server so you can retrieve them, then automatically removed.</li>
  <li><strong>Server logs.</strong> Standard web server logs may record IP address, user agent, request path, and timestamps for security and abuse prevention. Logs are rotated and not used to build user profiles.</li>
  <li><strong>Cookies.</strong> The site uses functional cookies only (e.g., to remember UI preferences and to maintain your session for the duration of an active download). No cross-site tracking cookies are set by us.</li>
  <li><strong>Advertising.</strong> The site loads Google AdSense scripts. Google may use cookies and similar technologies to serve ads; please refer to <a href="https://policies.google.com/technologies/ads">Google's Ads policy</a> for details. You can opt out of personalized ads at <a href="https://www.google.com/settings/ads">google.com/settings/ads</a>.</li>
  <li><strong>Free-trial email.</strong> To download the free trial of the desktop app, you provide an email address. That address is added to our mailing list, operated by <a href="https://kit.com">Kit</a> (formerly ConvertKit), so we can let you know when a new version of the app is available. Providing an email is required only for the free trial; you can unsubscribe at any time using the link in any email we send.</li>
</ul>

<h3>iOS app (+downloads)</h3>
<ul>
  <li><strong>Local files.</strong> The app reads audio and video files from a folder you explicitly choose with the iOS file picker. The files themselves are never transmitted to us.</li>
  <li><strong>iCloud Drive (optional).</strong> If the folder you choose lives in iCloud Drive, files that are not yet downloaded to your device are fetched on demand by Apple's iCloud Drive service when you press play. iCloud Drive operates directly between your device and Apple under Apple's privacy policy.</li>
  <li><strong>Apple Music library.</strong> If you choose to connect Apple Music, the app uses Apple's MusicKit framework to read your library and play tracks. A copy of your library's track metadata is kept locally on your device so the app opens quickly; that cache is deleted when you tap Disconnect in Settings.</li>
  <li><strong>Favorites and playlists.</strong> Your favorites and playlists are stored in your private iCloud Key-Value Store so they sync between your own devices. We never see this data.</li>
  <li><strong>Diagnostics.</strong> Crash and performance diagnostics are produced on-device by Apple's MetricKit framework and saved locally for your reference. Nothing is uploaded to us.</li>
  <li><strong>Wi-Fi desktop sync (optional).</strong> The app can pair with the +downloads desktop application over your local network using Apple's Bonjour service discovery and a PIN-gated HTTP connection. Audio and video files transfer directly between your device and your desktop computer; the data does not pass through any server we operate.</li>
  <li><strong>Track identification (optional, AcoustID).</strong> When you tap "Identify this track" in the tag editor, an acoustic fingerprint of the audio plus its duration is sent to the public <a href="https://acoustid.org">AcoustID</a> service to look up the recording. The fingerprint is derived from the audio content; the audio file itself is not uploaded. AcoustID may log requests; see their site for details.</li>
  <li><strong>Lyrics (optional, LRClib).</strong> When you open the lyrics view for a track, the artist name, track title, album, and duration are sent to the public <a href="https://lrclib.net">LRClib</a> service to look up lyrics. LRClib may log requests; see their site for details.</li>
  <li><strong>pCloud (optional).</strong> If you connect a pCloud account in Settings, the app authenticates with pCloud via their hosted sign-in page (OAuth), reads a list of audio files from your pCloud account, and streams playback directly from pCloud when you press play. Your access token is stored only in the iOS Keychain on your device. Your interactions with pCloud are governed by pCloud's own privacy policy.</li>
  <li><strong>Instagram Stories share.</strong> When you tap Share to Instagram Stories from the player, the app generates a share-card image on your device and places it on the iOS system pasteboard for the Instagram app to read. Nothing is sent to a server by us; the handoff happens locally between your device and the Instagram app.</li>
</ul>

<h2>2. How Information Is Used</h2>
<ul>
  <li>To process the downloads and playback you request.</li>
  <li>To deliver completed files back to your browser or device.</li>
  <li>To detect, prevent, and respond to abuse, fraud, or technical issues.</li>
  <li>To comply with legal obligations.</li>
</ul>

<h2>3. Information We Do Not Collect</h2>
<p>We do not collect names, phone numbers, payment information, contacts, microphone input, or camera input. The only personal information we collect is the email address you voluntarily submit to download the free trial, as described above. The iOS app does not include a third-party analytics SDK and does not implement Apple's App Tracking Transparency tracking.</p>

<h2>4. Sharing</h2>
<p>We do not sell or rent personal information. Limited disclosure may occur in the following cases:</p>
<ul>
  <li><strong>Service providers.</strong> Hosting and DNS providers process traffic on our behalf to operate the website.</li>
  <li><strong>Advertising partners.</strong> Google AdSense receives request information necessary to serve ads, as described above.</li>
  <li><strong>Email provider.</strong> Email addresses submitted for the free-trial signup are stored and processed by Kit (ConvertKit), our mailing-list provider, under their own privacy policy.</li>
  <li><strong>Apple platform services.</strong> The iOS app uses MusicKit, MetricKit, iCloud Drive, and iCloud Key-Value Store, which exchange data directly between your device and Apple under Apple's privacy policy.</li>
  <li><strong>Optional third-party services.</strong> When you use the iOS app's optional features for track identification (AcoustID), lyrics (LRClib), or pCloud playback, your device communicates directly with those services. We do not relay or intermediate that traffic, and each provider's own privacy policy applies to the data they receive.</li>
  <li><strong>Legal compliance.</strong> Information may be disclosed when required by law, subpoena, or to protect rights, safety, or property.</li>
</ul>

<h2>5. Retention</h2>
<ul>
  <li>Downloaded files: removed automatically after a short delivery window, typically within hours.</li>
  <li>Job queue entries: removed when the job completes or is cancelled.</li>
  <li>Server logs: retained for a short period for abuse prevention, then rotated.</li>
  <li>iCloud-synced favorites/playlists: retained on your iCloud account until you remove them.</li>
</ul>

<h2>6. Children's Privacy</h2>
<p>+downloads is not directed to children under 13, and we do not knowingly collect personal information from children. If you believe a child has provided information through the service, please contact us so we can remove it.</p>

<h2>7. International Use</h2>
<p>The service may be accessed from outside the country where it is hosted. By using it you understand that any limited information described above may be processed in jurisdictions with different data protection laws.</p>

<h2>8. Your Choices</h2>
<ul>
  <li>You can stop using the service at any time.</li>
  <li>In iOS Settings, you can revoke Apple Music, location, or iCloud permissions for the app individually.</li>
  <li>You can clear locally saved diagnostic reports from inside the iOS app's Settings screen.</li>
  <li>You can opt out of personalized advertising via Google's controls noted above.</li>
  <li>You can unsubscribe from the free-trial mailing list at any time using the link in any email we send.</li>
</ul>

<h2>9. Security</h2>
<p>We use commercially reasonable technical and organizational measures to protect the service. However, no system is perfectly secure, and we cannot guarantee absolute security of any data transmitted over the internet.</p>

<h2>10. Changes</h2>
<p>This Privacy Policy may be updated from time to time. Material changes will be reflected in the "Last updated" date above. Continued use of the service after a change indicates acceptance of the revised policy.</p>

<h2>11. Contact</h2>
<p>Questions or requests related to this Privacy Policy can be sent through the contact form on <a href="https://digitaldownloads.space">digitaldownloads.space</a>.</p>
"""

_TERMS_BODY = """
<p>These Terms of Service ("Terms") govern your access to and use of <strong>+downloads</strong> at <a href="https://digitaldownloads.space">digitaldownloads.space</a> and the +downloads iOS application (collectively, the "Service"). By using the Service you agree to these Terms in full. If you do not agree, do not use the Service.</p>

<div class="callout">USE AT YOUR OWN RISK. The Service is provided for personal, private use only. You are responsible for ensuring that your use complies with all applicable laws.</div>

<h2>1. The Service</h2>
<p>The web service lets you submit a public media URL and receive back the corresponding audio or video file. The iOS application is a media player that plays files from a folder you choose, songs in your Apple Music library, and live internet radio streams from public directories.</p>

<h2>2. Eligibility</h2>
<p>You must be at least 13 years old, or the minimum age of digital consent in your jurisdiction, to use the Service. By using the Service you represent that you meet this requirement.</p>

<h2>3. Acceptable Use</h2>
<p>You agree not to:</p>
<ul>
  <li>Use the Service to download or distribute content you do not have the right to download or distribute, including copyrighted material without authorization.</li>
  <li>Circumvent technical protection measures or terms of any third-party platform.</li>
  <li>Use the Service to harass, defame, or harm any person.</li>
  <li>Submit automated, abusive, or excessive requests, or otherwise attempt to overload the Service.</li>
  <li>Reverse engineer, decompile, or attempt to extract source code, except to the extent expressly permitted by law.</li>
  <li>Use the Service in violation of any applicable law, regulation, or third-party terms.</li>
</ul>

<h2>4. Your Responsibility for Content</h2>
<p>You are solely responsible for the URLs you submit and any media you download, store, share, or play through the Service. Downloading copyrighted material without authorization may be illegal in your jurisdiction. The operator does not review submitted URLs and does not condone or encourage any unlawful activity.</p>

<h2>5. Third-Party Platforms and Trademarks</h2>
<p>The Service is not affiliated with, endorsed by, or sponsored by YouTube, Google, SoundCloud, Spotify, Apple, Bandcamp, radio-browser.info, or any other third-party service. All trademarks and source platforms remain the property of their respective owners. Any references to such platforms are nominative only.</p>

<h2>6. Intellectual Property</h2>
<p>The Service, including its software, design, and branding, is owned by the operator and protected by intellectual property laws. You are granted a limited, non-exclusive, non-transferable, revocable license to use the Service for personal, non-commercial purposes consistent with these Terms.</p>

<h2>7. App Store Terms (iOS)</h2>
<p>If you obtain the iOS app through the Apple App Store, you also agree to Apple's Licensed Application End User License Agreement. Apple is not a party to these Terms and is not responsible for the app or any claims relating to it. To the extent there is a conflict between these Terms and Apple's EULA, Apple's EULA will govern, but only to the extent of that conflict.</p>

<h2>8. No Warranty</h2>
<p>THE SERVICE IS PROVIDED "AS IS" AND "AS AVAILABLE" WITHOUT WARRANTIES OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING WITHOUT LIMITATION WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE, NON-INFRINGEMENT, OR UNINTERRUPTED OR ERROR-FREE OPERATION. We make no warranty regarding the accuracy, completeness, reliability, or availability of any download or playback.</p>

<h2>9. Limitation of Liability</h2>
<p>TO THE FULLEST EXTENT PERMITTED BY LAW, IN NO EVENT WILL THE OPERATOR BE LIABLE FOR ANY INDIRECT, INCIDENTAL, SPECIAL, CONSEQUENTIAL, EXEMPLARY, OR PUNITIVE DAMAGES, OR FOR ANY LOSS OF PROFITS, REVENUE, DATA, OR GOODWILL, ARISING OUT OF OR RELATING TO YOUR USE OF OR INABILITY TO USE THE SERVICE, WHETHER BASED ON CONTRACT, TORT, STRICT LIABILITY, OR ANY OTHER LEGAL THEORY, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGES. THE OPERATOR'S TOTAL LIABILITY FOR ANY CLAIM RELATING TO THE SERVICE WILL NOT EXCEED ONE HUNDRED U.S. DOLLARS (US$100).</p>

<h2>10. Indemnification</h2>
<p>You agree to indemnify, defend, and hold harmless the operator and its affiliates from any claims, damages, liabilities, costs, or expenses (including reasonable legal fees) arising out of or related to your use of the Service, your violation of these Terms, or your violation of any law or third-party right.</p>

<h2>11. Termination</h2>
<p>We may suspend or terminate your access to the Service at any time, with or without notice, for any reason, including suspected violation of these Terms. You may stop using the Service at any time. Sections that by their nature should survive termination will survive.</p>

<h2>12. Changes</h2>
<p>We may modify these Terms at any time. Material changes will be reflected in the "Last updated" date above. Continued use of the Service after a change constitutes acceptance of the revised Terms.</p>

<h2>13. Governing Law and Disputes</h2>
<p>These Terms are governed by the laws of the United States and the State of California, without regard to conflict-of-laws principles. Any dispute arising out of or relating to these Terms or the Service will be brought in the state or federal courts located in California, and you consent to the personal jurisdiction of those courts.</p>

<h2>14. Severability</h2>
<p>If any provision of these Terms is held unenforceable, the remaining provisions will remain in full force and effect, and the unenforceable provision will be modified only to the extent necessary to make it enforceable.</p>

<h2>15. Contact</h2>
<p>Questions about these Terms can be sent through the contact form on <a href="https://digitaldownloads.space">digitaldownloads.space</a>.</p>
"""

_LEGAL_LAST_UPDATED = "May 21, 2026"


_DESKTOP_REDEEM_HTML = """<!doctype html>
<html lang="en">
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width, initial-scale=1">
  <meta name="theme-color" content="#1a1818">
  <title>Your purchase &middot; +downloads</title>
  <meta name="robots" content="noindex, follow">
  <link rel="icon" type="image/svg+xml" href="/static/favicon.svg">
  <link rel="icon" type="image/png" sizes="64x64" href="/static/favicon.png">
  <link rel="apple-touch-icon" href="/static/icon-192.png">
  <style>
    *, *::before, *::after { box-sizing: border-box; margin: 0; padding: 0; }
    body {
      font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', sans-serif;
      background: #1a1818; color: #f0eef0; min-height: 100vh;
    }
    .header {
      background: #242222; border-bottom: 1px solid #2e2c2c;
      padding: 0 32px; height: 62px; display: flex; align-items: center; gap: 12px;
    }
    .logo { font-size: 24px; font-weight: 800; color: #db52a6; text-decoration: none; letter-spacing: -0.5px; white-space: nowrap; }
    .logo .lo-prefix { color: #f0eef0; font-weight: 700; margin-right: 4px; }
    .wrap { max-width: 560px; margin: 0 auto; padding: 64px 24px 80px; text-align: center; }
    .icon-badge {
      width: 64px; height: 64px; border-radius: 50%;
      display: flex; align-items: center; justify-content: center; margin: 0 auto 22px;
    }
    .icon-ok { background: rgba(72,199,142,0.12); border: 1px solid rgba(72,199,142,0.30); }
    .icon-err { background: rgba(255,107,107,0.10); border: 1px solid rgba(255,107,107,0.28); }
    h1 { font-size: 28px; font-weight: 800; letter-spacing: -0.6px; margin-bottom: 12px; }
    .sub { font-size: 15px; color: #aaa6aa; line-height: 1.65; margin-bottom: 18px; }
    .sub strong { color: #f0eef0; font-weight: 600; }
    .card {
      background: #242222; border: 1px solid #2e2c2c; border-radius: 14px;
      padding: 18px 22px; margin: 22px auto 0; max-width: 420px; text-align: left;
    }
    .feat { display: flex; align-items: center; gap: 10px; font-size: 14px; color: #c8c4c8; margin: 8px 0; }
    .feat svg { color: #48c78e; flex-shrink: 0; }
    .dl-btns { display: flex; flex-direction: column; gap: 10px; max-width: 340px; margin: 6px auto 0; }
    .dl-btn {
      display: flex; align-items: center; justify-content: center; gap: 9px;
      padding: 14px 20px; border-radius: 12px; font-size: 15px; font-weight: 700;
      text-decoration: none; background: #242222; border: 1px solid #353333; color: #f0eef0;
      transition: border-color 0.15s, transform 0.1s;
    }
    .dl-btn:hover { border-color: #db52a6; }
    .dl-btn:active { transform: scale(0.98); }
    .dl-btn.primary {
      background: linear-gradient(95deg, #db52a6 0%, #c44e9a 100%);
      border-color: transparent; color: #fff; box-shadow: 0 8px 22px rgba(219,82,166,0.26);
    }
    .dl-btn svg { flex-shrink: 0; }
    .spinner {
      width: 42px; height: 42px; margin: 0 auto 22px;
      border: 3px solid #2e2c2c; border-top-color: #db52a6; border-radius: 50%;
      animation: spin 0.8s linear infinite;
    }
    @keyframes spin { to { transform: rotate(360deg); } }
    .helper { font-size: 13px; color: #777; margin-top: 22px; line-height: 1.6; }
    .helper a { color: #bf9b3a; }
    .back {
      display: inline-block; margin-top: 30px; padding: 10px 18px;
      background: #242222; border: 1px solid #353333; border-radius: 10px;
      color: #aaa; text-decoration: none; font-size: 13px;
    }
    .back:hover { color: #db52a6; border-color: #db52a6; }
    footer { text-align: center; padding: 22px 16px; font-size: 12px; color: #555; }
    footer a { color: #888; text-decoration: none; }
    footer .sep { margin: 0 8px; color: #3a3838; }
  </style>
</head>
<body>
  <header class="header">
    <a class="logo" href="/"><span class="lo-prefix">digital</span>+downloads</a>
  </header>
  <main class="wrap">
    {% if state == 'confirmed' %}
    <div class="icon-badge icon-ok">
      <svg width="30" height="30" viewBox="0 0 24 24" fill="none"><path d="M5 12l5 5L20 7" stroke="#48c78e" stroke-width="2.5" stroke-linecap="round" stroke-linejoin="round"/></svg>
    </div>
    <h1>Purchase confirmed</h1>
    {% if builds %}
    <p class="sub">Thanks for buying <strong>+downloads for Desktop</strong>. Pick your platform to download the installer.</p>
    <div class="dl-btns">
      {% for b in builds %}
      <a class="dl-btn {% if b.os == detected_os %}primary{% endif %}" href="/desktop/redeem/download?token={{ token|urlencode }}&amp;os={{ b.os }}">
        <svg width="18" height="18" viewBox="0 0 24 24" fill="none"><path d="M12 4v12m0 0l-4-4m4 4l4-4M4 20h16" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"/></svg>
        Download for {{ b.label }}
      </a>
      {% endfor %}
    </div>
    <p class="helper">Your purchase works on every platform &mdash; bookmark this link to grab the others or re-download later. The link is also in your confirmation email.</p>
    {% else %}
    <p class="sub">Thanks for buying <strong>+downloads for Desktop</strong>. Your installer download link has been emailed to you &mdash; check your inbox (and your spam folder, just in case).</p>
    <p class="helper">Didn't get the email within a few minutes? <a href="mailto:digitalsov2026@gmail.com?subject=Desktop%20installer%20link">Contact support</a> and we'll resend your download link.</p>
    {% endif %}
    {% elif state == 'update' %}
    <div class="icon-badge icon-ok">
      <svg width="30" height="30" viewBox="0 0 24 24" fill="none"><path d="M12 4v12m0 0l-4-4m4 4l4-4M4 20h16" stroke="#48c78e" stroke-width="2.5" stroke-linecap="round" stroke-linejoin="round"/></svg>
    </div>
    <h1>Download the latest +downloads</h1>
    {% if builds %}
    <p class="sub">You're an existing customer &mdash; updates are always free. Pick your platform to grab the newest version.</p>
    <div class="dl-btns">
      {% for b in builds %}
      <a class="dl-btn {% if b.os == detected_os %}primary{% endif %}" href="/desktop/update?os={{ b.os }}">
        <svg width="18" height="18" viewBox="0 0 24 24" fill="none"><path d="M12 4v12m0 0l-4-4m4 4l4-4M4 20h16" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"/></svg>
        Download for {{ b.label }}
      </a>
      {% endfor %}
    </div>
    <p class="helper">Free updates forever &mdash; bookmark this link or watch your inbox when a new version ships.</p>
    {% else %}
    <p class="sub">No builds are available right now &mdash; please check back shortly.</p>
    {% endif %}
    {% elif state == 'pending' %}
    <div class="spinner" id="spinner"></div>
    <h1 id="pending-title">Finalizing your purchase</h1>
    <p class="sub" id="pending-sub">This only takes a few seconds &mdash; hang tight while we confirm your payment.</p>
    <p class="helper" id="pending-help"></p>
    {% else %}
    <div class="icon-badge icon-err">
      <svg width="28" height="28" viewBox="0 0 24 24" fill="none"><path d="M12 8v5m0 3.5h.01M10.3 3.86 1.82 18a2 2 0 0 0 1.71 3h16.94a2 2 0 0 0 1.71-3L13.7 3.86a2 2 0 0 0-3.4 0Z" stroke="#ff6b6b" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round"/></svg>
    </div>
    <h1>Something's not right</h1>
    <p class="sub">{{ message }}</p>
    <p class="helper">Think this is a mistake? <a href="mailto:digitalsov2026@gmail.com?subject=Desktop%20redeem%20issue">Contact support</a> with the link from your purchase email and we'll sort it out.</p>
    {% endif %}
    <a class="back" href="/">&larr; Back to digitaldownloads.space</a>
  </main>
  <footer>
    <a href="/terms">Terms of Service</a>
    <span class="sep">&middot;</span>
    <a href="/privacy">Privacy Policy</a>
  </footer>
  {% if state == 'pending' %}
  <script>
    var TOKEN = {{ token|tojson }};
    var deadline = Date.now() + 30000;
    function settle(msg) {
      var sp = document.getElementById('spinner');
      if (sp) { sp.style.display = 'none'; }
      document.getElementById('pending-title').textContent = 'Still processing';
      document.getElementById('pending-sub').textContent = msg;
    }
    function poll() {
      if (Date.now() > deadline) {
        settle('We could not confirm a download for this link yet. If you just purchased, wait a moment and refresh this page. If you have already downloaded +downloads, your purchase is still complete — email digitalsov2026@gmail.com to get the installer again.');
        return;
      }
      fetch('/desktop/redeem/status?token=' + encodeURIComponent(TOKEN))
        .then(function (r) { return r.json(); })
        .then(function (d) {
          if (d.state === 'confirmed' || d.state === 'error') { window.location.reload(); }
          else { setTimeout(poll, 1500); }
        })
        .catch(function () { setTimeout(poll, 1500); });
    }
    setTimeout(poll, 1500);
  </script>
  {% endif %}
</body>
</html>
"""


# Free-trial download page — public, token-less (same access model as
# /desktop/update). Sells the upgrade: trial framing + a prominent buy-page CTA.
_DESKTOP_TRIAL_HTML = """<!doctype html>
<html lang="en">
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width, initial-scale=1">
  <meta name="theme-color" content="#1a1818">
  <title>Free Trial &middot; +downloads for Desktop</title>
  <meta name="description" content="Try +downloads for Desktop free — a no-cost, YouTube-only edition of the media downloader for macOS, Windows and Linux. Upgrade any time for 1000+ supported sites.">
  <link rel="canonical" href="https://digitaldownloads.space/trial">
  <meta name="robots" content="index, follow, max-image-preview:large">
  <meta property="og:type" content="website">
  <meta property="og:site_name" content="+downloads">
  <meta property="og:title" content="Try +downloads for Desktop — free">
  <meta property="og:description" content="A free, YouTube-only edition of the +downloads desktop app for macOS, Windows and Linux. No payment, no card — just download and go.">
  <meta property="og:url" content="https://digitaldownloads.space/trial">
  <meta property="og:image" content="https://digitaldownloads.space/static/og-image.png">
  <meta property="og:image:width" content="1200">
  <meta property="og:image:height" content="630">
  <meta name="twitter:card" content="summary_large_image">
  <meta name="twitter:title" content="Try +downloads for Desktop — free">
  <meta name="twitter:description" content="A free, YouTube-only edition of the +downloads desktop app for macOS, Windows and Linux.">
  <meta name="twitter:image" content="https://digitaldownloads.space/static/og-image.png">
  <link rel="icon" type="image/svg+xml" href="/static/favicon.svg">
  <link rel="icon" type="image/png" sizes="64x64" href="/static/favicon.png">
  <link rel="apple-touch-icon" href="/static/icon-192.png">
  <style>
    *, *::before, *::after { box-sizing: border-box; margin: 0; padding: 0; }
    body {
      font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', sans-serif;
      background: #1a1818; color: #f0eef0; min-height: 100vh;
    }
    .header {
      background: #242222; border-bottom: 1px solid #2e2c2c;
      padding: 0 32px; height: 62px; display: flex; align-items: center; gap: 12px;
    }
    .logo { font-size: 24px; font-weight: 800; color: #db52a6; text-decoration: none; letter-spacing: -0.5px; white-space: nowrap; }
    .logo .lo-prefix { color: #f0eef0; font-weight: 700; margin-right: 4px; }
    .wrap { max-width: 560px; margin: 0 auto; padding: 56px 24px 80px; text-align: center; }
    .badge {
      display: inline-block; font-size: 12px; font-weight: 700; letter-spacing: 0.6px;
      text-transform: uppercase; color: #bf9b3a; background: rgba(191,155,58,0.12);
      border: 1px solid rgba(191,155,58,0.32); border-radius: 999px; padding: 5px 14px; margin-bottom: 18px;
    }
    h1 { font-size: 28px; font-weight: 800; letter-spacing: -0.6px; margin-bottom: 12px; }
    .sub { font-size: 15px; color: #aaa6aa; line-height: 1.65; margin-bottom: 6px; }
    .sub strong { color: #f0eef0; font-weight: 600; }
    .dl-btns { display: flex; flex-direction: column; gap: 10px; max-width: 340px; margin: 24px auto 0; }
    .dl-btn {
      display: flex; align-items: center; justify-content: center; gap: 9px;
      padding: 14px 20px; border-radius: 12px; font-size: 15px; font-weight: 700;
      text-decoration: none; background: #242222; border: 1px solid #353333; color: #f0eef0;
      transition: border-color 0.15s, transform 0.1s;
    }
    .dl-btn:hover { border-color: #db52a6; }
    .dl-btn:active { transform: scale(0.98); }
    .dl-btn.primary {
      background: linear-gradient(95deg, #db52a6 0%, #c44e9a 100%);
      border-color: transparent; color: #fff; box-shadow: 0 8px 22px rgba(219,82,166,0.26);
    }
    .dl-btn svg { flex-shrink: 0; }
    .gate { display: flex; flex-direction: column; gap: 10px; max-width: 340px; margin: 24px auto 0; }
    .gate input {
      width: 100%; padding: 13px 16px; border-radius: 11px; font-size: 15px;
      background: #1f1d1d; border: 1px solid #353333; color: #f0eef0; outline: none;
      transition: border-color 0.15s;
    }
    .gate input::placeholder { color: #6c686c; }
    .gate input:focus { border-color: #db52a6; }
    .gate button {
      padding: 14px 20px; border-radius: 12px; font-size: 15px; font-weight: 800;
      border: none; cursor: pointer; color: #fff;
      background: linear-gradient(95deg, #db52a6 0%, #c44e9a 100%);
      box-shadow: 0 8px 22px rgba(219,82,166,0.26); transition: transform 0.1s;
    }
    .gate button:active { transform: scale(0.98); }
    .gate-note { font-size: 12px; color: #777; line-height: 1.5; }
    .gate-err { font-size: 13px; color: #ff6b6b; font-weight: 600; }
    .limits {
      background: #242222; border: 1px solid #2e2c2c; border-radius: 14px;
      padding: 16px 20px; margin: 26px auto 0; max-width: 420px; text-align: left;
    }
    .limits .lt { font-size: 13px; font-weight: 700; color: #f0eef0; margin-bottom: 8px; }
    .limit { display: flex; align-items: flex-start; gap: 9px; font-size: 13.5px; color: #c8c4c8; margin: 6px 0; line-height: 1.5; }
    .limit svg { flex-shrink: 0; margin-top: 2px; }
    .limit strong { color: #f0eef0; font-weight: 600; }
    .upgrade {
      background: linear-gradient(160deg, #2a2026 0%, #242222 100%);
      border: 1px solid #3a2e36; border-radius: 16px;
      padding: 24px 22px; margin: 30px auto 0; max-width: 440px;
    }
    .upgrade h2 { font-size: 19px; font-weight: 800; letter-spacing: -0.3px; margin-bottom: 8px; }
    .upgrade p { font-size: 14px; color: #aaa6aa; line-height: 1.6; margin-bottom: 16px; }
    .btn-buy {
      display: inline-flex; align-items: center; justify-content: center; gap: 8px;
      padding: 14px 26px; border-radius: 12px; font-size: 15px; font-weight: 800;
      text-decoration: none; background: linear-gradient(95deg, #db52a6 0%, #c44e9a 100%);
      color: #fff; box-shadow: 0 8px 22px rgba(219,82,166,0.30);
      transition: transform 0.1s;
    }
    .btn-buy:active { transform: scale(0.98); }
    .upgrade .price { font-size: 13px; color: #777; margin-top: 12px; }
    .helper { font-size: 13px; color: #777; margin-top: 24px; line-height: 1.6; }
    .helper a { color: #bf9b3a; }
    .back {
      display: inline-block; margin-top: 28px; padding: 10px 18px;
      background: #242222; border: 1px solid #353333; border-radius: 10px;
      color: #aaa; text-decoration: none; font-size: 13px;
    }
    .back:hover { color: #db52a6; border-color: #db52a6; }
    footer { text-align: center; padding: 22px 16px; font-size: 12px; color: #555; }
    footer a { color: #888; text-decoration: none; }
    footer .sep { margin: 0 8px; color: #3a3838; }
  </style>
</head>
<body>
  <header class="header">
    <a class="logo" href="/"><span class="lo-prefix">digital</span>+downloads</a>
  </header>
  <main class="wrap">
    <span class="badge">Free Trial</span>
    <h1>Try +downloads for Desktop &mdash; free</h1>
    {% if unlocked and builds %}
    <p class="sub">You're in &mdash; the free trial downloads from <strong>YouTube</strong> at no cost. Pick your platform to get started.</p>
    <div class="dl-btns">
      {% for b in builds %}
      <a class="dl-btn {% if b.os == detected_os %}primary{% endif %}" href="/trial?os={{ b.os }}">
        <svg width="18" height="18" viewBox="0 0 24 24" fill="none"><path d="M12 4v12m0 0l-4-4m4 4l4-4M4 20h16" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"/></svg>
        Download for {{ b.label }}
      </a>
      {% endfor %}
    </div>
    {% elif unlocked and not builds %}
    <p class="sub">The free trial installer isn't available right now &mdash; please check back shortly.</p>
    {% else %}
    <p class="sub">A free, <strong>YouTube-only</strong> taste of the desktop app. Enter your email and we'll unlock the download.</p>
    <form class="gate" method="post" action="/trial/unlock">
      <input type="email" name="email" placeholder="you@example.com" required autocomplete="email" autofocus>
      <button type="submit">Get the free trial &rarr;</button>
      {% if error %}<div class="gate-err">Please enter a valid email address.</div>{% endif %}
      <div class="gate-note">We'll email you when a new version ships. No spam &mdash; unsubscribe anytime.</div>
    </form>
    {% endif %}
    <div class="limits">
      <div class="lt">Free trial &mdash; what to expect</div>
      <div class="limit">
        <svg width="16" height="16" viewBox="0 0 24 24" fill="none"><path d="M5 12l5 5L20 7" stroke="#48c78e" stroke-width="2.5" stroke-linecap="round" stroke-linejoin="round"/></svg>
        <span>Download video &amp; audio from <strong>YouTube</strong></span>
      </div>
      <div class="limit">
        <svg width="16" height="16" viewBox="0 0 24 24" fill="none"><path d="M18 6 6 18M6 6l12 12" stroke="#ff6b6b" stroke-width="2.2" stroke-linecap="round"/></svg>
        <span>YouTube only &mdash; SoundCloud, Spotify &amp; Apple Music need the full app</span>
      </div>
      <div class="limit">
        <svg width="16" height="16" viewBox="0 0 24 24" fill="none"><circle cx="12" cy="12" r="9" stroke="#bf9b3a" stroke-width="2"/><path d="M12 7.5v5l3.5 2" stroke="#bf9b3a" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"/></svg>
        <span>Works for <strong>7 days</strong> from first launch</span>
      </div>
      <div class="limit">
        <svg width="16" height="16" viewBox="0 0 24 24" fill="none"><path d="M5 19V11M12 19V5M19 19v-7" stroke="#bf9b3a" stroke-width="2.2" stroke-linecap="round"/></svg>
        <span>Up to <strong>5 downloads per day</strong></span>
      </div>
    </div>
    <div class="upgrade">
      <h2>Want every supported site?</h2>
      <p>The full +downloads desktop app unlocks every supported site &mdash; no 7-day limit, no daily cap, plus auto-tagging, organizing &amp; iOS sync. One payment, free updates forever.</p>
      <a class="btn-buy" href="/?ref=trial-page">Get the full app &rarr;</a>
      <div class="price">One-time purchase &middot; works on macOS, Windows &amp; Linux</div>
    </div>
    <p class="helper">The trial is free to download and share. Bookmark this page to grab it again later.</p>
    <a class="back" href="/">&larr; Back to digitaldownloads.space</a>
  </main>
  <footer>
    <a href="/terms">Terms of Service</a>
    <span class="sep">&middot;</span>
    <a href="/privacy">Privacy Policy</a>
  </footer>
</body>
</html>
"""


def is_valid_url(url: str) -> bool:
    if not url:
        return False
    try:
        parsed = urlparse(url)
    except Exception:
        return False
    if parsed.scheme not in {"http", "https"} or not parsed.netloc:
        return False
    hostname = (parsed.hostname or "").strip("[]")
    if not hostname:
        return False
    try:
        infos = socket.getaddrinfo(hostname, None)
        for _, _, _, _, sockaddr in infos:
            ip = ipaddress.ip_address(sockaddr[0])
            if not ip.is_global:
                return False
    except (socket.gaierror, ValueError, OSError):
        return False
    return True

def detect_soundcloud(url: str) -> bool:
    try:
        host = urlparse(url).hostname or ""
    except Exception:
        return False
    host = host.lower()
    return "soundcloud.com" in host or "on.soundcloud.com" in host

def prune_jobs():
    """Remove finished jobs older than TTL to keep memory bounded."""
    cutoff = datetime.utcnow() - timedelta(seconds=JOB_TTL_SECONDS)
    with jobs_lock:
        old_ids = [
            jid for jid, meta in jobs.items()
            if meta.get("finished_at") and meta["finished_at"] < cutoff
        ]
        for jid in old_ids:
            jobs.pop(jid, None)

def queue_position(job_id: str):
    with queue_cv:
        for idx, jid in enumerate(job_queue):
            if jid == job_id:
                return idx
    return None

def dispatcher():
    while True:
        with queue_cv:
            while not job_queue:
                queue_cv.wait()
            job_id = None
        # wait for available slot
        if not job_sema.acquire(blocking=False):
            time.sleep(0.1)
            continue
        with queue_cv:
            if job_queue:
                job_id = job_queue.popleft()
            else:
                job_sema.release()
                continue
        threading.Thread(target=run_job, args=(job_id,), daemon=True).start()

def cleanup_worker():
    while True:
        time.sleep(30)

        # File TTL: delete downloaded files first so job metadata still points at them
        if FILE_TTL_DAYS > 0:
            file_cutoff = datetime.utcnow() - timedelta(days=FILE_TTL_DAYS)
            with jobs_lock:
                snapshot = list(jobs.values())
            for job in snapshot:
                finished = job.get("finished_at")
                if finished and finished < file_cutoff:
                    for p in (job.get("output_paths") or [job.get("output_path")]):
                        if p and os.path.exists(p):
                            try:
                                os.remove(p)
                            except OSError:
                                pass

            # Orphan sweep: any file in DOWNLOAD_DIR older than TTL, regardless of jobs state
            ttl_seconds = FILE_TTL_DAYS * 86400
            now_ts = time.time()
            for root, _dirs, files in os.walk(DOWNLOAD_DIR):
                for name in files:
                    fp = os.path.join(root, name)
                    try:
                        if now_ts - os.path.getmtime(fp) > ttl_seconds:
                            os.remove(fp)
                    except OSError:
                        pass

        # Job TTL: prune expired job records
        cutoff = datetime.utcnow() - timedelta(seconds=JOB_TTL_SECONDS)
        removed = False
        with jobs_lock:
            expired = [jid for jid, meta in jobs.items() if meta.get("finished_at") and meta["finished_at"] < cutoff]
            for jid in expired:
                jobs.pop(jid, None)
                removed = True
        for jid in expired:
            try:
                job_log_path(jid).unlink(missing_ok=True)
            except Exception:
                pass
        if removed:
            save_jobs()

        # Sweep stale IP tracking entries (#14)
        with _ip_lock:
            stale_ips = [ip for ip, ts in _ip_recent.items() if not ts or ts[-1] < time.time() - 3600]
            for ip in stale_ips:
                _ip_recent.pop(ip, None)
                _ip_jobs_active.pop(ip, None)
        with _global_rate_lock:
            stale_gr = [ip for ip, ts in _global_rate.items() if not ts or ts[-1] < time.time() - 120]
            for ip in stale_gr:
                _global_rate.pop(ip, None)

        # Clean empty subdirectories (#15)
        if FILE_TTL_DAYS > 0:
            for root, dirs, files in os.walk(DOWNLOAD_DIR, topdown=False):
                if root != DOWNLOAD_DIR and not os.listdir(root):
                    try:
                        os.rmdir(root)
                    except OSError:
                        pass

        # Drop page-view rows past the retention window
        _prune_pageviews()

def load_history() -> list:
    if not HISTORY_PATH.exists():
        return []
    try:
        with HISTORY_PATH.open("r", encoding="utf-8") as f:
            return json.load(f)
    except Exception:
        return []

def append_history(record: dict):
    with history_lock:
        items = load_history()
        items.append(record)
        # cap to last 500
        items = items[-500:]
        try:
            with HISTORY_PATH.open("w", encoding="utf-8") as f:
                json.dump(items, f, indent=2)
        except Exception:
            pass

def load_jobs() -> dict:
    if not JOBS_PATH.exists():
        return {}
    try:
        with JOBS_PATH.open("r", encoding="utf-8") as f:
            return json.load(f)
    except Exception:
        return {}

def save_jobs():
    with jobs_lock:
        meta = {jid: {k: v for k, v in data.items() if k != "log"} for jid, data in jobs.items()}
    try:
        with JOBS_PATH.open("w", encoding="utf-8") as f:
            json.dump(meta, f, indent=2, default=str)
    except Exception:
        pass

def job_log_path(job_id: str) -> Path:
    return LOG_DIR / f"{job_id}.log"


# ---- Phase detection & error classification ----
# Each yt-dlp stdout line is mapped to a short high-level phase shown to users.
_PHASE_PATTERNS = [
    (re.compile(r'Downloading webpage|Downloading API JSON|Downloading tweet', re.I), "Resolving URL"),
    (re.compile(r'Downloading (?:JSON metadata|m3u8 information|MPD manifest|player|signature|playlist)', re.I), "Fetching metadata"),
    (re.compile(r'\[download\] Destination:'), "Downloading"),
    (re.compile(r'\[download\]\s+\d'), "Downloading"),
    (re.compile(r'\[Merger\]|Merging formats'), "Merging video + audio"),
    (re.compile(r'\[ExtractAudio\]|\[ffmpeg\] Destination'), "Converting audio"),
    (re.compile(r'\[EmbedThumbnail\]|\[Metadata\]|\[ThumbnailsConvertor\]'), "Finalizing"),
]

def _detect_phase(line: str):
    for pat, phase in _PHASE_PATTERNS:
        if pat.search(line):
            return phase
    return None


# Friendly messages for common yt-dlp failures. Scanned against the job log tail.
_ERROR_SIGNALS = [
    ("No video could be found in this tweet", "This post doesn't contain a video."),
    ("Tweet is unavailable", "This tweet is unavailable (deleted, private, or requires login)."),
    ("NSFW tweet requires authentication", "This tweet is marked sensitive and requires a logged-in account."),
    ("Sign in to confirm your age", "This video is age-restricted and requires login."),
    ("Private video", "This video is private."),
    ("This video is only available for registered users", "This video requires a logged-in account."),
    ("Video unavailable", "Video is unavailable or region-locked."),
    ("This video has been removed", "This video has been removed."),
    ("Premieres in", "This video hasn't been released yet."),
    ("Unsupported URL", "This link isn't supported — try a direct video URL."),
    ("HTTP Error 404", "Page not found — double-check the URL."),
    ("HTTP Error 403", "Access was denied by the source server."),
    ("HTTP Error 429", "The source rate-limited us. Try again in a minute."),
    ("Requested format is not available", "No downloadable format is available for this content."),
    ("Unable to extract", "Couldn't extract media from this page."),
    ("The provided YouTube account cookies are no longer valid", "Our login cookies expired. The owner has been alerted — please try again shortly."),
]

def _classify_error(log_text: str) -> str:
    """Scan recent log lines for a known error signal and return a friendly message."""
    if not log_text:
        return ""
    tail = log_text.splitlines()[-60:]
    for line in reversed(tail):
        for needle, message in _ERROR_SIGNALS:
            if needle.lower() in line.lower():
                return message
    # Fall back to the last ERROR line, trimmed.
    for line in reversed(tail):
        stripped = line.strip()
        if stripped.startswith("ERROR:"):
            return stripped[:240]
    return ""


# Stall detection: warn at 60s of no stdout, kill at 300s.
STALL_WARN_SECONDS = int(os.environ.get("YT_UI_STALL_WARN", "60"))
STALL_KILL_SECONDS = int(os.environ.get("YT_UI_STALL_KILL", "300"))

def _stall_monitor(job_id: str):
    """Background thread: mark stalled jobs and kill ones that go fully silent."""
    while True:
        time.sleep(10)
        with jobs_lock:
            job = jobs.get(job_id)
            if not job or job.get("status") != "running":
                return
            last = job.get("last_output_at") or job.get("started_at") or time.time()
            proc = job.get("process")
        silence = time.time() - last
        if silence >= STALL_KILL_SECONDS and proc is not None:
            try:
                proc.kill()
            except Exception:
                pass
            with jobs_lock:
                j = jobs.get(job_id)
                if j:
                    j["stall_killed"] = True
                    j["phase_note"] = f"Timed out — no output for {int(silence)}s."
            return
        elif silence >= STALL_WARN_SECONDS:
            with jobs_lock:
                j = jobs.get(job_id)
                if j and j.get("status") == "running":
                    j["phase_note"] = f"Still working — no output for {int(silence)}s…"

def _parse_dt(val):
    if isinstance(val, datetime):
        return val
    if isinstance(val, str):
        try:
            return datetime.fromisoformat(val)
        except Exception:
            pass
    return None

def _sanitize_metadata(s: str) -> str:
    cleaned = re.sub(r'[\x00\n\r\t]', ' ', str(s or ''))
    cleaned = re.sub(r'["`$\\]', "'", cleaned)
    return cleaned

def detect_spotify(url: str) -> bool:
    try:
        host = urlparse(url).hostname or ""
    except Exception:
        return False
    return "spotify.com" in host.lower()


def detect_apple_music(url: str) -> bool:
    try:
        host = urlparse(url).hostname or ""
    except Exception:
        return False
    return "music.apple.com" in host.lower()


def _apple_music_fetch_metadata(url: str) -> dict:
    """Fetch Apple Music track/album metadata via iTunes Lookup API. No credentials needed."""
    try:
        parsed = urlparse(url)
    except Exception:
        raise ValueError("That doesn't look like a valid Apple Music URL.")

    parts = [p for p in parsed.path.strip("/").split("/") if p]
    if len(parts) < 3:
        raise ValueError(
            "Couldn't parse that Apple Music URL. "
            "Make sure you copied the full link to a song or album."
        )
    country = parts[0]
    kind = parts[1]
    entity_id = parts[-1]
    track_id = parse_qs(parsed.query).get("i", [None])[0]

    if not re.fullmatch(r"[a-z]{2}", country.lower()):
        raise ValueError(
            "That Apple Music URL is missing a country code — "
            "copy the link directly from the Apple Music app or website."
        )
    if kind == "playlist":
        raise ValueError(
            "Apple Music playlists aren't supported. "
            "Paste a single song or album URL instead."
        )
    if kind not in {"album", "song"}:
        raise ValueError(
            f"Unsupported Apple Music link type: '{kind}'. "
            "Only song and album URLs work."
        )
    if not re.fullmatch(r"\d+", entity_id):
        raise ValueError(
            "Couldn't find the song/album ID in that URL. "
            "Make sure you copied the full link."
        )

    def itunes_lookup(lookup_id, entity=None):
        params = f"id={lookup_id}&country={country}"
        if entity:
            params += f"&entity={entity}"
        last_exc = None
        for attempt in range(2):  # single retry for transient failures
            try:
                req = urllib.request.Request(
                    f"https://itunes.apple.com/lookup?{params}",
                    headers={"User-Agent": "Mozilla/5.0"},
                )
                with urllib.request.urlopen(req, timeout=10) as resp:
                    return json.loads(resp.read())
            except Exception as e:
                last_exc = e
                time.sleep(0.5)
        raise ValueError(f"Apple Music lookup service is unavailable right now ({last_exc}).")

    # Single track: song URL or album URL with ?i= parameter
    if kind == "song" or track_id:
        tid = track_id or entity_id
        data = itunes_lookup(tid)
        if not data.get("results"):
            raise ValueError("Track not found in the iTunes catalog for this country.")
        t = data["results"][0]
        title = t.get("trackName", "")
        artist = t.get("artistName", "")
        if not title:
            raise ValueError("iTunes returned no track info for this link.")
        return {"kind": "track", "name": title, "tracks": [{"title": title, "artist": artist}]}

    # Album
    data = itunes_lookup(entity_id, entity="song")
    if not data.get("results"):
        raise ValueError("Album not found in the iTunes catalog for this country.")
    collection = data["results"][0]
    album_name = collection.get("collectionName", "album")
    raw = [r for r in data["results"][1:] if r.get("wrapperType") == "track" and r.get("trackName")]
    raw.sort(key=lambda x: x.get("trackNumber", 0))
    tracks = [{"title": r["trackName"], "artist": r.get("artistName", "")} for r in raw]
    if not tracks:
        raise ValueError("iTunes returned no tracks for that album.")
    return {"kind": "album", "name": album_name, "tracks": tracks}


_EMBED_HEADERS = {
    "User-Agent": "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/122.0.0.0 Safari/537.36",
    "Accept": "text/html,application/xhtml+xml",
    "Accept-Language": "en-US,en;q=0.9",
}

def _spotify_embed_fetch(kind: str, entity_id: str) -> dict:
    """Fetch __NEXT_DATA__ from Spotify embed page. No auth required."""
    embed_url = f"https://open.spotify.com/embed/{kind}/{entity_id}"
    req = urllib.request.Request(embed_url, headers=_EMBED_HEADERS)
    with urllib.request.urlopen(req, timeout=15) as resp:
        html = resp.read().decode("utf-8", errors="replace")
    m = re.search(r'id="__NEXT_DATA__"[^>]*>(.*?)</script>', html, re.DOTALL)
    if not m:
        raise ValueError(f"Could not parse Spotify embed page for {kind}/{entity_id}")
    return json.loads(m.group(1))


def _spotify_fetch_metadata(url: str) -> dict:
    """Fetch Spotify track/album metadata via embed page. No API credentials needed.
    Playlists fall back to the official API if credentials are configured."""
    try:
        parts = [p for p in urlparse(url).path.strip("/").split("/") if p]
        kind = parts[0]
        entity_id = parts[1].split("?")[0]
    except (IndexError, Exception):
        raise ValueError(f"Unrecognized Spotify URL: {url}")
    if kind not in {"track", "playlist", "album"}:
        raise ValueError(f"Unsupported Spotify entity type: {kind}")

    if kind == "track":
        data = _spotify_embed_fetch("track", entity_id)
        entity = data["props"]["pageProps"]["state"]["data"]["entity"]
        title = entity.get("name", "")
        artist = ", ".join(a["name"] for a in entity.get("artists", []) if a.get("name"))
        return {"kind": "track", "name": title, "tracks": [{"title": title, "artist": artist}]}

    elif kind == "album":
        data = _spotify_embed_fetch("album", entity_id)
        entity = data["props"]["pageProps"]["state"]["data"]["entity"]
        album_name = entity.get("name", "album")
        tracks = []
        for t in entity.get("trackList", []):
            title = t.get("title", "")
            artist = t.get("subtitle", "")
            if title:
                tracks.append({"title": title, "artist": artist})
        return {"kind": "album", "name": album_name, "tracks": tracks}

    else:  # playlist — embed doesn't include track list; use official API if creds available
        if not SPOTIFY_CLIENT_ID or not SPOTIFY_CLIENT_SECRET:
            raise ValueError(
                "Playlist metadata requires SPOTIFY_CLIENT_ID and SPOTIFY_CLIENT_SECRET env vars. "
                "Track and album URLs work without credentials."
            )
        creds = base64.b64encode(
            f"{SPOTIFY_CLIENT_ID}:{SPOTIFY_CLIENT_SECRET}".encode()
        ).decode()
        token_req = urllib.request.Request(
            "https://accounts.spotify.com/api/token",
            data=b"grant_type=client_credentials",
            headers={"Authorization": f"Basic {creds}", "Content-Type": "application/x-www-form-urlencoded"},
            method="POST",
        )
        with urllib.request.urlopen(token_req, timeout=10) as resp:
            token = json.loads(resp.read())["access_token"]

        def api_get(path_or_url):
            full = path_or_url if path_or_url.startswith("http") else f"https://api.spotify.com/v1/{path_or_url.lstrip('/')}"
            r = urllib.request.Request(full, headers={"Authorization": f"Bearer {token}"})
            with urllib.request.urlopen(r, timeout=10) as resp:
                return json.loads(resp.read())

        data = api_get(f"playlists/{entity_id}")
        tdata = data.get("tracks", {})
        tracks = []
        items, next_url = tdata.get("items", []), tdata.get("next")
        while True:
            for item in items:
                t = item.get("track") if item else None
                if t and t.get("name"):
                    artist = ", ".join(a["name"] for a in t.get("artists", []))
                    tracks.append({"title": t["name"], "artist": artist})
            if not next_url:
                break
            page = api_get(next_url)
            items, next_url = page.get("items", []), page.get("next")
        return {"kind": "playlist", "name": data.get("name", "playlist"), "tracks": tracks}


def restore_jobs_from_disk():
    data = load_jobs()
    now = datetime.utcnow()
    with jobs_lock:
        for jid, meta in data.items():
            # Re-hydrate datetime fields that were serialized as strings
            for field in ("created_at", "finished_at"):
                meta[field] = _parse_dt(meta.get(field))
            status = meta.get("status", "unknown")
            if status == "running":
                meta["status"] = "error"
                meta["phase"] = "Failed"
                meta["error_message"] = "The server restarted while this job was running. Please try again."
                meta["log"] = "Server restarted during download"
                meta["finished_at"] = now
            elif status == "queued":
                meta["status"] = "cancelled"
                meta["phase"] = "Cancelled"
                meta["log"] = "Cancelled after restart"
                meta["finished_at"] = now
            meta.setdefault("log", "")
            meta.setdefault("output_paths", [])
            meta.setdefault("sc_quality", "m4a")
            meta.setdefault("sc_playlist", True)
            meta.setdefault("spotify_info", None)
            meta.setdefault("apple_music_info", None)
            meta.setdefault("current_index", 0)
            meta.setdefault("total_items", 0)
            meta.setdefault("progress_pct", 0)
            meta.setdefault("failures", [])
            jobs[jid] = meta
    save_jobs()

def run_job(job_id: str):
    with jobs_lock:
        job = jobs.get(job_id)
        if not job or job.get("status") != "queued":
            if job:
                _release_ip(job.get("client_ip"))
            job_sema.release()
            return
        job["status"] = "running"
        job_type = job.get("type", "video")
        url = job.get("url")
        sc_quality = job.get("sc_quality", "m4a")
        sc_playlist = job.get("sc_playlist", True)
        spotify_info = job.get("spotify_info") or {}
        apple_music_info = job.get("apple_music_info") or {}
        client_ip_val = job.get("client_ip")
        save_jobs()
    if not url:
        with jobs_lock:
            jobs[job_id]["status"] = "error"
            jobs[job_id]["log"] = "Missing URL"
        _release_ip(client_ip_val)
        job_sema.release()
        return

    cookies_args = []
    if COOKIES_PATH and os.path.exists(COOKIES_PATH) and os.path.getsize(COOKIES_PATH) > 10:
        cookies_args = ["--cookies", COOKIES_PATH]
    proxy_args = ["--proxy", PROXY_URL] if PROXY_URL else []

    if job_type == "audio":
        cmd = [
            YT_DLP_BIN,
            "--ffmpeg-location", FFMPEG_BIN,
            "--js-runtimes", "node",
            "-f", "bestaudio",
            "--extract-audio",
            "--audio-format", "mp3",
            "--print", "after_move:filepath",
            "-o", os.path.join(DOWNLOAD_DIR, "%(title).120s [%(id)s].%(ext)s"),
            url
        ]
    elif job_type == "soundcloud":
        if sc_playlist:
            output_template = os.path.join(
                SOUNDCLOUD_DIR,
                "%(playlist_title|)s",
                "%(uploader).80s - %(title).120s [%(id)s].%(ext)s"
            )
        else:
            output_template = os.path.join(
                SOUNDCLOUD_DIR,
                "%(uploader).80s - %(title).120s [%(id)s].%(ext)s"
            )
        cmd = [
            YT_DLP_BIN,
            "--ffmpeg-location", FFMPEG_BIN,
            "-f", "bestaudio",
            "--add-metadata",
            "--embed-metadata",
            "--embed-thumbnail",
            "--write-thumbnail",
            "--convert-thumbnails", "jpg",
            "--extract-audio",
            "--audio-format", sc_quality,
            "--audio-quality", "0",
            "--print", "after_move:filepath",
            "-o", output_template,
            url
        ]
        if not sc_playlist:
            cmd.insert(-1, "--no-playlist")
    else:
        cmd = [
            YT_DLP_BIN,
            "--ffmpeg-location", FFMPEG_BIN,
            "--js-runtimes", "node",
            "-f", "bv*+ba/b",
            "--merge-output-format", "mp4",
            "--print", "after_move:filepath",
            "-o", os.path.join(DOWNLOAD_DIR, "%(title).120s [%(id)s].%(ext)s"),
            url
        ]

    output_paths = []   # all non-thumbnail absolute paths printed by yt-dlp
    _IMAGE_EXTS = {".jpg", ".jpeg", ".png", ".webp", ".gif"}
    output_path = None  # backward-compat: last detected path
    last_file = None
    log_file = None
    cmd = cmd[:1] + cookies_args + proxy_args + cmd[1:]

    try:
        log_file = job_log_path(job_id).open("a", encoding="utf-8")

        if job_type == "spotify":
            tracks = spotify_info.get("tracks", [])
            kind = spotify_info.get("kind", "track")
            coll_name = spotify_info.get("name", "spotify_download")
            safe_coll = re.sub(r'[\\/:*?"<>|]', "_", coll_name)[:80].strip()
            out_dir = SPOTIFY_TRACKS_DIR if kind == "track" else os.path.join(SPOTIFY_DIR, safe_coll or "playlist")
            os.makedirs(out_dir, exist_ok=True)
            total = len(tracks)
            failures_list = []
            with jobs_lock:
                jobs[job_id]["started_at"] = time.time()
                jobs[job_id]["last_output_at"] = time.time()
                jobs[job_id]["phase"] = "Preparing Spotify tracks"
            threading.Thread(target=_stall_monitor, args=(job_id,), daemon=True).start()

            for idx, track_meta in enumerate(tracks):
                with jobs_lock:
                    if jobs[job_id].get("cancel_requested"):
                        break
                title = track_meta.get("title", "")
                artist = track_meta.get("artist", "")
                # Update per-track progress
                pct = int((idx / total) * 100) if total > 0 else 0
                with jobs_lock:
                    jobs[job_id]["current_index"] = idx
                    jobs[job_id]["progress_pct"] = pct
                    jobs[job_id]["last_output_at"] = time.time()
                    jobs[job_id]["phase"] = f"Downloading track {idx+1}/{total}"
                    jobs[job_id].pop("phase_note", None)
                    old_log = jobs[job_id].get("log", "")
                    jobs[job_id]["log"] = "\n".join(
                        (old_log + f"\n[{idx+1}/{total}] {artist} - {title}").splitlines()[-120:]
                    )
                # Build yt-dlp ytsearch command
                safe_title  = _sanitize_metadata(title)
                safe_artist = _sanitize_metadata(artist)
                safe_base = re.sub(r'[\\/:*?"<>|]', "_", f"{artist} - {title}")[:160]
                out_template = os.path.join(out_dir, safe_base + ".%(ext)s")
                ppa = f'ffmpeg:-metadata title="{safe_title}" -metadata artist="{safe_artist}"'
                track_cmd = [
                    YT_DLP_BIN,
                    "--ffmpeg-location", FFMPEG_BIN,
                    "--js-runtimes", "node",
                    f"ytsearch1:{artist} - {title}",
                    "--extract-audio", "--audio-format", "mp3", "--audio-quality", "0",
                    "--add-metadata",
                    "--postprocessor-args", ppa,
                    "--no-playlist",
                    "--print", "after_move:filepath",
                    "-o", out_template,
                ]
                track_cmd = track_cmd[:1] + cookies_args + proxy_args + track_cmd[1:]
                try:
                    p = subprocess.Popen(track_cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
                    with jobs_lock:
                        jobs[job_id]["process"] = p
                    track_out = None
                    for raw_line in p.stdout:
                        line = raw_line.rstrip()
                        try:
                            log_file.write(line + "\n")
                        except Exception:
                            pass
                        if os.path.isabs(line) and os.path.splitext(line)[1].lower() not in _IMAGE_EXTS:
                            track_out = line
                            output_path = line
                            output_paths.append(line)
                        with jobs_lock:
                            jobs[job_id]["log"] = "\n".join(
                                (jobs[job_id].get("log", "") + "\n" + line).splitlines()[-120:]
                            )
                            jobs[job_id]["last_output_at"] = time.time()
                            jobs[job_id].pop("phase_note", None)
                            jobs[job_id]["output_paths"] = list(output_paths)
                        with jobs_lock:
                            if jobs[job_id].get("cancel_requested"):
                                try: p.terminate()
                                except Exception: pass
                                break
                    track_code = p.wait()
                    with jobs_lock:
                        if jobs[job_id].get("cancel_requested"):
                            break
                    if track_code != 0 or not track_out:
                        failures_list.append(f"{artist} - {title}")
                        with jobs_lock:
                            jobs[job_id]["failures"] = list(failures_list)
                except Exception as ex:
                    failures_list.append(f"{artist} - {title}")
                    with jobs_lock:
                        jobs[job_id]["failures"] = list(failures_list)
                        jobs[job_id]["log"] += f"\nError: {ex}"

            # Final status
            with jobs_lock:
                cancelled = jobs[job_id].get("cancel_requested")
            if cancelled:
                with jobs_lock:
                    jobs[job_id]["status"] = "cancelled"
                    jobs[job_id]["phase"] = "Cancelled"
                    jobs[job_id].pop("phase_note", None)
                    jobs[job_id]["log"] += "\nCancelled by user"
                    save_jobs()
            elif failures_list and len(failures_list) == total:
                with jobs_lock:
                    jobs[job_id]["status"] = "error"
                    jobs[job_id]["phase"] = "Failed"
                    jobs[job_id].pop("phase_note", None)
                    jobs[job_id]["error_message"] = f"All {total} tracks failed to match on YouTube."
                    jobs[job_id]["log"] += f"\nAll {total} tracks failed."
                    save_jobs()
            else:
                with jobs_lock:
                    jobs[job_id]["status"] = "done"
                    jobs[job_id]["phase"] = "Complete"
                    jobs[job_id].pop("phase_note", None)
                    jobs[job_id]["progress_pct"] = 100
                    jobs[job_id]["current_index"] = total
                    jobs[job_id]["output_paths"] = list(output_paths)
                    if output_path:
                        jobs[job_id]["output_path"] = output_path
                        jobs[job_id]["file"] = os.path.basename(output_path)
                    if failures_list:
                        jobs[job_id]["log"] += f"\n{len(failures_list)} failed: {', '.join(failures_list[:5])}"
                    save_jobs()
            return  # finally block still fires
        # --- END SPOTIFY BRANCH ---

        if job_type == "apple_music":
            tracks = apple_music_info.get("tracks", [])
            kind = apple_music_info.get("kind", "track")
            coll_name = apple_music_info.get("name", "apple_music_download")
            safe_coll = re.sub(r'[\\/:*?"<>|]', "_", coll_name)[:80].strip()
            out_dir = APPLE_MUSIC_TRACKS_DIR if kind == "track" else os.path.join(APPLE_MUSIC_DIR, safe_coll or "album")
            os.makedirs(out_dir, exist_ok=True)
            total = len(tracks)
            failures_list = []
            with jobs_lock:
                jobs[job_id]["started_at"] = time.time()
                jobs[job_id]["last_output_at"] = time.time()
                jobs[job_id]["phase"] = "Preparing Apple Music tracks"
            threading.Thread(target=_stall_monitor, args=(job_id,), daemon=True).start()

            for idx, track_meta in enumerate(tracks):
                with jobs_lock:
                    if jobs[job_id].get("cancel_requested"):
                        break
                title = track_meta.get("title", "")
                artist = track_meta.get("artist", "")
                # Update per-track progress
                pct = int((idx / total) * 100) if total > 0 else 0
                with jobs_lock:
                    jobs[job_id]["current_index"] = idx
                    jobs[job_id]["progress_pct"] = pct
                    jobs[job_id]["last_output_at"] = time.time()
                    jobs[job_id]["phase"] = f"Downloading track {idx+1}/{total}"
                    jobs[job_id].pop("phase_note", None)
                    old_log = jobs[job_id].get("log", "")
                    jobs[job_id]["log"] = "\n".join(
                        (old_log + f"\n[{idx+1}/{total}] {artist} - {title}").splitlines()[-120:]
                    )
                # Build yt-dlp ytsearch command
                safe_title  = _sanitize_metadata(title)
                safe_artist = _sanitize_metadata(artist)
                safe_base = re.sub(r'[\\/:*?"<>|]', "_", f"{artist} - {title}")[:160]
                out_template = os.path.join(out_dir, safe_base + ".%(ext)s")
                ppa = f'ffmpeg:-metadata title="{safe_title}" -metadata artist="{safe_artist}"'
                track_cmd = [
                    YT_DLP_BIN,
                    "--ffmpeg-location", FFMPEG_BIN,
                    "--js-runtimes", "node",
                    f"ytsearch1:{artist} - {title}",
                    "--extract-audio", "--audio-format", "mp3", "--audio-quality", "0",
                    "--add-metadata",
                    "--postprocessor-args", ppa,
                    "--no-playlist",
                    "--print", "after_move:filepath",
                    "-o", out_template,
                ]
                track_cmd = track_cmd[:1] + cookies_args + proxy_args + track_cmd[1:]
                try:
                    p = subprocess.Popen(track_cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
                    with jobs_lock:
                        jobs[job_id]["process"] = p
                    track_out = None
                    for raw_line in p.stdout:
                        line = raw_line.rstrip()
                        try:
                            log_file.write(line + "\n")
                        except Exception:
                            pass
                        if os.path.isabs(line) and os.path.splitext(line)[1].lower() not in _IMAGE_EXTS:
                            track_out = line
                            output_path = line
                            output_paths.append(line)
                        with jobs_lock:
                            jobs[job_id]["log"] = "\n".join(
                                (jobs[job_id].get("log", "") + "\n" + line).splitlines()[-120:]
                            )
                            jobs[job_id]["last_output_at"] = time.time()
                            jobs[job_id].pop("phase_note", None)
                            jobs[job_id]["output_paths"] = list(output_paths)
                        with jobs_lock:
                            if jobs[job_id].get("cancel_requested"):
                                try: p.terminate()
                                except Exception: pass
                                break
                    track_code = p.wait()
                    with jobs_lock:
                        if jobs[job_id].get("cancel_requested"):
                            break
                    if track_code != 0 or not track_out:
                        failures_list.append(f"{artist} - {title}")
                        with jobs_lock:
                            jobs[job_id]["failures"] = list(failures_list)
                except Exception as ex:
                    failures_list.append(f"{artist} - {title}")
                    with jobs_lock:
                        jobs[job_id]["failures"] = list(failures_list)
                        jobs[job_id]["log"] += f"\nError: {ex}"

            # Final status
            with jobs_lock:
                cancelled = jobs[job_id].get("cancel_requested")
            if cancelled:
                with jobs_lock:
                    jobs[job_id]["status"] = "cancelled"
                    jobs[job_id]["phase"] = "Cancelled"
                    jobs[job_id].pop("phase_note", None)
                    jobs[job_id]["log"] += "\nCancelled by user"
                    save_jobs()
            elif failures_list and len(failures_list) == total:
                with jobs_lock:
                    jobs[job_id]["status"] = "error"
                    jobs[job_id]["phase"] = "Failed"
                    jobs[job_id].pop("phase_note", None)
                    jobs[job_id]["error_message"] = f"All {total} tracks failed to match on YouTube."
                    jobs[job_id]["log"] += f"\nAll {total} tracks failed."
                    save_jobs()
            else:
                with jobs_lock:
                    jobs[job_id]["status"] = "done"
                    jobs[job_id]["phase"] = "Complete"
                    jobs[job_id].pop("phase_note", None)
                    jobs[job_id]["progress_pct"] = 100
                    jobs[job_id]["current_index"] = total
                    jobs[job_id]["output_paths"] = list(output_paths)
                    if output_path:
                        jobs[job_id]["output_path"] = output_path
                        jobs[job_id]["file"] = os.path.basename(output_path)
                    if failures_list:
                        jobs[job_id]["log"] += f"\n{len(failures_list)} failed: {', '.join(failures_list[:5])}"
                    save_jobs()
            return  # finally block still fires
        # --- END APPLE MUSIC BRANCH ---

        p = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        with jobs_lock:
            jobs[job_id]["process"] = p
            jobs[job_id]["started_at"] = time.time()
            jobs[job_id]["last_output_at"] = time.time()
            jobs[job_id]["phase"] = "Resolving URL"
        threading.Thread(target=_stall_monitor, args=(job_id,), daemon=True).start()
        log_lines = []
        for raw_line in p.stdout:
            line = raw_line.rstrip()
            log_lines.append(line)
            try:
                log_file.write(line + "\n")
            except Exception:
                pass
            # Detect printed final path
            if os.path.isabs(line):
                if os.path.splitext(line)[1].lower() not in _IMAGE_EXTS:
                    output_paths.append(line)
                    output_path = line
            if "Destination:" in line and not output_path:
                last_file = line.split("Destination:", 1)[-1].strip()
            new_phase = _detect_phase(line)
            with jobs_lock:
                jobs[job_id]["log"] = "\n".join(log_lines[-120:])
                jobs[job_id]["last_output_at"] = time.time()
                jobs[job_id].pop("phase_note", None)
                if new_phase:
                    jobs[job_id]["phase"] = new_phase
                if output_path:
                    jobs[job_id]["output_path"] = output_path
                    jobs[job_id]["output_paths"] = list(output_paths)
            # stop early if cancel requested
            with jobs_lock:
                if jobs[job_id].get("cancel_requested"):
                    try:
                        p.terminate()
                    except Exception:
                        pass
        code = p.wait()
        with jobs_lock:
            cancelled = jobs[job_id].get("cancel_requested")
        if cancelled:
            with jobs_lock:
                jobs[job_id]["status"] = "cancelled"
                jobs[job_id]["phase"] = "Cancelled"
                jobs[job_id].pop("phase_note", None)
                jobs[job_id]["log"] = jobs[job_id].get("log", "") + "\nCancelled by user"
                save_jobs()
        elif code == 0:
            with jobs_lock:
                jobs[job_id]["status"] = "done"
                jobs[job_id]["phase"] = "Complete"
                jobs[job_id].pop("phase_note", None)
                jobs[job_id]["output_paths"] = list(output_paths)
                final_path = output_path or last_file
                if final_path:
                    jobs[job_id]["file"] = os.path.basename(final_path)
                    jobs[job_id]["output_path"] = final_path if os.path.isabs(final_path) else os.path.join(DOWNLOAD_DIR, final_path)
                save_jobs()
        else:
            COOKIE_EXPIRED_SIGNAL = "The provided YouTube account cookies are no longer valid"
            captured_output = "\n".join(log_lines)
            if cookies_args and COOKIE_EXPIRED_SIGNAL in captured_output:
                with jobs_lock:
                    jobs[job_id]["log"] = jobs[job_id].get("log", "") + "\n[auto-retry] Cookies expired — retrying without authentication...\n"
                    jobs[job_id]["status"] = "running"

                cmd_no_cookies = [cmd[0]] + [a for a in cmd[1:] if a not in ("--cookies", COOKIES_PATH)]

                p2 = subprocess.Popen(cmd_no_cookies, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
                with jobs_lock:
                    jobs[job_id]["process"] = p2
                    jobs[job_id]["last_output_at"] = time.time()
                log_lines = []
                for raw_line in p2.stdout:
                    line = raw_line.rstrip()
                    log_lines.append(line)
                    try:
                        log_file.write(line + "\n")
                    except Exception:
                        pass
                    if os.path.isabs(line):
                        if os.path.splitext(line)[1].lower() not in _IMAGE_EXTS:
                            output_paths.append(line)
                            output_path = line
                    if "Destination:" in line and not output_path:
                        last_file = line.split("Destination:", 1)[-1].strip()
                    new_phase = _detect_phase(line)
                    with jobs_lock:
                        jobs[job_id]["log"] = "\n".join(log_lines[-120:])
                        jobs[job_id]["last_output_at"] = time.time()
                        jobs[job_id].pop("phase_note", None)
                        if new_phase:
                            jobs[job_id]["phase"] = new_phase
                        if output_path:
                            jobs[job_id]["output_path"] = output_path
                            jobs[job_id]["output_paths"] = list(output_paths)
                    with jobs_lock:
                        if jobs[job_id].get("cancel_requested"):
                            try:
                                p2.terminate()
                            except Exception:
                                pass
                code = p2.wait()

            if code == 0:
                with jobs_lock:
                    jobs[job_id]["status"] = "done"
                    jobs[job_id]["phase"] = "Complete"
                    jobs[job_id].pop("phase_note", None)
                    jobs[job_id]["output_paths"] = list(output_paths)
                    final_path = output_path or last_file
                    if final_path:
                        jobs[job_id]["file"] = os.path.basename(final_path)
                        jobs[job_id]["output_path"] = final_path if os.path.isabs(final_path) else os.path.join(DOWNLOAD_DIR, final_path)
                    save_jobs()
            else:
                with jobs_lock:
                    j = jobs[job_id]
                    j["status"] = "error"
                    j["phase"] = "Failed"
                    j.pop("phase_note", None)
                    if j.get("stall_killed"):
                        j["error_message"] = "Timed out — the source stopped responding."
                    else:
                        friendly = _classify_error(j.get("log", ""))
                        if friendly:
                            j["error_message"] = friendly
                    save_jobs()
    except Exception as e:
        with jobs_lock:
            jobs[job_id]["status"] = "error"
            jobs[job_id]["phase"] = "Failed"
            jobs[job_id].pop("phase_note", None)
            jobs[job_id]["error_message"] = "Unexpected server error — please try again."
            jobs[job_id]["log"] = f"Exception: {e}"
            save_jobs()
    finally:
        try:
            log_file.close()
        except Exception:
            pass
        with jobs_lock:
            jobs[job_id]["finished_at"] = datetime.utcnow()
            jobs[job_id]["opened_folder"] = jobs[job_id].get("opened_folder", False)
            job_type = jobs[job_id].get("type", "video")
            url_val = jobs[job_id].get("url", url)
            status_val = jobs[job_id]["status"]
            file_val = jobs[job_id].get("file")
            output_val = jobs[job_id].get("output_path")
            output_paths_val = jobs[job_id].get("output_paths", [])
            sc_quality_val = jobs[job_id].get("sc_quality", "m4a")
            sc_playlist_val = jobs[job_id].get("sc_playlist", True)
            failures_val = jobs[job_id].get("failures", [])
            ip_val = jobs[job_id].get("client_ip")
            jobs[job_id].pop("process", None)
            jobs[job_id].pop("cancel_requested", None)
            save_jobs()
        job_sema.release()
        _release_ip(ip_val)
        if status_val == "error":
            with jobs_lock:
                final_log = jobs[job_id].get("log", "")
            _check_cookie_alert(final_log)
        # history record
        record = {
            "job_id": job_id,
            "timestamp": datetime.utcnow().isoformat(),
            "url": url_val,
            "type": job_type,
            "final_status": status_val,
            "output_path": output_val or (os.path.join(DOWNLOAD_DIR, file_val) if file_val else None),
            "output_paths": output_paths_val,
            "sc_quality": sc_quality_val if job_type == "soundcloud" else None,
            "sc_playlist": sc_playlist_val if job_type == "soundcloud" else None,
            "failures": failures_val if job_type in ("spotify", "apple_music") else [],
            "title": None,
            "id": None,
        }
        file_for_meta = os.path.basename(record["output_path"]) if record["output_path"] else file_val
        if file_for_meta and "[" in file_for_meta and "]" in file_for_meta:
            try:
                title_part, _, rest = file_for_meta.rpartition(" [")
                record["title"] = title_part.strip()
                record["id"] = rest.split("]", 1)[0]
            except Exception:
                pass
        append_history(record)

@app.get("/")
def index():
    return render_template_string(HTML)

# ── SEO: robots + sitemap ────────────────────────────────────────────
_SITE_ORIGIN = "https://digitaldownloads.space"

@app.get("/robots.txt")
def robots_txt():
    body = (
        "User-agent: *\n"
        "Allow: /\n"
        "Disallow: /admin\n"
        "Disallow: /desktop/redeem\n"
        "Disallow: /status/\n"
        "Disallow: /download/\n"
        "Disallow: /file/\n"
        "Disallow: /job-log/\n"
        "Disallow: /history\n"
        "\n"
        f"Sitemap: {_SITE_ORIGIN}/sitemap.xml\n"
    )
    return Response(body, mimetype="text/plain")

@app.get("/sitemap.xml")
def sitemap_xml():
    # Public, indexable pages only — priority hints the crawler, not a ranking.
    pages = [
        ("/", "1.0"),
        ("/trial", "0.8"),
        ("/privacy", "0.3"),
        ("/terms", "0.3"),
    ]
    lastmod = datetime.now().strftime("%Y-%m-%d")
    urls = "".join(
        f"  <url><loc>{_SITE_ORIGIN}{path}</loc>"
        f"<lastmod>{lastmod}</lastmod>"
        f"<priority>{prio}</priority></url>\n"
        for path, prio in pages
    )
    xml = (
        '<?xml version="1.0" encoding="UTF-8"?>\n'
        '<urlset xmlns="http://www.sitemaps.org/schemas/sitemap/0.9">\n'
        f"{urls}"
        "</urlset>\n"
    )
    return Response(xml, mimetype="application/xml")

# llms.txt — a markdown summary for AI crawlers/agents (llmstxt.org proposal).
# Plain-text, content-only; no ranking guarantees, just an accurate brief so
# LLMs cite +downloads correctly instead of guessing.
_LLMS_TXT = """# +downloads

> +downloads is a media downloader for YouTube, Spotify, Apple Music, SoundCloud and ~1000 other sites. It is available as a metered token-based online tool and as a $1.99 one-time desktop app for macOS, Windows and Linux, with free updates forever.

+downloads wraps yt-dlp and ffmpeg behind a simple interface. The desktop app runs entirely on the user's machine, so files never pass through a server. A free, feature-limited (YouTube-only) trial edition of the desktop app is also offered. The product is hosted at https://digitaldownloads.space.

## Products

- [Desktop app](https://digitaldownloads.space/desktop/buy): $1.99 one-time purchase, free updates forever, for macOS, Windows and Linux. Unlimited downloads, runs locally.
- [Online tool](https://digitaldownloads.space/): Browser-based downloader, metered with token-based download credits.
- [Free trial edition](https://digitaldownloads.space/trial): A no-cost, YouTube-only edition of the desktop app. No payment or card required.

## Pages

- [Home](https://digitaldownloads.space/): Desktop app overview, online tool, pricing and FAQ.
- [Free trial](https://digitaldownloads.space/trial): Download the free YouTube-only trial edition.
- [Privacy policy](https://digitaldownloads.space/privacy): How +downloads handles data — no third-party analytics, no tracking SDKs, no IP logging.
- [Terms of service](https://digitaldownloads.space/terms): Acceptable use and the user's responsibility for downloaded content.

## Key facts

- Supported sites include YouTube, Spotify, Apple Music, SoundCloud, Vimeo, Twitter/X, Facebook, TikTok, Twitch, Bandcamp, Mixcloud, Dailymotion and roughly 1000 more.
- The desktop app costs $1.99 as a one-time purchase. There are no subscriptions and no upgrade fees; all future versions are free.
- The desktop app has no in-app license check — payment gates obtaining the installer, not running it.
- The desktop app downloads media locally; URLs, files and activity are never seen by the +downloads server.
- An iOS companion app, "+ Media Player", plays a synced +downloads library and pairs with the desktop app over Wi-Fi.
"""

@app.get("/llms.txt")
def llms_txt():
    return Response(_LLMS_TXT, mimetype="text/plain")

# Google Search Console — HTML-file ownership verification. Served at the site
# root so the URL-prefix property https://digitaldownloads.space/ verifies.
@app.get("/google42d52abaf2591614.html")
def google_site_verification():
    return Response(
        "google-site-verification: google42d52abaf2591614.html\n",
        mimetype="text/html",
    )

@app.get("/privacy")
def privacy():
    return render_template_string(
        _LEGAL_PAGE_TEMPLATE,
        page_title="Privacy Policy",
        updated=_LEGAL_LAST_UPDATED,
        body=_PRIVACY_BODY,
        canonical="https://digitaldownloads.space/privacy",
        meta_desc="How +downloads handles your data: no third-party analytics, no tracking SDKs, no IP logging. The desktop app runs entirely on your machine.",
    )

@app.get("/terms")
def terms():
    return render_template_string(
        _LEGAL_PAGE_TEMPLATE,
        page_title="Terms of Service",
        updated=_LEGAL_LAST_UPDATED,
        body=_TERMS_BODY,
        canonical="https://digitaldownloads.space/terms",
        meta_desc="The terms of service for +downloads — acceptable use, your responsibility for downloaded content, and third-party platform trademark notes.",
    )

@app.get("/desktop/buy")
def desktop_buy():
    # Buy buttons on the landing page point here; hop to the payment app's
    # desktop checkout. Kept as a stable internal URL so the destination can
    # change via env var without editing the landing-page HTML.
    return redirect(DESKTOP_PAYMENT_URL, code=302)


def _desktop_redeem_state(token: str):
    """Resolve a desktop redeem token to (state, message).

    state is one of: 'confirmed' (paid desktop token, ready), 'pending' (the
    Stripe webhook hasn't activated the pre-minted token yet — keep polling),
    or 'error' (bad token, or an online-tool token used on the wrong page).
    """
    if not token or not token.strip():
        return "error", "This link is missing its purchase token. Use the link from your confirmation email."
    status = _check_token_status(token.strip())
    if status.get("valid"):
        if status.get("product") == "desktop":
            return "confirmed", ""
        return "error", "This token is for the online downloader, not the desktop app. Use it on the homepage instead."
    if not status:
        # Payment app unreachable or a transient error — let the page poll/retry.
        return "pending", ""
    if status.get("product") == "desktop":
        # Row exists but downloads_remaining is still 0: the checkout.session.completed
        # webhook hasn't activated it yet. This is the redirect/webhook race.
        return "pending", ""
    if status.get("reason") in ("not_found", "missing_token"):
        return "error", "We couldn't find a purchase for this link. Check that you used the full link from your confirmation email."
    return "error", "We couldn't verify this purchase. Contact support with the link from your email."


@app.get("/desktop/redeem")
def desktop_redeem():
    token = request.args.get("token", "")
    state, message = _desktop_redeem_state(token)
    detected = _detect_os(request.headers.get("User-Agent", ""))
    builds = _redeem_build_options(detected) if state == "confirmed" else []
    return render_template_string(
        _DESKTOP_REDEEM_HTML,
        state=state,
        message=message,
        token=token,
        builds=builds,
        detected_os=detected,
    )


@app.get("/desktop/redeem/status")
def desktop_redeem_status():
    token = request.args.get("token", "")
    state, message = _desktop_redeem_state(token)
    return {"state": state, "message": message}


@app.get("/desktop/redeem/download")
def desktop_redeem_download():
    token = request.args.get("token", "")
    os_key = request.args.get("os", "")
    if os_key not in _OS_ORDER:
        abort(400)
    fn = _load_builds_manifest().get(os_key) or ""
    path = DESKTOP_BUILDS_DIR / fn if fn else None
    if not fn or not path.exists():
        # No build for this OS — send them back to the redeem page.
        return redirect(f"/desktop/redeem?token={quote(token)}", code=302)
    # Block burning an online-tool token on the installer.
    status = _check_token_status(token)
    if not (status.get("valid") and status.get("product") == "desktop"):
        return redirect(f"/desktop/redeem?token={quote(token)}", code=302)
    # Atomically spend one download credit; bail if the token is exhausted.
    used = _consume_token(token)
    if not used.get("valid"):
        return redirect(f"/desktop/redeem?token={quote(token)}", code=302)
    return send_file(path, as_attachment=True, download_name=fn)


@app.get("/desktop/update")
def desktop_update():
    """Free-update download for existing customers. No token — the link is only
    distributed via the Kit broadcast to the desktop-customer segment."""
    os_key = request.args.get("os", "")
    if os_key:
        if os_key not in _OS_ORDER:
            abort(400)
        fn = _load_builds_manifest().get(os_key) or ""
        path = DESKTOP_BUILDS_DIR / fn if fn else None
        if not fn or not path.exists():
            abort(404)
        return send_file(path, as_attachment=True, download_name=fn)
    detected = _detect_os(request.headers.get("User-Agent", ""))
    return render_template_string(
        _DESKTOP_REDEEM_HTML,
        state="update",
        message="",
        token="",
        builds=_redeem_build_options(detected),
        detected_os=detected,
    )


@app.get("/trial")
def desktop_trial():
    """Free-trial download page. Public and token-less — serves the
    feature-limited trial installers from DESKTOP_BUILDS_TRIAL_DIR, never the
    paid builds. An email gate (see /trial/unlock) reveals the download; a
    signed cookie remembers the unlock. With ?os= it streams the installer."""
    os_key = request.args.get("os", "")
    if os_key:
        if os_key not in _OS_ORDER:
            abort(400)
        # The installer download is gated behind the email form.
        if not _trial_unlocked(request):
            return redirect("/trial")
        fn = _load_builds_manifest(DESKTOP_BUILDS_TRIAL_DIR).get(os_key) or ""
        path = DESKTOP_BUILDS_TRIAL_DIR / fn if fn else None
        if not fn or not path.exists():
            abort(404)
        return send_file(path, as_attachment=True, download_name=fn)
    detected = _detect_os(request.headers.get("User-Agent", ""))
    return render_template_string(
        _DESKTOP_TRIAL_HTML,
        builds=_redeem_build_options(detected, DESKTOP_BUILDS_TRIAL_DIR),
        detected_os=detected,
        unlocked=_trial_unlocked(request),
        error=request.args.get("e") == "1",
    )


@app.post("/trial/unlock")
def desktop_trial_unlock():
    """Email gate for /trial — validates the email, adds it to the Kit
    'desktop-trial' tag (local fallback on API failure), sets the unlock
    cookie, and redirects back to /trial with the download revealed."""
    email = (request.form.get("email") or "").strip().lower()
    if not email or len(email) > 254 or not _EMAIL_RE.match(email):
        return redirect("/trial?e=1")
    if not _kit_subscribe_trial(email):
        _record_trial_signup_fallback(email)
    resp = make_response(redirect("/trial"))
    resp.set_cookie(
        _TRIAL_COOKIE, _TRIAL_COOKIE_SIG,
        max_age=180 * 24 * 3600, httponly=True, samesite="Lax",
    )
    return resp


@app.post("/start")
def start():
    data = request.get_json() or {}
    url = (data.get("url") or "").strip()
    job_type = (data.get("type") or "video").strip().lower()
    # Token holders bypass the maintenance pause. Token comes from body or header.
    client_token = (data.get("token") or request.headers.get("X-Access-Token") or "").strip()
    paused_bypass = False
    if _is_paused():
        if not (client_token and _is_token_valid(client_token)):
            return jsonify({"error": "paused", "paused": True}), 503
        paused_bypass = True
    if not is_valid_url(url):
        return jsonify({"error": "Invalid URL"}), 400
    _BLOCKED_DOMAINS = {
        "pornhub", "xvideos", "xnxx", "xhamster", "redtube", "youporn",
        "tube8", "spankbang", "eporner", "tnaflix", "drtuber", "sunporno",
        "txxx", "hdzog", "hclips", "porntrex", "fuq", "beeg", "porn",
        "xxxbunker", "4tube", "porntube", "slutload", "motherless",
        "heavy-r", "efukt", "bestgore", "theync", "crazyshit",
        "anyporn", "nuvid", "pornone", "sexvid", "empflix", "porndig",
        "alohatube", "pornoxo", "3movs", "ashemaletube", "trannytube",
        "shemalestube", "chaturbate", "stripchat", "bongacams", "cam4",
        "livejasmin", "myfreecams", "camsoda", "onlyfans",
    }
    from urllib.parse import urlparse as _urlparse
    _host = (_urlparse(url).hostname or "").lower()
    if any(d in _host for d in _BLOCKED_DOMAINS):
        return jsonify({"error": "Adult content is not supported."}), 400
    if detect_soundcloud(url) and job_type in {"", "auto", "video", "audio"}:
        job_type = "soundcloud"
    if detect_spotify(url):
        job_type = "spotify"
    if detect_apple_music(url):
        job_type = "apple_music"
    if job_type not in {"video", "audio", "soundcloud", "spotify", "apple_music"}:
        return jsonify({"error": "Invalid type; must be video, audio, soundcloud, spotify, or apple_music"}), 400

    sc_quality = (data.get("sc_quality") or "m4a").strip().lower()
    if sc_quality not in {"m4a", "mp3"}:
        sc_quality = "m4a"
    sc_playlist = bool(data.get("sc_playlist", True))

    spotify_info = None
    if job_type == "spotify":
        try:
            spotify_info = _spotify_fetch_metadata(url)
        except Exception as e:
            return jsonify({"error": f"Spotify API error: {e}"}), 400
        if not spotify_info.get("tracks"):
            return jsonify({"error": "No tracks found in Spotify URL."}), 400

    apple_music_info = None
    if job_type == "apple_music":
        try:
            apple_music_info = _apple_music_fetch_metadata(url)
        except Exception as e:
            return jsonify({"error": f"Apple Music error: {e}"}), 400
        if not apple_music_info.get("tracks"):
            return jsonify({"error": "No tracks found in Apple Music URL."}), 400

    track_count = len((spotify_info or apple_music_info or {}).get("tracks", []))
    if track_count > MAX_PLAYLIST_TRACKS:
        return jsonify({"error": f"Playlist too large ({track_count} tracks). Limit is {MAX_PLAYLIST_TRACKS}."}), 400

    if DISK_CAP_GB > 0:
        try:
            used_gb = _disk_usage_gb(DOWNLOAD_DIR)
            if used_gb >= DISK_CAP_GB:
                return jsonify({"error": "Server storage is full. Try again later."}), 503
        except Exception:
            pass

    ip = _client_ip()
    err, code = _check_ip_limits(ip)
    if err:
        return jsonify({"error": err}), code

    prune_jobs()
    job_id = str(uuid.uuid4())
    with jobs_lock:
        jobs[job_id] = {
            "status": "queued",
            "log": "Queued\u2026",
            "created_at": datetime.utcnow(),
            "file": None,
            "finished_at": None,
            "opened_folder": False,
            "type": job_type,
            "url": url,
            "sc_quality": sc_quality,
            "sc_playlist": sc_playlist,
            "output_paths": [],
            "spotify_info": spotify_info,
            "apple_music_info": apple_music_info,
            "current_index": 0,
            "total_items": track_count,
            "progress_pct": 0,
            "failures": [],
            "client_ip": ip,
        }
        save_jobs()
    with queue_cv:
        if len(job_queue) >= MAX_QUEUE_DEPTH:
            with jobs_lock:
                jobs.pop(job_id, None)
            _release_ip(ip)
            return jsonify({"error": "Queue is full. Try again later."}), 429
        job_queue.append(job_id)
        queue_cv.notify()
    resp = {"job_id": job_id, "status": "queued"}
    if paused_bypass and client_token:
        consumed = _consume_token(client_token)
        if consumed.get("valid"):
            resp["token_remaining"] = consumed.get("remaining")
    return jsonify(resp)

@app.get("/status/<job_id>")
def status(job_id):
    with jobs_lock:
        job = jobs.get(job_id)
        if not job:
            return jsonify({"status": "unknown", "log": "No such job"})
        # return a shallow copy, excluding non-serializable internals
        payload = {k: v for k, v in job.items() if k not in ("process", "cancel_requested", "spotify_info", "apple_music_info", "client_ip")}
        payload["log"] = job.get("log", "")
    payload["queue_position"] = queue_position(job_id)
    with queue_cv:
        payload["queue_length"] = len(job_queue)
    with jobs_lock:
        payload["active_count"] = sum(1 for j in jobs.values() if j.get("status") == "running")
    return jsonify(payload)

@app.get("/download/<job_id>")
def download(job_id):
    with jobs_lock:
        job = jobs.get(job_id)
    if not job:
        abort(404)

    output_paths = job.get("output_paths") or []
    existing = [p for p in output_paths if p and os.path.exists(p) and _is_safe_path(p)]

    if len(existing) > 1:
        total_size = sum(os.path.getsize(p) for p in existing)
        if total_size > 2 * 1024 * 1024 * 1024:
            abort(413)
        first_dir = os.path.dirname(existing[0])
        zip_name = (os.path.basename(first_dir) or "soundcloud_download") + ".zip"
        tmp_dir = tempfile.mkdtemp()
        zip_path = os.path.join(tmp_dir, zip_name)
        try:
            with zipfile.ZipFile(zip_path, "w", compression=zipfile.ZIP_STORED) as zf:
                for fpath in existing:
                    zf.write(fpath, os.path.basename(fpath))
        except Exception:
            shutil.rmtree(tmp_dir, ignore_errors=True)
            abort(500)

        @after_this_request
        def cleanup(response):
            try:
                shutil.rmtree(tmp_dir, ignore_errors=True)
            except Exception:
                pass
            return response

        return send_file(zip_path, as_attachment=True, download_name=zip_name)

    # Single-file fallback (existing behavior)
    if not job.get("file") and not job.get("output_path"):
        abort(404)
    target_path = job.get("output_path") or os.path.join(DOWNLOAD_DIR, job["file"])
    if target_path and os.path.exists(target_path) and _is_safe_path(target_path):
        return send_from_directory(os.path.dirname(target_path), os.path.basename(target_path), as_attachment=True)
    if job.get("file"):
        candidate = os.path.join(DOWNLOAD_DIR, os.path.basename(job["file"]))
        if os.path.exists(candidate) and _is_safe_path(candidate):
            return send_from_directory(DOWNLOAD_DIR, os.path.basename(job["file"]), as_attachment=True)
    abort(404)

@app.get("/file/<job_id>")
def download_single(job_id):
    with jobs_lock:
        job = jobs.get(job_id)
    if not job:
        abort(404)
    path = job.get("output_path") or (job.get("output_paths") or [None])[0]
    if not path or not os.path.exists(path) or not _is_safe_path(path):
        abort(404)
    return send_file(path, as_attachment=True)

@app.get("/history")
def history():
    try:
        limit = int(request.args.get("limit", "10"))
    except ValueError:
        limit = 10
    items = load_history()[-limit:]
    for item in items:
        if item.get("output_path"):
            item["output_path"] = os.path.basename(item["output_path"])
        if item.get("output_paths"):
            item["output_paths"] = [os.path.basename(p) for p in item["output_paths"] if p]
    return jsonify({"items": items[::-1]})

@app.post("/cancel")
def cancel():
    data = request.get_json() or {}
    job_id = (data.get("job_id") or "").strip()
    if not job_id:
        return jsonify({"error": "job_id required"}), 400
    removed = False
    with queue_cv:
        for idx, jid in enumerate(list(job_queue)):
            if jid == job_id:
                job_queue.remove(jid)
                removed = True
                break
    with jobs_lock:
        job = jobs.get(job_id)
        if not job:
            return jsonify({"error": "Unknown job"}), 404
        if removed:
            job["status"] = "cancelled"
            job["log"] = "Cancelled before start"
            _release_ip(job.get("client_ip"))
        elif job.get("status") == "running":
            proc = job.get("process")
            job["cancel_requested"] = True
            job["status"] = "cancelled"
            if proc and proc.poll() is None:
                proc.terminate()
        else:
            return jsonify({"error": "Job not cancellable"}), 400
    save_jobs()
    return jsonify({"status": "cancelled"})

@app.get("/job-log/<job_id>")
def job_log(job_id):
    if not re.fullmatch(r'[0-9a-f\-]{36}', job_id):
        abort(400)
    tail = request.args.get("tail", "200")
    path = job_log_path(job_id)
    if not path.exists():
        return jsonify({"error": "log not found"}), 404
    try:
        tail_n = int(tail)
    except ValueError:
        tail_n = 200
    lines = path.read_text(encoding="utf-8").splitlines()
    if tail_n > 0:
        lines = lines[-tail_n:]
    return jsonify({"log": "\n".join(lines)})

@app.get("/health")
def health():
    with jobs_lock:
        running = sum(1 for j in jobs.values() if j.get("status") == "running")
    with queue_cv:
        qlen = len(job_queue)
    return jsonify({"queue_length": qlen, "running": running, "version": VERSION})

@app.get("/admin")
def admin_page():
    if not COOKIES_PASSWORD:
        abort(503)
    return render_template_string(ADMIN_HTML)


@app.post("/upload-cookies")
def upload_cookies():
    if not COOKIES_PASSWORD:
        abort(503)
    if not hmac.compare_digest(request.form.get("password", ""), COOKIES_PASSWORD):
        return jsonify({"error": "Invalid password"}), 403
    if not COOKIES_PATH:
        return jsonify({"error": "YT_UI_COOKIES not configured"}), 400
    f = request.files.get("cookies")
    if not f:
        return jsonify({"error": "No file provided"}), 400
    f.save(COOKIES_PATH)
    return jsonify({"ok": True})


@app.post("/admin/builds/upload")
def admin_builds_upload():
    if not COOKIES_PASSWORD:
        abort(503)
    if not hmac.compare_digest(request.form.get("password", ""), COOKIES_PASSWORD):
        return jsonify({"error": "Invalid password"}), 403
    os_key = request.form.get("os", "")
    if os_key not in _OS_ORDER:
        return jsonify({"error": "Invalid OS"}), 400
    edition = request.form.get("edition", "full")
    if edition not in ("full", "trial"):
        return jsonify({"error": "Invalid edition"}), 400
    builds_dir = _builds_dir_for(edition)
    f = request.files.get("build")
    if not f or not f.filename:
        return jsonify({"error": "No file provided"}), 400
    fn = secure_filename(f.filename)
    if not fn:
        return jsonify({"error": "Unusable filename"}), 400
    builds_dir.mkdir(parents=True, exist_ok=True)
    f.save(builds_dir / fn)
    m = _load_builds_manifest(builds_dir)
    old = m.get(os_key)
    m[os_key] = fn
    _save_builds_manifest(m, builds_dir)
    if old and old != fn:
        _maybe_delete_build_file(old, m, builds_dir)
    return jsonify({"ok": True, "filename": fn})


@app.post("/admin/builds/delete")
def admin_builds_delete():
    if not COOKIES_PASSWORD:
        abort(503)
    data = request.get_json(silent=True) or {}
    if not hmac.compare_digest(data.get("password", ""), COOKIES_PASSWORD):
        return jsonify({"error": "Invalid password"}), 403
    os_key = data.get("os", "")
    if os_key not in _OS_ORDER:
        return jsonify({"error": "Invalid OS"}), 400
    edition = data.get("edition", "full")
    if edition not in ("full", "trial"):
        return jsonify({"error": "Invalid edition"}), 400
    builds_dir = _builds_dir_for(edition)
    m = _load_builds_manifest(builds_dir)
    old = m.get(os_key)
    m[os_key] = ""
    _save_builds_manifest(m, builds_dir)
    if old:
        _maybe_delete_build_file(old, m, builds_dir)
    return jsonify({"ok": True})


@app.post("/admin/stats")
def admin_stats():
    if not COOKIES_PASSWORD:
        abort(503)
    data = request.get_json(silent=True) or {}
    if not hmac.compare_digest(data.get("password", ""), COOKIES_PASSWORD):
        return jsonify({"error": "Invalid password"}), 403
    history = load_history()
    by_status: dict = {}
    by_type: dict = {}
    for item in history:
        s = item.get("final_status", "unknown")
        t = item.get("type", "unknown")
        by_status[s] = by_status.get(s, 0) + 1
        by_type[t] = by_type.get(t, 0) + 1
    with jobs_lock:
        running = sum(1 for j in jobs.values() if j.get("status") == "running")
        active_jobs = [
            {
                "job_id": jid,
                "status": j.get("status"),
                "type": j.get("type"),
                "url": j.get("url"),
                "progress_pct": j.get("progress_pct", 0),
                "created_at": str(j.get("created_at", "")),
            }
            for jid, j in jobs.items()
            if j.get("status") in ("running", "queued")
        ]
    with queue_cv:
        qlen = len(job_queue)
    return jsonify({
        "version": VERSION,
        "running": running,
        "queue_length": qlen,
        "total_history": len(history),
        "by_status": by_status,
        "by_type": by_type,
        "recent": history[-50:][::-1],
        "active_jobs": active_jobs,
        "pageviews": _pageview_analytics(),
        "builds": _list_desktop_builds(),
        "trial_builds": _list_desktop_builds(DESKTOP_BUILDS_TRIAL_DIR),
    })


@app.post("/admin/clear-history")
def admin_clear_history():
    if not COOKIES_PASSWORD:
        abort(503)
    data = request.get_json(silent=True) or {}
    if not hmac.compare_digest(data.get("password", ""), COOKIES_PASSWORD):
        return jsonify({"error": "Invalid password"}), 403
    with open(HISTORY_PATH, "w", encoding="utf-8") as f:
        json.dump([], f)
    return jsonify({"ok": True, "message": "History cleared"})


@app.get("/service-status")
def service_status():
    return jsonify({"paused": _is_paused()})


@app.post("/token-unlock")
def token_unlock():
    data = request.get_json(silent=True) or {}
    token = (data.get("token") or "").strip()
    if not token or not TOKEN_INTERNAL_SECRET:
        return jsonify({"valid": False, "reason": "invalid"})
    try:
        body = json.dumps({"token": token}).encode()
        req = urllib.request.Request(
            f"{PAYMENT_APP_URL}/payment/api/access/internal/token/check",
            data=body,
            headers={"Content-Type": "application/json", "x-internal-secret": TOKEN_INTERNAL_SECRET, "x-forwarded-proto": "https"},
            method="POST",
        )
        with urllib.request.urlopen(req, timeout=3) as resp:
            result = json.loads(resp.read())
        if result.get("valid"):
            _remember_valid_token(token)
        return jsonify(result)
    except Exception:
        return jsonify({"valid": False, "reason": "service_unavailable"})


@app.get("/admin/debug-job/<job_id>")
def admin_debug_job(job_id):
    if not COOKIES_PASSWORD:
        abort(503)
    pw = request.args.get("pw", "")
    if not hmac.compare_digest(pw, COOKIES_PASSWORD):
        return jsonify({"error": "Invalid password"}), 403
    if not re.fullmatch(r'[0-9a-f\-]{36}', job_id):
        abort(400)
    with jobs_lock:
        job = jobs.get(job_id)
    if not job:
        return jsonify({"error": "Unknown job"}), 404
    # Sanitize internal fields that aren't JSON-serializable.
    sanitized = {}
    for k, v in job.items():
        if k in ("process", "cancel_requested"):
            continue
        try:
            json.dumps(v, default=str)
            sanitized[k] = v
        except Exception:
            sanitized[k] = str(v)
    log_path = job_log_path(job_id)
    full_log = ""
    if log_path.exists():
        try:
            full_log = log_path.read_text(encoding="utf-8", errors="replace")
        except Exception:
            full_log = ""
    return jsonify({"job": json.loads(json.dumps(sanitized, default=str)), "full_log": full_log})


@app.post("/admin/pause")
def admin_pause():
    global _service_paused, _pause_cache_at
    if not COOKIES_PASSWORD:
        abort(503)
    data = request.get_json(silent=True) or {}
    if not hmac.compare_digest(data.get("password", ""), COOKIES_PASSWORD):
        return jsonify({"error": "Invalid password"}), 403
    new_val = bool(data.get("paused", True))
    with _pause_lock:
        _service_paused = new_val
        _pause_cache_at = time.time()
    _save_paused(new_val)
    return jsonify({"ok": True, "paused": new_val})


@app.before_request
def _global_rate_limit():
    if request.path.startswith(('/status/', '/health', '/static/')):
        return
    ip = _client_ip()
    now = time.time()
    minute_ago = now - 60
    with _global_rate_lock:
        timestamps = _global_rate.setdefault(ip, deque())
        while timestamps and timestamps[0] < minute_ago:
            timestamps.popleft()
        if len(timestamps) >= GLOBAL_RATE_PER_MIN:
            return jsonify({"error": "Too many requests. Slow down."}), 429
        timestamps.append(now)


@app.after_request
def add_security_headers(response):
    try:
        if request.method == "GET" and request.path in _TRACKED_PAGES and response.status_code < 400:
            _record_pageview(request.path)
            # Conversion attribution: when the landing page is hit with a ?ref=
            # tag (e.g. the trial app's in-app Upgrade CTA uses ?ref=trial, the
            # /trial web page uses ?ref=trial-page), also count it under a
            # distinct path so the admin Top Pages list surfaces referred visits.
            if request.path == "/":
                ref = re.sub(r"[^a-z0-9_-]", "", request.args.get("ref", "").lower())[:32]
                if ref:
                    _record_pageview("/?ref=" + ref)
    except Exception:
        pass
    response.headers["Content-Security-Policy"] = (
        "default-src 'self'; "
        "style-src 'self' 'unsafe-inline'; "
        "script-src 'self' 'unsafe-inline' https://pagead2.googlesyndication.com https://www.googletagservices.com; "
        "img-src 'self' data: https://pagead2.googlesyndication.com; "
        "frame-src https://googleads.g.doubleclick.net https://tpc.googlesyndication.com; "
        "connect-src 'self' https://pagead2.googlesyndication.com"
    )
    response.headers["X-Content-Type-Options"] = "nosniff"
    response.headers["X-Frame-Options"] = "DENY"
    response.headers["Referrer-Policy"] = "no-referrer"
    return response

# restore persisted jobs then kick off background threads
restore_jobs_from_disk()
dispatcher_thread = threading.Thread(target=dispatcher, daemon=True)
dispatcher_thread.start()
cleanup_thread = threading.Thread(target=cleanup_worker, daemon=True)
cleanup_thread.start()

if __name__ == "__main__":
    host = os.environ.get("FLASK_HOST", "127.0.0.1")
    port = int(os.environ.get("PORT", "5055"))
    app.run(host=host, port=port, debug=False, use_reloader=False)
