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
from urllib.parse import urlparse, parse_qs
from flask import Flask, request, jsonify, send_from_directory, send_file, render_template_string, abort, after_this_request, make_response
import sys
import zipfile
import base64
import re
import urllib.request
import urllib.error
import tempfile
import shutil
import smtplib
from email.mime.text import MIMEText

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

def _load_paused() -> bool:
    try:
        return bool(json.loads(PAUSE_PATH.read_text()).get("paused", False))
    except Exception:
        return False

def _save_paused(val: bool):
    PAUSE_PATH.write_text(json.dumps({"paused": val}))

_service_paused: bool = _load_paused()
_pause_lock = threading.Lock()

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
  <link rel="icon" type="image/png" href="/static/favicon.png">
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
    @media (max-width: 600px) {
      .stat-grid { grid-template-columns: repeat(2, 1fr); }
      .url-cell { max-width: 140px; }
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
  </script>
</body>
</html>
"""

HTML = """
<!doctype html>
<html>
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width, initial-scale=1">
  <meta name="theme-color" content="#1a1818">
  <meta name="apple-mobile-web-app-capable" content="yes">
  <meta name="apple-mobile-web-app-status-bar-style" content="black-translucent">
  <meta name="apple-mobile-web-app-title" content="+downloads">
  <link rel="manifest" href="/static/manifest.json">
  <title>+downloads</title>
  <link rel="icon" type="image/png" href="/static/favicon.png">
  <link rel="apple-touch-icon" href="/static/icon-192.png">
  <script async src="https://pagead2.googlesyndication.com/pagead/js/adsbygoogle.js?client=ca-pub-5597587878564683"
     crossorigin="anonymous"></script>
  <style>
    *, *::before, *::after { box-sizing: border-box; margin: 0; padding: 0; }
    body {
      font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', sans-serif;
      background: #1a1818;
      color: #f0eef0;
      min-height: 100vh;
    }
    .header {
      background: #242222;
      border-bottom: 1px solid #2e2c2c;
      padding: 0 32px;
      height: 62px;
      display: flex;
      align-items: center;
      gap: 12px;
    }
    .logo { font-size: 24px; font-weight: 800; color: #db52a6; letter-spacing: -0.5px; }
    .version-badge {
      font-size: 11px; background: #2a2828; color: #555;
      padding: 3px 9px; border-radius: 999px; font-weight: 600;
    }
    .main {
      max-width: 520px; margin: 0 auto; padding: 24px;
      display: flex; flex-direction: column; gap: 20px;
    }
    .left-col { display: flex; flex-direction: column; min-width: 0; }
    .card {
      background: #242222; border: 1px solid #2e2c2c;
      border-radius: 16px; padding: 22px 24px; margin-bottom: 16px;
    }
    .url-row { display: flex; gap: 10px; }
    input[type=text] {
      background: #1a1818; border: 1.5px solid #353333; color: #f0eef0;
      padding: 13px 16px; border-radius: 10px; font-size: 15px;
      flex: 1; min-width: 0; outline: none;
      transition: border-color 0.2s, box-shadow 0.2s;
    }
    input[type=text]:focus { border-color: #db52a6; box-shadow: 0 0 0 3px rgba(219,82,166,0.1); }
    input::placeholder { color: #464444; }
    .btn-primary {
      background: #db52a6; color: #fff; border: none;
      padding: 13px 22px; border-radius: 10px; font-size: 15px; font-weight: 700;
      cursor: pointer; white-space: nowrap; flex-shrink: 0;
      transition: background 0.15s, transform 0.1s;
    }
    .btn-primary:hover { background: #c9479a; }
    .btn-primary:active { transform: scale(0.97); }
    .btn-secondary {
      background: #242222; color: #bf9b3a; border: 1.5px solid #353333;
      padding: 11px 18px; border-radius: 10px; font-size: 14px; font-weight: 600;
      cursor: pointer; white-space: nowrap; flex-shrink: 0;
      transition: background 0.15s, border-color 0.15s;
    }
    .btn-secondary:hover { background: #2e2c2c; border-color: #bf9b3a; }
    .btn-ghost {
      background: transparent; color: #555; border: 1px solid #353333;
      padding: 12px 15px; border-radius: 10px; font-size: 13px;
      cursor: pointer; white-space: nowrap; flex-shrink: 0;
      transition: color 0.15s, border-color 0.15s;
    }
    .btn-ghost:hover { color: #f0eef0; border-color: #555; }
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
      background-image: url("data:image/svg+xml,%3Csvg xmlns='http://www.w3.org/2000/svg' width='12' height='7' viewBox='0 0 12 7'%3E%3Cpath d='M1 1l5 5 5-5' stroke='%23555' stroke-width='1.5' fill='none' stroke-linecap='round' stroke-linejoin='round'/%3E%3C/svg%3E");
      background-repeat: no-repeat; background-position: right 13px center;
      transition: border-color 0.2s;
    }
    select:focus { border-color: #db52a6; outline: none; }
    #scOptions { display: none; margin-top: 12px; gap: 14px; align-items: center; flex-wrap: wrap; }
    #scOptions label { font-size: 13px; color: #888; display: flex; align-items: center; gap: 7px; cursor: pointer; }
    #scOptions select { padding: 8px 32px 8px 12px; font-size: 13px; flex: none; width: auto; }
    .note-pill {
      display: none; margin-top: 12px;
      background: rgba(191,155,58,0.07); border: 1px solid rgba(191,155,58,0.18);
      border-radius: 8px; padding: 9px 14px; font-size: 13px; color: #bf9b3a; line-height: 1.5;
    }
    .divider { height: 1px; background: #2a2828; margin: 18px 0; }
    .token-row { display: flex; gap: 10px; }
    .dir-label { font-size: 12px; color: #3e3c3c; margin-top: 10px; }
    .dir-label b { color: #5a5858; font-weight: 500; }
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
    pre#log {
      background: #141212; border: 1px solid #242222; border-radius: 10px;
      color: #a09aa0; padding: 14px 16px;
      font-size: 12px; font-family: 'SF Mono', 'Fira Code', monospace;
      min-height: 60px; max-height: 200px; overflow-y: auto;
      white-space: pre-wrap; word-break: break-all; line-height: 1.6; margin: 0;
    }
    #meta { font-size: 13px; color: #777; margin-top: 10px; }
    #meta a { color: #db52a6; text-decoration: none; }
    #meta a:hover { text-decoration: underline; }
    .section-label {
      font-size: 11px; font-weight: 700; color: #444;
      text-transform: uppercase; letter-spacing: 1.2px; margin-bottom: 14px;
    }
    .hist-empty { font-size: 13px; color: #444; padding: 16px 0; text-align: center; }
    .hist-row {
      display: flex; align-items: center; gap: 12px;
      padding: 11px 14px; background: #1e1c1c; border: 1px solid #282626;
      border-radius: 10px; margin-bottom: 7px; transition: border-color 0.15s;
    }
    .hist-row:hover { border-color: #353333; }
    .hist-left { flex: 1; min-width: 0; overflow: hidden; }
    .hist-main { font-size: 13px; color: #b8b0b8; white-space: nowrap; overflow: hidden; text-overflow: ellipsis; }
    .hist-sub { font-size: 11px; color: #4a4848; margin-top: 3px; display: flex; gap: 6px; align-items: center; }
    .hist-tag {
      display: inline-block; background: #252323; color: #5a5858;
      padding: 1px 7px; border-radius: 999px; font-size: 11px; font-weight: 600;
    }
    .hist-status { font-size: 11px; font-weight: 600; }
    .hist-status.done { color: #48c78e; }
    .hist-status.error { color: #ff6b6b; }
    .hist-status.cancelled { color: #555; }
    .hist-btns { display: flex; gap: 6px; flex-shrink: 0; }
    .hist-btn {
      background: #252323; border: 1px solid #353333; color: #666;
      padding: 5px 12px; border-radius: 7px; font-size: 12px; cursor: pointer;
      white-space: nowrap; transition: color 0.15s, border-color 0.15s;
    }
    .hist-btn:hover { color: #db52a6; border-color: #db52a6; }
    /* Paused banner */
    .paused-banner {
      display: none; background: #2a1a1a; border: 1.5px solid #e05c5c;
      border-radius: 14px; padding: 18px 22px; margin-bottom: 16px;
      text-align: center;
    }
    .paused-banner h2 {
      font-size: 16px; font-weight: 800; color: #e05c5c; margin-bottom: 6px;
    }
    .paused-banner p {
      font-size: 13px; color: #aaa; margin-bottom: 14px; line-height: 1.5;
    }
    .btn-get-app {
      display: inline-block; background: #db52a6; color: #fff;
      padding: 11px 24px; border-radius: 10px; font-size: 14px; font-weight: 700;
      text-decoration: none; transition: background 0.15s;
    }
    .btn-get-app:hover { background: #c9479a; }
    /* Library panel */
    ::-webkit-scrollbar { width: 5px; }
    ::-webkit-scrollbar-track { background: transparent; }
    ::-webkit-scrollbar-thumb { background: #353333; border-radius: 3px; }

    /* ── Tablet ────────────────────────────────────────────── */
    @media (max-width: 900px) {
      .main { padding: 14px; }
    }

    /* ── Mobile / iPhone ───────────────────────────────────── */
    @media (max-width: 600px) {
      .header { padding: 0 14px; height: 52px; }
      .logo   { font-size: 20px; }
      .main   { padding: 10px; gap: 0; }
      .card   { padding: 16px 14px; border-radius: 12px; margin-bottom: 10px; }

      /* URL row — stack on narrow screens */
      .url-row   { flex-wrap: wrap; gap: 8px; }
      .btn-primary { width: 100%; padding: 14px; font-size: 16px; }

      /* Type row — full-width select, full-width button */
      .type-row { flex-wrap: wrap; gap: 8px; }
      .type-row select { min-width: 0; }
      .btn-secondary { width: 100%; text-align: center; }

      /* Token row */
      .token-row { flex-wrap: wrap; gap: 8px; }
      .token-row .btn-ghost { width: 100%; }

      /* Status log */
      pre#log { font-size: 11px; max-height: 160px; }
    }
  </style>
</head>
<body>
  <header class="header">
    <span class="logo">+downloads</span>
    <span class="version-badge">v{{version}}</span>
    <a href="mailto:digitalsov2026@gmail.com?subject=+downloads%20Bug%20Report" style="margin-left:auto; color:#555; font-size:12px; font-weight:600; text-decoration:none; padding:6px 12px; border:1px solid #353333; border-radius:8px; transition:color 0.15s, border-color 0.15s;" onmouseover="this.style.color='#f0eef0';this.style.borderColor='#555'" onmouseout="this.style.color='#555';this.style.borderColor='#353333'">Bug Report</a>
    <a href="https://joshuaisaiah.art/payment/tip/573083b1f69f451c903db55d1a22ef2b" target="_blank" rel="noopener noreferrer" style="color:#1a1818; font-size:12px; font-weight:700; text-decoration:none; padding:6px 14px; background:#bf9b3a; border-radius:8px; transition:background 0.15s;" onmouseover="this.style.background='#d4ad42'" onmouseout="this.style.background='#bf9b3a'">Tip Jar</a>
  </header>
  <main class="main">
  <div class="left-col">
    <div class="paused-banner" id="paused-banner">
      <h2>Service Temporarily Paused</h2>
      <p>The web service is currently unavailable. For unlimited, uninterrupted downloads, get the full +downloads app.</p>
      <a class="btn-get-app" href="https://urapages.com/downloads/app" target="_blank" rel="noopener noreferrer">Get the Full Version</a>
    </div>
    <div class="card">
      <div class="url-row">
        <input id="url" type="text" placeholder="Paste YouTube, Spotify, or Apple Music URL here" />
        <button class="btn-primary" onclick="start()">Download</button>
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
    </div>

    <div class="card">
      <div class="status-row">
        <span id="statusPill">idle</span>
        <span id="queuePos"></span>
        <button onclick="cancel()" id="cancelBtn" class="btn-cancel" style="display:none;">Cancel</button>
      </div>
      <div id="progressWrap">
        <div id="progressTrack"><div id="progressBar"></div><div id="progressLabel"></div></div>
        <small id="progressText"></small>
      </div>
      <pre id="log">Idle…</pre>
      <div id="meta"></div>
    </div>

    <a href="https://urapages.com/downloads/app" target="_blank" rel="noopener noreferrer" style="display:flex;align-items:center;gap:12px;background:#242222;border:1px solid #2e2c2c;border-radius:14px;padding:16px 20px;text-decoration:none;transition:border-color 0.2s;" onmouseover="this.style.borderColor='#db52a6'" onmouseout="this.style.borderColor='#2e2c2c'">
      <svg width="28" height="28" viewBox="0 0 24 24" fill="none" xmlns="http://www.w3.org/2000/svg" style="flex-shrink:0">
        <path d="M3 7C3 5.89543 3.89543 5 5 5H9.58579C9.851 5 10.1054 5.10536 10.2929 5.29289L11.7071 6.70711C11.8946 6.89464 12.149 7 12.4142 7H19C20.1046 7 21 7.89543 21 9V17C21 18.1046 20.1046 19 19 19H5C3.89543 19 3 18.1046 3 17V7Z" fill="#db52a6" opacity="0.2"/>
        <path d="M3 7C3 5.89543 3.89543 5 5 5H9.58579C9.851 5 10.1054 5.10536 10.2929 5.29289L11.7071 6.70711C11.8946 6.89464 12.149 7 12.4142 7H19C20.1046 7 21 7.89543 21 9V17C21 18.1046 20.1046 19 19 19H5C3.89543 19 3 18.1046 3 17V7Z" stroke="#db52a6" stroke-width="1.5" stroke-linejoin="round"/>
        <path d="M12 11V15M12 15L10 13M12 15L14 13" stroke="#db52a6" stroke-width="1.5" stroke-linecap="round" stroke-linejoin="round"/>
      </svg>
      <div>
        <div style="font-size:13px;font-weight:700;color:#f0eef0;">Get +downloads</div>
        <div style="font-size:12px;color:#666;margin-top:2px;">Unlimited downloads — no queue, no limits</div>
      </div>
      <svg width="16" height="16" viewBox="0 0 24 24" fill="none" style="margin-left:auto;flex-shrink:0"><path d="M9 18l6-6-6-6" stroke="#444" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"/></svg>
    </a>

    <!-- download-complete modal -->
    <div id="dlModal" style="display:none; position:fixed; inset:0; z-index:999; background:rgba(0,0,0,0.55); backdrop-filter:blur(4px); align-items:center; justify-content:center;">
      <div style="background:#1e1c1c; border:1px solid #333; border-radius:14px; padding:28px 32px; max-width:420px; width:90%; text-align:center;">
        <svg width="48" height="48" viewBox="0 0 24 24" fill="none" style="margin-bottom:12px;">
          <circle cx="12" cy="12" r="10" fill="rgba(72,199,142,0.15)"/>
          <path d="M8 12l3 3 5-6" stroke="#48c78e" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"/>
        </svg>
        <div id="dlModalTitle" style="font-size:15px; font-weight:600; color:#f0eef0; margin-bottom:6px;"></div>
        <div id="dlModalSub" style="font-size:12px; color:#777; margin-bottom:20px;"></div>
        <div style="display:flex; gap:10px; justify-content:center;">
          <a id="dlModalBtn" href="#" style="display:inline-flex; align-items:center; gap:6px; padding:10px 28px; background:#db52a6; color:#fff; font-size:14px; font-weight:600; border-radius:8px; text-decoration:none; transition:background 0.15s;"
             onmouseover="this.style.background='#c4478f'" onmouseout="this.style.background='#db52a6'">
            <svg width="16" height="16" viewBox="0 0 24 24" fill="none"><path d="M12 4v12m0 0l-4-4m4 4l4-4M4 18h16" stroke="#fff" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"/></svg>
            Download
          </a>
          <button onclick="closeDlModal()" style="padding:10px 20px; background:transparent; border:1px solid #333; color:#999; font-size:13px; border-radius:8px; cursor:pointer; transition:border-color 0.15s;"
                  onmouseover="this.style.borderColor='#555'" onmouseout="this.style.borderColor='#333'">Close</button>
        </div>
      </div>
    </div>
  </div><!-- /left-col -->

  </main>

<script>
let currentJob = null;

async function checkPaused() {
  try {
    const r = await fetch('/service-status');
    const d = await r.json();
    const banner = document.getElementById('paused-banner');
    if (d.paused) {
      banner.style.display = 'block';
      document.getElementById('url').disabled = true;
      document.querySelector('.btn-primary').disabled = true;
    } else {
      banner.style.display = 'none';
      document.getElementById('url').disabled = false;
      document.querySelector('.btn-primary').disabled = false;
    }
  } catch (e) {}
}
checkPaused();

function escHtml(s) {
  return String(s == null ? '' : s)
    .replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;')
    .replace(/"/g,'&quot;').replace(/'/g,'&#39;');
}
document.querySelectorAll('details').forEach(function(el) {
  el.addEventListener('toggle', function() {
    const chevronId = this.querySelector('summary span[id]');
    if (chevronId) chevronId.style.transform = this.open ? 'rotate(90deg)' : '';
  });
});

function syncScOptions() {
  const t = document.getElementById('type').value;
  document.getElementById('scOptions').style.display = t === 'soundcloud' ? 'flex' : 'none';
  document.getElementById('spNote').style.display = t === 'spotify' ? 'block' : 'none';
  document.getElementById('amNote').style.display = t === 'apple_music' ? 'block' : 'none';
}
document.getElementById('type').addEventListener('change', syncScOptions);
syncScOptions();

async function start() {
  const url = document.getElementById('url').value.trim();
  if (!url) return;
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
  document.getElementById('log').textContent = "Starting\u2026";
  document.getElementById('meta').textContent = "";
  const res = await fetch('/start', {
    method: 'POST',
    headers: {'Content-Type':'application/json'},
    body: JSON.stringify({url, type, sc_quality: scQuality, sc_playlist: scPlaylist})
  });
  if (!res.ok) {
    const err = await res.json().catch(() => ({}));
    if (err.paused) { checkPaused(); return; }
    document.getElementById('log').textContent = err.error || 'Failed to start';
    return;
  }
  const data = await res.json();
  currentJob = data.job_id;
  document.getElementById('cancelBtn').style.display = 'inline-block';
  poll();
}

async function poll() {
  if (!currentJob) return;
  const res = await fetch('/status/' + currentJob);
  const data = await res.json();
  document.getElementById('log').textContent = data.log || data.status;
  setStatus(data.status);
  updateProgress(data.status, data.log || '', data);
  if ((data.type === 'spotify' || data.type === 'apple_music') && data.total_items > 0) {
    const done = data.current_index || 0;
    const tot = data.total_items;
    const n = (data.output_paths || []).length;
    let meta = done + '/' + tot + ' tracks';
    if (data.status === 'done' && n > 0) {
      meta += ' \u2014 <a href="/download/' + currentJob + '" target="_blank">Download ZIP</a>';
    }
    meta += ' | <a href="/job-log/' + currentJob + '?tail=200" target="_blank">View log</a>';
    document.getElementById('meta').innerHTML = meta;
  } else if (data.output_paths && data.output_paths.length > 1) {
    const n = data.output_paths.length;
    document.getElementById('meta').innerHTML =
      n + ' files \u2014 <a href="/download/' + currentJob + '" target="_blank">Download ZIP</a>'
      + ' | <a href="/job-log/' + currentJob + '?tail=200" target="_blank">View full log</a>';
  } else if (data.file || data.output_path) {
    const name = data.file || data.output_path.split('/').pop();
    document.getElementById('meta').innerHTML =
      'File: <a href="/download/' + currentJob + '" target="_blank">' + escHtml(name) + '</a>'
      + ' | <a href="/job-log/' + currentJob + '?tail=200" target="_blank">View full log</a>';
  }
  if (data.status === "done") {
    document.getElementById('cancelBtn').style.display = 'none';
    showDlModal(data);
    setTimeout(resetUI, 1500);
    return;
  }
  if (data.status === "error" || data.status === "cancelled") {
    document.getElementById('cancelBtn').style.display = 'none';
    return;
  }
  setTimeout(poll, 700);
}

function extractPercent(log) {
  const lines = log.split('\\n');
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
    let qText = 'Waiting in queue\u2026';
    if (pos != null) qText = 'Queue position: ' + pos + ' of ' + qLen;
    if (data.active_count > 0) qText += ' \u00B7 ' + data.active_count + ' downloading now';
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
        text.textContent = 'Processing\u2026';
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
    const stem = (paths[0].split('/').pop() || '').replace(/\\.[^.]+$/, '').trim();
    title.textContent = stem + (paths.length > 1 ? ' + ' + (paths.length - 1) + ' more' : '');
    sub.textContent = paths.length + ' files \u2014 zipped together';
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
  document.getElementById('url').value = '';
  document.getElementById('log').textContent = 'Idle…';
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

<footer style="text-align:center; padding:24px 16px 20px; font-size:12px; color:#555;">
  <a href="#" onclick="document.getElementById('tcModal').style.display='flex'; return false;"
     style="color:#555; text-decoration:underline; text-underline-offset:3px;">Terms &amp; Conditions</a>
</footer>

<!-- Terms & Conditions modal -->
<div id="tcModal" style="display:none; position:fixed; inset:0; background:rgba(0,0,0,0.75); z-index:2000; align-items:center; justify-content:center; padding:20px; box-sizing:border-box;">
  <div style="background:#1a1a1a; border:1px solid #333; border-radius:14px; padding:32px 28px; width:600px; max-width:100%; max-height:85vh; overflow-y:auto; box-shadow:0 8px 40px rgba(0,0,0,0.7);">
    <h2 style="margin:0 0 6px; font-size:18px; color:#f0f0f0;">Terms &amp; Conditions</h2>
    <p style="margin:0 0 20px; font-size:12px; color:#555;">Last updated: February 2026</p>

    <div style="font-size:13px; color:#aaa; line-height:1.7;">
      <p><strong style="color:#f0f0f0;">USE AT YOUR OWN RISK.</strong> This tool is provided for personal, private use only. By using it, you agree to the following terms in full.</p>

      <p><strong style="color:#f0f0f0;">1. No Warranty</strong><br>
      This software is provided "as is", without warranty of any kind, express or implied. The operator makes no guarantees regarding availability, reliability, accuracy, or fitness for any purpose.</p>

      <p><strong style="color:#f0f0f0;">2. Limitation of Liability</strong><br>
      To the fullest extent permitted by applicable law, the operator of this service shall not be liable for any direct, indirect, incidental, special, consequential, or punitive damages arising from your use of or inability to use this tool, including but not limited to loss of data, loss of profits, or any other losses.</p>

      <p><strong style="color:#f0f0f0;">3. Your Responsibility</strong><br>
      You are solely responsible for ensuring that your use of this tool complies with all applicable laws in your jurisdiction, including copyright law. Downloading copyrighted content without authorization may be illegal. The operator does not condone or encourage any unlawful activity.</p>

      <p><strong style="color:#f0f0f0;">4. No Affiliation</strong><br>
      This tool is not affiliated with, endorsed by, or connected to YouTube, Google, SoundCloud, Spotify, Apple, or any other third-party platform. All trademarks belong to their respective owners.</p>

      <p><strong style="color:#f0f0f0;">5. Indemnification</strong><br>
      You agree to indemnify and hold harmless the operator from any claims, damages, or expenses (including legal fees) arising from your use of this service or your violation of these terms.</p>

      <p><strong style="color:#f0f0f0;">6. Changes</strong><br>
      These terms may be updated at any time without notice. Continued use of the service constitutes acceptance of the current terms.</p>

      <p style="margin-top:24px; padding:14px; background:#111; border-radius:8px; color:#888; font-size:12px;">
        By using this tool you acknowledge that you have read, understood, and agreed to these terms and that you use this service entirely at your own risk.
      </p>
    </div>

    <button onclick="document.getElementById('tcModal').style.display='none'"
      style="margin-top:20px; width:100%; padding:11px; background:#333; border:none; border-radius:8px; color:#f0f0f0; font-size:14px; cursor:pointer;">
      Close
    </button>
  </div>
</div>

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
        parts = [p for p in parsed.path.strip("/").split("/") if p]
        country = parts[0]
        kind = parts[1]
        entity_id = parts[-1]
        track_id = parse_qs(parsed.query).get("i", [None])[0]
    except (IndexError, Exception):
        raise ValueError(f"Unrecognized Apple Music URL: {url}")

    if kind == "playlist":
        raise ValueError(
            "Apple Music playlist lookup is not supported. "
            "Paste a single song or album URL instead."
        )
    if kind not in {"album", "song"}:
        raise ValueError(f"Unsupported Apple Music entity type: {kind}")

    def itunes_lookup(lookup_id, entity=None):
        params = f"id={lookup_id}&country={country}"
        if entity:
            params += f"&entity={entity}"
        req = urllib.request.Request(
            f"https://itunes.apple.com/lookup?{params}",
            headers={"User-Agent": "Mozilla/5.0"},
        )
        with urllib.request.urlopen(req, timeout=10) as resp:
            return json.loads(resp.read())

    # Single track: song URL or album URL with ?i= parameter
    if kind == "song" or track_id:
        tid = track_id or entity_id
        data = itunes_lookup(tid)
        if not data["results"]:
            raise ValueError("Track not found in iTunes catalog")
        t = data["results"][0]
        title = t.get("trackName", "")
        artist = t.get("artistName", "")
        return {"kind": "track", "name": title, "tracks": [{"title": title, "artist": artist}]}

    # Album
    data = itunes_lookup(entity_id, entity="song")
    if not data["results"]:
        raise ValueError("Album not found in iTunes catalog")
    collection = data["results"][0]
    album_name = collection.get("collectionName", "album")
    raw = [r for r in data["results"][1:] if r.get("wrapperType") == "track" and r.get("trackName")]
    raw.sort(key=lambda x: x.get("trackNumber", 0))
    tracks = [{"title": r["trackName"], "artist": r.get("artistName", "")} for r in raw]
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
                meta["log"] = "Server restarted during download"
                meta["finished_at"] = now
            elif status == "queued":
                meta["status"] = "cancelled"
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
                    jobs[job_id]["log"] += "\nCancelled by user"
                    save_jobs()
            elif failures_list and len(failures_list) == total:
                with jobs_lock:
                    jobs[job_id]["status"] = "error"
                    jobs[job_id]["log"] += f"\nAll {total} tracks failed."
                    save_jobs()
            else:
                with jobs_lock:
                    jobs[job_id]["status"] = "done"
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
                    jobs[job_id]["log"] += "\nCancelled by user"
                    save_jobs()
            elif failures_list and len(failures_list) == total:
                with jobs_lock:
                    jobs[job_id]["status"] = "error"
                    jobs[job_id]["log"] += f"\nAll {total} tracks failed."
                    save_jobs()
            else:
                with jobs_lock:
                    jobs[job_id]["status"] = "done"
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
            with jobs_lock:
                jobs[job_id]["log"] = "\n".join(log_lines[-120:])
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
                jobs[job_id]["log"] = jobs[job_id].get("log", "") + "\nCancelled by user"
                save_jobs()
        elif code == 0:
            with jobs_lock:
                jobs[job_id]["status"] = "done"
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
                    with jobs_lock:
                        jobs[job_id]["log"] = "\n".join(log_lines[-120:])
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
                    jobs[job_id]["output_paths"] = list(output_paths)
                    final_path = output_path or last_file
                    if final_path:
                        jobs[job_id]["file"] = os.path.basename(final_path)
                        jobs[job_id]["output_path"] = final_path if os.path.isabs(final_path) else os.path.join(DOWNLOAD_DIR, final_path)
                    save_jobs()
            else:
                with jobs_lock:
                    jobs[job_id]["status"] = "error"
                    save_jobs()
    except Exception as e:
        with jobs_lock:
            jobs[job_id]["status"] = "error"
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
    return render_template_string(HTML, version=VERSION)

@app.post("/start")
def start():
    global _service_paused
    with _pause_lock:
        if _service_paused:
            return jsonify({"error": "paused", "paused": True}), 503
    data = request.get_json() or {}
    url = (data.get("url") or "").strip()
    job_type = (data.get("type") or "video").strip().lower()
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
    return jsonify({"job_id": job_id, "status": "queued"})

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
    global _service_paused
    with _pause_lock:
        paused = _service_paused
    return jsonify({"paused": paused})


@app.post("/admin/pause")
def admin_pause():
    global _service_paused
    if not COOKIES_PASSWORD:
        abort(503)
    data = request.get_json(silent=True) or {}
    if not hmac.compare_digest(data.get("password", ""), COOKIES_PASSWORD):
        return jsonify({"error": "Invalid password"}), 403
    new_val = bool(data.get("paused", True))
    with _pause_lock:
        _service_paused = new_val
    _save_paused(new_val)
    return jsonify({"ok": True, "paused": new_val})


_GATE_HTML = """<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Access Required</title>
<style>
  body { font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', sans-serif; background: #fafafa; color: #111; margin: 0; display: flex; align-items: center; justify-content: center; min-height: 100vh; }
  .card { background: #fff; border: 1px solid #e5e7eb; border-radius: 12px; padding: 40px 32px; max-width: 420px; width: 100%; box-shadow: 0 1px 3px rgba(0,0,0,.06); }
  h2 { margin: 0 0 8px; font-size: 22px; }
  p { color: #6b7280; margin: 0 0 24px; font-size: 15px; }
  .btn { display: block; width: 100%; text-align: center; background: #2D6A4F; color: #fff; padding: 14px; border-radius: 8px; text-decoration: none; font-size: 16px; font-weight: 600; margin-bottom: 16px; }
  .btn:hover { background: #1e4f3a; }
  form { display: flex; gap: 8px; }
  input { flex: 1; border: 1.5px solid #d1d5db; border-radius: 8px; padding: 10px 12px; font-size: 14px; font-family: monospace; outline: none; }
  input:focus { border-color: #2D6A4F; }
  button { background: #111; color: #fff; border: none; border-radius: 8px; padding: 10px 16px; font-size: 14px; font-weight: 600; cursor: pointer; }
  .err { color: #dc2626; font-size: 13px; margin-top: 8px; }
</style>
</head>
<body>
<div class="card">
  <h2>Access Required</h2>
  <p>Purchase a token to use this downloader. Your token arrives by email immediately after payment.</p>
  <a class="btn" href="{payment_url}">Buy Access</a>
  <p style="margin-bottom:12px;font-size:13px;">Already have a token? Enter it below.</p>
  <form method="GET" action="/">
    <input name="token" type="text" placeholder="Paste your token" required autocomplete="off">
    <button type="submit">Go</button>
  </form>
  {error_msg}
</div>
</body>
</html>"""


def _call_token_api(endpoint: str, token: str) -> dict:
    try:
        data = json.dumps({"token": token}).encode()
        req = urllib.request.Request(
            f"{PAYMENT_APP_URL}/payment/api/access/internal/{endpoint}",
            data=data,
            headers={"Content-Type": "application/json", "x-internal-secret": TOKEN_INTERNAL_SECRET},
            method="POST",
        )
        with urllib.request.urlopen(req, timeout=3) as resp:
            return json.loads(resp.read())
    except Exception:
        return {"valid": False, "reason": "payment_app_unreachable"}


_SKIP_GATE = {"/health", "/admin", "/upload-cookies", "/service-status"}
_SKIP_PREFIXES = ("/static/", "/admin/")
_DOWNLOAD_PREFIXES = ("/download/", "/file/")


@app.before_request
def _token_gate():
    path = request.path
    if path in _SKIP_GATE or any(path.startswith(p) for p in _SKIP_PREFIXES):
        return

    if not TOKEN_INTERNAL_SECRET:
        return  # gate is disabled if secret not configured

    token = request.cookies.get("access_token") or request.args.get("token", "")

    if not token:
        error_html = ""
        if "token" in request.args:
            error_html = '<p class="err">Token not recognised. Please check and try again.</p>'
        return _GATE_HTML.replace("{payment_url}", ACCESS_PAYMENT_URL).replace("{error_msg}", error_html), 403

    is_download = any(path.startswith(p) for p in _DOWNLOAD_PREFIXES)
    endpoint = "token/use" if is_download else "token/check"
    result = _call_token_api(endpoint, token)

    if not result.get("valid"):
        reason = result.get("reason", "invalid")
        if reason == "exhausted":
            error_html = '<p class="err">Your token has no downloads remaining. Purchase a new one below.</p>'
        else:
            error_html = '<p class="err">Token not recognised. Please check and try again.</p>'
        resp = app.make_response(
            (_GATE_HTML.replace("{payment_url}", ACCESS_PAYMENT_URL).replace("{error_msg}", error_html), 403)
        )
        resp.delete_cookie("access_token")
        return resp

    # Token came in via query param — set cookie and redirect to clean URL
    if request.args.get("token"):
        clean_url = request.path
        if request.query_string:
            params = {k: v for k, v in request.args.items() if k != "token"}
            if params:
                clean_url += "?" + "&".join(f"{k}={v}" for k, v in params.items())
        resp = app.make_response(("", 302))
        resp.headers["Location"] = clean_url
        resp.set_cookie("access_token", token, httponly=True, samesite="Lax", max_age=365 * 24 * 3600)
        return resp


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
    app.run(host=host, port=5055, debug=False, use_reloader=False)
