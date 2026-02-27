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
from flask import Flask, request, jsonify, send_from_directory, send_file, render_template_string, abort, after_this_request
import webbrowser
import argparse
import sys
import zipfile
import base64
import re
import urllib.request
import urllib.error
import tempfile
import shutil

app = Flask(__name__)

DOWNLOAD_DIR = os.path.expanduser("~/Downloads/YT")
os.makedirs(DOWNLOAD_DIR, exist_ok=True)
SOUNDCLOUD_DIR = os.path.join(DOWNLOAD_DIR, "SoundCloud")
os.makedirs(SOUNDCLOUD_DIR, exist_ok=True)
SPOTIFY_DIR = os.path.join(DOWNLOAD_DIR, "Spotify")
SPOTIFY_TRACKS_DIR = os.path.join(SPOTIFY_DIR, "Tracks")
os.makedirs(SPOTIFY_TRACKS_DIR, exist_ok=True)
APPLE_MUSIC_DIR = os.path.join(DOWNLOAD_DIR, "AppleMusic")
APPLE_MUSIC_TRACKS_DIR = os.path.join(APPLE_MUSIC_DIR, "Tracks")
os.makedirs(APPLE_MUSIC_TRACKS_DIR, exist_ok=True)
# Data directory: ~/Library/Application Support/+downloads when frozen, else next to app.py
if getattr(sys, "frozen", False):
    _data_dir = Path(os.path.expanduser("~/Library/Application Support/+downloads"))
else:
    _data_dir = Path(__file__).parent
_data_dir.mkdir(parents=True, exist_ok=True)

HISTORY_PATH = _data_dir / "history.json"
JOBS_PATH    = _data_dir / "jobs.json"
LOG_DIR      = _data_dir / "job-logs"
LOG_DIR.mkdir(exist_ok=True)

_raw_tokens = os.environ.get("YT_UI_TOKEN") or ""
VALID_TOKENS: set = {t.strip() for t in _raw_tokens.split(",") if t.strip()}
MAX_CONCURRENT_JOBS = int(os.environ.get("YT_UI_MAX_CONCURRENT", "3"))
JOB_TTL_SECONDS = int(os.environ.get("YT_UI_JOB_TTL_SECONDS", str(60 * 60)))
FILE_TTL_DAYS = float(os.environ.get("YT_UI_FILE_TTL_DAYS", "0"))  # 0 = disabled
VERSION = "1.3"
COOKIES_PATH = os.environ.get("YT_UI_COOKIES") or ""
COOKIES_PASSWORD = os.environ.get("YT_UI_COOKIES_PASSWORD") or ""
MAX_QUEUE_DEPTH = int(os.environ.get("YT_UI_MAX_QUEUE", "10"))
_LOCAL_HOSTS = {"localhost", "127.0.0.1", "::1"}
SPOTIFY_CLIENT_ID = os.environ.get("SPOTIFY_CLIENT_ID", "")
SPOTIFY_CLIENT_SECRET = os.environ.get("SPOTIFY_CLIENT_SECRET", "")
_spotify_token_cache: dict = {}
_spotify_token_lock = threading.Lock()

# Binary paths — bundled inside .app when frozen, system PATH otherwise
if getattr(sys, "frozen", False):
    _bin_dir = Path(sys._MEIPASS)
    YT_DLP_BIN = str(_bin_dir / "yt-dlp")
    FFMPEG_BIN  = str(_bin_dir / "ffmpeg")
else:
    YT_DLP_BIN = shutil.which("yt-dlp") or "yt-dlp"
    FFMPEG_BIN  = shutil.which("ffmpeg") or "ffmpeg"

jobs = {}  # job_id -> {"status": "...", "log": "...", "file": "...", timestamps}
jobs_lock = threading.RLock()
burn_jobs = {}
burn_lock = threading.Lock()
job_sema = threading.Semaphore(MAX_CONCURRENT_JOBS)
history_lock = threading.Lock()
job_queue = deque()
queue_cv = threading.Condition()

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
      </div>
      <div id="upload-msg"></div>
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
      max-width: 1400px; margin: 0 auto; padding: 24px;
      display: grid; grid-template-columns: 420px 1fr; gap: 20px; align-items: start;
    }
    .left-col { display: flex; flex-direction: column; min-width: 0; }
    .right-col { position: sticky; top: 24px; }
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
    #progressTrack { background: #1a1818; border-radius: 999px; height: 5px; overflow: hidden; }
    #progressBar {
      height: 100%; width: 0%; border-radius: 999px;
      background: linear-gradient(90deg, #db52a6, #bf9b3a); transition: width 0.4s ease;
    }
    #progressBar.indeterminate {
      width: 30%; background: #db52a6; animation: barslide 1.5s infinite ease-in-out;
    }
    @keyframes barslide { 0%{transform:translateX(-200%)} 100%{transform:translateX(500%)} }
    #progressText { font-size: 12px; color: #555; margin-top: 6px; display: block; }
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
    /* Library panel */
    .lib-panel {
      background: #242222; border: 1px solid #2e2c2c; border-radius: 16px;
      overflow: hidden; display: flex; flex-direction: column;
    }
    .lib-top { padding: 18px 18px 0; }
    .lib-tabs { display: flex; gap: 4px; margin-bottom: 12px; }
    .lib-tab {
      background: transparent; border: none; color: #555;
      padding: 7px 16px; border-radius: 8px; font-size: 13px; font-weight: 600;
      cursor: pointer; transition: background 0.15s, color 0.15s;
    }
    .lib-tab.active { background: rgba(219,82,166,0.15); color: #db52a6; }
    .lib-tab:hover:not(.active) { background: #2a2828; color: #888; }
    .lib-search {
      width: 100%; background: #1a1818; border: 1.5px solid #353333; color: #f0eef0;
      padding: 9px 13px; border-radius: 9px; font-size: 13px; outline: none;
      margin-bottom: 12px; transition: border-color 0.2s;
    }
    .lib-search:focus { border-color: #db52a6; }
    .lib-search::placeholder { color: #464444; }
    .lib-list { overflow-y: auto; flex: 1; padding: 8px 10px 12px; min-height: 0; max-height: 360px; }
    .lib-row {
      display: flex; align-items: center; gap: 11px;
      padding: 9px 10px; border-radius: 10px; cursor: pointer;
      transition: background 0.15s; margin-bottom: 2px;
    }
    .lib-row:hover { background: #2a2828; }
    .lib-icon {
      width: 36px; height: 36px; border-radius: 8px; flex-shrink: 0;
      background: rgba(219,82,166,0.12); color: #db52a6;
      display: flex; align-items: center; justify-content: center; font-size: 17px;
    }
    .lib-icon.song  { background: rgba(191,155,58,0.12); color: #bf9b3a; }
    .lib-icon.video { background: rgba(91,155,213,0.12); color: #5b9bd5; }
    .lib-info { flex: 1; min-width: 0; }
    .lib-name { font-size: 13px; color: #c8c0c8; white-space: nowrap; overflow: hidden; text-overflow: ellipsis; }
    .lib-meta { font-size: 11px; color: #4a4848; margin-top: 2px; display: flex; align-items: center; gap: 5px; }
    .lib-empty { font-size: 13px; color: #444; text-align: center; padding: 40px 0; }
    .lib-header-row { display: flex; align-items: center; justify-content: space-between; margin-bottom: 10px; }
    /* Burn card */
    .burn-card-header {
      display: flex; align-items: center; gap: 14px; margin-bottom: 14px;
    }
    .disc-gfx { flex-shrink: 0; }
    .burn-card-title { font-size: 15px; font-weight: 700; color: #f0eef0; }
    .burn-card-subtitle { font-size: 11px; color: #555; margin-top: 3px; }
    .burn-tracklist {
      overflow-y: auto; max-height: 260px; margin: 0 -4px;
      padding: 0 4px;
    }
    .burn-track-row {
      display: flex; align-items: center; gap: 10px;
      padding: 8px 10px; border-radius: 9px; cursor: pointer;
      transition: background 0.15s; margin-bottom: 2px;
    }
    .burn-track-row:hover { background: #2a2828; }
    .burn-track-row input[type=checkbox] { width: 14px; height: 14px; accent-color: #db52a6; flex-shrink: 0; cursor: pointer; }
    .burn-track-icon {
      width: 30px; height: 30px; border-radius: 7px; flex-shrink: 0;
      display: flex; align-items: center; justify-content: center; font-size: 14px;
    }
    .burn-track-icon.album { background: rgba(219,82,166,0.1); color: #db52a6; }
    .burn-track-icon.song  { background: rgba(191,155,58,0.1);  color: #bf9b3a; }
    .burn-track-info { flex: 1; min-width: 0; }
    .burn-track-name { font-size: 13px; color: #c0b8c0; white-space: nowrap; overflow: hidden; text-overflow: ellipsis; }
    .burn-track-meta { font-size: 11px; color: #4a4848; margin-top: 2px; display: flex; gap: 5px; }
    .burn-footer { margin-top: 14px; border-top: 1px solid #2a2828; padding-top: 14px; }
    .burn-cap-wrap { display: flex; align-items: center; gap: 10px; margin-bottom: 12px; }
    .burn-cap-track {
      flex: 1; height: 4px; background: #1a1818; border-radius: 999px; overflow: hidden;
    }
    .burn-cap-fill {
      height: 100%; width: 0%; border-radius: 999px;
      background: linear-gradient(90deg, #db52a6, #bf9b3a); transition: width 0.3s;
    }
    .burn-cap-fill.over { background: #ff6b6b; }
    .burn-cap-label { font-size: 11px; color: #555; white-space: nowrap; }
    .burn-ctrl-row { display: flex; gap: 8px; align-items: center; }
    .burn-mode-sel {
      background: #1a1818; border: 1.5px solid #353333; color: #f0eef0;
      padding: 9px 30px 9px 12px; border-radius: 9px; font-size: 13px;
      flex: 1; cursor: pointer; appearance: none; -webkit-appearance: none;
      background-image: url("data:image/svg+xml,%3Csvg xmlns='http://www.w3.org/2000/svg' width='10' height='6' viewBox='0 0 10 6'%3E%3Cpath d='M1 1l4 4 4-4' stroke='%23555' stroke-width='1.5' fill='none' stroke-linecap='round'/%3E%3C/svg%3E");
      background-repeat: no-repeat; background-position: right 10px center;
    }
    .btn-burn {
      background: #db52a6; color: #fff; border: none; flex-shrink: 0;
      padding: 9px 20px; border-radius: 9px; font-size: 13px; font-weight: 700;
      cursor: pointer; white-space: nowrap; transition: background 0.15s;
    }
    .btn-burn:hover { background: #c9479a; }
    .btn-burn:disabled { background: #2e2c2c; color: #555; cursor: not-allowed; }
    .burn-log {
      margin-top: 10px; background: #141212; border: 1px solid #242222; border-radius: 8px;
      color: #a09aa0; padding: 10px 12px; font-size: 11px; font-family: 'SF Mono', monospace;
      max-height: 110px; overflow-y: auto; white-space: pre-wrap; display: none;
    }
    /* Burn modal */
    .burn-modal-overlay {
      position: fixed; inset: 0; z-index: 300;
      display: flex; align-items: center; justify-content: center;
      background: rgba(12, 10, 10, 0.78);
      backdrop-filter: blur(8px); -webkit-backdrop-filter: blur(8px);
    }
    .burn-modal {
      background: #242222; border: 1px solid #3a3838; border-radius: 18px;
      width: min(540px, 92vw); max-height: 82vh;
      display: flex; flex-direction: column; overflow: hidden;
      box-shadow: 0 32px 80px rgba(0,0,0,0.85), 0 0 0 1px rgba(219,82,166,0.08);
      animation: modalPop 0.2s cubic-bezier(0.34,1.4,0.64,1);
    }
    @keyframes modalPop {
      from { opacity:0; transform: scale(0.88) translateY(16px); }
      to   { opacity:1; transform: scale(1)    translateY(0); }
    }
    .burn-modal-header {
      display: flex; align-items: center; gap: 14px;
      padding: 20px 20px 0;
    }
    .burn-modal-title { font-size: 15px; font-weight: 700; color: #f0eef0; }
    .burn-modal-sub   { font-size: 11px; color: #555; margin-top: 3px; }
    .burn-modal-close {
      margin-left: auto; background: #2e2c2c; border: 1px solid #3a3838; color: #888;
      width: 28px; height: 28px; border-radius: 50%; font-size: 16px; line-height: 1;
      cursor: pointer; display: flex; align-items: center; justify-content: center;
      flex-shrink: 0; transition: background 0.15s, color 0.15s;
    }
    .burn-modal-close:hover { background: #3a3838; color: #f0eef0; }
    .burn-modal-search {
      margin: 14px 20px 0;
      background: #1a1818; border: 1.5px solid #353333; color: #f0eef0;
      padding: 9px 13px; border-radius: 9px; font-size: 13px; outline: none;
      transition: border-color 0.2s;
    }
    .burn-modal-search:focus { border-color: #db52a6; }
    .burn-modal-search::placeholder { color: #464444; }
    .burn-modal-tracklist {
      flex: 1; overflow-y: auto; padding: 10px 12px;
    }
    .burn-modal-track {
      display: flex; align-items: center; gap: 10px;
      padding: 8px 10px; border-radius: 9px; cursor: pointer;
      transition: background 0.12s; margin-bottom: 2px;
    }
    .burn-modal-track:hover { background: #2e2c2c; }
    .burn-modal-track input[type=checkbox] { width: 14px; height: 14px; accent-color: #db52a6; flex-shrink: 0; }
    .burn-modal-track-num { font-size: 11px; color: #4a4848; width: 22px; text-align: right; flex-shrink: 0; }
    .burn-modal-track-name { font-size: 13px; color: #c8c0c8; flex: 1; min-width: 0; white-space: nowrap; overflow: hidden; text-overflow: ellipsis; }
    .burn-modal-footer {
      display: flex; align-items: center; gap: 8px;
      padding: 14px 20px; border-top: 1px solid #2a2828;
    }
    .burn-modal-count { font-size: 12px; color: #555; flex: 1; }
    /* Queue badge on burn list rows */
    .burn-queue-badge {
      font-size: 11px; padding: 3px 9px; border-radius: 999px; flex-shrink: 0;
      background: #252323; color: #555; font-weight: 600; border: 1px solid #353333;
      transition: background 0.2s, color 0.2s, border-color 0.2s;
    }
    .burn-queue-badge.active { background: rgba(219,82,166,0.15); color: #db52a6; border-color: rgba(219,82,166,0.3); }
    /* Burn queue list */
    .burn-queue-section { margin-top: 14px; border-top: 1px solid #2a2828; padding-top: 12px; }
    .burn-queue-header { display: flex; align-items: center; justify-content: space-between; margin-bottom: 8px; }
    .burn-queue-label { font-size: 11px; font-weight: 700; color: #444; text-transform: uppercase; letter-spacing: 1px; }
    .burn-queue-count { font-size: 11px; color: #555; }
    .burn-queue-list { overflow-y: auto; max-height: 180px; }
    .burn-queue-empty { font-size: 12px; color: #383636; text-align: center; padding: 18px 0; }
    .burn-queue-item { display: flex; align-items: center; gap: 8px; padding: 5px 8px; border-radius: 7px; transition: background 0.12s; }
    .burn-queue-item:hover { background: #2a2828; }
    .burn-queue-num { font-size: 11px; color: #4a4848; width: 22px; text-align: right; flex-shrink: 0; }
    .burn-queue-name { font-size: 12px; color: #b0a8b0; flex: 1; min-width: 0; white-space: nowrap; overflow: hidden; text-overflow: ellipsis; }
    .burn-queue-rm { background: transparent; border: none; color: #3e3c3c; cursor: pointer; padding: 2px 6px; border-radius: 5px; font-size: 15px; flex-shrink: 0; transition: color 0.15s; line-height: 1; }
    .burn-queue-rm:hover { color: #ff6b6b; }
    ::-webkit-scrollbar { width: 5px; }
    ::-webkit-scrollbar-track { background: transparent; }
    ::-webkit-scrollbar-thumb { background: #353333; border-radius: 3px; }

    /* ── Tablet ────────────────────────────────────────────── */
    @media (max-width: 900px) {
      .main { grid-template-columns: 1fr; padding: 14px; }
      .right-col { position: static; top: auto; }
      .lib-list  { max-height: 280px; }
      .burn-tracklist { max-height: 200px; }
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

      /* History rows — wrap action buttons below title */
      .hist-row  { flex-wrap: wrap; }
      .hist-btns { width: 100%; justify-content: flex-end; margin-top: 6px; }

      /* Library */
      .lib-list       { max-height: 220px; }
      .lib-tabs button { padding: 6px 12px; font-size: 12px; }

      /* Burn card */
      .burn-tracklist  { max-height: 160px; }
      .burn-queue-list { max-height: 110px; }
      .burn-ctrl-row   { flex-wrap: wrap; }
      .btn-burn        { width: 100%; margin-top: 6px; }

      /* Status log */
      pre#log { font-size: 11px; max-height: 160px; }
    }
  </style>
</head>
<body>
  <header class="header">
    <span class="logo">+downloads</span>
    <span class="version-badge">v{{version}}</span>
  </header>
  <main class="main">
  <div class="left-col">
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
        <button class="btn-secondary" onclick="openFolder()">Open Folder</button>
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
      <details style="margin-top:14px;">
        <summary style="font-size:12px; color:#444; cursor:pointer; list-style:none; display:flex; align-items:center; gap:5px; user-select:none;">
          <span id="tokenChevron" style="font-size:10px; transition:transform 0.2s;">&#9654;</span>
          <span>Advanced</span>
        </summary>
        <div style="margin-top:12px;">
          <div class="token-row">
            <input id="token" type="text" placeholder="Optional bearer token (YT_UI_TOKEN)" />
            <button class="btn-ghost" onclick="saveToken()">Save token</button>
          </div>
          <p class="dir-label" style="margin-top:10px;">Downloads to: <b>{{download_dir}}</b></p>
        </div>
      </details>
    </div>

    <div class="card">
      <div class="status-row">
        <span id="statusPill">idle</span>
        <span id="queuePos"></span>
        <button onclick="cancel()" id="cancelBtn" class="btn-cancel" style="display:none;">Cancel</button>
      </div>
      <div id="progressWrap">
        <div id="progressTrack"><div id="progressBar"></div></div>
        <small id="progressText"></small>
      </div>
      <pre id="log">Idle…</pre>
      <div id="meta"></div>
    </div>

    <div class="card">
      <div class="section-label" style="margin-bottom:12px;">History</div>
      <div id="historyPreview"></div>
      <details id="historyDetails" style="margin-top:8px;">
        <summary style="font-size:12px; color:#444; cursor:pointer; list-style:none; display:flex; align-items:center; gap:5px; user-select:none; margin-top:4px;">
          <span id="histChevron" style="font-size:10px; transition:transform 0.2s;">&#9654;</span>
          <span>View all</span>
        </summary>
        <div id="history" style="margin-top:14px;"></div>
      </details>
    </div>
  </div><!-- /left-col -->

  <div class="right-col">
    <div class="lib-panel">
      <div class="lib-top">
        <div class="lib-header-row">
          <div class="lib-tabs">
            <button class="lib-tab active" data-tab="albums" onclick="switchLibTab('albums')">Albums</button>
            <button class="lib-tab" data-tab="songs" onclick="switchLibTab('songs')">Songs</button>
            <button class="lib-tab" data-tab="videos" onclick="switchLibTab('videos')">Videos</button>
          </div>
        </div>
        <input id="libSearch" class="lib-search" type="text" placeholder="Search library…" oninput="renderLibrary()" />
      </div>
      <div class="lib-list" id="libContent"></div>
    </div>

    <!-- Download full version -->
    <a href="http://urapages.com/downloads/app" target="_blank" rel="noopener noreferrer"
       style="display:flex; flex-direction:column; align-items:center; justify-content:center;
              gap:10px; margin-top:16px; padding:28px 18px;
              background:#1a1a1a; border:1px solid #2a2a2a; border-radius:12px;
              text-decoration:none; cursor:pointer; transition:border-color 0.15s;"
       onmouseover="this.style.borderColor='#e03c8a'" onmouseout="this.style.borderColor='#2a2a2a'">
      <svg width="72" height="72" viewBox="0 0 24 24" fill="none" xmlns="http://www.w3.org/2000/svg">
        <path d="M3 7C3 5.9 3.9 5 5 5H10L12 7H19C20.1 7 21 7.9 21 9V17C21 18.1 20.1 19 19 19H5C3.9 19 3 18.1 3 17V7Z" fill="#e03c8a"/>
        <path d="M12 10V15M12 15L9.5 12.5M12 15L14.5 12.5" stroke="#fff" stroke-width="1.5" stroke-linecap="round" stroke-linejoin="round"/>
      </svg>
      <div style="text-align:center; line-height:1.4;">
        <div style="font-size:15px; font-weight:700; color:#f0f0f0;">+downloads</div>
        <div style="font-size:13px; font-weight:400; color:#aaa;">full version</div>
      </div>
    </a>

    <!-- Burn a CD card -->
    <div class="card" style="margin-top:16px;">
      <div class="burn-card-header">
        <div class="disc-gfx">
          <svg width="52" height="52" viewBox="0 0 52 52" xmlns="http://www.w3.org/2000/svg">
            <defs>
              <radialGradient id="discBody" cx="38%" cy="30%" r="70%">
                <stop offset="0%" stop-color="#4e4c4c"/>
                <stop offset="45%" stop-color="#2e2c2c"/>
                <stop offset="100%" stop-color="#1a1818"/>
              </radialGradient>
              <linearGradient id="sheen" x1="0%" y1="0%" x2="100%" y2="110%">
                <stop offset="0%"   stop-color="rgba(219,82,166,0.45)"/>
                <stop offset="28%"  stop-color="rgba(191,155,58,0.3)"/>
                <stop offset="58%"  stop-color="rgba(91,155,213,0.25)"/>
                <stop offset="100%" stop-color="rgba(72,199,142,0.2)"/>
              </linearGradient>
              <radialGradient id="hubGrad" cx="45%" cy="38%" r="65%">
                <stop offset="0%" stop-color="#3a3838"/>
                <stop offset="100%" stop-color="#1c1a1a"/>
              </radialGradient>
            </defs>
            <circle cx="26" cy="26" r="24" fill="url(#discBody)" stroke="#3a3838" stroke-width="1.2"/>
            <circle cx="26" cy="26" r="24" fill="url(#sheen)"/>
            <circle cx="26" cy="26" r="19.5" fill="none" stroke="rgba(255,255,255,0.055)" stroke-width="3"/>
            <circle cx="26" cy="26" r="15"   fill="none" stroke="rgba(255,255,255,0.04)"  stroke-width="2.5"/>
            <circle cx="26" cy="26" r="11"   fill="none" stroke="rgba(255,255,255,0.03)"  stroke-width="2"/>
            <circle cx="26" cy="26" r="8"  fill="url(#hubGrad)" stroke="#404040" stroke-width="0.8"/>
            <circle cx="26" cy="26" r="3.2" fill="#0f0d0d"/>
          </svg>
        </div>
        <div style="flex:1; min-width:0;">
          <div class="burn-card-title">Burn a CD</div>
          <div class="burn-card-subtitle" id="burnerStatus">Checking for optical drive…</div>
        </div>
        <div style="display:flex; gap:6px;">
          <button class="hist-btn" onclick="selectAllBurn()">All</button>
          <button class="hist-btn" onclick="clearBurnSelection()">Clear</button>
        </div>
      </div>
      <div class="burn-tracklist" id="burnTrackList">
        <div class="lib-empty">No downloads yet.</div>
      </div>
      <div class="burn-queue-section" id="burnQueueSection">
        <div class="burn-queue-header">
          <span class="burn-queue-label">Queue</span>
          <span class="burn-queue-count" id="burnQueueCount">0 tracks</span>
        </div>
        <div class="burn-queue-list" id="burnQueueList">
          <div class="burn-queue-empty">No tracks queued yet.</div>
        </div>
      </div>
      <div class="burn-footer">
        <div class="burn-cap-wrap">
          <div class="burn-cap-track"><div class="burn-cap-fill" id="burnCapFill"></div></div>
          <span class="burn-cap-label" id="burnCapLabel">0 / 74 min</span>
        </div>
        <div class="burn-ctrl-row">
          <select class="burn-mode-sel" id="burnMode">
            <option value="data">Data CD  ·  MP3</option>
            <option value="audio">Audio CD  ·  AIFF</option>
          </select>
          <button class="btn-burn" id="burnBtn" onclick="doBurn()" disabled>Burn CD</button>
        </div>
        <div class="burn-log" id="burnLog"></div>
      </div>
    </div>
  </div><!-- /right-col -->

  </main>

  <!-- Burn tracklist modal -->
  <div class="burn-modal-overlay" id="burnModalOverlay" style="display:none;" onclick="closeBurnModalOutside(event)">
    <div class="burn-modal">
      <div class="burn-modal-header">
        <svg width="36" height="36" viewBox="0 0 52 52" xmlns="http://www.w3.org/2000/svg" style="flex-shrink:0;">
          <defs>
            <radialGradient id="mDiscBody" cx="38%" cy="30%" r="70%">
              <stop offset="0%" stop-color="#4e4c4c"/><stop offset="45%" stop-color="#2e2c2c"/><stop offset="100%" stop-color="#1a1818"/>
            </radialGradient>
            <linearGradient id="mSheen" x1="0%" y1="0%" x2="100%" y2="110%">
              <stop offset="0%" stop-color="rgba(219,82,166,0.45)"/><stop offset="28%" stop-color="rgba(191,155,58,0.3)"/>
              <stop offset="58%" stop-color="rgba(91,155,213,0.25)"/><stop offset="100%" stop-color="rgba(72,199,142,0.2)"/>
            </linearGradient>
          </defs>
          <circle cx="26" cy="26" r="24" fill="url(#mDiscBody)" stroke="#3a3838" stroke-width="1.2"/>
          <circle cx="26" cy="26" r="24" fill="url(#mSheen)"/>
          <circle cx="26" cy="26" r="19.5" fill="none" stroke="rgba(255,255,255,0.055)" stroke-width="3"/>
          <circle cx="26" cy="26" r="14"   fill="none" stroke="rgba(255,255,255,0.04)"  stroke-width="2.5"/>
          <circle cx="26" cy="26" r="8" fill="#1c1a1a" stroke="#404040" stroke-width="0.8"/>
          <circle cx="26" cy="26" r="3.2" fill="#0f0d0d"/>
        </svg>
        <div>
          <div class="burn-modal-title" id="burnModalTitle">Album</div>
          <div class="burn-modal-sub"   id="burnModalSub"></div>
        </div>
        <button class="burn-modal-close" onclick="closeBurnModal()">&#10005;</button>
      </div>
      <input class="burn-modal-search" id="burnModalSearch" type="text" placeholder="Search tracks…" oninput="filterModalTracks()" />
      <div class="burn-modal-tracklist" id="burnModalTracks"></div>
      <div class="burn-modal-footer">
        <button class="hist-btn" onclick="selectAllModal()">All</button>
        <button class="hist-btn" onclick="clearModal()">Clear</button>
        <span class="burn-modal-count" id="burnModalCount"></span>
        <button class="btn-burn" id="burnModalAddBtn" onclick="addModalToQueue()" disabled>Add to Queue</button>
      </div>
    </div>
  </div>

  <!-- Token gate modal -->
  <div id="tokenModal" style="display:none; position:fixed; inset:0; background:rgba(12,10,10,0.82); backdrop-filter:blur(8px); -webkit-backdrop-filter:blur(8px); z-index:1000; align-items:center; justify-content:center; padding:16px;">
    <div class="card" style="width:100%; max-width:360px; box-shadow:0 32px 80px rgba(0,0,0,0.85); animation:modalPop 0.2s cubic-bezier(0.34,1.4,0.64,1);">
      <h2 style="margin:0 0 6px; font-size:18px; font-weight:800; color:#f0eef0; letter-spacing:-0.3px;">Enter your token</h2>
      <p style="margin:0 0 18px; font-size:13px; color:#555; line-height:1.5;">A token is required to use this app.</p>
      <input id="tokenModalInput" type="text" placeholder="Bearer token" autocomplete="off"
        style="width:100%; display:block; margin-bottom:12px; flex:none;"
        onkeydown="if(event.key==='Enter') submitTokenModal();" />
      <button onclick="submitTokenModal()" class="btn-primary" style="width:100%; margin:0; display:block;">Submit</button>
    </div>
  </div>

<script>
const IS_LOCAL = {{ 'true' if is_local else 'false' }};
let currentJob = null;
let savedToken = sessionStorage.getItem("yt_token") || "";

function showTokenModal() {
  const m = document.getElementById('tokenModal');
  m.style.display = 'flex';
  document.getElementById('tokenModalInput').focus();
}
function hideTokenModal() {
  document.getElementById('tokenModal').style.display = 'none';
}
function submitTokenModal() {
  const val = document.getElementById('tokenModalInput').value.trim();
  if (!val) return;
  savedToken = val;
  sessionStorage.setItem("yt_token", savedToken);
  document.getElementById('token').value = savedToken;
  hideTokenModal();
}
if (!IS_LOCAL && !savedToken) showTokenModal();

function escHtml(s) {
  return String(s == null ? '' : s)
    .replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;')
    .replace(/"/g,'&quot;').replace(/'/g,'&#39;');
}
let libData = { albums: [], songs: [], videos: [] };
let activeLibTab = 'albums';

function categorizeLibrary(items) {
  const albums = [], songs = [], videos = [];
  (items || []).filter(i => i.final_status === 'done').forEach(item => {
    if (item.type === 'video') {
      const path = item.output_path || (item.output_paths && item.output_paths[0]) || '';
      const filename = path.split('/').pop() || item.title || 'Unknown';
      videos.push({ ...item, videoName: item.title || filename.replace(/\.[^.]+$/, '') });
      return;
    }
    const multi = item.output_paths && item.output_paths.length > 1;
    if (multi) {
      const parts = item.output_paths[0].split('/');
      const folder = parts[parts.length - 2] || 'Unknown Album';
      albums.push({ ...item, albumName: folder });
    } else {
      const path = item.output_path || (item.output_paths && item.output_paths[0]) || '';
      const filename = path.split('/').pop() || item.title || 'Unknown';
      songs.push({ ...item, songName: item.title || filename });
    }
  });
  libData = { albums, songs, videos };
}

function switchLibTab(tab) {
  activeLibTab = tab;
  document.querySelectorAll('.lib-tab').forEach(t =>
    t.classList.toggle('active', t.dataset.tab === tab));
  renderLibrary();
}

function renderLibrary() {
  const q = (document.getElementById('libSearch').value || '').toLowerCase();
  const container = document.getElementById('libContent');
  container.innerHTML = '';
  const tabMap = { albums: libData.albums, songs: libData.songs, videos: libData.videos };
  const items = tabMap[activeLibTab] || [];
  const getName = item => activeLibTab === 'albums' ? item.albumName
                        : activeLibTab === 'songs'  ? item.songName
                        : item.videoName;
  const filtered = items.filter(item => {
    const name = getName(item);
    return !q || (name || '').toLowerCase().includes(q) || (item.type || '').includes(q);
  });
  if (!filtered.length) {
    container.innerHTML = '<div class="lib-empty">Nothing here yet.</div>';
    return;
  }
  filtered.forEach(item => {
    const row = document.createElement('div');
    row.className = 'lib-row';
    const icon = document.createElement('div');
    const iconClass = activeLibTab === 'songs' ? ' song' : activeLibTab === 'videos' ? ' video' : '';
    icon.className = 'lib-icon' + iconClass;
    icon.textContent = activeLibTab === 'albums' ? '\u266b'
                     : activeLibTab === 'songs'  ? '\u266a'
                     : '\u25b6';
    const info = document.createElement('div');
    info.className = 'lib-info';
    const name = document.createElement('div');
    name.className = 'lib-name';
    name.textContent = getName(item);
    const meta = document.createElement('div');
    meta.className = 'lib-meta';
    const tag = document.createElement('span');
    tag.className = 'hist-tag';
    tag.textContent = item.type;
    const ts = document.createElement('span');
    ts.textContent = (item.timestamp || '').split('T')[0];
    if (activeLibTab === 'albums') {
      const cnt = document.createElement('span');
      cnt.textContent = item.output_paths.length + ' tracks';
      meta.append(tag, cnt, ts);
    } else {
      meta.append(tag, ts);
    }
    info.append(name, meta);
    const btns = document.createElement('div');
    btns.className = 'hist-btns';
    const revealPath = activeLibTab === 'albums'
      ? item.output_paths[0]
      : (item.output_path || (item.output_paths && item.output_paths[0]) || '');
    if (IS_LOCAL) {
      const revBtn = document.createElement('button');
      revBtn.className = 'hist-btn';
      revBtn.textContent = 'Reveal';
      revBtn.onclick = e => { e.stopPropagation(); reveal(revealPath); };
      btns.appendChild(revBtn);
    } else if (activeLibTab !== 'albums' && item.job_id) {
      const dlBtn = document.createElement('button');
      dlBtn.className = 'hist-btn';
      dlBtn.textContent = 'Download';
      dlBtn.onclick = e => { e.stopPropagation(); window.location.href = '/file/' + item.job_id + (savedToken ? '?token=' + encodeURIComponent(savedToken) : ''); };
      btns.appendChild(dlBtn);
    }
    if (activeLibTab === 'albums' && item.job_id) {
      const zipBtn = document.createElement('button');
      zipBtn.className = 'hist-btn';
      zipBtn.textContent = 'ZIP';
      zipBtn.onclick = e => { e.stopPropagation(); window.location.href = '/download/' + item.job_id + (savedToken ? '?token=' + encodeURIComponent(savedToken) : ''); };
      btns.appendChild(zipBtn);
    }
    row.onclick = () => reveal(revealPath);
    row.append(icon, info, btns);
    container.appendChild(row);
  });
}

// ── Burn a CD ─────────────────────────────────────────────────────────────────
let burnPaths = [];
let activeBurnId = null;
let modalItem = null;
let modalSelected = new Set();

function openBurnModal(item) {
  modalItem = item;
  const paths = item._kind === 'album'
    ? (item.output_paths || [])
    : [item.output_path || (item.output_paths && item.output_paths[0]) || ''];
  // Pre-check paths already in burn queue
  modalSelected = new Set(paths.filter(p => burnPaths.includes(p)));
  document.getElementById('burnModalTitle').textContent = item._kind === 'album' ? item.albumName : item.songName;
  document.getElementById('burnModalSub').textContent =
    item.type + (item._kind === 'album' ? ' \u00b7 ' + paths.length + ' tracks' : ' \u00b7 single');
  document.getElementById('burnModalSearch').value = '';
  renderModalTracks('');
  document.getElementById('burnModalOverlay').style.display = 'flex';
}

function filterModalTracks() {
  renderModalTracks(document.getElementById('burnModalSearch').value);
}

function renderModalTracks(query) {
  const q = (query || '').toLowerCase();
  const container = document.getElementById('burnModalTracks');
  container.innerHTML = '';
  const paths = modalItem._kind === 'album'
    ? (modalItem.output_paths || [])
    : [modalItem.output_path || (modalItem.output_paths && modalItem.output_paths[0]) || ''];
  const filtered = paths.map((p, i) => ({ p, i, name: p.split('/').pop().replace(/\.[^.]+$/, '') }))
    .filter(t => !q || t.name.toLowerCase().includes(q));
  if (!filtered.length) {
    container.innerHTML = '<div class="lib-empty" style="padding:24px 0;">No tracks match.</div>';
    updateModalCount();
    return;
  }
  filtered.forEach(({ p, i, name }) => {
    const row = document.createElement('div');
    row.className = 'burn-modal-track';
    const cb = document.createElement('input');
    cb.type = 'checkbox';
    cb.checked = modalSelected.has(p);
    const toggle = () => {
      if (cb.checked) modalSelected.add(p); else modalSelected.delete(p);
      updateModalCount();
    };
    cb.onchange = e => { e.stopPropagation(); toggle(); };
    row.onclick = () => { cb.checked = !cb.checked; toggle(); };
    const num = document.createElement('span');
    num.className = 'burn-modal-track-num';
    num.textContent = String(i + 1).padStart(2, '0');
    const lbl = document.createElement('span');
    lbl.className = 'burn-modal-track-name';
    lbl.textContent = name;
    row.append(cb, num, lbl);
    container.appendChild(row);
  });
  updateModalCount();
}

function updateModalCount() {
  const n = modalSelected.size;
  document.getElementById('burnModalCount').textContent =
    n === 0 ? 'No tracks selected' : n + ' track' + (n !== 1 ? 's' : '') + ' selected';
  document.getElementById('burnModalAddBtn').disabled = n === 0;
}

function selectAllModal() {
  const paths = modalItem._kind === 'album'
    ? (modalItem.output_paths || [])
    : [modalItem.output_path || (modalItem.output_paths && modalItem.output_paths[0]) || ''];
  paths.forEach(p => modalSelected.add(p));
  renderModalTracks(document.getElementById('burnModalSearch').value);
}

function clearModal() {
  modalSelected.clear();
  renderModalTracks(document.getElementById('burnModalSearch').value);
}

function addModalToQueue() {
  modalSelected.forEach(p => { if (p && !burnPaths.includes(p)) burnPaths.push(p); });
  updateBurnFooter();
  renderBurnTrackList();
  closeBurnModal();
}

function closeBurnModal() {
  document.getElementById('burnModalOverlay').style.display = 'none';
  modalItem = null;
  modalSelected.clear();
}

function closeBurnModalOutside(e) {
  if (e.target === document.getElementById('burnModalOverlay')) closeBurnModal();
}

function renderBurnTrackList() {
  const container = document.getElementById('burnTrackList');
  container.innerHTML = '';
  const all = [
    ...libData.albums.map(a => ({ ...a, _kind: 'album' })),
    ...libData.songs.map(s => ({ ...s, _kind: 'song' })),
  ];
  if (!all.length) {
    container.innerHTML = '<div class="lib-empty">No downloads yet.</div>';
    return;
  }
  all.forEach(item => {
    const paths = item._kind === 'album'
      ? (item.output_paths || [])
      : [item.output_path || (item.output_paths && item.output_paths[0]) || ''];
    const label = item._kind === 'album' ? item.albumName : item.songName;
    const inQueue = paths.filter(p => burnPaths.includes(p)).length;
    const row = document.createElement('div');
    row.className = 'burn-track-row';
    row.onclick = () => openBurnModal(item);
    const ico = document.createElement('div');
    ico.className = 'burn-track-icon ' + item._kind;
    ico.textContent = item._kind === 'album' ? '\u266b' : '\u266a';
    const info = document.createElement('div');
    info.className = 'burn-track-info';
    const nm = document.createElement('div');
    nm.className = 'burn-track-name';
    nm.textContent = label;
    const mt = document.createElement('div');
    mt.className = 'burn-track-meta';
    const tag = document.createElement('span');
    tag.className = 'hist-tag';
    tag.textContent = item.type;
    mt.appendChild(tag);
    if (item._kind === 'album') {
      const cnt = document.createElement('span');
      cnt.textContent = paths.length + ' tracks';
      mt.appendChild(cnt);
    }
    info.append(nm, mt);
    const badge = document.createElement('div');
    badge.className = 'burn-queue-badge' + (inQueue > 0 ? ' active' : '');
    badge.textContent = inQueue > 0 ? inQueue + '/' + paths.length : '\u2795';
    row.append(ico, info, badge);
    container.appendChild(row);
  });
}

function renderBurnQueue() {
  const list = document.getElementById('burnQueueList');
  const countEl = document.getElementById('burnQueueCount');
  const n = burnPaths.length;
  countEl.textContent = n + ' track' + (n !== 1 ? 's' : '');
  if (n === 0) {
    list.innerHTML = '<div class="burn-queue-empty">No tracks queued yet.</div>';
    return;
  }
  list.innerHTML = '';
  burnPaths.forEach((p, i) => {
    const name = p.split('/').pop().replace(/\.[^.]+$/, '');
    const item = document.createElement('div');
    item.className = 'burn-queue-item';
    const num = document.createElement('span');
    num.className = 'burn-queue-num';
    num.textContent = String(i + 1).padStart(2, '0');
    const lbl = document.createElement('span');
    lbl.className = 'burn-queue-name';
    lbl.textContent = name;
    const rm = document.createElement('button');
    rm.className = 'burn-queue-rm';
    rm.textContent = '\u00d7';
    rm.title = 'Remove';
    rm.onclick = () => {
      burnPaths.splice(i, 1);
      renderBurnQueue();
      renderBurnTrackList();
      updateBurnFooter();
    };
    item.append(num, lbl, rm);
    list.appendChild(item);
  });
}

function updateBurnFooter() {
  const n = burnPaths.length;
  const mins = n * 4;
  const pct = Math.min((mins / 74) * 100, 100);
  const fill = document.getElementById('burnCapFill');
  fill.style.width = pct + '%';
  fill.className = 'burn-cap-fill' + (mins > 74 ? ' over' : '');
  document.getElementById('burnCapLabel').textContent = mins + ' / 74 min (est.)';
  document.getElementById('burnBtn').disabled = n === 0;
  renderBurnQueue();
}

function selectAllBurn() {
  burnPaths = [];
  [...libData.albums, ...libData.songs].forEach(item => {
    const paths = item.output_paths && item.output_paths.length > 1
      ? item.output_paths
      : [item.output_path || (item.output_paths && item.output_paths[0]) || ''];
    paths.forEach(p => { if (p && !burnPaths.includes(p)) burnPaths.push(p); });
  });
  renderBurnTrackList();
  updateBurnFooter();
}

function clearBurnSelection() {
  burnPaths = [];
  renderBurnTrackList();
  updateBurnFooter();
}

async function doBurn() {
  if (!burnPaths.length) return;
  const mode = document.getElementById('burnMode').value;
  const log = document.getElementById('burnLog');
  const btn = document.getElementById('burnBtn');
  log.style.display = 'block';
  log.textContent = 'Starting burn job…';
  btn.disabled = true;
  const headers = {'Content-Type': 'application/json'};
  if (savedToken) headers['Authorization'] = 'Bearer ' + savedToken;
  const res = await fetch('/burn-cd', {
    method: 'POST', headers,
    body: JSON.stringify({ paths: burnPaths, mode })
  });
  const data = await res.json();
  if (!res.ok) { log.textContent = data.error || 'Failed to start burn'; btn.disabled = false; return; }
  activeBurnId = data.burn_id;
  pollBurn();
}

async function pollBurn() {
  if (!activeBurnId) return;
  const headers = {};
  if (savedToken) headers['Authorization'] = 'Bearer ' + savedToken;
  const res = await fetch('/burn-status/' + activeBurnId, {headers});
  const data = await res.json();
  const log = document.getElementById('burnLog');
  log.textContent = data.log || '';
  log.scrollTop = log.scrollHeight;
  if (data.status === 'done' || data.status === 'error') {
    document.getElementById('burnBtn').disabled = false;
    activeBurnId = null;
    return;
  }
  setTimeout(pollBurn, 1500);
}

async function checkBurner() {
  const headers = {};
  if (savedToken) headers['Authorization'] = 'Bearer ' + savedToken;
  try {
    const res = await fetch('/check-burner', {headers});
    const data = await res.json();
    const el = document.getElementById('burnerStatus');
    el.textContent = data.available ? 'Optical drive detected' : 'No optical drive found';
    el.style.color = data.available ? '#48c78e' : '#ff6b6b';
  } catch(e) {}
}

async function fetchLibrary() {
  const headers = {};
  if (savedToken) headers['Authorization'] = 'Bearer ' + savedToken;
  const res = await fetch('/history?limit=500', {headers});
  if (!res.ok) return;
  const data = await res.json();
  categorizeLibrary(data.items);
  try {
    localStorage.setItem('yt_lib_cache', JSON.stringify({ts: Date.now(), data: libData}));
  } catch(e) {}
  renderLibrary();
  renderBurnTrackList();
  updateBurnFooter();
}
document.getElementById("token").value = savedToken;
document.querySelectorAll('details').forEach(function(el) {
  el.addEventListener('toggle', function() {
    const chevronId = this.querySelector('summary span[id]').id;
    document.getElementById(chevronId).style.transform = this.open ? 'rotate(90deg)' : '';
    if (this.id === 'historyDetails' && this.open) fetchFullHistory();
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
  if (!IS_LOCAL && !savedToken) { showTokenModal(); return; }
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
  const headers = {'Content-Type':'application/json'};
  if (savedToken) headers['Authorization'] = 'Bearer ' + savedToken;
  document.getElementById('log').textContent = "Starting\u2026";
  document.getElementById('meta').textContent = "";
  const res = await fetch('/start', {
    method: 'POST',
    headers,
    body: JSON.stringify({url, type, sc_quality: scQuality, sc_playlist: scPlaylist})
  });
  if (!res.ok) {
    const err = await res.json().catch(() => ({}));
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
  const headers = {};
  if (savedToken) headers['Authorization'] = 'Bearer ' + savedToken;
  const res = await fetch('/status/' + currentJob, {headers});
  const data = await res.json();
  document.getElementById('log').textContent = data.log || data.status;
  setStatus(data.status, data.queue_position);
  updateProgress(data.status, data.log || '', data);
  if ((data.type === 'spotify' || data.type === 'apple_music') && data.total_items > 0) {
    const done = data.current_index || 0;
    const tot = data.total_items;
    const n = (data.output_paths || []).length;
    let meta = done + '/' + tot + ' tracks';
    if (data.status === 'done' && n > 0) {
      meta += ' \u2014 <a href="/download/' + currentJob + (savedToken ? '?token=' + encodeURIComponent(savedToken) : '') + '" target="_blank">Download ZIP</a>';
    }
    meta += ' | <a href="/job-log/' + currentJob + '?tail=200" target="_blank">View log</a>';
    document.getElementById('meta').innerHTML = meta;
  } else if (data.output_paths && data.output_paths.length > 1) {
    const n = data.output_paths.length;
    document.getElementById('meta').innerHTML =
      n + ' files \u2014 <a href="/download/' + currentJob + (savedToken ? '?token=' + encodeURIComponent(savedToken) : '') + '" target="_blank">Download ZIP</a>'
      + ' | <a href="/job-log/' + currentJob + '?tail=200" target="_blank">View full log</a>';
  } else if (data.file || data.output_path) {
    const name = data.file || data.output_path.split('/').pop();
    document.getElementById('meta').innerHTML =
      'File: <a href="/download/' + currentJob + (savedToken ? '?token=' + encodeURIComponent(savedToken) : '') + '" target="_blank">' + escHtml(name) + '</a>'
      + ' | <a href="/job-log/' + currentJob + '?tail=200" target="_blank">View full log</a>';
  }
  if (data.status === "done") {
    document.getElementById('cancelBtn').style.display = 'none';
    fetchHistory(); fetchLibrary();
    setTimeout(resetUI, 3000);
    return;
  }
  if (data.status === "error" || data.status === "cancelled") {
    document.getElementById('cancelBtn').style.display = 'none';
    fetchHistory(); fetchLibrary();
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
  if (status === 'queued') {
    wrap.style.display = 'block';
    bar.className = '';
    bar.style.width = '0%';
    text.textContent = 'Queued…';
  } else if (status === 'running') {
    wrap.style.display = 'block';
    if (data && (data.type === 'spotify' || data.type === 'apple_music') && data.total_items > 0) {
      const pct = data.progress_pct || 0;
      const cur = (data.current_index || 0) + 1;
      const tot = data.total_items;
      bar.className = '';
      bar.style.width = pct + '%';
      text.textContent = cur + ' / ' + tot + ' tracks';
    } else {
      const pct = extractPercent(log);
      if (pct !== null) {
        bar.className = '';
        bar.style.width = pct + '%';
        text.textContent = pct.toFixed(1) + '%';
      } else {
        bar.className = 'indeterminate';
        bar.style.width = '';
        text.textContent = 'Processing…';
      }
    }
  } else if (status === 'done') {
    wrap.style.display = 'block';
    bar.className = '';
    bar.style.width = '100%';
    text.textContent = 'Done';
  } else {
    wrap.style.display = 'none';
    bar.className = '';
    bar.style.width = '0%';
    text.textContent = '';
  }
}

function resetUI() {
  currentJob = null;
  document.getElementById('url').value = '';
  document.getElementById('log').textContent = 'Idle…';
  document.getElementById('meta').innerHTML = '';
  document.getElementById('progressWrap').style.display = 'none';
  document.getElementById('progressBar').style.width = '0%';
  document.getElementById('progressText').textContent = '';
  setStatus('idle', null);
}

function saveToken() {
  savedToken = document.getElementById('token').value.trim();
  sessionStorage.setItem("yt_token", savedToken);
}

async function openFolder() {
  const headers = {};
  if (savedToken) headers['Authorization'] = 'Bearer ' + savedToken;
  await fetch('/open-folder', {headers});
}

function setStatus(status, queuePos) {
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
  pos.textContent = status === 'queued' && queuePos != null ? 'Position in queue: ' + (queuePos + 1) : '';
}

async function cancel() {
  if (!currentJob) return;
  const headers = {'Content-Type':'application/json'};
  if (savedToken) headers['Authorization'] = 'Bearer ' + savedToken;
  await fetch('/cancel', {
    method: 'POST',
    headers,
    body: JSON.stringify({job_id: currentJob})
  });
  poll();
}

function buildHistoryList(items) {
  const list = document.createElement('div');
  items.forEach(item => {
    const row = document.createElement('div');
    row.className = 'hist-row';
    const left = document.createElement('div');
    left.className = 'hist-left';
    const multi = item.output_paths && item.output_paths.length > 1;
    const mainLabel = multi
      ? (item.output_paths.length + ' files')
      : (item.title || (item.output_path ? item.output_path.split('/').pop() : item.url || ''));
    const statusCls = 'hist-status ' + (item.final_status || 'cancelled');
    left.innerHTML =
      '<div class="hist-main">' + escHtml(mainLabel || item.url || '') + '</div>'
      + '<div class="hist-sub">'
      + '<span class="hist-tag">' + escHtml(item.type) + '</span>'
      + '<span class="' + escHtml(statusCls) + '">' + escHtml(item.final_status || '') + '</span>'
      + '<span>' + escHtml(item.timestamp) + '</span>'
      + '</div>';
    const right = document.createElement('div');
    right.className = 'hist-btns';
    if (multi) {
      if (IS_LOCAL) {
        const revealBtn = document.createElement('button');
        revealBtn.className = 'hist-btn';
        revealBtn.textContent = 'Reveal';
        revealBtn.onclick = () => reveal(item.output_paths[0]);
        right.appendChild(revealBtn);
      }
      if (item.job_id) {
        const zipBtn = document.createElement('button');
        zipBtn.className = 'hist-btn';
        zipBtn.textContent = 'ZIP';
        zipBtn.onclick = () => { window.location.href = '/download/' + item.job_id + (savedToken ? '?token=' + encodeURIComponent(savedToken) : ''); };
        right.appendChild(zipBtn);
      }
    } else {
      if (IS_LOCAL) {
        const btn = document.createElement('button');
        btn.className = 'hist-btn';
        btn.textContent = 'Reveal';
        btn.onclick = () => reveal(item.output_path);
        right.appendChild(btn);
      }
      if (!IS_LOCAL && item.job_id) {
        const dlBtn = document.createElement('button');
        dlBtn.className = 'hist-btn';
        dlBtn.textContent = 'Download';
        dlBtn.onclick = () => { window.location.href = '/file/' + item.job_id + (savedToken ? '?token=' + encodeURIComponent(savedToken) : ''); };
        right.appendChild(dlBtn);
      }
    }
    row.appendChild(left);
    row.appendChild(right);
    list.appendChild(row);
  });
  return list;
}

async function fetchHistory() {
  const headers = {};
  if (savedToken) headers['Authorization'] = 'Bearer ' + savedToken;
  const res = await fetch('/history?limit=5', {headers});
  if (!res.ok) return;
  const data = await res.json();
  const container = document.getElementById('historyPreview');
  container.innerHTML = '';
  if (!data.items || data.items.length === 0) {
    container.innerHTML = '<div class="hist-empty">No history yet.</div>';
  } else {
    container.appendChild(buildHistoryList(data.items));
  }
  const details = document.getElementById('historyDetails');
  if (details && details.open) fetchFullHistory();
}

async function fetchFullHistory() {
  const headers = {};
  if (savedToken) headers['Authorization'] = 'Bearer ' + savedToken;
  const res = await fetch('/history?limit=500', {headers});
  if (!res.ok) return;
  const data = await res.json();
  const container = document.getElementById('history');
  container.innerHTML = '';
  if (!data.items || data.items.length === 0) {
    container.innerHTML = '<div class="hist-empty">No history yet.</div>';
  } else {
    container.appendChild(buildHistoryList(data.items));
  }
}

async function reveal(path) {
  if (!path) {
    openFolder();
    return;
  }
  const headers = {'Content-Type':'application/json'};
  if (savedToken) headers['Authorization'] = 'Bearer ' + savedToken;
  await fetch('/reveal', {
    method: 'POST',
    headers,
    body: JSON.stringify({path})
  });
}

if (!IS_LOCAL) {
  document.querySelectorAll('.right-col .card').forEach(c => c.style.display = 'none');
}

fetchHistory();
try {
  const cached = JSON.parse(localStorage.getItem('yt_lib_cache') || 'null');
  if (cached && cached.data) {
    libData = cached.data;
    renderLibrary();
    renderBurnTrackList();
    updateBurnFooter();
  }
} catch(e) {}
fetchLibrary();
checkBurner();
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

def require_auth():
    if not VALID_TOKENS:
        host = request.host.split(":")[0].lower().strip("[]")
        if host not in _LOCAL_HOSTS:
            abort(403)
        return
    header = request.headers.get("Authorization", "")
    scheme, _, token = header.partition(" ")
    if scheme.lower() == "bearer" and token in VALID_TOKENS:
        return
    qs_token = request.args.get("token", "")
    if qs_token in VALID_TOKENS:
        return
    abort(401)

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

        # File TTL: delete actual downloaded files on a separate, independent schedule
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

def open_download_folder(select_path: str | None = None):
    try:
        if select_path and Path(select_path).exists():
            subprocess.Popen(["open", "-R", select_path])
        else:
            subprocess.Popen(["open", DOWNLOAD_DIR])
    except Exception:
        pass

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
    return re.sub(r'[\x00\n\r\t]', ' ', str(s or '')).replace('"', "'")

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
            job_sema.release()
            return
        job["status"] = "running"
        job_type = job.get("type", "video")
        url = job.get("url")
        sc_quality = job.get("sc_quality", "m4a")
        sc_playlist = job.get("sc_playlist", True)
        spotify_info = job.get("spotify_info") or {}
        apple_music_info = job.get("apple_music_info") or {}
        save_jobs()
    if not url:
        with jobs_lock:
            jobs[job_id]["status"] = "error"
            jobs[job_id]["log"] = "Missing URL"
        job_sema.release()
        return

    cookies_args = []
    if COOKIES_PATH and os.path.exists(COOKIES_PATH):
        cookies_args = ["--cookies", COOKIES_PATH]

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
    cmd = cmd[:1] + cookies_args + cmd[1:]

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
                track_cmd = track_cmd[:1] + cookies_args + track_cmd[1:]
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
                track_cmd = track_cmd[:1] + cookies_args + track_cmd[1:]
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
            jobs[job_id].pop("process", None)
            jobs[job_id].pop("cancel_requested", None)
            save_jobs()
        job_sema.release()
        # open folder once on success
        if status_val == "done":
            with jobs_lock:
                already_opened = jobs[job_id].get("opened_folder", False)
                if not already_opened:
                    jobs[job_id]["opened_folder"] = True
            if not already_opened:
                open_download_folder(output_val or (os.path.join(DOWNLOAD_DIR, file_val) if file_val else None))
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
    host = request.host.split(":")[0]
    is_local = host in ("localhost", "127.0.0.1", "::1")
    return render_template_string(HTML, download_dir=DOWNLOAD_DIR, version=VERSION, is_local=is_local)

@app.post("/start")
def start():
    require_auth()
    data = request.get_json() or {}
    url = (data.get("url") or "").strip()
    job_type = (data.get("type") or "video").strip().lower()
    if not is_valid_url(url):
        return jsonify({"error": "Invalid URL"}), 400
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
            "total_items": len((spotify_info or apple_music_info or {}).get("tracks", [])),
            "progress_pct": 0,
            "failures": [],
        }
        save_jobs()
    with queue_cv:
        if len(job_queue) >= MAX_QUEUE_DEPTH:
            with jobs_lock:
                jobs.pop(job_id, None)
            return jsonify({"error": "Queue is full. Try again later."}), 429
        job_queue.append(job_id)
        queue_cv.notify()
    return jsonify({"job_id": job_id, "status": "queued"})

@app.get("/status/<job_id>")
def status(job_id):
    require_auth()
    with jobs_lock:
        job = jobs.get(job_id)
        if not job:
            return jsonify({"status": "unknown", "log": "No such job"})
        # return a shallow copy, excluding non-serializable internals
        payload = {k: v for k, v in job.items() if k not in ("process", "cancel_requested", "spotify_info", "apple_music_info")}
        payload["log"] = job.get("log", "")
    payload["queue_position"] = queue_position(job_id)
    return jsonify(payload)

@app.get("/download/<job_id>")
def download(job_id):
    require_auth()
    with jobs_lock:
        job = jobs.get(job_id)
    if not job:
        abort(404)

    output_paths = job.get("output_paths") or []
    existing = [p for p in output_paths if p and os.path.exists(p)]

    if len(existing) > 1:
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
    if target_path and os.path.exists(target_path):
        return send_from_directory(os.path.dirname(target_path), os.path.basename(target_path), as_attachment=True)
    if job.get("file"):
        return send_from_directory(DOWNLOAD_DIR, job["file"], as_attachment=True)
    abort(404)

@app.get("/file/<job_id>")
def download_single(job_id):
    require_auth()
    with jobs_lock:
        job = jobs.get(job_id)
    if not job:
        abort(404)
    path = job.get("output_path") or (job.get("output_paths") or [None])[0]
    if not path or not os.path.exists(path):
        abort(404)
    return send_file(path, as_attachment=True)

@app.get("/open-folder")
def open_folder():
    require_auth()
    open_download_folder()
    return jsonify({"status": "ok"})

@app.get("/history")
def history():
    require_auth()
    limit = int(request.args.get("limit", "10"))
    items = load_history()[-limit:]
    host = request.host.split(":")[0].lower().strip("[]")
    if host not in _LOCAL_HOSTS:
        for item in items:
            if item.get("output_path"):
                item["output_path"] = os.path.basename(item["output_path"])
            if item.get("output_paths"):
                item["output_paths"] = [os.path.basename(p) for p in item["output_paths"] if p]
    return jsonify({"items": items[::-1]})

@app.post("/reveal")
def reveal():
    require_auth()
    data = request.get_json() or {}
    path = (data.get("path") or "").strip()
    if path:
        abs_dl   = os.path.abspath(DOWNLOAD_DIR)
        abs_path = os.path.abspath(path)
        if (abs_path == abs_dl or abs_path.startswith(abs_dl + os.sep)) and Path(abs_path).exists():
            open_download_folder(abs_path)
            return jsonify({"status": "ok", "opened": abs_path})
    open_download_folder()
    return jsonify({"status": "ok", "opened": DOWNLOAD_DIR})

@app.post("/cancel")
def cancel():
    require_auth()
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
    require_auth()
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
    require_auth()
    with jobs_lock:
        running = sum(1 for j in jobs.values() if j.get("status") == "running")
    with queue_cv:
        qlen = len(job_queue)
    return jsonify({"queue_length": qlen, "running": running, "version": VERSION})

# ── CD Burning ────────────────────────────────────────────────────────────────

def _do_burn(burn_id: str, paths: list, mode: str):
    """Background worker: converts files (if audio CD) and calls drutil burn."""
    tmpdir = tempfile.mkdtemp(prefix="ytui_burn_")
    log_lines = []

    def log(msg):
        log_lines.append(msg)
        with burn_lock:
            burn_jobs[burn_id]["log"] = "\n".join(log_lines[-80:])

    try:
        if mode == "audio":
            log("Converting tracks to AIFF (audio CD format)…")
            src_files = []
            for i, src in enumerate(paths):
                name = os.path.splitext(os.path.basename(src))[0]
                dst = os.path.join(tmpdir, f"{i+1:02d} {name}.aiff")
                log(f"  [{i+1}/{len(paths)}] {os.path.basename(src)}")
                r = subprocess.run(
                    ["afconvert", "-f", "AIFF", "-d", "LEI16@44100", "-c", "2", src, dst],
                    capture_output=True, text=True, timeout=180,
                )
                if r.returncode != 0:
                    log(f"    Warning: {r.stderr.strip()}")
                else:
                    src_files.append(dst)
            burn_cmd = ["drutil", "burn", "-audio", "-noeject", tmpdir]
        else:
            log("Staging files for data CD…")
            for src in paths:
                dst = os.path.join(tmpdir, os.path.basename(src))
                shutil.copy2(src, dst)
                log(f"  Copied: {os.path.basename(src)}")
            burn_cmd = ["drutil", "burn", "-data", "-noeject", tmpdir]

        log("Insert a blank CD if not already present…")
        log("Burning — this may take a few minutes…")
        with burn_lock:
            burn_jobs[burn_id]["status"] = "burning"
        r = subprocess.run(burn_cmd, capture_output=True, text=True, timeout=900)
        if r.stdout.strip():
            log(r.stdout.strip())
        if r.returncode == 0:
            log("✓ Burn complete!")
            with burn_lock:
                burn_jobs[burn_id]["status"] = "done"
        else:
            log(f"✗ drutil error:\n{r.stderr.strip()}")
            with burn_lock:
                burn_jobs[burn_id]["status"] = "error"
    except Exception as e:
        log(f"Exception: {e}")
        with burn_lock:
            burn_jobs[burn_id]["status"] = "error"
    finally:
        shutil.rmtree(tmpdir, ignore_errors=True)


@app.get("/check-burner")
def check_burner():
    require_auth()
    try:
        r = subprocess.run(["drutil", "list"], capture_output=True, text=True, timeout=5)
        lines = [l.strip() for l in r.stdout.splitlines() if l.strip()]
        available = any(str(i) in r.stdout for i in range(1, 10))
        return jsonify({"available": available, "info": "\n".join(lines)})
    except Exception as e:
        return jsonify({"available": False, "info": str(e)})


@app.post("/burn-cd")
def burn_cd_route():
    require_auth()
    data = request.get_json() or {}
    paths = [p for p in (data.get("paths") or [])
             if isinstance(p, str) and os.path.isfile(p) and os.path.abspath(p).startswith(os.path.abspath(DOWNLOAD_DIR))]
    if not paths:
        return jsonify({"error": "No valid files found in download directory"}), 400
    mode = data.get("mode", "data")
    if mode not in {"data", "audio"}:
        mode = "data"
    burn_id = str(uuid.uuid4())
    with burn_lock:
        burn_jobs[burn_id] = {"status": "running", "log": "Starting…", "mode": mode, "total": len(paths)}
    threading.Thread(target=_do_burn, args=(burn_id, paths, mode), daemon=True).start()
    return jsonify({"burn_id": burn_id})


@app.get("/burn-status/<burn_id>")
def burn_status(burn_id):
    require_auth()
    with burn_lock:
        job = burn_jobs.get(burn_id)
    if not job:
        return jsonify({"error": "Unknown burn job"}), 404
    return jsonify(job)

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


@app.after_request
def add_security_headers(response):
    response.headers["Content-Security-Policy"] = (
        "default-src 'self'; "
        "style-src 'self' 'unsafe-inline'; "
        "script-src 'self' 'unsafe-inline'; "
        "img-src 'self' data:; "
        "connect-src 'self'"
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
    parser = argparse.ArgumentParser(description="Local yt-dlp UI")
    parser.add_argument("--menubar", action="store_true", help="Run macOS menu bar tray (requires rumps)")
    args = parser.parse_args()
    menubar_env = os.environ.get("YT_UI_MENUBAR", "").lower() in {"1", "true", "yes"}
    is_frozen = getattr(sys, "frozen", False)

    def run_flask():
        host = os.environ.get("FLASK_HOST", "127.0.0.1")
        app.run(host=host, port=5055, debug=False, use_reloader=False)

    run_tray = args.menubar or menubar_env

    if is_frozen:
        # If a server is already running on 5055, just open the browser and exit
        _probe = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        _already_running = _probe.connect_ex(("127.0.0.1", 5055)) == 0
        _probe.close()
        if _already_running:
            webbrowser.open("http://127.0.0.1:5055")
        else:
            # Dock app: open browser automatically after Flask starts, then serve
            def _open_browser():
                time.sleep(1.5)
                webbrowser.open("http://127.0.0.1:5055")
            threading.Thread(target=_open_browser, daemon=True).start()
            run_flask()
    elif run_tray:
        try:
            import rumps  # type: ignore
        except ImportError:
            print("rumps not installed. Install with: pip install rumps (macOS only)")
            raise SystemExit(1)

        # start flask in background
        flask_thread = threading.Thread(target=run_flask, daemon=True)
        flask_thread.start()

        class Tray(rumps.App):
            def __init__(self):
                super().__init__("YT", quit_button=None)
                self.menu = [
                    rumps.MenuItem("Open UI", callback=self.open_ui),
                    rumps.MenuItem("Open Downloads Folder", callback=self.open_dl),
                    None,
                    rumps.MenuItem("Quit", callback=self.quit_app),
                ]

            def open_ui(self, _):
                webbrowser.open("http://127.0.0.1:5055")

            def open_dl(self, _):
                open_download_folder()

            def quit_app(self, _):
                rumps.quit_application()

        Tray().run()
    else:
        run_flask()
