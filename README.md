# +downloads

A local media downloader for YouTube, SoundCloud, Spotify, and Apple Music — runs entirely on your Mac.

---

## Installation

1. Download and unzip `+downloads.zip`
2. Move `+downloads.app` to your **Applications** folder (optional but recommended)
3. Double-click to open

---

## macOS Security Warning

The first time you open the app, macOS may block it with a message like:

> *"+downloads" can't be opened because Apple cannot check it for malicious software."*

**To allow it:**

1. Click **Done** on the warning dialog (do not click Move to Trash)
2. Open **System Settings** → **Privacy & Security**
3. Scroll down to the **Security** section
4. You'll see a message: *"+downloads" was blocked from use because it is not from an identified developer"*
5. Click **Open Anyway**
6. A new dialog will appear — click **Open** to confirm

The app will open normally from that point on and you won't see this prompt again.

> **Note:** If you moved the app after your first open attempt, repeat these steps — macOS ties the security exception to the file's location.

---

## Using the App

### Opening the UI

Double-clicking the app opens your browser automatically at `http://127.0.0.1:5055`.

If the page doesn't load, make sure the app is running (check your Dock) and navigate to `http://127.0.0.1:5055` manually.

---

### Downloading Media

1. **Paste a URL** into the input field at the top
2. **Select a format** (Video, Audio/MP3, SoundCloud)
3. Click **Download**

The status pill below the button will update in real time:
- **Queued** — waiting for a download slot
- **Running** — actively downloading (progress bar shows percentage)
- **Done** — file saved to your Downloads folder

---

### Supported URLs

| Service | What you can paste |
|---|---|
| **YouTube** | Video or playlist URL |
| **SoundCloud** | Track or playlist URL |
| **Spotify** | Track, album, or playlist URL |
| **Apple Music** | Track or album URL |

**Spotify & Apple Music** are matched to YouTube and downloaded as MP3 with metadata embedded. Playlist support requires Spotify API credentials (see Advanced Setup below).

---

### Download Formats

| Mode | Output |
|---|---|
| **Video** | MP4 (best quality) |
| **Audio / MP3** | MP3 extracted from best audio |
| **SoundCloud** | M4A or MP3 (your choice) |

---

### Where Files Are Saved

All downloads go to your **Downloads/YT** folder:

```
~/Downloads/YT/                  ← YouTube videos & audio
~/Downloads/YT/SoundCloud/       ← SoundCloud tracks
~/Downloads/YT/Spotify/          ← Spotify downloads
~/Downloads/YT/AppleMusic/       ← Apple Music downloads
```

Click **Reveal in Finder** next to any history item to jump straight to the file.

---

### History & Library

- **History** — shows your recent downloads with status and a Reveal button
- **Library** — organizes your downloads into Albums, Songs, and Videos tabs with search

---

### Cancelling a Download

Click **Cancel** while a download is running. The job will stop and be marked as cancelled in History.

---

### Burn to CD (macOS only)

1. Open the **Library** panel
2. Select tracks you want to burn
3. Click **Burn to CD**
4. Insert a blank CD when prompted

Supports audio CD and data CD modes.

---

## Advanced Setup

### Spotify Downloads

To enable Spotify support, set two environment variables before launching:

```bash
export SPOTIFY_CLIENT_ID=your_client_id
export SPOTIFY_CLIENT_SECRET=your_client_secret
```

Get credentials for free at [developer.spotify.com](https://developer.spotify.com/dashboard).

---

## Docker / Self-Hosting

To run on a Linux server:

```bash
git clone https://github.com/jaysperspective/download.git
cd download
cp .env.example .env   # set YT_UI_TOKEN in .env
docker compose up -d --build
```

The app will be available on port `5055`. Set a strong token in `.env` — all requests require a Bearer token when `YT_UI_TOKEN` is set.

### Updating the server

```bash
git pull && docker compose up -d --build
```

---

## Troubleshooting

**App opens but browser doesn't load**
→ Navigate manually to `http://127.0.0.1:5055`

**"Address already in use" in logs**
→ The app is already running. Double-clicking again will open your browser to the existing session.

**Download stuck at 0% or fails immediately**
→ Make sure you have an internet connection. Spotify/Apple Music failures usually mean no matching YouTube result was found for that track.

**SoundCloud downloads missing tracks**
→ Some SoundCloud tracks are region-locked or private. The download will complete with a failure count shown in the log.
