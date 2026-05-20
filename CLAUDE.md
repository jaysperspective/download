# +downloads — codebase notes for Claude

A Flask-based media downloader hosted at **digitaldownloads.space**. Wraps `yt-dlp` + `ffmpeg` behind a web UI, queues jobs, and gates access via a token-based payment system. A companion desktop app is on sale at $7 one-time; the buy/redeem flow is wired through the payment app (installer file-serving still deferred — see "Deferred work" below).

## Project shape

**One file does almost everything.** `app.py` is ~3200 lines: Flask routes, job runner, queue/dispatcher, token gate, history, admin, and **four large inline HTML templates as Python string constants**. Do not split into modules unless explicitly asked — the user prefers the single-file layout.

Important globals & locations (verify line numbers before quoting — file is actively edited):

- **HTML templates** (giant string constants near the top of the file):
  - `HTML` — landing page at `/`. Uses `r"""..."""` (raw string) so JS `\n` and regex backslashes survive Python parsing.
  - `ADMIN_HTML` — `/admin`. Standard `"""..."""`.
  - `_LEGAL_PAGE_TEMPLATE` + `_PRIVACY_BODY` + `_TERMS_BODY` — `/privacy` and `/terms`.
  - `_DESKTOP_REDEEM_HTML` — `/desktop/redeem` post-purchase page (confirmed / pending / error states; polls `/desktop/redeem/status` to clear the Stripe-redirect/webhook race).
- **Token gate** (~line 75–200): `_is_token_valid()` and `_consume_token()` call out to a separate payment app via `PAYMENT_APP_URL/payment/api/access/internal/token/{check,use}`, authed with `TOKEN_INTERNAL_SECRET` (`x-internal-secret` header). `_check_token_status()` is the uncached variant that returns the full check JSON (`product`, `reason`) for the desktop redeem flow. User-facing checkout URLs are `ACCESS_PAYMENT_URL` (online tool) and `DESKTOP_PAYMENT_URL` (desktop app, defaults to `ACCESS_PAYMENT_URL?product=desktop`).
- **Job lifecycle**: `start()` → `dispatcher()` → `run_job()` → status polled via `/status/<job_id>` → download via `/download/<job_id>`.

## Editing the landing page

The `HTML` constant is ~1230 lines of HTML/CSS/JS embedded in a Python raw triple-quoted string. **Do not try to replace it with a 1000-line `old_string` Edit** — it's too big. Pattern that works:

1. Write the new HTML to `/tmp/new_index.html` with `Write`.
2. Run a small Python script via `Bash` that regex-matches `^HTML = r?"""\n.*?\n"""\n` and swaps the body.
3. `python3 -c "import ast; ast.parse(open('app.py').read())"` to sanity-check the result.
4. Restart the dev server, `curl /` to verify.

If the new HTML contains JS string-literal `\n` or regex escapes (`\.`, `\[`), keep `r"""..."""`. If you switch to non-raw `"""`, you must double-escape (`\\n`). The previous commit *"Fix banner JS: escape \n in non-raw HTML template string"* exists because someone forgot this.

## Brand & UI conventions

- Header brand mark: **"digital +downloads"** (`digital` in white `#f0eef0`, `+downloads` in pink `#db52a6`). Implemented as `<a class="logo"><span class="lo-prefix">digital</span>+downloads</a>` with `.lo-prefix { color: #f0eef0; }`. Use this pattern in any new top-level template.
- No version badge — it was removed deliberately. Don't add it back.
- Color palette:
  - Primary pink: `#db52a6` (hover `#c9479a`)
  - Gold accent: `#bf9b3a`
  - Purple accent: `#9b3adb` (used for the "best value" $5/10-downloads card)
  - BG: `#1a1818`, Card: `#242222`, Border: `#2e2c2c`
  - Status: success `#48c78e`, error `#ff6b6b`
- Favicon is now `static/favicon.svg` (pink `+` on dark rounded ground). `favicon.png` / `icon-192.png` / `icon-512.png` are PNG fallbacks generated from the SVG via `sips`. If you regenerate the SVG, regenerate all three PNGs.

## Two products, one payment app

- **Online tool** (`/`): metered. Token = N download credits. Two SKUs: $1/3-downloads, $5/10-downloads. Both link to `https://joshuaisaiah.art/payment/access`. Users either paste a token into the inline Insert-Token entry, or buy one and get it emailed.
- **Desktop app** ($7 one-time, free updates forever, macOS/Windows/Linux): the four landing-page Buy buttons point at `/desktop/buy`, which `302`-redirects to `DESKTOP_PAYMENT_URL` (the payment app's `?product=desktop` checkout). After Stripe checkout the buyer lands on `/desktop/redeem?token=…` — it validates the desktop token via `_check_token_status()` and, when confirmed, shows Mac/Windows/Linux download buttons (UA-detected default first). Each button hits `/desktop/redeem/download?token=…&os=…`, which `_consume_token()`s one of the 5 credits and `send_file()`s the matching installer from `DESKTOP_BUILDS_DIR` (resolved through `manifest.json`). Installers are uploaded/removed from the **Installer Builds** card on `/admin`. The desktop token starts at 5 credits so re-downloads work. The webhook race (`exhausted` right after redirect) is handled by the redeem page polling `/desktop/redeem/status`.

## Running locally

```bash
pip install -r requirements.txt    # flask + gunicorn only
python app.py                       # dev server on 127.0.0.1:5055
```

`DOWNLOAD_DIR` and `YT_UI_STATE_DIR` default to `~/Downloads` style paths but can be redirected (e.g. `DOWNLOAD_DIR=/tmp/yt_smoke_dl YT_UI_STATE_DIR=/tmp/yt_smoke_state python app.py`) for isolated smoke tests. The port defaults to `5055` but honors a `PORT` env var, so a smoke-test instance can run alongside a server already on 5055.

Production runs in Docker via `docker-compose.yml` on a DigitalOcean droplet. SSH access and deploy steps are in the [server access memory](~/.claude/projects/-Users-joshuaharrington-yt-web-ui/memory/reference_server_access.md).

## YouTube cookies

`cookies.txt` at repo root holds a Netscape-format cookie jar for `yt-dlp`. If downloads start failing with *"Sign in to confirm you're not a bot"*, cookies are stale — refresh via the `/admin` upload flow. The app emails an alert on the first such failure per 24h (gated by `YT_UI_SMTP_USER`/`PASS`/`ALERT_EMAIL`). A Decodo residential proxy (`YT_UI_PROXY`) bypasses YouTube's datacenter-IP block — see the [bot detection fix memory](~/.claude/projects/-Users-joshuaharrington-yt-web-ui/memory/project_youtube_bot_detection_fix.md).

## Conventions to follow

- Single-file architecture — don't refactor `app.py` into modules unprompted.
- HTML strings are big and edited by hand — don't introduce Jinja includes or external template files unless asked.
- The token system is the source of truth for access — don't add parallel paywall logic. Funnel new SKUs through the existing payment app's internal endpoints.
- Keep the brand pink as the only saturated UI color. The gold and purple are accents.
- Don't add a version badge, "powered by" footer, or third-party analytics.

## Known limitations

- **Exhausted vs. pending desktop tokens are indistinguishable.** The payment app returns the same `{valid:false, reason:"exhausted"}` for a not-yet-activated token (webhook race) and a fully-used token (all 5 download credits spent). `/desktop/redeem` treats both as "pending" and polls; the genuine race resolves in seconds, a truly-exhausted token never resolves and settles on a support message. A clean fix needs the payment app to expose an `activated` flag or the live `remaining` count.
