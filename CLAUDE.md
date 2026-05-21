# +downloads — codebase notes for Claude

A Flask-based media downloader hosted at **digitaldownloads.space**. Wraps `yt-dlp` + `ffmpeg` behind a web UI, queues jobs, and gates access via a token-based payment system. A companion **desktop app** is sold at $1.99 one-time through the same payment system — buy, redeem, OS-aware installer download, and free updates are all live.

## Project shape

**One file does almost everything.** `app.py` is ~3800 lines: Flask routes, job runner, queue/dispatcher, token gate, page-view analytics, history, admin, and **four large inline HTML templates as Python string constants**. Do not split into modules unless explicitly asked — the user prefers the single-file layout.

Important globals & locations (verify line numbers before quoting — file is actively edited):

- **HTML templates** (giant string constants near the top of the file):
  - `HTML` — landing page at `/`. Uses `r"""..."""` (raw string) so JS `\n` and regex backslashes survive Python parsing. The desktop product section leads the page; the online tool sits below it.
  - `ADMIN_HTML` — `/admin`. Standard `"""..."""`.
  - `_LEGAL_PAGE_TEMPLATE` + `_PRIVACY_BODY` + `_TERMS_BODY` — `/privacy` and `/terms`.
  - `_DESKTOP_REDEEM_HTML` — shared template for `/desktop/redeem` (confirmed / pending / error states) and `/desktop/update` (the `update` state).
- **Token gate** (~line 75–200): `_is_token_valid()` / `_consume_token()` call the payment app at `PAYMENT_APP_URL/payment/api/access/internal/token/{check,use}`, authed with `TOKEN_INTERNAL_SECRET` (`x-internal-secret` header). `_check_token_status()` is the uncached variant returning the full check JSON (`product`, `reason`). Checkout URLs: `ACCESS_PAYMENT_URL` (online), `DESKTOP_PAYMENT_URL` (desktop, defaults to `ACCESS_PAYMENT_URL?product=desktop`).
- **Desktop paywall**: `/desktop/buy` (302 → checkout) · `/desktop/redeem` (post-purchase, token-gated, polls `/desktop/redeem/status` for the webhook race) · `/desktop/redeem/download` (consumes a credit, serves the installer) · `/desktop/update` (token-less free-update download). Installers resolve via `_load_builds_manifest()` from `DESKTOP_BUILDS_DIR`.
- **Page-view analytics**: first-party, no cookies/IPs. SQLite at `ANALYTICS_DB` (under the state dir, gitignored). `_record_pageview()` runs inside `add_security_headers` for an allowlist of pages; `_pageview_analytics()` aggregates for `/admin`; rows pruned after 90 days.
- **Job lifecycle**: `start()` → `dispatcher()` → `run_job()` → status polled via `/status/<job_id>` → download via `/download/<job_id>`.

## Editing the landing page

The `HTML` constant is ~1400 lines of HTML/CSS/JS in a Python raw triple-quoted string. **Do not replace it with a giant `old_string` Edit.** For large swaps, write the new body to a temp file and use a Python regex script (`^HTML = r?"""\n.*?\n"""\n`); for small changes, targeted Edits with unique anchors are fine. Always `python3 -c "import ast; ast.parse(open('app.py').read())"` after, then restart the dev server and `curl /`.

If new HTML contains JS string-literal `\n` or regex escapes (`\.`, `\[`), keep `r"""..."""`. Non-raw `"""` requires double-escaping (`\\n`).

## Brand & UI conventions

- Header brand mark: **"digital +downloads"** (`digital` in white `#f0eef0`, `+downloads` in pink `#db52a6`). Implemented as `<a class="logo"><span class="lo-prefix">digital</span>+downloads</a>` with `.lo-prefix { color: #f0eef0; }`. Use this pattern in any new top-level template.
- No version badge — it was removed deliberately. Don't add it back.
- Color palette:
  - Primary pink: `#db52a6` (hover `#c9479a`)
  - Gold accent: `#bf9b3a`
  - Purple accent: `#9b3adb` (used for the "best value" $5/10-downloads card)
  - BG: `#1a1818`, Card: `#242222`, Border: `#2e2c2c`
  - Status: success `#48c78e`, error `#ff6b6b`
- Favicon is `static/favicon.svg` (pink `+` on dark rounded ground). `favicon.png` / `icon-192.png` / `icon-512.png` are PNG fallbacks generated from the SVG via `sips`. If you regenerate the SVG, regenerate all three PNGs.

## Two products, one payment app

- **Online tool** (`/`): metered, token = N download credits. Two SKUs ($1/3-downloads, $5/10-downloads), both → `https://joshuaisaiah.art/payment/access`. **The free web service is permanently paused** — the online tool now requires a purchased token (paste it into the inline Insert-Token entry).
- **Desktop app** ($1.99 one-time, free updates forever, macOS/Windows/Linux):
  - **Buy:** landing-page Buy buttons → `/desktop/buy` → 302 → `DESKTOP_PAYMENT_URL` (payment app's `?product=desktop` checkout).
  - **Redeem:** after Stripe checkout the buyer lands on `/desktop/redeem?token=…` → Mac/Windows/Linux download buttons (UA-detected default first) → `/desktop/redeem/download` consumes one of the token's 5 credits and serves the installer. **Pay-to-download model** — no in-app license check; installers are freely shareable.
  - **Free updates:** when a new version ships, installers are replaced on the server and a Kit broadcast goes to the **whole mailing list** linking to **`/desktop/update`** — a token-less page serving the latest installers. The 5 redeem credits are a re-download buffer for the purchased version; updates ride the `/desktop/update` channel.
  - **Builds:** the three installers + `manifest.json` live in `DESKTOP_BUILDS_DIR`. Admins upload/remove them via the **Installer Builds** card on `/admin`, or installers are `scp`'d directly into the server's bind-mounted `~/yt-web-ui/desktop-builds/`. No app restart needed — routes read `manifest.json` live.
- **Free Trial edition** (feature-limited, YouTube-only, free):
  - **Page:** `/trial` — public, token-less, OS-detected. Sells the upgrade: trial framing + a buy-page CTA to `/?ref=trial-page`. Own template constant `_DESKTOP_TRIAL_HTML`.
  - **Email gate:** `/trial` reveals the download only after the visitor submits an email. `POST /trial/unlock` validates the email, adds it to the Kit "desktop-trial" tag via the v3 API (`_kit_subscribe_trial`, `KIT_API_KEY` + `KIT_TRIAL_TAG_ID`), and sets a signed `trial_unlocked` cookie (`_TRIAL_COOKIE_SIG`, HMAC over `TOKEN_INTERNAL_SECRET`). It's a *soft* gate — the cookie lets return visits skip the form, and `/trial?os=` 302s back to `/trial` without it. If the Kit call fails the email is appended to `trial-signups-fallback.jsonl` in the state dir (gitignored) so no lead is lost and the download still unlocks. The landing-page Buy section has a gold "Try the free trial" button (`.btn-trial`) linking to `/trial`.
  - **Builds:** separate `DESKTOP_BUILDS_TRIAL_DIR` (`~/yt-web-ui/desktop-builds-trial/`, its own bind-mount + `manifest.json`) — **never mixed with the paid `desktop-builds/`**. The manifest helpers (`_load_builds_manifest`, `_list_desktop_builds`, etc.) all take a `builds_dir` arg; `_builds_dir_for(edition)` maps `"full"|"trial"` to a dir. Admins manage it via the **Trial Installer Builds** card on `/admin` (the builds upload/delete routes take an `edition` form field).
  - **Conversion attribution:** the trial desktop app's in-app Upgrade CTAs link to `/?ref=trial`; the `/trial` web page's CTA uses `?ref=trial-page`. `add_security_headers` records a `/?ref=<tag>` pageview so referred visits show up in the admin Top Pages list. Note: this counts *visits*, not purchases — true purchase attribution would need the payment app to carry the ref through checkout.

## Admin (`/admin`)

Password-gated by `YT_UI_COOKIES_PASSWORD` (503 if unset). "Load Stats" (`POST /admin/stats`) renders the page-view dashboard (stat cards, 30-day bar chart, top pages, recent views), the Installer Builds + Trial Installer Builds management cards, and download stats. Cookie upload and service-pause controls are always visible.

## Running locally

```bash
pip install -r requirements.txt    # flask + gunicorn only
python app.py                       # dev server on 127.0.0.1:5055
```

`DOWNLOAD_DIR` and `YT_UI_STATE_DIR` can be redirected (e.g. `DOWNLOAD_DIR=/tmp/yt_smoke_dl YT_UI_STATE_DIR=/tmp/yt_smoke_state python app.py`) for isolated smoke tests. The port defaults to `5055` but honors a `PORT` env var, so a smoke-test instance can run alongside a server already on 5055.

Production runs in Docker via `docker-compose.yml` on a DigitalOcean droplet. **The container uses `network_mode: host`** — required so it can reach the payment app on the host's `127.0.0.1:4001`: the payment app's internal API binds loopback only, and its public hostname is behind Cloudflare which 403s scripted requests. `PAYMENT_APP_URL` must therefore be `http://127.0.0.1:4001` in prod. The `desktop-builds/` dir is bind-mounted to `/data/desktop-builds`. SSH access and deploy steps are in the [server access memory](~/.claude/projects/-Users-joshuaharrington-yt-web-ui/memory/reference_server_access.md).

## YouTube cookies

`cookies.txt` at repo root holds a Netscape-format cookie jar for `yt-dlp`. If downloads start failing with *"Sign in to confirm you're not a bot"*, cookies are stale — refresh via the `/admin` upload flow. The app emails an alert on the first such failure per 24h (gated by `YT_UI_SMTP_USER`/`PASS`/`ALERT_EMAIL`). A Decodo residential proxy (`YT_UI_PROXY`) bypasses YouTube's datacenter-IP block — see the [bot detection fix memory](~/.claude/projects/-Users-joshuaharrington-yt-web-ui/memory/project_youtube_bot_detection_fix.md).

## Conventions to follow

- Single-file architecture — don't refactor `app.py` into modules unprompted.
- HTML strings are big and edited by hand — don't introduce Jinja includes or external template files unless asked.
- The token system is the source of truth for access — don't add parallel paywall logic. Funnel new SKUs through the payment app's internal endpoints.
- Keep the brand pink as the only saturated UI color. The gold and purple are accents.
- Don't add a version badge or "powered by" footer. First-party page-view counting exists; don't add third-party analytics SDKs.

## Known limitations

- **Exhausted vs. pending desktop tokens are indistinguishable.** The payment app returns the same `{valid:false, reason:"exhausted"}` for a not-yet-activated token (webhook race) and a fully-used one (5 redeem credits spent). `/desktop/redeem` treats both as "pending" and polls — the genuine race resolves in seconds; a truly-exhausted token settles on a support message. A clean fix needs the payment app to expose an `activated` flag or live `remaining`. Low impact in practice: free updates go through token-less `/desktop/update`, so redeem credits rarely exhaust.
