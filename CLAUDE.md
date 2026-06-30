# +downloads — codebase notes for Claude

A Flask-based media downloader hosted at **digitaldownloads.space**. Wraps `yt-dlp` + `ffmpeg` behind a web UI, queues jobs, and gates access via a token-based payment system. A companion **desktop app** is sold at $1.99 one-time through the same payment system — buy, redeem, OS-aware installer download, and free updates are all live. A free, feature-limited **trial edition** is offered at `/trial` behind an email gate (live since 2026-05-21).

## Project shape

**One file does almost everything.** `app.py` is ~5000 lines: Flask routes, job runner, queue/dispatcher, token gate, page-view analytics, history, admin, SEO routes, and **five large inline HTML templates as Python string constants**. Do not split into modules unless explicitly asked — the user prefers the single-file layout.

Important globals & locations (verify line numbers before quoting — file is actively edited):

- **HTML templates** (giant string constants near the top of the file):
  - `HTML` — landing page at `/`. Uses `r"""..."""` (raw string) so JS `\n` and regex backslashes survive Python parsing. The desktop product section leads the page; the online tool sits below it.
  - `ADMIN_HTML` — `/admin`. Standard `"""..."""`.
  - `_LEGAL_PAGE_TEMPLATE` + `_PRIVACY_BODY` + `_TERMS_BODY` + `_TROUBLESHOOTING_BODY` — `/privacy`, `/terms`, and `/troubleshooting` (all share the same dark template).
  - `_DESKTOP_REDEEM_HTML` — shared template for `/desktop/redeem` (confirmed / pending / error states) and `/desktop/update` (the `update` state).
  - `_DESKTOP_TRIAL_HTML` — `/trial`, the free-trial page. Renders an email-gate form or the OS-detected download buttons depending on the `unlocked` flag.
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

- **Online tool** (`/`): metered, token = N download credits. Two SKUs ($1/3-downloads, $5/10-downloads), both → `https://joshuaisaiah.art/payment/access`. **The free web service is permanently paused** — the online tool now requires a purchased token (paste it into the inline Insert-Token entry). **Currently also hard-paused for token holders** (see *Hard pause + Decodo dependency* section below) — the two `.token-buy` cards on the landing page are grayed out and click-intercepted to a desktop-app explainer modal (`showOnlineOfflineModal`), and `/start` 503s every request including paid ones.
- **Desktop app** ($1.99 one-time, free updates forever, macOS/Windows/Linux):
  - **Buy:** landing-page Buy buttons → `/desktop/buy` → 302 → `DESKTOP_PAYMENT_URL` (payment app's `?product=desktop` checkout).
  - **Redeem:** after Stripe checkout the buyer lands on `/desktop/redeem?token=…` → Mac/Windows/Linux download buttons (UA-detected default first) → `/desktop/redeem/download` consumes one of the token's 5 credits and serves the installer. **Pay-to-download model** — no in-app license check; installers are freely shareable.
  - **Free updates:** when a new version ships, installers are replaced on the server and a Kit broadcast goes to the **whole mailing list** linking to **`/desktop/update`** — a token-less page serving the latest installers. The 5 redeem credits are a re-download buffer for the purchased version; updates ride the `/desktop/update` channel.
  - **Version probe (`GET /desktop/latest`):** returns `{"version": "<paid manifest version>"}` as JSON (cache 5 min), read live from `_load_builds_manifest()`. The **desktop app polls this once a day** to show a non-blocking in-app "update available" banner (full edition only) — see the desktop repo's *In-app update notification* convention. It gates nothing, so it's safe to hit unauthenticated; **don't rename/remove it without coordinating the desktop app**, and don't point it at the trial manifest (full builds only).
  - **Builds:** the three installers + `manifest.json` live in `DESKTOP_BUILDS_DIR`. Admins upload/remove them via the **Installer Builds** card on `/admin`, or installers are `scp`'d directly into the server's bind-mounted `~/yt-web-ui/desktop-builds/`. No app restart needed — routes read `manifest.json` live.
- **Free Trial edition** (feature-limited, YouTube-only, free):
  - **Page:** `/trial` — public, token-less, OS-detected. Sells the upgrade: trial framing + a buy-page CTA to `/?ref=trial-page`. Own template constant `_DESKTOP_TRIAL_HTML`.
  - **Email gate:** `/trial` reveals the download only after the visitor submits an email. `POST /trial/unlock` validates the email, adds it to the Kit "desktop-trial" tag via the v3 API (`_kit_subscribe_trial`, `KIT_API_KEY` + `KIT_TRIAL_TAG_ID`), and sets a signed `trial_unlocked` cookie (`_TRIAL_COOKIE_SIG`, HMAC over `TOKEN_INTERNAL_SECRET`). It's a *soft* gate — the cookie lets return visits skip the form, and `/trial?os=` 302s back to `/trial` without it. If the Kit call fails the email is appended to `trial-signups-fallback.jsonl` in the state dir (gitignored) so no lead is lost and the download still unlocks. The landing-page Buy section has a gold "Try the free trial" button (`.btn-trial`) linking to `/trial`.
  - **Builds:** separate `DESKTOP_BUILDS_TRIAL_DIR` (`~/yt-web-ui/desktop-builds-trial/`, its own bind-mount + `manifest.json`) — **never mixed with the paid `desktop-builds/`**. The manifest helpers (`_load_builds_manifest`, `_list_desktop_builds`, etc.) all take a `builds_dir` arg; `_builds_dir_for(edition)` maps `"full"|"trial"` to a dir. Admins manage it via the **Trial Installer Builds** card on `/admin` (the builds upload/delete routes take an `edition` form field).
  - **Conversion attribution:** the trial desktop app's in-app Upgrade CTAs link to `/?ref=trial`; the `/trial` web page's CTA uses `?ref=trial-page`. `add_security_headers` records a `/?ref=<tag>` pageview so referred visits show up in the admin Top Pages list. Note: this counts *visits*, not purchases — true purchase attribution would need the payment app to carry the ref through checkout.
  - **Nurture sequence (Kit-side, no code):** the `desktop-trial` tag-add fires a Kit Visual Automation ("Desktop trial nurture trigger") that enrolls new signups in a 3-email Sequence ("Desktop trial nurture") on a day 0 / day 3 / day 9 cadence — welcome, source breakdown, upgrade ask. The whole flow is configured in Kit's UI; the only repo-side piece is `_kit_subscribe_trial` adding the tag. Each email's CTA links to `https://digitaldownloads.space/?ref=trial-email-{1,2,3}` so per-email click attribution shows up separately in admin Top Pages. A separate one-off broadcast (`?ref=trial-existing-broadcast`) catches up subscribers who joined before the sequence existed (live 2026-05-23). If you find yourself wanting to send transactional/marketing email from `app.py` to trial users, you're probably duplicating something Kit already handles — extend the Kit sequence instead.

## Admin (`/admin`)

Password-gated by `YT_UI_COOKIES_PASSWORD` (503 if unset). "Load Stats" (`POST /admin/stats`) renders the page-view dashboard (stat cards, 30-day bar chart, top pages, recent views), the Installer Builds + Trial Installer Builds management cards, and download stats. Cookie upload and service-pause controls are always visible.

## SEO & discoverability

On-page SEO lives in the inline template heads plus a few small routes (added 2026-05-21):

- **Meta tags:** the `HTML`, `_DESKTOP_TRIAL_HTML` and `_LEGAL_PAGE_TEMPLATE` heads carry `<meta description>`, canonical, Open Graph and Twitter Card tags. The legal template takes `canonical` + `meta_desc` as render vars passed from the `privacy()`/`terms()` routes. `_DESKTOP_REDEEM_HTML` is `noindex` — `/desktop/redeem` carries a token in the URL and `/desktop/update` is a utility page.
- **Structured data:** the landing page embeds one JSON-LD `<script type="application/ld+json">` with an `@graph` of `WebSite`, `Organization`, `SoftwareApplication` (the $1.99 offer) and `FAQPage`. The `FAQPage` mirrors the on-page `<details>` FAQ — **keep the two in sync** if you edit either.
- **Routes** (plain `Response` routes near `index()`): `/robots.txt`, `/sitemap.xml` (lists `/`, `/trial`, `/troubleshooting`, `/privacy`, `/terms`), and `/llms.txt` (an [llmstxt.org](https://llmstxt.org)-format brief for AI crawlers). `_SITE_ORIGIN` is the canonical origin used to build absolute URLs. `/google42d52abaf2591614.html` is the Google Search Console HTML-file token — kept as a backup only; the property is verified by DNS (a `digitaldownloads.space` **Domain** property), and the sitemap is submitted.
- **Social image:** `static/og-image.svg` → `static/og-image.png` (1200×630 branded share card), regenerated via `sips -s format png` like the favicons.

## Running locally

```bash
pip install -r requirements.txt    # flask + gunicorn only
python app.py                       # dev server on 127.0.0.1:5055
```

`DOWNLOAD_DIR` and `YT_UI_STATE_DIR` can be redirected (e.g. `DOWNLOAD_DIR=/tmp/yt_smoke_dl YT_UI_STATE_DIR=/tmp/yt_smoke_state python app.py`) for isolated smoke tests. The port defaults to `5055` but honors a `PORT` env var, so a smoke-test instance can run alongside a server already on 5055.

Production runs in Docker via `docker-compose.yml` on a DigitalOcean droplet. **The container uses `network_mode: host`** — required so it can reach the payment app on the host's `127.0.0.1:4001`: the payment app's internal API binds loopback only, and its public hostname is behind Cloudflare which 403s scripted requests. `PAYMENT_APP_URL` must therefore be `http://127.0.0.1:4001` in prod. The `desktop-builds/` and `desktop-builds-trial/` dirs are bind-mounted to `/data/desktop-builds{,-trial}` (both must exist on the host before `docker compose up`). `KIT_API_KEY` + `KIT_TRIAL_TAG_ID` live in the server's `.env`. SSH access and deploy steps are in the [server access memory](~/.claude/projects/-Users-joshuaharrington-yt-web-ui/memory/reference_server_access.md).

## YouTube cookies

`cookies.txt` at repo root holds a Netscape-format cookie jar for `yt-dlp`. If downloads start failing with *"Sign in to confirm you're not a bot"*, cookies are stale — refresh via the `/admin` upload flow. The app emails an alert on the first such failure per 24h (gated by `YT_UI_SMTP_USER`/`PASS`/`ALERT_EMAIL`). A Decodo residential proxy (`YT_UI_PROXY`) bypasses YouTube's datacenter-IP block — see the [bot detection fix memory](~/.claude/projects/-Users-joshuaharrington-yt-web-ui/memory/project_youtube_bot_detection_fix.md).

## Conventions to follow

- Single-file architecture — don't refactor `app.py` into modules unprompted.
- HTML strings are big and edited by hand — don't introduce Jinja includes or external template files unless asked.
- The token system is the source of truth for access — don't add parallel paywall logic. Funnel new SKUs through the payment app's internal endpoints.
- Keep the brand pink as the only saturated UI color. The gold and purple are accents.
- Don't add a version badge or "powered by" footer. First-party page-view counting exists; don't add third-party analytics SDKs.

## `/troubleshooting` page

Plain-language landing spot for users hitting upgrade snags (added 2026-06-06 after the first paying customer ran into the trial→full port-collision bug). Reuses `_LEGAL_PAGE_TEMPLATE` with body `_TROUBLESHOOTING_BODY` and date `_TROUBLESHOOTING_LAST_UPDATED` (separate from `_LEGAL_LAST_UPDATED` so it can move without touching legal pages). Indexable; OG-tagged. Covers: how to tell trial vs full apart (banner + tab title), per-OS "fully quit the trial" steps (Mac dock right-click / Activity Monitor, Windows Task Manager, Linux `pkill`), and a support-email fallback. Linked from:
- top nav (`Help` link in the homepage `<nav class="nav">`)
- every page's footer (the `_LEGAL_PAGE_TEMPLATE` footer link, plus the duplicated footers in `HTML`, `_DESKTOP_REDEEM_HTML`, and `_DESKTOP_TRIAL_HTML`)
- inline helper paragraphs on `/desktop/redeem` (`confirmed` state) and `/desktop/update`

When updating: the v3.0.1 desktop app fixes the bug automatically, so the page frames the manual steps as "you only need these on pre-3.0.1 trial installs." Don't drop the manual steps even after that becomes ancient history — same shape of bug can come back (any cross-edition port collision, e.g. user is running an old beta) and the page is also linked from the Kit broadcast.

## Hard pause + Decodo dependency

The online tool only works because outbound YouTube requests are proxied through a Decodo residential-IP plan (env var `YT_UI_PROXY=http://<user>:<pass>@gate.decodo.com:10001`). Without it, YouTube bot-walls the droplet's datacenter IP on *every* yt-dlp player_client variant (web/tv_simply/mweb/ios/tv_embedded/android — all return "Sign in to confirm you're not a bot"). The proxy is therefore load-bearing for any YouTube path — including Spotify/Apple Music downloads, which match each track to a YouTube video under the hood.

**Two pause flags** live in `/data/state/pause.json`:
- `{"paused": true}` — the original "free service paused" flag. **Bypassed by valid paid tokens** at `/start` (line ~4555): token holders can still queue jobs. This has been `true` since 2026-04-17.
- `{"hard_paused": true}` — added 2026-06-06. Blocks **everyone**, including paid token holders. `/start` returns 503 with `{"error":"paused","message":"…temporarily offline…","paused":true}`. Loaded by `_load_hard_paused()`; checked at the top of `/start` *before* the token-bypass branch. Use for upstream-outage style stops where serving paid users would just stack up errors. Currently `true` because the Decodo plan hit its 3 GB monthly cap on 2026-06-05 and started returning **HTTP 407 Proxy Authentication Required** on every request (Decodo's quota-exceeded behavior — *not* a credentials problem).

**The bot-detection alert is too narrow.** `app.py:473` arms only on the literal substring `"Sign in to confirm you're not a bot"` in yt-dlp stderr. When Decodo runs out of bandwidth, the proxy 407 shows up as `Tunnel connection failed: 407 Proxy Authentication Required` — different substring, alert never fires, you find out from users instead. Worth broadening the trigger to also catch `407 Proxy Authentication Required` / `Tunnel connection failed` if/when we bring the online tool back.

**Restore sequence** (once Decodo is upgraded / quota resets / a different proxy is wired in):
1. Verify outbound via the new proxy from inside the container: `docker compose exec app curl --proxy "$YT_UI_PROXY" https://api.ipify.org` — should return an IP, not `407`.
2. Flip `pause.json` back to `{"paused": true, "hard_paused": false}` (keeps the free tier paused, lets paid tokens through again). `_PAUSE_CACHE_TTL` is 5 s so the change takes effect within seconds; no restart needed.
3. Restore the landing page UX: remove the `offline` class + `onclick="showOnlineOfflineModal(); return false;"` from both `<a class="token-buy">` elements, change `href="#"` back to `href="https://joshuaisaiah.art/payment/access"`, and restore the section label from `Online tool &mdash; temporarily offline` to `Buy a token to use it online`. The `paused-banner` paragraph at the top of `#downloader` should also revert from the outage-explainer copy to its prior wording.
4. (Optional) keep the `_load_hard_paused()` mechanism and the `showOnlineOfflineModal` markup in place — they cost nothing dormant and the next outage will need them again.

The "should we even keep the online YouTube tool alive" question is real: the desktop app runs on the user's residential IP and doesn't have this problem at all, so the online tool is effectively perpetual-maintenance for a marketing surface. Decision deferred 2026-06-06 — hard-paused while the user decides between renewing Decodo, moving the worker to a home machine, or retiring the online path entirely.

## Known limitations

- **Exhausted vs. pending desktop tokens are indistinguishable.** The payment app returns the same `{valid:false, reason:"exhausted"}` for a not-yet-activated token (webhook race) and a fully-used one (5 redeem credits spent). `/desktop/redeem` treats both as "pending" and polls — the genuine race resolves in seconds; a truly-exhausted token settles on a support message. A clean fix needs the payment app to expose an `activated` flag or live `remaining`. Low impact in practice: free updates go through token-less `/desktop/update`, so redeem credits rarely exhaust.
