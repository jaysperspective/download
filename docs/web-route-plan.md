# `/web` — mobile-first account edition (implementation plan)

Route: **digitaldownloads.space/web**. A mobile-first downloader that mirrors the
desktop app, backed by real user accounts and an **audio-less library index**
(metadata only — files live on the user's device, never on the server). On
iPhone/iPad the **+media** app is the download client and holds the files;
the desktop browser gets a plain download to the Files/Downloads folder.

## Key architectural facts

- **The existing online tool IS the ephemeral, queued, capped engine.** `run_job()`,
  the `dispatcher()`, `job_queue`/`job_sema`, `cleanup_worker` (≈15 min file TTL),
  per-IP caps, stall-killer, and the payment-app token gate already exist. `/web`
  reuses all of it — **no Redis/RQ**, staying on the single-file `app.py` convention.
- **Store the index, never the audio.** `library_items` holds title/artist/source
  URL/cover URL/tags/playlist. Re-download on demand from the source URL. This keeps
  server storage flat and keeps us on the "tool, not host" side legally.
- **Subscription status lives in the payment app** (source of truth), per the
  "funnel new SKUs through the payment app" convention. The web app keeps only a
  local `tier` cache until repo 2 lands.

## Freemium tiers (`WEB_TIER_LIMITS` in app.py)

| | free | pro (~$3.99/mo) |
|---|---|---|
| queue lane | standard | **priority** (front of deque) |
| per-file | ~15 min, ~200 MB | uncapped |
| daily downloads | 10 | 500 |
| library index | (unbounded for now) | (unbounded) |

Two cost centers → two levers: **priority** protects responsiveness (CPU/ffmpeg);
**daily count + size caps** protect bandwidth egress (the real bill).

## Repo 1 — `yt-web-ui` (this repo) — STATUS: A–D IMPLEMENTED (uncommitted)

Backend block after the IP-limit helpers; routes before `@app.before_request`;
`WEB_HTML` page constant just above the routes.

- **A. Accounts** — `users.db` (`users`, `sessions`, `usage`, `library_items`).
  `POST /web/signup`, `/web/login`, `/web/logout`, `GET /web/me`. Passwords via
  `generate_password_hash(method="pbkdf2:sha256")`. Session = opaque
  `secrets.token_urlsafe` stored as a SHA-256 hash; delivered as an HttpOnly
  `web_session` cookie (browser) **and** returned in the JSON body as a Bearer
  token (the iOS app). `_current_web_user()` resolves either.
- **B. Mobile-first page** — `GET /web` renders `WEB_HTML` (on-brand, mobile-first,
  vanilla JS). Login/signup → downloader → live queue/progress → library grid with
  delete. iOS-detected banner points to +media. Served via `Response(...)` (no
  Jinja) so the page's JS braces are safe; `__IOS_URL__` placeholder replaced.
- **C. Priority queue** — jobs carry `user_id` + `priority`. Priority jobs
  `appendleft` onto the **same** `job_queue`; standard `append`. `dispatcher()` and
  `queue_position()` unchanged. (Within the priority group, order is LIFO — fine at
  this scale.)
- **D. Caps + library API** — `POST /web/start` (auth-gated) enforces the daily cap
  before queuing and stamps the job with tier caps. `run_job()` injects
  `--max-filesize` / `--match-filter "duration <=? N"` from those fields (legacy
  online-tool jobs have them `None` → unchanged). `GET/POST /web/api/library` +
  `DELETE /web/api/library/<id>` (per-user, de-duped by source URL). `/download`
  gained an **ownership check**: `/web` jobs (those with `user_id`) are 403 to
  anyone but the owner; legacy anonymous jobs stay publicly fetchable by id.

Verified: `ast.parse` + `node --check` (extracted page JS) + a live isolated-port
smoke test (signup/dup/weak-pw, cookie & Bearer auth, library add/dedupe/list,
`/web/start` validation + daily-usage bump, `/download` cross-user 403).

### Remaining in repo 1 (not yet done)
- **Per-file caps on Spotify/Apple playlist tracks** — those build their own
  `track_cmd` at run_job ~4728/4856 and don't yet get `cap_args`. Track-count cap
  still applies.
- **CSP for external cover thumbnails** — `add_security_headers` CSP `img-src`
  doesn't allow external hosts, so covers won't render in the browser view (they
  work in +media, which isn't subject to CSP). Relax `img-src` for `/web` if we
  want covers on the web.
- **Playlists** — `library_items.playlist` column exists; no playlist CRUD/UI yet.
- **HQ formats for pro** — tier has the flag conceptually; formats not yet
  differentiated (still bestaudio→mp3 / bv*+ba→mp4).
- **F. Retire the old tool** — decision pending: hard-remove vs 301 the anonymous
  download entry points to `/web`.
- **Email verification / password reset** — deferred: outbound SMTP is DO-blocked
  on the droplet; needs the HTTPS mail-API TODO, or Sign-in-with-Apple on iOS.

## Repo 2 — payment app (`sovereignpaymentapp`, on the droplet) — NOT STARTED
- Recurring Stripe Price `STRIPE_PRICE_WEB_SUB` in `.env`.
- Web app creates a subscription-mode checkout with `client_reference_id = user_id`.
- Webhook on `customer.subscription.*` records `{user_id → active/tier}`.
- Internal `payment/api/access/internal/subscription/check?user_id=` (mirrors the
  token-check call + `x-internal-secret`). Then `_web_user_tier()` consults it.

## Repo 3 — `downloads-ios` / +media (1.5.0) — NOT STARTED
- `CloudAuthManager` singleton (mirrors `PCloudClient`): login → Bearer token in
  Keychain (new `Keychain.Item` case).
- `CloudBackendClient` (mirrors `PCloudAPI` + `DesktopSyncViewModel.downloadSelected`):
  `POST /web/start` → poll `/status` → `URLSession.download /download/<id>` → move
  into the user's folder → `FileScanner` rescan. Downloaded tracks become normal
  `.localFile` items, so playback is unchanged.
- Library-index sync from `GET /web/api/library`; missing-locally entries shown as
  `cloudOnly` (the `CloudStatus` enum already models this).
- Deep-link `space-digitaldownloads://download?...` so `/web` on mobile Safari hands
  off to the app (URL scheme already registered).

## Client-direct fetch — VALIDATED (2026-08-27), reshapes the cost model

The residential-proxy bill is per-GB, and it's the dominant cost. **Prototype proved
we can move the bytes off the proxy entirely** for the mobile path:

- **Extraction:** `yt-dlp --extractor-args "youtube:player_client=android_vr" -f 140 -g <url>`
  yields an m4a googlevideo URL with **no `po_token`** needed. Extraction is tiny
  (~KB of API traffic) — cheap to proxy even if the server IP is bot-walled.
- **Fetch portability:** a URL minted by one IP **can be fetched by a different IP**
  — confirmed cross-IP (Mac→droplet = 206) and on a real phone over cellular (all
  test clips played). The `ip` param in `sparams` is not enforced at fetch time.
- **Client requirements:** fetch with **Range requests + follow redirects** (a full
  GET without Range → 403; the `&range=0-N` query param also works for a plain GET).
  itag 140 (m4a/AAC) plays natively in AVPlayer — **no server ffmpeg for audio**.
- **Browser caveats (native app unaffected):** a browser `<audio>` tag can't *play*
  raw DASH itag 140 even when bytes fetch fine (use itag 18 progressive to test in a
  browser); googlevideo sends no permissive CORS so browser JS `fetch()` can't read
  status. `URLSession` in +media has neither limitation.

**Architecture impact:** **`POST /web/api/resolve` is BUILT** — returns the direct
googlevideo URL + metadata (`_resolve_direct` via `yt-dlp -J`; audio itag 140,
video itag 18; extraction through proxy/cookies, media fetched by the client). Same
tier rules as `/web/start` (video→402, daily/duration caps, usage bump); non-YouTube
→415 (use `/web/start`). Verified end-to-end (returned URL fetched 206). **+media
fetches the media directly from Google** (Repo 3) → proxy carries ~none of the bytes
→ **~95% proxy-cost cut**, no server transcode for audio. `run_job` stays the
fallback (desktop browser, formats needing mux). Video Pro-gated (DASH mux is harder;
progressive itag 18 is 360p-only).

Dev tooling for this lives at `GET /web/dev/portability` (gated by `WEB_DEV_TOOLS=1`).

## Cross-cutting risks
1. **Cloudflare may 403 scripted requests** from the +media API client (same reason
   the payment app's public host is loopback-only). Verify early; may need an API
   path/subdomain that skips the challenge.
2. **SMTP is DO-blocked** → no verification/reset email yet (see above).
3. **Bandwidth egress** is the real scaling cost (every byte pulled + pushed through
   the droplet).
4. **The online engine is currently hard-paused** (Decodo proxy over quota) — `/web`
   downloads won't run end-to-end until the proxy is restored.

## Build order
1. Repo 1 A–D ✅ → usable download-only web app, no paywall.
2. Repo 2 + web gating → subscription live.
3. Repo 3 → +media becomes the mobile client.
