# +downloads browser extension

A Manifest V3 extension that sends the page you're on to the **+downloads desktop
app** in one click, via the app's token-guarded `POST /external/start` endpoint on
`127.0.0.1:5055`.

## How it works

- **Context menu** "Download this page / link with +downloads" (right-click) and a
  **toolbar popup** (download the current tab as video or audio).
- The extension pairs with the app using a **per-install token**. On first use it
  calls `GET /external/token` (allowed because the extension has an explicit
  `host_permissions` entry for `127.0.0.1:5055`; a normal website can't read it —
  CORS blocks that cross-origin read). The token is then sent as the
  `X-Downloads-Token` header on every `/external/start` call.
- Everything stays on the machine — the extension only ever talks to localhost.

## Security model

`/external/start` trusts the loopback peer, so without a guard any website could
POST downloads to it. The guard is:
1. **Pairing token** (`X-Downloads-Token`, constant-time compared) — the load-bearing
   control. A random website doesn't have it and can't read it.
2. **Origin allowlist** — only extension origins + the supported media sites get CORS
   headers back; never `*`.
3. **Loopback-only** peer check, plus Chrome's Private-Network-Access preflight.

## Load unpacked (development)

- **Chrome/Edge:** `chrome://extensions` → enable Developer mode → *Load unpacked* →
  pick this folder.
- **Firefox:** `about:debugging` → *This Firefox* → *Load Temporary Add-on* → pick
  `manifest.json`.

Then open the +downloads desktop app, click the extension's **Connect** button
(Options), and right-click any video to download.

## Packaging for the stores

- Chrome Web Store: zip the contents of this folder (not the folder itself).
- Firefox AMO: zip likewise; the `browser_specific_settings.gecko.id` is set.
- Safari: wrap via Xcode (`xcrun safari-web-extension-converter`) — phase 2; Safari
  is stricter about localhost fetches from extensions.

Keep `version` in `manifest.json` in step with the desktop app's `VERSION`.
