// +downloads browser extension — background service worker (MV3).
// Sends the current page (or a right-clicked link) to the local +downloads desktop
// app at 127.0.0.1:5055 via the token-guarded /external/start endpoint.

const api = globalThis.browser || globalThis.chrome;
const BASE = "http://127.0.0.1:5055";

// ---- menus ----------------------------------------------------------------
api.runtime.onInstalled.addListener(() => {
  api.contextMenus.create({
    id: "dl-page",
    title: "Download this page with +downloads",
    contexts: ["page", "video", "audio"]
  });
  api.contextMenus.create({
    id: "dl-link",
    title: "Download this link with +downloads",
    contexts: ["link"]
  });
});

api.contextMenus.onClicked.addListener((info, tab) => {
  const url = info.menuItemId === "dl-link"
    ? info.linkUrl
    : (info.pageUrl || (tab && tab.url));
  if (url) startDownload(url);
});

// ---- token ----------------------------------------------------------------
async function getToken() {
  const got = await api.storage.local.get("token");
  return (got && got.token) || "";
}

// ---- the download call ----------------------------------------------------
// Exposed to the popup via runtime messaging so both entry points share it.
async function startDownload(url, opts) {
  const token = await getToken();
  if (!token) {
    notify("Pairing needed", "Open the +downloads extension options and paste your pairing token from Settings.");
    api.runtime.openOptionsPage && api.runtime.openOptionsPage();
    return { ok: false, error: "no_token" };
  }
  const body = Object.assign({ url }, opts || {});
  let res, payload;
  try {
    res = await fetch(BASE + "/external/start", {
      method: "POST",
      headers: { "Content-Type": "application/json", "X-Downloads-Token": token },
      body: JSON.stringify(body)
    });
  } catch (e) {
    notify("+downloads isn't running", "Open the +downloads desktop app, then try again.");
    return { ok: false, error: "unreachable" };
  }
  payload = await res.json().catch(() => ({}));
  if (res.ok) {
    const n = payload.track_count || 1;
    notify("Queued in +downloads", n > 1 ? ("Queued " + n + " tracks.") : "Download queued.");
    return { ok: true, payload };
  }
  if (res.status === 403 && payload.error === "bad_token") {
    notify("Pairing token rejected", "Re-copy the token from +downloads Settings into the extension options.");
    api.runtime.openOptionsPage && api.runtime.openOptionsPage();
  } else if (payload.error === "upgrade_required") {
    notify("Full version needed", payload.message || "This site needs the full +downloads.");
  } else {
    notify("Couldn't queue", payload.message || payload.error || ("Error " + res.status));
  }
  return { ok: false, error: payload.error || String(res.status), payload };
}

// ---- popup bridge ---------------------------------------------------------
api.runtime.onMessage.addListener((msg, sender, sendResponse) => {
  if (msg && msg.type === "download") {
    startDownload(msg.url, msg.opts).then(sendResponse);
    return true; // async response
  }
});

function notify(title, message) {
  try {
    api.notifications.create({
      type: "basic",
      iconUrl: api.runtime.getURL("icons/icon-128.png"),
      title: title,
      message: message
    });
  } catch (e) { /* notifications optional */ }
}
