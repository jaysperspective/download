const api = globalThis.browser || globalThis.chrome;
const BASE = "http://127.0.0.1:5055";
const statusEl = document.getElementById("status");

function setStatus(msg, cls) {
  statusEl.textContent = msg;
  statusEl.className = "status" + (cls ? " " + cls : "");
}

// Show the current pairing state on load.
(async () => {
  const got = await api.storage.local.get("token");
  if (got && got.token) setStatus("Paired ✓ — you're ready to download.", "ok");
})();

// Auto-connect: the extension has host permission for 127.0.0.1:5055, so it can read
// the install's pairing token directly (a website cannot — CORS blocks that read).
document.getElementById("connect").addEventListener("click", async () => {
  setStatus("Connecting…");
  let token;
  try {
    const res = await fetch(BASE + "/external/token");
    if (!res.ok) throw new Error("status " + res.status);
    token = (await res.json()).token;
  } catch (e) {
    setStatus("Couldn't reach +downloads. Make sure the app is open, then try again.", "err");
    return;
  }
  if (!token) { setStatus("No token returned by the app.", "err"); return; }
  await api.storage.local.set({ token });
  setStatus("Paired ✓ — you're ready to download.", "ok");
});

// Manual fallback.
document.getElementById("save").addEventListener("click", async () => {
  const token = document.getElementById("token").value.trim();
  if (!token) { setStatus("Paste a token first.", "err"); return; }
  await api.storage.local.set({ token });
  setStatus("Token saved ✓", "ok");
});
