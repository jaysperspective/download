const api = globalThis.browser || globalThis.chrome;

const statusEl = document.getElementById("status");

document.getElementById("opts").addEventListener("click", () => {
  api.runtime.openOptionsPage();
});

document.getElementById("go").addEventListener("click", async () => {
  const btn = document.getElementById("go");
  const type = document.getElementById("fmt").value;
  const tabs = await api.tabs.query({ active: true, currentWindow: true });
  const url = tabs && tabs[0] && tabs[0].url;
  if (!url || !/^https?:/i.test(url)) {
    statusEl.textContent = "No downloadable page in this tab.";
    return;
  }
  btn.disabled = true;
  statusEl.textContent = "Sending to +downloads…";
  const res = await api.runtime.sendMessage({ type: "download", url, opts: { type } });
  btn.disabled = false;
  if (res && res.ok) {
    const n = (res.payload && res.payload.track_count) || 1;
    statusEl.textContent = n > 1 ? ("Queued " + n + " tracks ✓") : "Queued ✓";
    statusEl.style.color = "#48c78e";
  } else if (res && res.error === "no_token") {
    statusEl.textContent = "Paste your pairing token first →";
  } else if (res && res.error === "unreachable") {
    statusEl.textContent = "Is the +downloads app running?";
    statusEl.style.color = "#ff6b6b";
  } else {
    statusEl.textContent = (res && (res.payload && (res.payload.message || res.payload.error))) || "Couldn't queue.";
    statusEl.style.color = "#ff6b6b";
  }
});
