"use strict";
const $ = s => document.querySelector(s);
const esc = s => String(s == null ? "" : s).replace(/[&<>"']/g, c => ({"&":"&amp;","<":"&lt;",">":"&gt;",'"':"&quot;","'":"&#39;"}[c]));
const COLORS = ["a1","a2","a3","a4","a5","a6"];
const DAY = 86400;
let V = null, tabInfo = null;

/* ---------- time helpers (same wording as the app) ---------- */
const nowS = () => Date.now()/1000;
const plural = (n, w) => n + " " + w + (n === 1 ? "" : "s");
const fmtDue = ts => new Date(ts*1000).toLocaleString(undefined,{weekday:"short",day:"numeric",month:"short",hour:"numeric",minute:"2-digit"});
function calDays(ts){
  const a = new Date(ts*1000), b = new Date();
  a.setHours(0,0,0,0); b.setHours(0,0,0,0);
  return Math.round((a-b)/(DAY*1000));
}
function rel(ts){
  const d = ts - nowS(), a = Math.abs(d);
  if (d < 0){
    if (a < 3600) return "just passed";
    if (a < DAY) return "overdue by " + plural(Math.round(a/3600),"hour");
    return "overdue by " + plural(Math.round(a/DAY),"day");
  }
  if (a < 3600) return "in under an hour";
  const cd = calDays(ts);
  if (cd === 0) return "today, in " + plural(Math.round(a/3600),"hour");
  if (cd === 1) return "tomorrow";
  return "in " + plural(cd,"day");
}
function ago(ts){
  if (!ts) return "never";
  const s = nowS() - ts;
  if (s < 90) return "just now";
  if (s < 3600) return plural(Math.round(s/60),"minute") + " ago";
  if (s < DAY) return plural(Math.round(s/3600),"hour") + " ago";
  return plural(Math.round(s/DAY),"day") + " ago";
}
function urgency(it){
  const n = nowS();
  if (it.done || it.gone) return "done";
  if (it.due < n) return "late";
  if (n >= it.start) return "go";
  if (it.due - n < 2*DAY) return "soon";
  return "calm";
}
let names = [];
const courseColor = name => COLORS[Math.max(0, names.indexOf(name)) % COLORS.length];

function rootOf(url){
  const u = new URL(url);
  const path = u.pathname.split(/\/(?:login|my|course|mod|user|calendar|index\.php|webservice|blocks|grade|enrol|admin)(?:\/|$)/)[0];
  return u.origin + path.replace(/\/$/, "");
}

/* ---------- data ---------- */
function currentItems(){
  if (V.state && V.state.configured) return V.state.items;
  return ((V.st && V.st.items) || []).map(i => Object.assign({}, i, {start: i.due - 2*DAY, prep: 2, done: false, gone: false}));
}

/* ---------- views ---------- */
function card(it){
  const u = urgency(it), col = courseColor(it.course);
  const span = Math.max(1, it.due - it.start);
  const pct = Math.max(0, Math.min(1, (nowS() - it.start) / span));
  const x = Math.round(3 + pct*94);
  const title = it.url ? `<a href="${esc(it.url)}" target="_blank" rel="noopener noreferrer">${esc(it.title)}</a>` : esc(it.title);
  return `<article class="card u-${u}">
    <div class="top"><span class="chip" style="background:var(--${col}-t)"><i style="background:var(--${col})"></i><span>${esc(it.course)}</span></span>
      <span class="pill">${esc(rel(it.due))}</span></div>
    <h3>${title}</h3>
    <div class="when">Due ${esc(fmtDue(it.due))}</div>
    <div class="track" aria-hidden="true"><div class="fill" style="width:${x}%"></div><div class="you" style="left:${x}%"></div></div>
  </article>`;
}
function group(title, list){
  if (!list.length) return "";
  return `<section class="group"><h2>${esc(title)}</h2><div class="cards">${list.map(card).join("")}</div></section>`;
}

function renderSetup(){
  const site = tabInfo ? `<span class="site">${esc(tabInfo.host)}</span>` : "";
  const hasSite = !!tabInfo;
  $("#root").innerHTML = `
    <h1>Connect Duey to your course portal</h1>
    <p class="sub">Two steps, once. Your password is never shared.</p>
    <ol class="steps">
      <li><b>1. Be on your course portal</b>
        ${hasSite ? `Duey will read deadlines from ${site}. Not the right site? Switch to your portal's tab and click the Duey icon again.`
                  : "Open your course portal in this tab and log in, then click the Duey icon again."}</li>
      <li><b>2. Type the pairing code</b>
        Find it in the Duey app: Settings, then Browser extension.
        <input type="text" id="code" maxlength="9" placeholder="XXXX-XXXX" autocomplete="off" spellcheck="false"></li>
    </ol>
    <div class="foot"><button class="btn primary" data-act="connect" ${hasSite ? "" : "disabled"}>Connect</button></div>
    <div class="status" id="status" role="status"></div>`;
  $("#syncBtn").hidden = true;
}

function renderMain(){
  const items = currentItems();
  names = [...new Set(items.map(i => i.course))].sort();
  const open = items.filter(i => !i.done && !i.gone);
  const late = open.filter(i => urgency(i) === "late");
  const go = open.filter(i => urgency(i) === "go");
  const soon = open.filter(i => urgency(i) === "soon" || (urgency(i) === "calm" && i.due - nowS() < 7*DAY));
  const dueWeek = open.filter(i => i.due - nowS() < 7*DAY).length;

  let h1;
  if (late.length && !go.length) h1 = plural(late.length,"thing") + " slipped past its deadline";
  else if (go.length) h1 = plural(go.length,"thing") + " to start today";
  else if (soon.length) h1 = plural(soon.length,"deadline") + " this week, nothing to start yet";
  else if (open.length) h1 = "Nothing pressing today";
  else h1 = "You're all caught up";

  const lastSync = V.state && V.state.configured ? V.state.last_sync : Math.floor(((V.st && V.st.lastSync) || 0)/1000);
  let html = `<h1>${esc(h1)}</h1>
    <div class="stats">
      <div class="stat ${late.length ? "warn" : ""}"><b>${late.length}</b><span>Overdue</span></div>
      <div class="stat ${go.length ? "go" : ""}"><b>${go.length}</b><span>Start today</span></div>
      <div class="stat"><b>${dueWeek}</b><span>Due this week</span></div>
    </div>`;

  if (V.st.lastError) html += `<div class="banner" role="alert"><strong>Couldn't read your portal.</strong> ${esc(V.st.lastError)}</div>`;
  if (!V.port) html += `<div class="banner info"><strong>Duey isn't running.</strong> Start it for reminders, study help and videos. Showing your last update.</div>`;

  const shown = late.length + go.length + soon.length;
  if (!shown){
    html += `<div class="empty"><h3>${open.length ? "Nothing needs you right now" : "No upcoming deadlines"}</h3>
      <p>${open.length ? "Everything left is further away. Duey will nudge you when it's time to start." : "Either you're free, or your portal has nothing listed yet."}</p></div>`;
  } else {
    html += group("Overdue", late) + group("Start these now", go) + group("Due this week", soon);
  }

  html += `<div class="foot">
      <a class="btn primary" ${V.port ? `href="http://127.0.0.1:${V.port}" target="_blank" rel="noopener noreferrer"` : "aria-disabled=\"true\" style=\"opacity:.55;pointer-events:none\""}>Open Duey for study help, videos and AI help</a>
    </div>
    <div class="meta"><span>Last checked ${esc(ago(lastSync))}</span><button class="linkbtn" data-act="disconnect">Disconnect</button></div>`;
  $("#root").innerHTML = html;
  $("#syncBtn").hidden = false;
}

function render(){
  if (!V.st || !V.st.root || !V.st.code) renderSetup(); else renderMain();
}
async function load(){
  V = await chrome.runtime.sendMessage({type: "view"});
  render();
}
function status(msg, cls){ const el = $("#status"); if (el){ el.textContent = msg; el.className = "status " + (cls || ""); } }

/* ---------- actions ---------- */
document.addEventListener("click", async e => {
  const b = e.target.closest("[data-act]");
  if (!b) return;
  const act = b.dataset.act;
  if (act === "connect"){
    const code = $("#code").value.trim();
    if (!code) return status("Type the pairing code from Duey first.", "err");
    let granted = false;
    try { granted = await chrome.permissions.request({origins: [tabInfo.root + "/*"]}); } catch (err) { /* denied */ }
    if (!granted) return status("Duey needs your OK to read this site. Press Connect again and allow it.", "err");
    status("Connecting\u2026");
    b.disabled = true;
    const r = await chrome.runtime.sendMessage({type: "connect", code, root: tabInfo.root});
    b.disabled = false;
    if (!r.ok && !(await chrome.storage.local.get("root")).root) return status(r.error, "err");
    await load();
  } else if (act === "sync"){
    b.disabled = true; b.textContent = "Checking\u2026";
    await chrome.runtime.sendMessage({type: "sync"});
    b.disabled = false; b.textContent = "Check now";
    await load();
  } else if (act === "disconnect"){
    await chrome.runtime.sendMessage({type: "disconnect"});
    await load();
  }
});

(async function init(){
  try {
    const [tab] = await chrome.tabs.query({active: true, currentWindow: true});
    if (tab && /^https?:/.test(tab.url || "") && !/^https?:\/\/(127\.0\.0\.1|localhost)/.test(tab.url)) tabInfo = {host: new URL(tab.url).host, root: rootOf(tab.url)};
  } catch (e) { /* no tab info */ }
  await load();
})();
