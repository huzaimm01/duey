"use strict";
/* Duey background worker.
   Every minute it asks the local Duey app how often to check. When it's time, it reads your
   deadlines from the course portal you're already logged into and hands them to Duey on this
   computer (127.0.0.1). Nothing leaves your machine except the portal request itself. */

const PORTS = Array.from({length: 15}, (_, i) => 8777 + i);
const ALARM = "duey-tick";
const DAY = 86400;
const get = keys => chrome.storage.local.get(keys);
const set = obj => chrome.storage.local.set(obj);

class PErr extends Error {}

/* ---------- finding Duey ---------- */
async function findDuey(preferred){
  const order = preferred ? [preferred, ...PORTS.filter(p => p !== preferred)] : PORTS;
  for (const port of order){
    try {
      const ctl = new AbortController();
      const t = setTimeout(() => ctl.abort(), 700);
      const r = await fetch(`http://127.0.0.1:${port}/api/ping`, {signal: ctl.signal});
      clearTimeout(t);
      const ping = await r.json();
      if (ping && ping.duey) return {port, ping};
    } catch (e) { /* not this port */ }
  }
  return null;
}
async function post(port, body){
  try {
    const r = await fetch(`http://127.0.0.1:${port}/api/ingest`, {
      method: "POST", headers: {"Content-Type": "application/json"}, body: JSON.stringify(body)});
    return await r.json();
  } catch (e) { return {ok: false, error: "Duey isn't running. Start it and the extension will catch up."}; }
}

/* ---------- reading the portal ---------- */
function rootOf(url){
  const u = new URL(url);
  const path = u.pathname.split(/\/(?:login|my|course|mod|user|calendar|index\.php|webservice|blocks|grade|enrol|admin)(?:\/|$)/)[0];
  return u.origin + path.replace(/\/$/, "");
}
const MOD = {assign: "assignment", quiz: "quiz", forum: "discussion", workshop: "assignment", lesson: "assignment"};
function guessKind(name){
  const t = (name || "").toLowerCase();
  if (t.includes("quiz")) return "quiz";
  if (/exam|test/.test(t)) return "exam";
  if (/discussion|forum/.test(t)) return "discussion";
  return "assignment";
}

async function readPortal(root){
  let page, html;
  try {
    page = await fetch(root + "/my/", {credentials: "include"});
    html = await page.text();
  } catch (e) {
    throw new PErr("Couldn't open your course portal. Log in to it in a browser tab, then press Check now.");
  }
  if (/\/login\//.test(page.url)) throw new PErr("You're logged out of your course portal. Log in again and Duey will catch up.");
  if (!/M\.cfg/.test(html)) throw new PErr("This site doesn't look like a course portal Duey can read.");
  const sk = (html.match(/"sesskey":"([^"]+)"/) || [])[1];
  const wr = (html.match(/"wwwroot":"([^"]+)"/) || [])[1];
  if (!sk || !wr) throw new PErr("Couldn't read your portal's page. It may be a version Duey doesn't support yet.");
  const base = JSON.parse('"' + wr + '"');

  const now = Math.floor(Date.now() / 1000);
  const out = [];
  let after = 0;
  for (let i = 0; i < 8; i++){
    const args = {timesortfrom: now - 14 * DAY, timesortto: now + 180 * DAY, limitnum: 50, limittononsuspendedevents: true};
    if (after) args.aftereventid = after;
    const method = "core_calendar_get_action_events_by_timesort";
    let js;
    try {
      const res = await fetch(`${base}/lib/ajax/service.php?sesskey=${encodeURIComponent(sk)}&info=${method}`, {
        method: "POST", credentials: "include", headers: {"Content-Type": "application/json"},
        body: JSON.stringify([{index: 0, methodname: method, args}])});
      js = await res.json();
    } catch (e) { throw new PErr("Couldn't read your deadlines from the portal. Try again in a minute."); }
    const first = Array.isArray(js) ? js[0] : null;
    if (!first) throw new PErr("Your portal answered in a way Duey doesn't understand.");
    if (first.error){
      const code = (first.exception && first.exception.errorcode) || "";
      if (/login|sesskey/i.test(code)) throw new PErr("You're logged out of your course portal. Log in again and Duey will catch up.");
      throw new PErr("Your portal said: " + ((first.exception && first.exception.message) || "something went wrong") + ".");
    }
    const events = (first.data && first.data.events) || [];
    for (const ev of events){
      const due = ev.timesort || ev.timestart;
      if (!due) continue;
      const action = ev.action || {};
      out.push({
        id: "a-" + ev.id,
        course: (ev.course && ev.course.fullname) || "General",
        title: (ev.name || "").replace(/\s+(is due|closes|is open until|due)$/i, "").trim() || "Untitled",
        due: Number(due),
        url: action.url || ev.url || "",
        desc: ev.description || "",
        kind: MOD[ev.modulename] || guessKind(ev.name)
      });
    }
    if (events.length < 50) break;
    after = (first.data && first.data.lastid) || events[events.length - 1].id;
  }
  return out;
}

/* ---------- syncing ---------- */
let busy = false;
async function syncNow(){
  if (busy) return {ok: false, error: "Already checking, hang on a sec."};
  busy = true;
  try {
    const st = await get(["root", "code", "port"]);
    if (!st.root || !st.code) return {ok: false, error: "Not set up yet."};
    let items;
    try { items = await readPortal(st.root); }
    catch (e) {
      const msg = e instanceof PErr ? e.message : "Something unexpected happened while reading your portal.";
      await set({lastError: msg, lastAttempt: Date.now()});
      const d = await findDuey(st.port);
      if (d) await post(d.port, {code: st.code, error: msg});
      await badge();
      return {ok: false, error: msg};
    }
    await set({items, lastAttempt: Date.now(), lastSync: Date.now(), lastError: ""});
    await badge();
    const d = await findDuey(st.port);
    if (!d) return {ok: true, duey: false};
    const r = await post(d.port, {code: st.code, items});
    if (!r.ok){ await set({lastError: r.error || "Duey didn't accept the update."}); return {ok: false, error: r.error}; }
    await set({port: d.port});
    return {ok: true, duey: true, count: items.length};
  } finally { busy = false; }
}

async function tick(){
  const st = await get(["root", "code", "port", "lastAttempt", "lastError"]);
  if (!st.root || !st.code) return;
  const d = await findDuey(st.port);
  const every = Math.max(d ? Number(d.ping.every) || 5 : 15, st.lastError ? 2 : 1);
  const timeIsUp = !st.lastAttempt || Date.now() - st.lastAttempt >= every * 60000 - 5000;
  if (timeIsUp || (d && d.ping.want)) await syncNow();
}

async function badge(){
  const {items = []} = await get(["items"]);
  const now = Date.now() / 1000;
  const n = items.filter(i => i.due < now + 2 * DAY).length;
  chrome.action.setBadgeBackgroundColor({color: items.some(i => i.due < now) ? "#9A2B3B" : "#12172E"});
  chrome.action.setBadgeText({text: n ? String(n) : ""});
}

/* ---------- what the popup asks for ---------- */
async function view(){
  const st = await get(null);
  const d = await findDuey(st.port);
  let state = null;
  if (d){
    try { state = await (await fetch(`http://127.0.0.1:${d.port}/api/state`)).json(); } catch (e) { /* ignore */ }
  }
  return {st, port: d ? d.port : null, state};
}

async function handle(msg){
  if (msg.type === "view") return view();
  if (msg.type === "sync") return syncNow();
  if (msg.type === "connect"){
    const d = await findDuey(null);
    if (!d) return {ok: false, error: "Duey isn't running. Start it (run duey.py), then try again."};
    const chk = await post(d.port, {code: msg.code, check: true});
    if (!chk.ok) return {ok: false, error: chk.error || "That pairing code didn't work."};
    await set({root: msg.root, code: String(msg.code).trim().toUpperCase(), port: d.port, lastError: "", items: []});
    return syncNow();
  }
  if (msg.type === "disconnect"){
    await chrome.storage.local.clear();
    chrome.action.setBadgeText({text: ""});
    return {ok: true};
  }
  return {ok: false};
}

chrome.runtime.onMessage.addListener((msg, _sender, send) => { handle(msg).then(send); return true; });
chrome.alarms.onAlarm.addListener(a => { if (a.name === ALARM) tick(); });
function ensureAlarm(){ chrome.alarms.get(ALARM, a => { if (!a) chrome.alarms.create(ALARM, {periodInMinutes: 1}); }); }
chrome.runtime.onInstalled.addListener(ensureAlarm);
chrome.runtime.onStartup.addListener(() => { ensureAlarm(); tick(); });
ensureAlarm();
