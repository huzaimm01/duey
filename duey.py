#!/usr/bin/env python3
"""
Duey  -  your friendly deadline buddy, for whatever portal your school uses
=============================================================================

WHAT IT DOES
  * Pulls your deadlines from your school's course portal and keeps them fresh
  * Tells you when an instructor moves a date or edits the instructions
  * Guesses how long each task needs and starts nudging you that many days ahead
  * Pings you on the page AND by email
  * Reads the assignment brief and suggests what to study + YouTube videos

WHO THIS WORKS WITH
  Duey speaks two underlying systems under the hood and figures out which one
  your school is running automatically - you never have to tell it. Between
  those two systems, and the universal calendar-link option, it covers the
  vast majority of school course portals, whatever your school happens to
  brand its portal as.

HOW TO RUN (no installs needed, just Python 3.9 or newer)
  1.  python duey.py          (or double-click it / run "python3 duey.py")
  2.  Your browser opens. Click the sliders icon (top right) and paste your details.
  3.  Leave the window open. Duey keeps checking in the background.

Your settings and data are saved in a folder in your home directory
(~/.duey), NOT next to this file, so you can't accidentally upload your
passwords or tokens to GitHub.
"""

import gzip
import hashlib
import hmac
import html
import json
import os
import re
import secrets
import smtplib
import sqlite3
import sys
import threading
import time
import urllib.error
import urllib.parse
import urllib.request
import webbrowser
from collections import Counter
from datetime import datetime, timedelta, timezone
from email.message import EmailMessage
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

if sys.version_info < (3, 9):
    sys.exit("Duey needs Python 3.9 or newer. Get it free at python.org")
try:
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")
except Exception:
    pass

DEFAULT_PORT = 8777
DATA_DIR = os.path.join(os.path.expanduser("~"), ".duey")
CONFIG_PATH = os.path.join(DATA_DIR, "config.json")
DB_PATH = os.path.join(DATA_DIR, "duey.db")
os.makedirs(DATA_DIR, exist_ok=True)

DEFAULTS = {
    "mode": "ical",            # "ical" = paste a calendar link, "api" = use an access token
    "base_url": "",
    "ical_url": "",
    "token": "",
    "api_kind": "",            # auto-detected: which system the access token speaks to
    "email_enabled": False,
    "email_to": "",
    "smtp_host": "",
    "smtp_port": 587,
    "smtp_user": "",
    "smtp_pass": "",
    "sync_minutes": 5,
    "youtube_key": "",
    "anthropic_key": "",
}
SECRET_KEYS = ("token", "ical_url", "smtp_pass", "youtube_key", "anthropic_key")
CLAUDE_MODEL = "claude-haiku-4-5-20251001"
EXT_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), "duey-extension")
EXT_HINT = " Or choose Browser extension in settings \u2014 it works without a security key."

# Built-in sender so students only type their email. Set these as environment variables on
# the machine running Duey (use a dedicated throwaway mail account, never a personal one).
# Do NOT paste a password into this file if you share it with others.
DUEY_SENDER = {"host": os.environ.get("DUEY_SMTP_HOST", ""),
               "port": os.environ.get("DUEY_SMTP_PORT", "587"),
               "user": os.environ.get("DUEY_SMTP_USER", ""),
               "pass": os.environ.get("DUEY_SMTP_PASS", "")}


# ----------------------------------------------------------------------------
# Small helpers
# ----------------------------------------------------------------------------
class DueyError(Exception):
    """An error with a message that is safe and helpful to show the student."""

    def __init__(self, msg, code=None):
        super().__init__(msg)
        self.code = code


def load_cfg():
    cfg = dict(DEFAULTS)
    try:
        with open(CONFIG_PATH, encoding="utf-8") as f:
            cfg.update(json.load(f))
    except (OSError, ValueError):
        pass
    return cfg


def save_cfg(cfg):
    tmp = CONFIG_PATH + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(cfg, f, indent=2)
    try:
        os.chmod(tmp, 0o600)
    except OSError:
        pass
    os.replace(tmp, CONFIG_PATH)


def configured(cfg):
    if cfg.get("mode") == "ext":
        return meta_get("ext_paired") == "1"
    if cfg.get("mode") == "api":
        return bool(cfg.get("base_url") and cfg.get("token"))
    return bool(cfg.get("ical_url"))


# A plain Python script's default User-Agent ("Python-urllib/3.x") gets silently
# blocked or challenged by a lot of campus security filters (Cloudflare, Akamai,
# Imperva and similar) that let an ordinary browser straight through. Looking like
# a real browser avoids that entire class of failure.
BROWSER_HEADERS = {
    "User-Agent": ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
                   "(KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36"),
    "Accept": "application/json, text/calendar, text/html, */*",
    "Accept-Language": "en-US,en;q=0.9",
    "Accept-Encoding": "gzip",
}

_BLOCK_MARKERS = (
    ("cloudflare", "A security check (Cloudflare) blocked this request before it reached your "
                   "school's actual system."),
    ("checking your browser", "A security check blocked this request before it reached your "
                              "school's actual system."),
    ("captcha", "Your school's site asked for a CAPTCHA, which Duey can't complete on its own."),
    ("access denied", "Your school's site refused the request outright (\u201cAccess Denied\u201d)."),
    ("incapsula", "A security check (Imperva/Incapsula) blocked this request before it reached "
                 "your school's actual system."),
)


def _diagnose_block(body):
    low = (body or "")[:4000].lower()
    for marker, msg in _BLOCK_MARKERS:
        if marker in low:
            return msg + " This isn't something Duey can get around \u2014 try again in a few " \
                        "minutes, or check with your campus IT whether automated/API access is " \
                        "blocked for your account."
    return None


def _slow_msg(host, timeout):
    return ("%s took longer than %d seconds to answer. It may just be slow right now, and Duey will keep "
            "trying. If it keeps happening, open your calendar link in a browser to see whether it loads." % (host, timeout))


def _read_body(r):
    raw = r.read()
    if (r.headers.get("Content-Encoding") or "").lower() == "gzip":
        try:
            raw = gzip.decompress(raw)
        except Exception:
            pass
    return raw.decode("utf-8", "replace")


def http(url, data=None, headers=None, timeout=30, retries=0):
    """Fetch a URL. Slow portals get a second try before we give up."""
    for attempt in range(retries + 1):
        try:
            return _http_once(url, data, headers, timeout)
        except DueyError as e:
            if e.code != "timeout" or attempt == retries:
                raise
            time.sleep(2)


def _http_once(url, data=None, headers=None, timeout=30):
    url = (url or "").strip()
    send_headers = dict(BROWSER_HEADERS)
    send_headers.update(headers or {})
    req = urllib.request.Request(url, data=data, headers=send_headers)
    try:
        with urllib.request.urlopen(req, timeout=timeout) as r:
            return _read_body(r), r.headers
    except urllib.error.HTTPError as e:
        body = ""
        try:
            body = _read_body(e)
        except Exception:
            pass
        blocked = _diagnose_block(body)
        if blocked:
            raise DueyError(blocked, "blocked")  # a distinct marker: retrying other API shapes is pointless
        if e.code == 403:
            raise DueyError("Your school's site said \u201cforbidden\u201d (403). Double-check the "
                            "address and token/link, or your school may be blocking this kind of "
                            "access entirely.", 403)
        if e.code == 429:
            raise DueyError("Your school's site says Duey is asking too often (429). Wait a few "
                            "minutes and try again, or check for updates less frequently in "
                            "settings.", 429)
        raise DueyError("The server answered with error %s." % e.code, e.code)
    except urllib.error.URLError as e:
        host = urllib.parse.urlparse(url).netloc or url
        reason = getattr(e, "reason", e)
        if isinstance(reason, TimeoutError) or "timed out" in str(reason).lower():
            raise DueyError(_slow_msg(host, timeout), "timeout")
        if "ssl" in str(reason).lower() or "certificate" in str(reason).lower():
            raise DueyError("Couldn't make a secure connection to %s (certificate problem). "
                            "Double-check the address is correct and starts with https://." % host)
        raise DueyError("Couldn't reach %s. Check the address and your internet connection." % host)
    except (TimeoutError, OSError):
        raise DueyError(_slow_msg(urllib.parse.urlparse(url).netloc or "your school's site", timeout), "timeout")


def strip_html(s):
    s = re.sub(r"(?is)<(script|style).*?</\1>", " ", s or "")
    s = re.sub(r"(?i)<br\s*/?>|</p>|</li>|</div>|</h\d>|</tr>", "\n", s)
    s = re.sub(r"<[^>]+>", " ", s)
    s = html.unescape(s)
    s = re.sub(r"[ \t\r\f\v\u00a0]+", " ", s)
    s = re.sub(r"\s*\n\s*", "\n", s)
    return s.strip()[:8000]


def fmt_dt(ts):
    d = datetime.fromtimestamp(ts)
    h = d.hour % 12 or 12
    return "%s %d %s, %d:%02d %s" % (d.strftime("%a"), d.day, d.strftime("%b"), h, d.minute,
                                     "AM" if d.hour < 12 else "PM")


def plural(n, word):
    return "%d %s%s" % (n, word, "" if n == 1 else "s")


# ----------------------------------------------------------------------------
# Database
# ----------------------------------------------------------------------------
LOCK = threading.RLock()
CON = sqlite3.connect(DB_PATH, check_same_thread=False, timeout=15)
CON.row_factory = sqlite3.Row
with LOCK:
    CON.executescript("""
    CREATE TABLE IF NOT EXISTS items(
        id TEXT PRIMARY KEY, course TEXT, title TEXT, due INTEGER, url TEXT, descr TEXT,
        kind TEXT, points REAL, desc_hash TEXT, first_seen INTEGER, last_seen INTEGER,
        gone INTEGER DEFAULT 0, done INTEGER DEFAULT 0, prep_override INTEGER,
        prep_auto INTEGER, prep_why TEXT);
    CREATE TABLE IF NOT EXISTS changes(
        id INTEGER PRIMARY KEY AUTOINCREMENT, ts INTEGER, item_id TEXT, kind TEXT, text TEXT);
    CREATE TABLE IF NOT EXISTS notifications(
        id INTEGER PRIMARY KEY AUTOINCREMENT, ts INTEGER, kind TEXT, title TEXT, body TEXT,
        item_id TEXT, read INTEGER DEFAULT 0);
    CREATE TABLE IF NOT EXISTS reminders_sent(
        item_id TEXT, kind TEXT, due INTEGER, PRIMARY KEY(item_id, kind, due));
    CREATE TABLE IF NOT EXISTS help(item_id TEXT PRIMARY KEY, desc_hash TEXT, made INTEGER, payload TEXT);
    CREATE TABLE IF NOT EXISTS meta(k TEXT PRIMARY KEY, v TEXT);
    CREATE TABLE IF NOT EXISTS focus_log(
        id INTEGER PRIMARY KEY AUTOINCREMENT, item_id TEXT, ts INTEGER, seconds INTEGER);
    """)
    for stmt in ("ALTER TABLE items ADD COLUMN completed_ts INTEGER",
                 "ALTER TABLE items ADD COLUMN focus_seconds INTEGER DEFAULT 0"):
        try:
            CON.execute(stmt)
        except sqlite3.OperationalError:
            pass  # column already exists from an earlier version of Duey
    CON.commit()


def q(sql, args=()):
    with LOCK:
        return CON.execute(sql, args).fetchall()


def x(sql, args=()):
    with LOCK:
        cur = CON.execute(sql, args)
        CON.commit()
        return cur


def meta_get(k, default=None):
    r = q("SELECT v FROM meta WHERE k=?", (k,))
    return r[0]["v"] if r else default


def meta_set(k, v):
    x("INSERT INTO meta(k,v) VALUES(?,?) ON CONFLICT(k) DO UPDATE SET v=excluded.v", (k, str(v)))


# ----------------------------------------------------------------------------
# Calendar-link (iCal) reader - works for any school, even with single sign-on
# ----------------------------------------------------------------------------
def _ical_unescape(v):
    return re.sub(r"\\(.)", lambda m: "\n" if m.group(1) in "nN" else m.group(1), v)


def _ical_time(val, params):
    val = val.strip()
    if re.fullmatch(r"\d{8}", val):  # all-day event: treat as end of that day
        return int(datetime.strptime(val, "%Y%m%d").replace(hour=23, minute=59).timestamp())
    m = re.fullmatch(r"(\d{8}T\d{6})(Z?)", val)
    if not m:
        return None
    d = datetime.strptime(m.group(1), "%Y%m%dT%H%M%S")
    if m.group(2):
        return int(d.replace(tzinfo=timezone.utc).timestamp())
    for p in params:
        if p.upper().startswith("TZID="):
            try:
                from zoneinfo import ZoneInfo
                return int(d.replace(tzinfo=ZoneInfo(p[5:])).timestamp())
            except Exception:
                break
    return int(d.timestamp())


def parse_ical(text):
    """Returns a list of dicts: uid, summary, desc, url, category, due."""
    text = re.sub(r"\r?\n[ \t]", "", text)
    events, cur = [], None
    for line in text.splitlines():
        if line.strip() == "BEGIN:VEVENT":
            cur = {}
        elif line.strip() == "END:VEVENT":
            if cur is not None:
                events.append(cur)
            cur = None
        elif cur is not None and ":" in line:
            key, val = line.split(":", 1)
            name, *params = key.split(";")
            cur[name.upper()] = (val, params)
    out = []
    for e in events:
        def get(k):
            return _ical_unescape(e[k][0]) if k in e else ""
        start = e.get("DTSTART") or e.get("DTEND")
        due = _ical_time(*start) if start else None
        if not due:
            continue
        out.append({"uid": get("UID") or hashlib.md5(get("SUMMARY").encode()).hexdigest(),
                    "summary": get("SUMMARY"), "desc": get("DESCRIPTION"), "url": get("URL"),
                    "category": get("CATEGORIES"), "due": due})
    return out


def fetch_ical(url):
    url = url.strip()
    if url.lower().startswith("webcal://"):
        url = "https://" + url[9:]
    body, _ = http(url, timeout=60, retries=1)
    if "BEGIN:VCALENDAR" not in body:
        raise DueyError("That link didn't return a calendar. Make sure you copied the whole "
                        "calendar link (it usually ends in .ics or has 'export' in it).")
    return parse_ical(body)


def guess_kind(text):
    t = text.lower()
    for word, kind in (("quiz", "quiz"), ("exam", "exam"), ("test", "exam"),
                       ("discussion", "discussion"), ("forum", "discussion")):
        if word in t:
            return kind
    return "assignment"


# ----------------------------------------------------------------------------
# "How long will this take?"  A simple, friendly rule-of-thumb estimator
# ----------------------------------------------------------------------------
RULES = [
    (r"\b(final exam|midterm|exam|examination|finals)\b", 5, "an exam, so it's worth spreading revision out"),
    (r"\b(portfolio|capstone|thesis|dissertation|exhibition|studio project)\b", 6, "a big portfolio-style project"),
    (r"\b(project|prototype|build)\b", 5, "a project"),
    (r"\b(essay|paper|report|research|literature review|case study|proposal|article)\b", 4, "a written piece"),
    (r"\b(presentation|pitch|seminar|slides|critique|poster)\b", 3, "a presentation"),
    (r"\b(sketch|drawing|painting|illustration|design|composition|photo)\b", 3, "a hands-on creative task"),
    (r"\b(quiz|test)\b", 2, "a quiz"),
    (r"\b(lab|problem set|homework|worksheet|exercise|problems)\b", 2, "practice work"),
    (r"\b(reflection|journal|discussion|forum|response|reading|survey|attendance|check-in|quick)\b", 1, "a quick task"),
]


def estimate_days(title, desc, kind="", points=None):
    title_l = (title or "").lower()
    days, why = 2, "a standard task"
    hit = False
    for pat, d, w in RULES:
        if re.search(pat, title_l):
            days, why, hit = d, w, True
            break
    if not hit:
        if kind in ("quiz",):
            days, why, hit = 2, "a quiz", True
        elif kind in ("discussion", "forum"):
            days, why, hit = 1, "a quick task", True
    if not hit:
        head = (desc or "")[:300].lower()
        for pat, d, w in RULES:
            if re.search(pat, head):
                days, why = d, w
                break
    extras = []
    m = re.search(r"(\d[\d,]{2,5})\s*(?:-|to)?\s*(?:\d[\d,]*\s*)?words?", (desc or "").lower())
    if m:
        words = int(m.group(1).replace(",", ""))
        if 300 <= words <= 20000:
            need = min(14, round(words / 500) + 1)
            if need > days:
                days = need
            extras.append("about %d words" % words)
    if len(desc or "") > 1800:
        days += 1
        extras.append("a long brief")
    if re.search(r"\b(group|team|partner)\b", title_l + " " + (desc or "")[:500].lower()):
        days += 1
        extras.append("group work")
    if points and points >= 40:
        days += 1
        extras.append("lots of marks")
    days = max(1, min(21, int(days)))
    text = "Looks like %s" % why
    if extras:
        text += " (%s)" % ", ".join(extras)
    return days, text


# ----------------------------------------------------------------------------
# Platform connector (this is the only part that differs between Moodle and Canvas)
# ----------------------------------------------------------------------------
# ---- PORTAL CONNECTOR -------------------------------------------------------
# Duey works two ways, and never needs to be told which system your school
# runs underneath its own branding:
#
#   "ical": paste a calendar / iCal export link from your course portal.
#           This is completely universal - every major course portal produces
#           a standard calendar file, and the parsing below doesn't care which
#           one made it. This is the recommended option.
#   "api" : paste your portal's address and an access token. Duey quietly
#           tries each API shape it knows (there are two major ones in use
#           at most schools) and remembers which one worked. A handful of
#           schools don't expose a personal access token at all - for those,
#           the calendar link is the only option, which is fine since it
#           covers everything anyway.
#
# Nothing below ever needs to say which specific system or school is involved;
# it just tries things and reports back in plain language.

COURSE_SUFFIX_RE = re.compile(r"\[([^\]]+)\]\s*$")                         # "Essay 2 [ART 101]"
COURSE_DASH_RE = re.compile(r"[-\u2013]\s*([A-Z]{2,10}\s?\d[\dA-Z]{0,4})\s*$")  # "Essay 2 - ART 101" / "Lab 2 - CHEM 1A03"
VERB_SUFFIX_RE = re.compile(r"\s+(is due|closes|is open until|due)$", re.I)


def clean_ical_event(e):
    """Pulls a plausible course name and a clean title out of one calendar
    event, regardless of which portal produced it."""
    summary = e["summary"]
    course = e.get("category") or ""  # one well-known system fills this in directly
    title = summary
    if not course:
        m = COURSE_SUFFIX_RE.search(summary)
        if m:
            course, title = m.group(1), COURSE_SUFFIX_RE.sub("", summary)
        else:
            m = COURSE_DASH_RE.search(summary)
            if m:
                course, title = m.group(1), COURSE_DASH_RE.sub("", summary)
    title = VERB_SUFFIX_RE.sub("", title).strip().strip("-\u2013").strip()
    return (course or "General"), (title or summary or "Untitled")


def fetch_items_ical(cfg):
    now = int(time.time())
    out = []
    for e in fetch_ical(cfg["ical_url"]):
        if e["due"] < now - 3 * 86400 or "calendar-event" in e["uid"]:
            continue  # a plain personal calendar entry, not an assignment
        course, title = clean_ical_event(e)
        out.append({"id": "ical-" + e["uid"], "course": course, "title": title, "due": e["due"],
                    "url": e["url"], "desc": strip_html(e["desc"]), "kind": guess_kind(e["summary"]),
                    "points": None, "done": None})
    return out


# ---- one well-known API shape: a bearer token + REST JSON endpoints --------
def canvaslike_pages(cfg, path, params=None):
    url = "%s/api/v1%s?%s" % (cfg["base_url"], path, urllib.parse.urlencode(params or {}, doseq=True))
    for _ in range(30):
        try:
            body, headers = http(url, headers={"Authorization": "Bearer " + cfg["token"]})
        except DueyError as e:
            if e.code == 401:
                raise DueyError("That access token was rejected. Make a fresh one in your account "
                                "settings and paste it in.", 401)
            raise
        try:
            data = json.loads(body)
        except ValueError:
            raise DueyError("That didn't look like the response Duey expected from this system.", 0)
        if isinstance(data, dict):
            raise DueyError("Your school portal said: %s" % (data.get("errors") or data.get("message") or data), 0)
        for row in data:
            yield row
        nxt = re.search(r'<([^>]+)>;\s*rel="next"', headers.get("Link") or "")
        if not nxt:
            return
        url = nxt.group(1)


def canvaslike_iso(s):
    try:
        return int(datetime.fromisoformat(s.replace("Z", "+00:00")).timestamp())
    except (ValueError, AttributeError):
        return None


def detect_canvaslike(cfg):
    """A cheap, fast probe: does this address + token work against this API shape?"""
    body, _ = http("%s/api/v1/users/self" % cfg["base_url"],
                   headers={"Authorization": "Bearer " + cfg["token"]}, timeout=10)
    js = json.loads(body)
    if not isinstance(js, dict) or "id" not in js:
        raise DueyError("not this system", 0)


def fetch_items_canvaslike(cfg):
    now = int(time.time())
    out = []
    courses = list(canvaslike_pages(cfg, "/courses", {"enrollment_state": "active", "per_page": 100}))
    for c in courses:
        if not c.get("name"):
            continue  # a hidden or restricted course
        try:
            assignments = list(canvaslike_pages(cfg, "/courses/%s/assignments" % c["id"],
                                                {"include[]": "submission", "order_by": "due_at", "per_page": 100}))
        except DueyError:
            continue  # this particular course won't share its assignment list
        for a in assignments:
            due = canvaslike_iso(a.get("due_at"))
            if not due or due < now - 14 * 86400:
                continue
            sub = a.get("submission") or {}
            done = bool(sub.get("submitted_at")) or sub.get("workflow_state") in ("submitted", "graded", "pending_review") \
                or bool(sub.get("excused"))
            types = a.get("submission_types") or []
            kind = "quiz" if (a.get("is_quiz_assignment") or "online_quiz" in types) else \
                   "discussion" if "discussion_topic" in types else "assignment"
            out.append({"id": "a-%s" % a["id"], "course": c["name"], "title": a.get("name") or "Untitled",
                        "due": due, "url": a.get("html_url") or "", "desc": strip_html(a.get("description")),
                        "kind": kind, "points": a.get("points_possible"), "done": done})
    return out


# ---- the other well-known API shape: a token sent as a form field ----------
def moodlelike_ws(cfg, fn, **params):
    data = {"wstoken": cfg["token"], "wsfunction": fn, "moodlewsrestformat": "json"}
    data.update(params)
    body, _ = http(cfg["base_url"] + "/webservice/rest/server.php",
                   data=urllib.parse.urlencode(data).encode(), timeout=10)
    try:
        js = json.loads(body)
    except ValueError:
        raise DueyError("That didn't look like the response Duey expected from this system.", 0)
    if isinstance(js, dict) and (js.get("exception") or js.get("errorcode")):
        code = js.get("errorcode", "")
        if code in ("invalidtoken", "invalidlogin"):
            raise DueyError("That access token isn't valid (or it's expired). Make a fresh one and paste it in.", 401)
        if code in ("accessexception", "servicenotavailable", "webservicesnotenabled"):
            raise DueyError("Your school portal doesn't allow this kind of access. Use the calendar "
                            "link instead \u2014 it covers everything.", 0)
        raise DueyError("Your school portal said: %s" % (js.get("message") or code or "unknown problem"), 0)
    return js


def detect_moodlelike(cfg):
    js = moodlelike_ws(cfg, "core_webservice_get_site_info")
    if "sitename" not in js and "userid" not in js:
        raise DueyError("not this system", 0)


def moodlelike_token_from_login(base, user, pw):
    """Returns (token, None) on success, or (None, a plain-language reason) otherwise."""
    body, _ = http(base + "/login/token.php",
                   data=urllib.parse.urlencode({"username": user, "password": pw,
                                                "service": "moodle_mobile_app"}).encode())
    try:
        js = json.loads(body)
    except ValueError:
        return None, "not this system"  # handled by the caller; not shown to the person
    if js.get("token"):
        return js["token"], None
    msg = (js.get("error") or "").strip()
    code = (js.get("errorcode") or "").strip().lower()
    if code in ("cannotloginfromexternalapp",) or "sso" in msg.lower() or "oauth" in msg.lower():
        return None, "sso"
    if msg:
        return None, msg  # a real, specific reason from the system itself - worth showing as-is
    return None, None


def fetch_items_moodlelike(cfg):
    now = int(time.time())
    out = []
    after = 0
    for _ in range(8):  # page through, 50 at a time
        args = {"timesortfrom": now - 14 * 86400, "timesortto": now + 180 * 86400,
                "limitnum": 50, "limittononsuspendedevents": 1}
        if after:
            args["aftereventid"] = after
        js = moodlelike_ws(cfg, "core_calendar_get_action_events_by_timesort", **args)
        events = js.get("events", [])
        for ev in events:
            due = ev.get("timesort") or ev.get("timestart")
            if not due:
                continue
            action = ev.get("action") or {}
            title = VERB_SUFFIX_RE.sub("", ev.get("name", "")).strip()
            # this system marks an event as "actionable" while it still needs you to do
            # something; once you've submitted it, actionable flips to false
            done = (not action["actionable"]) if isinstance(action.get("actionable"), bool) else None
            out.append({"id": "a-%s" % ev["id"],
                        "course": (ev.get("course") or {}).get("fullname") or "General",
                        "title": title or "Untitled", "due": int(due),
                        "url": action.get("url") or ev.get("url") or "",
                        "desc": strip_html(ev.get("description")),
                        "kind": ev.get("modulename") or guess_kind(ev.get("name", "")),
                        "points": None, "done": done})
        if len(events) < 50:
            break
        after = js.get("lastid") or events[-1]["id"]
    return out


API_KINDS = {
    "canvas": (detect_canvaslike, fetch_items_canvaslike),
    "moodle": (detect_moodlelike, fetch_items_moodlelike),
}


def prepare_settings(cfg, incoming, changed_connection):
    """Runs when you press Save. If you typed a username and password instead of
    pasting a token, Duey quietly tries to exchange them for one (this only
    works on some systems; the password itself is never stored).

    Duey only forgets which system it previously detected when the address,
    mode, or token actually changed - saving an unrelated setting (email,
    sync interval, and so on) never forces a needless re-guess, which is
    what previously made the detected system seem to flip-flop."""
    user, pw = incoming.get("username", ""), incoming.get("password", "")
    if user and pw and cfg["mode"] == "api" and not str(incoming.get("token", "")).strip():
        if not cfg["base_url"]:
            return "Add your school portal's address first."
        token, reason = moodlelike_token_from_login(cfg["base_url"], user, pw)
        if token:
            cfg["token"] = token
            cfg["api_kind"] = "moodle"
        elif reason == "sso":
            return ("Your school uses single sign-on, which blocks signing in this way entirely. "
                    "Generate an access token from your account settings instead, or use the "
                    "calendar link above \u2014 it works everywhere, SSO included." + EXT_HINT)
        elif reason and reason != "not this system":
            return "Your school's site said: \u201c%s\u201d" % reason
        else:
            return ("That didn't work. Signing in this way only works on some school portals. "
                    "Generate an access token from your account settings instead, or use the "
                    "calendar link above \u2014 it works everywhere." + EXT_HINT)
    elif changed_connection:
        cfg["api_kind"] = ""  # the address, mode, or token actually changed; re-detect on next sync
    return None


def fetch_items(cfg):
    if cfg["mode"] == "ext":
        return load_ext_items()
    if cfg["mode"] == "ical":
        return fetch_items_ical(cfg)
    cached = cfg.get("api_kind") if cfg.get("api_kind") in API_KINDS else None
    order = ([cached] if cached else []) + [k for k in API_KINDS if k != cached]
    cached_err = None
    errs = {}
    for kind in order:
        detect, fetch = API_KINDS[kind]
        try:
            detect(cfg)
        except Exception as e:
            if isinstance(e, DueyError) and e.code == "blocked":
                raise e  # the address itself is blocked - trying another API shape won't help
            errs[kind] = e
            if kind == cached:
                cached_err = e
            continue
        if cfg.get("api_kind") != kind:
            cfg["api_kind"] = kind
            save_cfg(cfg)
        return fetch(cfg)
    if cfg.get("api_kind"):
        cfg["api_kind"] = ""
        save_cfg(cfg)
    for e in errs.values():
        if isinstance(e, DueyError) and e.code == 401:
            raise DueyError(str(e) + EXT_HINT, 401)  # the key was rejected - say so plainly
    me = errs.get("moodle")
    if isinstance(me, DueyError) and me.code == 0 and "didn't look like" not in str(me):
        raise DueyError(str(me) + EXT_HINT, 0)  # the portal itself said something specific
    raise DueyError("Duey couldn't connect using that address and token together. Double-check both "
                    "\u2014 the token is the most common culprit \u2014 or use the calendar link "
                    "instead, which works everywhere." + EXT_HINT)
# ---------------------------------------------------------------------------







# ----------------------------------------------------------------------------
# Notifications + email
# ----------------------------------------------------------------------------
def send_email(notifs, subject=None):
    """Returns None on success, or an error message."""
    cfg = load_cfg()
    if not (cfg["email_enabled"] and cfg["email_to"]):
        return "Type your email address in settings first."
    if cfg["smtp_host"] and cfg["smtp_user"] and cfg["smtp_pass"]:   # advanced: their own account
        host, port, user, pw = (cfg["smtp_host"], int(cfg["smtp_port"] or 587),
                                cfg["smtp_user"], cfg["smtp_pass"])
    else:                                                             # normal: Duey's built-in sender
        host, port = DUEY_SENDER["host"], int(DUEY_SENDER["port"] or 587)
        user, pw = DUEY_SENDER["user"], DUEY_SENDER["pass"]
    if not host:
        return ("Email alerts aren't set up on this copy of Duey yet. Whoever installed it needs to "
                "set the DUEY_SMTP_* sender details, or you can use \u201cAdvanced\u201d in settings.")
    try:
        msg = EmailMessage()
        msg["Subject"] = subject or ("[Duey] " + (notifs[0]["title"] if len(notifs) == 1
                                                  else "%d updates for you" % len(notifs)))
        msg["From"] = user or cfg["email_to"]
        msg["To"] = cfg["email_to"]
        lines = ["%s\n%s\n" % (n["title"], n["body"]) for n in notifs]
        msg.set_content("Hi!\n\n" + "\n".join(lines) + "\n- Duey")
        rows = "".join(
            '<div style="border:2px solid #24214A;border-radius:14px;padding:12px 14px;margin:0 0 10px;">'
            '<div style="font-weight:800;font-size:16px">%s</div>'
            '<div style="color:#6B6890;margin-top:4px">%s</div></div>'
            % (html.escape(n["title"]), html.escape(n["body"])) for n in notifs)
        msg.add_alternative(
            '<div style="font-family:Arial,sans-serif;color:#24214A;max-width:520px">'
            '<h2 style="margin:0 0 12px">Duey has news</h2>%s'
            '<div style="color:#6B6890;font-size:12px">Sent by your local Duey app.</div></div>' % rows,
            subtype="html")
        if port == 465:
            s = smtplib.SMTP_SSL(host, port, timeout=20)
        else:
            s = smtplib.SMTP(host, port, timeout=20)
            s.ehlo()
            if port != 25:
                s.starttls()
                s.ehlo()
        with s:
            if user:
                s.login(user, pw)
            s.send_message(msg)
        return None
    except smtplib.SMTPAuthenticationError:
        return ("The email server rejected the login. With Gmail you need an 'App password', "
                "not your normal password.")
    except Exception as e:
        return "Couldn't send the email: %s" % e


def _email_bg(notifs):
    err = send_email(notifs)
    meta_set("email_error", err or "")


def emit(notifs):
    if not notifs:
        return
    now = int(time.time())
    for n in notifs:
        x("INSERT INTO notifications(ts,kind,title,body,item_id) VALUES(?,?,?,?,?)",
          (now, n["kind"], n["title"], n["body"], n.get("item_id")))
    if load_cfg()["email_enabled"]:
        threading.Thread(target=_email_bg, args=(notifs,), daemon=True).start()


# ----------------------------------------------------------------------------
# Reminders: start nudging N days ahead, where N = the prep time
# ----------------------------------------------------------------------------
def prep_days_of(it):
    v = it["prep_override"] if it["prep_override"] is not None else it["prep_auto"]
    return int(v or 2)


def start_ts(due, days):
    d = datetime.fromtimestamp(due - days * 86400).replace(hour=9, minute=0, second=0, microsecond=0)
    return min(int(d.timestamp()), due - 3600)


def milestones(it):
    due, d = it["due"], prep_days_of(it)
    start = start_ts(due, d)
    ms = [("start", start)]
    if d >= 4:
        ms.append(("mid", start + (due - start) // 2))
    if d > 1:
        ms.append(("day", due - 86400))
    ms.append(("hours", due - 3 * 3600))
    return sorted(ms, key=lambda m: m[1])


def reminder_text(it, kind, now):
    d = prep_days_of(it)
    left = (it["due"] - now) / 86400
    left_txt = "less than a day" if left < 1 else plural(int(round(left)), "day")
    due = fmt_dt(it["due"])
    base = "%s - due %s." % (it["course"], due)
    if kind == "start":
        if left + 0.5 < d:
            body = ("%s You have %s left and it usually needs about %s of prep, so today is the day. "
                    "Start small, just open it and do the first bit." % (base, left_txt, plural(d, "day")))
        else:
            body = ("%s Duey thinks this needs about %s of prep, so this is the perfect moment to begin."
                    % (base, plural(d, "day")))
        return {"kind": "remind", "title": "Time to start: " + it["title"], "body": body}
    if kind == "mid":
        return {"kind": "remind", "title": "Halfway point: " + it["title"],
                "body": "%s About %s left. A quick progress check now saves stress later." % (base, left_txt)}
    if kind == "day":
        return {"kind": "remind", "title": "Due tomorrow: " + it["title"],
                "body": "%s Time to polish it and get it submitted." % base}
    if kind == "hours":
        return {"kind": "remind", "title": "Due in about 3 hours: " + it["title"],
                "body": "%s Final stretch. Submit it before the deadline!" % base}
    # kind is "late-N": still incomplete after the deadline, nagged with escalating urgency
    n = kind.split("-", 1)[1]
    if n == "0":
        return {"kind": "remind", "title": "Still open: " + it["title"],
                "body": "%s This passed its deadline earlier. If it's in, mark it done here so Duey stops "
                        "pestering you; if not, get it submitted or message your professor." % base}
    days_late = int(n)
    return {"kind": "remind", "title": plural(days_late, "day").capitalize() + " overdue: " + it["title"],
            "body": "%s Still showing as incomplete, now %s overdue. Submit it, mark it done if it's already "
                    "in, or check with your professor about next steps." % (base, plural(days_late, "day"))}


def overdue_kind(now, due):
    hours_late = (now - due) / 3600
    if hours_late < 24:
        return "late-0"
    return "late-%d" % min(int(hours_late // 24), 30)


def check_reminders():
    now = int(time.time())
    out = []
    for it in q("SELECT * FROM items WHERE gone=0 AND done=0 AND due>?", (now - 30 * 86400,)):
        if it["due"] > now:
            passed = [m for m in milestones(it) if m[1] <= now]
        else:
            passed = [(overdue_kind(now, it["due"]), now)]
        if not passed:
            continue
        sent = {r["kind"] for r in q("SELECT kind FROM reminders_sent WHERE item_id=? AND due=?",
                                     (it["id"], it["due"]))}
        fresh = [m for m in passed if m[0] not in sent]
        if not fresh:
            continue
        for kind, _ in fresh:
            x("INSERT OR IGNORE INTO reminders_sent VALUES(?,?,?)", (it["id"], kind, it["due"]))
        n = reminder_text(it, fresh[-1][0], now)  # only the most recent one, never a pile-up
        n["item_id"] = it["id"]
        out.append(n)
    emit(out)


# ----------------------------------------------------------------------------
# Syncing + change detection
# ----------------------------------------------------------------------------
SYNC_LOCK = threading.Lock()


def log_change(item_id, kind, text):
    x("INSERT INTO changes(ts,item_id,kind,text) VALUES(?,?,?,?)", (int(time.time()), item_id, kind, text))


def sync():
    if not SYNC_LOCK.acquire(blocking=False):
        return {"ok": False, "error": "Already checking, hang on a sec."}
    try:
        cfg = load_cfg()
        if not configured(cfg):
            return {"ok": False, "error": "Add your school portal details in settings first."}
        meta_set("last_attempt", int(time.time()))
        try:
            fetched = fetch_items(cfg)
        except DueyError as e:
            meta_set("last_error", str(e))
            return {"ok": False, "error": str(e)}
        except Exception as e:
            msg = "Something unexpected happened while reading your school portal: %s" % e
            meta_set("last_error", msg)
            return {"ok": False, "error": msg}

        fetched = list({it["id"]: it for it in fetched}.values())  # guard against duplicates
        now = int(time.time())
        first = meta_get("last_sync") is None
        existing = {r["id"]: r for r in q("SELECT * FROM items")}
        notifs, seen = [], set()

        for it in fetched:
            seen.add(it["id"])
            desc = it["desc"] or ""
            h = hashlib.md5(desc.encode("utf-8")).hexdigest()
            old = existing.get(it["id"])
            days, why = estimate_days(it["title"], desc, it.get("kind", ""), it.get("points"))
            if old is None:
                x("""INSERT INTO items(id,course,title,due,url,descr,kind,points,desc_hash,first_seen,
                     last_seen,done,prep_auto,prep_why,completed_ts) VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)""",
                  (it["id"], it["course"], it["title"], it["due"], it["url"], desc, it.get("kind", ""),
                   it.get("points"), h, now, now, 1 if it.get("done") else 0, days, why,
                   now if it.get("done") else None))
                if not first and not it.get("done"):
                    notifs.append({"kind": "new", "item_id": it["id"],
                                   "title": "New deadline: " + it["title"],
                                   "body": "%s - due %s. Duey guesses about %s of prep."
                                           % (it["course"], fmt_dt(it["due"]), plural(days, "day"))})
                continue
            if old["due"] != it["due"] and not old["done"]:
                txt = "Moved from %s to %s" % (fmt_dt(old["due"]), fmt_dt(it["due"]))
                log_change(it["id"], "due", txt)
                notifs.append({"kind": "change", "item_id": it["id"],
                               "title": "Date changed: " + it["title"],
                               "body": "%s - was %s, now %s." % (it["course"], fmt_dt(old["due"]),
                                                                 fmt_dt(it["due"]))})
            if old["title"] != it["title"]:
                log_change(it["id"], "title", "Renamed from '%s' to '%s'" % (old["title"], it["title"]))
                notifs.append({"kind": "change", "item_id": it["id"], "title": "Renamed: " + it["title"],
                               "body": "It used to be called '%s'." % old["title"]})
            if old["desc_hash"] != h and not old["done"]:
                log_change(it["id"], "desc", "Instructions were edited")
                notifs.append({"kind": "change", "item_id": it["id"],
                               "title": "Instructions edited: " + it["title"],
                               "body": "%s - the assignment description changed. Worth a re-read." % it["course"]})
            if old["gone"] and not old["done"]:
                log_change(it["id"], "back", "Back on your list")
            done = 1 if (old["done"] or it.get("done")) else 0
            completed_ts = old["completed_ts"]
            if done and not old["done"]:
                completed_ts = now  # the platform (or a prior click) just marked this complete
            x("""UPDATE items SET course=?,title=?,due=?,url=?,descr=?,kind=?,points=?,desc_hash=?,
                 last_seen=?,gone=0,done=?,prep_auto=?,prep_why=?,completed_ts=? WHERE id=?""",
              (it["course"], it["title"], it["due"], it["url"], desc, it.get("kind", ""), it.get("points"),
               h, now, done, days, why, completed_ts, it["id"]))

        for iid, old in existing.items():
            if iid in seen or old["gone"]:
                continue
            x("UPDATE items SET gone=1 WHERE id=?", (iid,))
            if old["due"] > now and not old["done"] and not first:
                log_change(iid, "gone", "No longer on your list (submitted, or removed by your prof)")
                notifs.append({"kind": "change", "item_id": iid, "title": "Gone from your list: " + old["title"],
                               "body": "%s - probably submitted, but if you didn't do it, ask your prof." % old["course"]})

        if first:
            notifs.append({"kind": "system", "title": "Connected!",
                           "body": "Found %s. Duey will keep checking for changes." % plural(len(fetched), "deadline")})
            meta_set("first_sync", now)
        meta_set("last_sync", now)
        meta_set("last_error", "")
        emit(notifs)
        check_reminders()
        return {"ok": True, "count": len(fetched)}
    finally:
        SYNC_LOCK.release()


# ----------------------------------------------------------------------------
# Browser extension intake: the extension reads the portal while you're logged in
# and hands the list to Duey here, on this computer only.
# ----------------------------------------------------------------------------
def ensure_ext_code():
    cfg = load_cfg()
    if not cfg.get("ext_code"):
        raw = "".join(secrets.choice("ABCDEFGHJKMNPQRSTUVWXYZ23456789") for _ in range(8))
        cfg["ext_code"] = raw[:4] + "-" + raw[4:]
        save_cfg(cfg)
    return cfg["ext_code"]


def load_ext_items():
    raw = meta_get("ext_items")
    if raw is None:
        raise DueyError("Waiting for the first update from the browser extension.")
    return json.loads(raw)


def ingest(body):
    cfg = load_cfg()
    code = str(body.get("code") or "").strip().upper()
    real = str(cfg.get("ext_code") or "")
    if not real or not hmac.compare_digest(code.encode(), real.encode()):
        return {"ok": False, "error": "That pairing code doesn't match. Copy it from Duey's settings (Browser extension)."}
    if body.get("check"):
        return {"ok": True}
    if cfg["mode"] != "ext":
        cfg["mode"] = "ext"
        cfg["api_kind"] = ""
        save_cfg(cfg)
    meta_set("ext_paired", "1")
    if body.get("error"):
        meta_set("last_error", str(body["error"])[:300])
        return {"ok": True}
    clean = []
    rows = body.get("items")
    for r in (rows if isinstance(rows, list) else [])[:500]:
        try:
            url = str(r.get("url") or "")
            clean.append({"id": str(r["id"])[:80], "course": str(r.get("course") or "General")[:120],
                          "title": str(r.get("title") or "Untitled")[:300], "due": int(r["due"]),
                          "url": url if re.match(r"https?://", url) else "",
                          "desc": strip_html(str(r.get("desc") or "")),
                          "kind": str(r.get("kind") or "assignment")[:20], "points": None,
                          "done": True if r.get("done") is True else None})
        except (KeyError, TypeError, ValueError, AttributeError):
            continue
    meta_set("ext_items", json.dumps(clean))
    return sync()


def privacy_html():
    try:
        with open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "PRIVACY.md"), encoding="utf-8") as f:
            lines = f.read().splitlines()
    except OSError:
        lines = ["# Privacy", "PRIVACY.md wasn't found next to duey.py."]
    out, in_list = [], False
    for ln in lines:
        item = ln.startswith("- ")
        if in_list and not item:
            out.append("</ul>")
            in_list = False
        if item:
            if not in_list:
                out.append("<ul>")
                in_list = True
            out.append("<li>%s</li>" % html.escape(ln[2:]))
        elif ln.startswith("## "):
            out.append("<h2>%s</h2>" % html.escape(ln[3:]))
        elif ln.startswith("# "):
            out.append("<h1>%s</h1>" % html.escape(ln[2:]))
        elif ln.strip():
            out.append("<p>%s</p>" % html.escape(ln))
    if in_list:
        out.append("</ul>")
    return ("<!doctype html><meta charset=utf-8><meta name=viewport content='width=device-width,initial-scale=1'>"
            "<title>Duey privacy</title><style>body{font:16px/1.55 system-ui,'Segoe UI',sans-serif;max-width:46em;"
            "margin:32px auto;padding:0 20px;color:#12172E}h1{font-size:30px}h2{font-size:20px;margin-top:28px}"
            "li{margin:6px 0}</style>" + "".join(out))


def worker():
    while True:
        try:
            cfg = load_cfg()
            if cfg.get("mode") == "ext":
                check_reminders()
            elif configured(cfg):
                last = int(meta_get("last_attempt", 0) or 0)
                wait = 120 if meta_get("last_error") else max(1, int(cfg["sync_minutes"])) * 60
                if time.time() - last >= wait:
                    sync()
                else:
                    check_reminders()
        except Exception as e:
            print("worker hiccup:", e)
        time.sleep(30)


# ----------------------------------------------------------------------------
# Study helper: read the brief, find topics, suggest videos
# ----------------------------------------------------------------------------
STOP = set("""a about above after again all also am an and any are as at be because been before being below
between both but by can could did do does doing down during each few for from further had has have having he
her here hers him his how i if in into is it its just me more most my no nor not now of off on once only or
other our out over own same she should so some such than that the their them then there these they this those
through to too under until up us very was we were what when where which while who whom why will with would you
your yours must may might""".split())
BORING = set("""assignment assignments submit submission submitted due deadline students student please marks mark
points point upload file files page pages word words format document attached following include including using
use need needs required requirement requirements moodle canvas course class lecture lectures week weeks task
tasks work answer answers question questions complete completed write written part parts example examples
ensure make provide via per etc read minimum maximum around least reference references grade grading late
penalty instructions instruction total online link links click available bring check-in sure cite cited citing matter matters explain discuss compare analyse analyze describe demonstrate show shows choose select sources source essay paper report project presentation quiz exam test homework worksheet one two three four five six seven eight nine ten first second third new best good well many much every something anything thing things around based given later within without between however overall then thus""".split())
ASK_WORDS = re.compile(r"\b(must|should|need to|required|include|submit|upload|write|create|use|minimum|"
                       r"maximum|at least|no more than|words|pages|cite|present|explain|discuss|compare|"
                       r"analy[sz]e|design|choose|select|describe|research)\b", re.I)


def topics_from(title, desc, n=4):
    uni, bi = Counter(), Counter()
    sources = [(3, title or "")]
    if len((desc or "").split()) >= 25:  # a thin brief only adds noise
        sources.append((1, (desc or "")[:6000]))
    for weight, text in sources:
        prev = None
        for w in re.findall(r"[A-Za-zÀ-ÿ][A-Za-zÀ-ÿ'-]{2,}", text):
            w = w.lower().strip("'-")
            if w in STOP or w in BORING or len(w) < 3:
                prev = None
                continue
            uni[w] += weight
            if prev:
                bi[prev + " " + w] += weight
            prev = w
    cands = [(s * 2, t) for t, s in bi.items() if s >= 2] + [(s, t) for t, s in uni.items()]
    cands.sort(key=lambda c: (-c[0], c[1]))
    picked = []
    for _, t in cands:
        if any(t == p or t in p.split() or p in t.split() for p in picked):
            continue
        picked.append(t)
        if len(picked) >= n:
            break
    return picked


def clean_title(title):
    return re.sub(r"\s+", " ", re.sub(r"[\[\(].*?[\]\)]|\b(assignment|homework|hw|task)\b|\d+", " ",
                                      title or "", flags=re.I)).strip()


def youtube_search(key, query, n=2):
    url = "https://www.googleapis.com/youtube/v3/search?" + urllib.parse.urlencode({
        "part": "snippet", "type": "video", "maxResults": n, "q": query, "safeSearch": "strict",
        "videoEmbeddable": "true", "key": key})
    js = json.loads(http(url)[0])
    out = []
    for i in js.get("items", []):
        sn = i.get("snippet", {})
        out.append({"id": i["id"]["videoId"], "title": html.unescape(sn.get("title", "")),
                    "channel": sn.get("channelTitle", ""),
                    "thumb": ((sn.get("thumbnails") or {}).get("medium") or {}).get("url", ""),
                    "query": query})
    return out


CLAUDE_SYSTEM = (
    "You help a student get started on an assignment. Reply with ONLY compact JSON, no markdown: "
    '{"summary": "2 short plain-English sentences", "steps": ["3 to 6 concrete steps"], '
    '"topics": ["2 to 4 concepts worth studying"], '
    '"video_queries": ["3 YouTube search queries a beginner would use"], '
    '"prep_days": <integer, realistic days of prep for a typical student>}')


def ask_claude(key, it):
    prompt = "Course: %s\nTitle: %s\nDue: %s\n\nAssignment brief:\n%s" % (
        it["course"], it["title"], fmt_dt(it["due"]), (it["descr"] or "(no written brief)")[:5000])
    body = {"model": CLAUDE_MODEL, "max_tokens": 900, "system": CLAUDE_SYSTEM,
            "messages": [{"role": "user", "content": prompt}]}
    txt, _ = http("https://api.anthropic.com/v1/messages", data=json.dumps(body).encode(),
                  headers={"x-api-key": key, "anthropic-version": "2023-06-01",
                           "content-type": "application/json"}, timeout=60)
    out = json.loads(txt)["content"][0]["text"]
    return json.loads(re.search(r"\{.*\}", out, re.S).group(0))


def build_help(it, cfg):
    desc = it["descr"] or ""
    sentences = [s.strip() for s in re.split(r"(?<=[.!?])\s+|\n", desc) if s.strip()]
    asks = [s for s in sentences if 15 <= len(s) <= 240 and ASK_WORDS.search(s)][:6]
    summary = " ".join(sentences[:2])[:320]
    topics = topics_from(it["title"], desc)
    if not topics and clean_title(it["title"]):
        topics = [clean_title(it["title"])]
    queries = []
    if topics:
        queries.append(topics[0] + " explained simply")
    if len(topics) > 1:
        queries.append(topics[1] + " tutorial for beginners")
    if topics and it["course"] and it["course"] != "General":
        queries.append("%s %s" % (it["course"], topics[0]))
    if not queries:
        queries.append("how to " + it["title"])
    result = {"summary": summary, "asks": asks, "topics": topics, "steps": [], "ai": False,
              "ai_days": None, "words": len(desc.split()), "videos": [], "notes": []}
    if cfg.get("anthropic_key"):
        try:
            ai = ask_claude(cfg["anthropic_key"], it)
            result.update(ai=True, summary=ai.get("summary") or summary,
                          steps=[str(s) for s in (ai.get("steps") or [])][:6],
                          topics=[str(s) for s in (ai.get("topics") or topics)][:4])
            queries = [str(s) for s in (ai.get("video_queries") or queries)][:3]
            if isinstance(ai.get("prep_days"), (int, float)):
                result["ai_days"] = max(1, min(21, int(ai["prep_days"])))
        except Exception as e:
            result["notes"].append("Claude couldn't help this time (%s). Showing Duey's own reading instead." % e)
    result["queries"] = queries
    if cfg.get("youtube_key"):
        seen = set()
        for query in queries:
            try:
                for v in youtube_search(cfg["youtube_key"], query):
                    if v["id"] not in seen:
                        seen.add(v["id"])
                        result["videos"].append(v)
            except Exception as e:
                result["notes"].append("YouTube search failed (%s)." % e)
                break
    return result


def help_for(item_id, refresh=False):
    rows = q("SELECT * FROM items WHERE id=?", (item_id,))
    if not rows:
        return {"ok": False, "error": "Couldn't find that item."}
    it = rows[0]
    cfg = load_cfg()
    stamp = hashlib.md5(("%s|%s|%s" % (it["desc_hash"], bool(cfg["youtube_key"]),
                                       bool(cfg["anthropic_key"]))).encode()).hexdigest()
    cached = q("SELECT * FROM help WHERE item_id=?", (item_id,))
    if cached and cached[0]["desc_hash"] == stamp and not refresh:
        return {"ok": True, "help": json.loads(cached[0]["payload"])}
    result = build_help(it, cfg)
    x("INSERT INTO help(item_id,desc_hash,made,payload) VALUES(?,?,?,?) ON CONFLICT(item_id) DO UPDATE "
      "SET desc_hash=excluded.desc_hash, made=excluded.made, payload=excluded.payload",
      (item_id, stamp, int(time.time()), json.dumps(result)))
    return {"ok": True, "help": result}


# ----------------------------------------------------------------------------
# The web app
# ----------------------------------------------------------------------------
def public_settings(cfg):
    s = {k: v for k, v in cfg.items() if k not in SECRET_KEYS}
    for k in SECRET_KEYS:
        s["has_" + k] = bool(cfg.get(k))
    s["ext_path"] = EXT_DIR if os.path.isdir(EXT_DIR) else ""
    return s


def compute_streak():
    """Consecutive days (ending today or yesterday) on which something was marked done."""
    days = set()
    for r in q("SELECT DISTINCT completed_ts FROM items WHERE completed_ts IS NOT NULL"):
        days.add(datetime.fromtimestamp(r["completed_ts"]).date())
    if not days:
        return 0
    cur = datetime.now().date()
    if cur not in days:
        cur -= timedelta(days=1)
        if cur not in days:
            return 0
    streak = 0
    while cur in days:
        streak += 1
        cur -= timedelta(days=1)
    return streak


def build_state():
    now = int(time.time())
    cfg = load_cfg()
    first_sync = int(meta_get("first_sync", 0) or 0)
    changed = {r["item_id"] for r in q("SELECT DISTINCT item_id FROM changes WHERE ts>?", (now - 172800,))}
    items = []
    for it in q("SELECT * FROM items WHERE due>? ORDER BY due", (now - 30 * 86400,)):
        d = prep_days_of(it)
        items.append({
            "id": it["id"], "course": it["course"], "title": it["title"], "due": it["due"],
            "url": it["url"], "kind": it["kind"], "done": bool(it["done"]), "gone": bool(it["gone"]),
            "prep": d, "prep_manual": it["prep_override"] is not None, "why": it["prep_why"],
            "start": start_ts(it["due"], d), "has_brief": bool((it["descr"] or "").strip()),
            "fresh": bool(first_sync and it["first_seen"] > first_sync + 60 and it["first_seen"] > now - 86400),
            "changed": it["id"] in changed, "focus_min": round((it["focus_seconds"] or 0) / 60)})
    titles = {r["id"]: r["title"] for r in q("SELECT id,title FROM items")}
    changes = [{"ts": r["ts"], "kind": r["kind"], "text": r["text"], "title": titles.get(r["item_id"], "")}
               for r in q("SELECT * FROM changes ORDER BY id DESC LIMIT 40")]
    notes = [dict(r) for r in q("SELECT * FROM notifications ORDER BY id DESC LIMIT 40")]
    done_total = q("SELECT COUNT(*) c FROM items WHERE done=1")[0]["c"]
    stats = {"streak": compute_streak(), "done_total": done_total,
             "focus_min_total": round(sum((it["focus_seconds"] or 0) for it in q("SELECT focus_seconds FROM items")) / 60)}
    return {"configured": configured(cfg), "now": now, "items": items,
            "changes": changes, "notifications": notes,
            "unread": q("SELECT COUNT(*) c FROM notifications WHERE read=0")[0]["c"],
            "last_sync": int(meta_get("last_sync", 0) or 0), "last_error": meta_get("last_error", ""),
            "email_error": meta_get("email_error", ""), "syncing": SYNC_LOCK.locked(),
            "settings": public_settings(cfg), "stats": stats}


ALLOWED = set(DEFAULTS) | {"username", "password"}


def apply_settings(incoming):
    cfg = load_cfg()
    old_base, old_token, old_mode = cfg["base_url"], cfg["token"], cfg["mode"]
    incoming = {k: v for k, v in (incoming or {}).items() if k in ALLOWED}
    for k, v in incoming.items():
        if k in ("username", "password"):
            continue
        if k in SECRET_KEYS and (v is None or str(v).strip() == ""):
            continue  # blank secret box = keep what's saved
        if k in ("email_enabled",):
            v = bool(v)
        elif k in ("smtp_port", "sync_minutes"):
            try:
                v = int(v)
            except (TypeError, ValueError):
                v = DEFAULTS[k]
        elif isinstance(v, str):
            v = v.strip()
        cfg[k] = v
    if cfg["base_url"] and not re.match(r"https?://", cfg["base_url"], re.I):
        cfg["base_url"] = "https://" + cfg["base_url"]
    cfg["base_url"] = cfg["base_url"].rstrip("/")
    if cfg["base_url"]:
        u = urllib.parse.urlparse(cfg["base_url"])
        path = re.split(r"/(?:login|my|course|mod|user|calendar|index\.php|webservice)(?:/|$)", u.path, 1)[0]
        cfg["base_url"] = (u.scheme + "://" + u.netloc + path).rstrip("/")
    # Only treat this as a *new connection* if the address, mode, or an actually-typed
    # token changed - not just because the person flipped the email toggle or changed
    # the sync interval. This is what keeps a once-detected system from being
    # needlessly re-guessed (and potentially flip-flopping) on every unrelated save.
    changed_connection = (cfg["base_url"] != old_base or cfg["mode"] != old_mode
                          or (incoming.get("token") and cfg["token"] != old_token))
    err = prepare_settings(cfg, incoming, changed_connection)  # connector hook
    if err:
        return err
    save_cfg(cfg)
    return None


PAGE = r"""<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>Duey</title>
<link rel="preconnect" href="https://fonts.googleapis.com">
<link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
<link href="https://fonts.googleapis.com/css2?family=Figtree:wght@400;500;600;700&family=Gabarito:wght@500;700;900&display=swap" rel="stylesheet">
<style>
:root{
  --paper:#FFFFFF; --ink:#12172E; --ink2:#5B5F79; --line:#E1E3EE; --line2:#EDEEF5;
  --navy:#12172E; --navy-soft:#1E2749;
  --a1:#1E2749; --a1-t:#E8EAF2;   /* deep navy   */
  --a2:#0F6F63; --a2-t:#DFF1EE;   /* teal        */
  --a3:#9A5B12; --a3-t:#F5E8D6;   /* ochre       */
  --a4:#5B4B8A; --a4-t:#EBE6F5;   /* plum        */
  --a5:#2B5F7E; --a5-t:#E1EEF4;   /* steel blue  */
  --a6:#7A3B46; --a6-t:#F2E3E6;   /* wine        */
  --u-late:#9A2B3B; --u-late-t:#F7E6E9;
  --u-go:#9A5B12; --u-go-t:#F5E8D6;
  --u-soon:#8A7419; --u-soon-t:#F6F1DA;
  --u-calm:#0F6F63; --u-calm-t:#DFF1EE;
  --u-done:#8A8FA3; --u-done-t:#EEEFF4;
  --display:'Gabarito','Segoe UI',system-ui,sans-serif;
  --body:'Figtree','Segoe UI','Helvetica Neue',system-ui,sans-serif;
  --shadow:0 1px 2px rgba(18,23,46,.06), 0 8px 24px -12px rgba(18,23,46,.18);
  --shadow-lg:0 24px 60px -20px rgba(18,23,46,.35);
}
*{box-sizing:border-box}
html{-webkit-text-size-adjust:100%}
body{
  margin:0;font:500 16px/1.5 var(--body);color:var(--ink);background:var(--paper);
  background-image:
    repeating-linear-gradient(120deg, rgba(18,23,46,.05) 0 1px, transparent 1px 84px),
    repeating-linear-gradient(60deg, rgba(18,23,46,.05) 0 1px, transparent 1px 84px),
    repeating-linear-gradient(0deg, rgba(18,23,46,.028) 0 1px, transparent 1px 168px);
  background-attachment:fixed;
}
h1,h2,h3,h4{font-family:var(--display);margin:0;line-height:1.15;letter-spacing:-.01em;font-weight:700}
p{margin:0}
button,input,select{font:inherit;color:inherit}
a{color:var(--a5)}
:focus-visible{outline:2.5px solid var(--navy);outline-offset:2px;border-radius:6px}
[hidden]{display:none!important}

/* header */
.bar{max-width:1080px;margin:0 auto;padding:20px 22px 0;display:flex;align-items:center;gap:12px}
.brand{display:flex;align-items:center;gap:12px;margin-right:auto}
.brand svg{flex:none}
.brand b{font:700 24px/1 var(--display);letter-spacing:-.01em}
.brand small{display:block;font-size:12.5px;color:var(--ink2);font-weight:600;margin-top:3px;letter-spacing:.01em}
.btn{display:inline-flex;align-items:center;gap:8px;padding:9px 15px;border:1.5px solid var(--line);border-radius:10px;
  background:#fff;font-weight:600;cursor:pointer;text-decoration:none;color:var(--ink);box-shadow:var(--shadow);
  transition:border-color .12s,background .12s,transform .06s}
.btn:hover{border-color:var(--navy);background:var(--line2)}
.btn:active{transform:translateY(1px)}
.btn.primary{background:var(--navy);color:#fff;border-color:var(--navy)}
.btn.primary:hover{background:var(--navy-soft)}
.btn.small{padding:6px 12px;font-size:13.5px;border-radius:8px}
.btn.ghost{border-color:transparent;box-shadow:none;background:transparent}
.btn.ghost:hover{background:var(--line2);border-color:var(--line)}
.btn[disabled]{opacity:.55;cursor:progress}
.icon{width:19px;height:19px;fill:none;stroke:currentColor;stroke-width:2;stroke-linecap:round;stroke-linejoin:round;flex:none}
.iconbtn{padding:9px 10px;position:relative}
.badge{position:absolute;top:-7px;right:-7px;min-width:19px;height:19px;padding:0 5px;border-radius:99px;background:var(--u-late);
  color:#fff;border:2px solid #fff;font:700 11px/15px var(--body);text-align:center;box-shadow:0 0 0 1px var(--u-late)}
.spin .icon{animation:spin 1s linear infinite}
@keyframes spin{to{transform:rotate(360deg)}}

main{max-width:1080px;margin:0 auto;padding:26px 22px 90px}

/* hero */
.hero h1{font-size:clamp(28px,4.6vw,42px);font-weight:700;max-width:18em}
.hero .sub{color:var(--ink2);margin-top:9px;font-weight:500;max-width:52em}

/* stat strip */
.stats{display:grid;grid-template-columns:repeat(auto-fit,minmax(130px,1fr));gap:10px;margin:20px 0 24px}
.stat{border:1.5px solid var(--line);border-radius:12px;padding:13px 15px;background:#fff;box-shadow:var(--shadow)}
.stat b{display:block;font:700 26px/1 var(--display);letter-spacing:-.01em}
.stat span{display:block;color:var(--ink2);font-size:12.5px;font-weight:600;margin-top:4px;text-transform:uppercase;letter-spacing:.03em}
.stat.warn b{color:var(--u-late)}
.stat.go b{color:var(--u-go)}
.stat.calm b{color:var(--u-calm)}

.week{display:grid;grid-template-columns:repeat(7,minmax(0,1fr));gap:8px;margin:0 0 26px}
.day{border:1.5px solid var(--line);border-radius:12px;padding:9px 6px 10px;text-align:center;background:#fff;min-height:80px}
.day .dn{font-size:12px;color:var(--ink2);font-weight:600;text-transform:uppercase;letter-spacing:.02em}
.day .dd{font:700 21px/1.1 var(--display);margin:3px 0 7px}
.day.today{border-color:var(--navy);box-shadow:inset 0 0 0 1px var(--navy)}
.day.has{background:var(--a5-t)}
.dots{display:flex;flex-wrap:wrap;gap:4px;justify-content:center;min-height:8px}
.dots i{width:7px;height:7px;border-radius:2px}

/* banners */
.banner{border:1.5px solid var(--u-late);border-radius:12px;padding:12px 14px;margin:0 0 16px;display:flex;gap:10px;align-items:flex-start;background:var(--u-late-t)}
.banner.info{border-color:var(--a5);background:var(--a5-t)}
.banner strong{font-family:var(--display)}

/* tabs */
.tabs{display:flex;gap:6px;flex-wrap:wrap;margin:4px 0 22px;border-bottom:1.5px solid var(--line);padding-bottom:0}
.tab{padding:9px 14px;border-radius:8px 8px 0 0;border:0;background:transparent;font-weight:600;cursor:pointer;color:var(--ink2);
  border-bottom:2.5px solid transparent;margin-bottom:-1.5px}
.tab[aria-selected=true]{color:var(--navy);border-bottom-color:var(--navy)}
.tab .ct{margin-left:6px;opacity:.7;font-weight:600;font-size:13px}

/* groups + cards */
.group{margin:0 0 30px}
.group>h2{font-size:21px}
.group>p{color:var(--ink2);margin:4px 0 14px;font-weight:500}
.cards{display:grid;gap:14px;grid-template-columns:repeat(auto-fill,minmax(min(100%,420px),1fr))}
.card{--shade:var(--u-calm);--shade-t:var(--u-calm-t);background:#fff;border:1.5px solid var(--line);border-left:4px solid var(--shade);
  border-radius:12px;padding:16px 18px;box-shadow:var(--shadow);display:flex;flex-direction:column;gap:7px;min-width:0}
.u-late{--shade:var(--u-late);--shade-t:var(--u-late-t)}
.u-go{--shade:var(--u-go);--shade-t:var(--u-go-t)}
.u-soon{--shade:var(--u-soon);--shade-t:var(--u-soon-t)}
.u-calm{--shade:var(--u-calm);--shade-t:var(--u-calm-t)}
.u-done{--shade:var(--u-done);--shade-t:var(--u-done-t)}
.card .top{display:flex;flex-wrap:wrap;gap:8px;align-items:center}
.chip{display:inline-flex;align-items:center;gap:6px;padding:3px 10px;border-radius:7px;font-weight:600;font-size:12.5px;max-width:100%}
.chip i{width:7px;height:7px;border-radius:2px;flex:none}
.chip span{overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.kind{font-size:12.5px;color:var(--ink2);font-weight:600;text-transform:uppercase;letter-spacing:.02em}
.pill{margin-left:auto;padding:3px 10px;border-radius:7px;font-weight:700;font-size:12.5px;background:var(--shade-t);color:var(--shade)}
.sticker{padding:2px 8px;border-radius:6px;font-size:10.5px;font-weight:700;background:var(--a4-t);color:var(--a4);text-transform:uppercase;letter-spacing:.04em}
.sticker.upd{background:var(--a3-t);color:var(--a3)}
.card h3{font-size:19px;font-weight:700;margin-top:2px;overflow-wrap:anywhere;font-family:var(--display)}
.when{color:var(--ink2);font-weight:500;font-size:14.5px}

/* the runway */
.runway{margin:14px 2px 2px}
.track{position:relative;height:8px;border-radius:99px;background:var(--line)}
.fill{position:absolute;left:0;top:0;bottom:0;border-radius:99px;background:var(--shade);opacity:.85}
.you{position:absolute;top:50%;width:15px;height:15px;margin:-7.5px 0 0 -7.5px;border-radius:3px;background:var(--shade);
  border:2px solid #fff;box-shadow:0 0 0 1.5px var(--shade);transform:rotate(45deg)}
.ends{display:flex;justify-content:space-between;gap:10px;font-size:12.5px;color:var(--ink2);margin-top:8px;font-weight:500}
.note{font-size:13.5px;margin-top:1px;font-weight:600;color:var(--ink)}

.prep{display:flex;flex-wrap:wrap;align-items:center;gap:8px 10px;margin-top:9px;font-size:13.5px}
.stepper{display:inline-flex;align-items:center;border:1.5px solid var(--line);border-radius:8px;overflow:hidden}
.stepper button{width:26px;height:26px;border:0;background:var(--line2);font-weight:700;cursor:pointer;font-size:16px;line-height:1;color:var(--ink)}
.stepper button:hover{background:var(--line)}
.stepper span{padding:0 9px;font-weight:700;min-width:66px;text-align:center;font-size:13px}
.why{color:var(--ink2);flex:1 1 180px}
.linkbtn{background:none;border:0;padding:0;color:var(--a5);font-weight:600;cursor:pointer;text-decoration:underline}
.focusnote{font-size:12.5px;color:var(--ink2);font-weight:600}
.actions{display:flex;flex-wrap:wrap;gap:8px;margin-top:11px}

/* lists */
.feed{list-style:none;margin:0;padding:0;display:grid;gap:10px}
.feed li{border:1.5px solid var(--line);border-radius:12px;padding:12px 14px;background:#fff;display:flex;gap:12px;box-shadow:var(--shadow)}
.feed .ic{font-size:19px;line-height:1.3}
.feed small{color:var(--ink2);font-weight:500}
.empty{border:1.5px dashed var(--line);border-radius:14px;padding:36px 22px;text-align:center;background:#fff}
.empty h3{font-size:21px;margin-bottom:8px}
.empty p{color:var(--ink2);max-width:34em;margin:0 auto 16px}

/* notifications */
.notewrap{position:relative}
#notepanel{position:absolute;right:0;top:calc(100% + 12px);width:min(400px,calc(100vw - 32px));max-height:70vh;overflow:auto;z-index:20;
  background:#fff;border:1.5px solid var(--line);border-radius:14px;box-shadow:var(--shadow-lg);padding:14px}
#notepanel header{display:flex;align-items:center;justify-content:space-between;gap:8px;margin-bottom:8px}
#notepanel h3{font-size:18px}
.nlist{list-style:none;margin:0;padding:0;display:grid;gap:8px}
.nlist li{display:flex;gap:10px;padding:10px;border-radius:10px;border:1.5px solid var(--line2)}
.nlist li.new{background:var(--a5-t);border-color:var(--a5)}
.nlist p{font-size:13.5px;color:var(--ink2)}
.nlist strong{font-family:var(--display);font-size:15px;display:block}

#toasts{position:fixed;right:16px;bottom:16px;z-index:60;display:grid;gap:10px;width:min(380px,calc(100vw - 32px))}
.toast{display:flex;gap:10px;align-items:flex-start;background:#fff;border:1.5px solid var(--line);border-left:4px solid var(--a5);
  border-radius:12px;padding:12px 12px 12px 14px;box-shadow:var(--shadow-lg);animation:pop .3s cubic-bezier(.2,.9,.3,1.1)}
.toast.k-remind{border-left-color:var(--u-go)} .toast.k-change{border-left-color:var(--u-late)} .toast.k-new{border-left-color:var(--u-calm)}
.toast strong{font-family:var(--display);display:block;font-size:15px}
.toast p{font-size:13.5px;color:var(--ink2)}
.toast .ti{font-size:19px}
.toast button{margin-left:auto;border:0;background:none;font-size:20px;line-height:1;cursor:pointer;color:var(--ink2)}
@keyframes pop{from{transform:translateY(10px);opacity:0}}

/* drawer */
#drawer{position:fixed;inset:0;z-index:40;display:flex;justify-content:flex-end;background:rgba(18,23,46,.4)}
#drawer .panel{width:min(560px,100vw);height:100%;overflow:auto;background:#fff;border-left:1.5px solid var(--line);padding:22px 22px 60px;animation:slide .22s ease-out}
@keyframes slide{from{transform:translateX(30px);opacity:0}}
.panel h2{font-size:25px;font-weight:700;margin:10px 0 4px;overflow-wrap:anywhere}
.panel h4{font-size:17px;margin:22px 0 8px}
.panel ul,.panel ol{margin:0;padding-left:20px;display:grid;gap:6px}
.tags{display:flex;flex-wrap:wrap;gap:8px}
.tag{padding:5px 12px;border-radius:8px;border:1.5px solid var(--line);background:var(--line2);font-weight:600;font-size:13.5px;text-decoration:none;color:var(--ink)}
.tag:hover{border-color:var(--navy);background:#fff}
.vids{display:grid;gap:12px;grid-template-columns:repeat(auto-fill,minmax(210px,1fr))}
.vid{display:flex;flex-direction:column;gap:4px;text-decoration:none;color:var(--ink);border:1.5px solid var(--line);border-radius:10px;padding:8px;background:#fff}
.vid:hover{border-color:var(--navy)}
.vid img{width:100%;aspect-ratio:16/9;object-fit:cover;border-radius:6px;background:var(--line)}
.vid b{font-size:13.5px;line-height:1.25}
.vid small{color:var(--ink2)}
.searches{display:grid;gap:8px}
.callout{border:1.5px solid var(--a5);border-radius:10px;padding:12px 14px;background:var(--a5-t);margin-top:14px;font-size:14px}
.skel{height:16px;border-radius:6px;background:linear-gradient(90deg,var(--line),var(--line2),var(--line));background-size:200% 100%;animation:sh 1.2s infinite;margin:10px 0}
@keyframes sh{to{background-position:-200% 0}}

/* settings */
dialog{border:1.5px solid var(--line);border-radius:16px;padding:0;width:min(640px,calc(100vw - 24px));max-height:calc(100vh - 24px);box-shadow:var(--shadow-lg);color:var(--ink)}
dialog::backdrop{background:rgba(18,23,46,.45)}
.dlg{padding:24px}
.dlg h2{font-size:26px;font-weight:700}
.dlg fieldset{border:1.5px solid var(--line);border-radius:12px;margin:18px 0 0;padding:6px 16px 16px}
.dlg legend{font:700 16px var(--display);padding:0 8px}
.field{display:grid;gap:4px;margin-top:12px}
.field label{font-weight:600;font-size:14.5px}
.field small{color:var(--ink2)}
.field input,.field select{border:1.5px solid var(--line);border-radius:9px;padding:10px 12px;background:#fff;width:100%;min-width:0}
.field input:focus,.field select:focus{outline:2.5px solid var(--a5-t);border-color:var(--navy)}
.row2{display:grid;grid-template-columns:1fr 110px;gap:12px}
.seg{display:grid;grid-template-columns:repeat(3,1fr);gap:10px;margin-top:10px}
.codebox{font:700 28px/1 var(--display);letter-spacing:.12em;padding:14px 16px;border:1.5px dashed var(--navy);border-radius:10px;background:var(--line2);user-select:all;text-align:center}
.hint{font-size:13.5px;color:var(--ink2);margin-top:10px}
code{overflow-wrap:anywhere;background:var(--line2);padding:2px 6px;border-radius:6px;font-size:13px}
.seg label{border:1.5px solid var(--line);border-radius:10px;padding:10px 12px;cursor:pointer;display:block;font-weight:600;position:relative}
.seg label small{display:block;font-weight:500;color:var(--ink2)}
.seg input{position:absolute;opacity:0}
.seg label:has(input:checked){border-color:var(--navy);background:var(--line2)}
.seg label:has(input:focus-visible){outline:2.5px solid var(--navy)}
details{margin-top:10px;border:1.5px solid var(--line);border-radius:10px;padding:8px 12px;background:#fff}
details summary{cursor:pointer;font-weight:600}
details ol{margin:8px 0 4px;padding-left:20px;display:grid;gap:6px;font-size:14.5px}
.toggle{display:flex;gap:10px;align-items:center;font-weight:600;margin-top:12px}
.toggle input{width:18px;height:18px;accent-color:var(--navy)}
.status{min-height:24px;margin-top:14px;font-weight:600}
.status.err{color:var(--u-late)}
.status.ok{color:var(--u-calm)}
.dfoot{display:flex;gap:10px;flex-wrap:wrap;justify-content:flex-end;margin-top:8px}

/* focus timer */
#focusDlg .dlg{text-align:center;padding:30px 24px}
#focusDlg h2{font-size:15px;text-transform:uppercase;letter-spacing:.05em;color:var(--ink2);font-weight:700}
#focusTitle{font-size:21px;margin-top:4px}
#focusTime{font:700 64px/1 var(--display);margin:22px 0 6px;letter-spacing:-.02em;font-variant-numeric:tabular-nums}
.focuslens{display:flex;justify-content:center;gap:8px;margin-bottom:18px}
.focuslens button{border:1.5px solid var(--line);border-radius:8px;padding:6px 12px;background:#fff;font-weight:600;cursor:pointer;font-size:13px}
.focuslens button[aria-pressed=true]{border-color:var(--navy);background:var(--line2)}
.focusctl{display:flex;justify-content:center;gap:10px}

@media (max-width:640px){
  .bar{flex-wrap:wrap}
  .btn .lbl{display:none}
  .week{gap:5px}
  .day{padding:6px 2px 8px;min-height:72px}
  .day .dd{font-size:17px}
  .seg,.row2{grid-template-columns:1fr}
  .stats{grid-template-columns:repeat(2,1fr)}
}
@media (prefers-reduced-motion:reduce){
  *,*::before,*::after{animation:none!important;transition:none!important}
}

</style>
</head>
<body>
<header class="bar">
  <div class="brand">
    <svg width="38" height="38" viewBox="0 0 38 38" aria-hidden="true">
      <rect x="1.5" y="1.5" width="35" height="35" rx="9" fill="#12172E"/>
      <path d="M11 26V12h6.2a7 7 0 0 1 0 14H11Z" fill="none" stroke="#fff" stroke-width="2.3" stroke-linejoin="round"/>
      <path d="M24 12.5 27.5 16 24 19.5" fill="none" stroke="#0F6F63" stroke-width="2.3" stroke-linecap="round" stroke-linejoin="round" transform="translate(0 4)"/>
    </svg>
    <div><b>Duey</b><small>your deadline buddy, wherever your school keeps them</small></div>
  </div>
  <button class="btn" id="syncBtn" data-act="sync" title="Check for updates now">
    <svg class="icon" viewBox="0 0 24 24"><path d="M3 12a9 9 0 0 1 15-6.7L21 8"/><path d="M21 3v5h-5"/><path d="M21 12a9 9 0 0 1-15 6.7L3 16"/><path d="M8 16H3v5"/></svg>
    <span class="lbl">Check now</span>
  </button>
  <div class="notewrap">
    <button class="btn iconbtn" id="bellBtn" data-act="bell" aria-label="Notifications" aria-expanded="false">
      <svg class="icon" viewBox="0 0 24 24"><path d="M6 8a6 6 0 0 1 12 0c0 7 3 9 3 9H3s3-2 3-9"/><path d="M10.3 21a1.94 1.94 0 0 0 3.4 0"/></svg>
      <span class="badge" id="badge" hidden>0</span>
    </button>
    <section id="notepanel" hidden aria-label="Notifications"></section>
  </div>
  <button class="btn iconbtn" data-act="settings" aria-label="Settings">
    <svg class="icon" viewBox="0 0 24 24"><line x1="21" x2="14" y1="4" y2="4"/><line x1="10" x2="3" y1="4" y2="4"/><line x1="21" x2="12" y1="12" y2="12"/><line x1="8" x2="3" y1="12" y2="12"/><line x1="21" x2="16" y1="20" y2="20"/><line x1="12" x2="3" y1="20" y2="20"/><line x1="14" x2="14" y1="2" y2="6"/><line x1="8" x2="8" y1="10" y2="14"/><line x1="16" x2="16" y1="18" y2="22"/></svg>
  </button>
</header>

<main id="app"><div class="skel" style="max-width:420px"></div></main>
<div id="toasts" aria-live="polite"></div>

<div id="drawer" hidden>
  <div class="panel" role="dialog" aria-modal="true" aria-label="Study help">
    <button class="btn small" data-act="closehelp">Close</button>
    <div id="dbody"></div>
  </div>
</div>

<dialog id="focusDlg" aria-label="Focus timer">
  <div class="dlg">
    <h2>Focus session</h2>
    <div id="focusTitle">&nbsp;</div>
    <div id="focusTime">25:00</div>
    <div class="focuslens" id="focusLens">
      <button type="button" data-act="focuslen" data-min="15">15 min</button>
      <button type="button" data-act="focuslen" data-min="25" aria-pressed="true">25 min</button>
      <button type="button" data-act="focuslen" data-min="50">50 min</button>
    </div>
    <div class="focusctl">
      <button class="btn primary" type="button" id="focusToggle" data-act="focustoggle">Start</button>
      <button class="btn" type="button" data-act="focusreset">Reset</button>
      <button class="btn" type="button" data-act="closefocus">Close</button>
    </div>
  </div>
</dialog>

<dialog id="settings">
  <div class="dlg">
    <h2>Settings</h2>
    <p style="color:var(--ink2);margin-top:6px">Your settings and deadlines are saved on this computer only. Optional extras (email, Claude, YouTube) send limited data when you turn them on. <a href="/privacy" target="_blank" rel="noopener noreferrer">How Duey handles your data</a>. Blank password boxes keep what you saved before.</p>

    <fieldset>
      <legend>Connect your school portal</legend>
      <div class="seg" role="radiogroup" aria-label="How to connect">
        <label><input type="radio" name="mode" value="ical"> Calendar link<small>Easiest. Works for everyone.</small></label>
        <label><input type="radio" name="mode" value="api"> Security key<small>Knows what you've handed in, if your school offers one.</small></label>
        <label><input type="radio" name="mode" value="ext"> Browser extension<small>No key needed. Knows what you've handed in.</small></label>
      </div>

      <div id="pane-ical">
        <div class="field">
          <label for="f_cal">Your calendar link</label>
          <input id="f_cal" type="password" autocomplete="new-password" placeholder="Paste your calendar / iCal link here">
        </div>
        <details><summary>Where do I find this?</summary>
          <ol>
            <li>Look for a <b>Calendar</b> page or menu in your course portal.</li>
            <li>Look for an option called something like <b>Export</b>, <b>Subscribe</b>, or <b>Calendar feed</b> — it's usually in the calendar's settings or a small icon near the top.</li>
            <li>If asked, set the date range to cover your whole term (not just "today").</li>
            <li>Copy the link it gives you (it usually contains the word "ical", "ics", or "calendar") and paste it above.</li>
          </ol>
        </details>
      </div>

      <div id="pane-ext" hidden>
        <p style="margin-top:12px">Use this when there's no calendar link or security key that does the job. A small add-on for Chrome, Edge or Brave reads your deadlines while you're logged in and hands them to Duey on this computer. Your password is never shared.</p>
        <div class="field"><label>Your pairing code</label><div class="codebox" id="extCode">&nbsp;</div>
          <small>You'll type this into the extension once.</small></div>
        <details open><summary>Install it (about a minute)</summary>
          <ol>
            <li>In your browser's address bar, go to <b>chrome://extensions</b> (Edge: <b>edge://extensions</b>).</li>
            <li>Turn on <b>Developer mode</b> (the switch in the top right).</li>
            <li>Click <b>Load unpacked</b> and pick this folder: <code id="extPath"></code></li>
            <li>Click the puzzle-piece icon in your toolbar and pin <b>Duey</b>.</li>
            <li>Open your course portal and log in. Click the Duey icon, type the pairing code, and press <b>Connect</b>.</li>
          </ol>
        </details>
        <p class="hint">Press Save below first, then follow the steps. Keep your browser open and Duey stays up to date.</p>
      </div>

      <div id="pane-api" hidden>
        <div class="field">
          <label for="f_addr">School portal address</label>
          <input id="f_addr" type="url" autocomplete="off" spellcheck="false" placeholder="https://your-school-portal.edu">
        </div>
        <div class="field">
          <label for="f_key">Security key (access token)</label>
          <input id="f_key" type="password" autocomplete="new-password">
        </div>
        <p class="hint">No security key on your account, or it doesn't work? <button class="linkbtn" type="button" data-act="gotoext">Use the browser extension instead</button>.</p>
        <details><summary>Or sign in once with your school username and password</summary>
          <div class="field"><label for="f_user">Username</label><input id="f_user" autocomplete="off"></div>
          <div class="field"><label for="f_pass">Password</label><input id="f_pass" type="password" autocomplete="off">
            <small>Only used once, to ask your school portal for a token. Duey never saves your password. This only
            works on some school portals, and never on ones with single sign-on — if it doesn't work, generate a
            token by hand below, or use the calendar link instead.</small></div>
        </details>
        <details><summary>Where do I find this?</summary>
          <ol>
            <li>Type your school portal's address above — the same address you log in at.</li>
            <li>Look in your account, profile, or settings menu for something called <b>Access Tokens</b>,
              <b>Security keys</b>, <b>API tokens</b>, or <b>Developer settings</b>.</li>
            <li>Generate one and copy it right away — some systems only show it once.</li>
            <li>Not every school offers this. If you can't find anything like it, use the calendar link
              above instead — it works everywhere.</li>
          </ol>
        </details>
      </div>
    </fieldset>

    <fieldset>
      <legend>Email me too</legend>
      <div class="field"><label for="f_email_to">Your email address</label>
        <input id="f_email_to" type="email" autocomplete="email" placeholder="you@example.com">
        <small>Type your email to get deadline alerts. Leave it blank for none.</small></div>
      <div class="dfoot" style="justify-content:flex-start;margin-top:12px">
        <button class="btn small" type="button" data-act="testmail">Send a test email</button>
      </div>
      <details><summary>Advanced: send from my own mail account</summary>
        <div class="row2">
          <div class="field"><label for="f_smtp_host">Mail server</label><input id="f_smtp_host" placeholder="smtp.gmail.com"></div>
          <div class="field"><label for="f_smtp_port">Port</label><input id="f_smtp_port" inputmode="numeric" placeholder="587"></div>
        </div>
        <div class="field"><label for="f_smtp_user">Mail login</label><input id="f_smtp_user" autocomplete="off"></div>
        <div class="field"><label for="f_smtp_pass">Mail password</label><input id="f_smtp_pass" type="password" autocomplete="off">
          <small>Gmail needs an App Password from myaccount.google.com/apppasswords.</small></div>
        <button class="btn small" type="button" data-act="gmail">Fill in Gmail settings</button>
      </details>
    </fieldset>

    <fieldset>
      <legend>Extras</legend>
      <div class="field"><label for="f_minutes">Check for updates every</label>
        <select id="f_minutes"><option value="1">1 minute</option><option value="5">5 minutes</option><option value="15">15 minutes</option><option value="30">30 minutes</option><option value="60">1 hour</option></select></div>
      <div class="field"><label for="f_yt">YouTube API key (optional)</label><input id="f_yt" type="password" autocomplete="off">
        <small>Shows real video suggestions in Study help. <a href="https://console.cloud.google.com/apis/library/youtube.googleapis.com" target="_blank" rel="noopener noreferrer">Open Google Cloud Console</a>, click <b>Enable</b>, then open <a href="https://console.cloud.google.com/apis/credentials" target="_blank" rel="noopener noreferrer">Credentials</a> and choose <b>Create credentials → API key</b>. Paste it here. Without it you still get tailored YouTube searches.</small></div>
      <div class="field"><label for="f_ai">Claude API key (optional)</label><input id="f_ai" type="password" autocomplete="off">
        <small>Gives smarter summaries, study plans and time estimates. If you add one, the assignment text is sent to Anthropic when you open Study help.</small></div>
    </fieldset>

    <div class="status" id="setStatus" role="status"></div>
    <div class="dfoot">
      <button class="btn" type="button" data-act="cancelset">Cancel</button>
      <button class="btn primary" type="button" data-act="saveset">Save and check for updates</button>
    </div>
  </div>
</dialog>

<script>
"use strict";
const $ = s => document.querySelector(s);
const esc = s => String(s == null ? "" : s).replace(/[&<>"']/g, c => ({"&":"&amp;","<":"&lt;",">":"&gt;",'"':"&quot;","'":"&#39;"}[c]));
const COLORS = ["a1","a2","a3","a4","a5","a6"];
const ICON = {remind:"⏰", new:"🆕", change:"📅", system:"👋"};
const DAY = 86400;
let S = null, tab = "focus", sig = "", seenNote = -1, firstRender = true, opened = false, newIds = new Set();

async function api(path, body){
  const opt = body === undefined ? {} : {method:"POST", headers:{"Content-Type":"application/json"}, body:JSON.stringify(body)};
  const r = await fetch(path, opt);
  return r.json();
}

/* ---------- time helpers ---------- */
const nowS = () => Date.now()/1000;
function fmtDue(ts){ return new Date(ts*1000).toLocaleString(undefined,{weekday:"short",day:"numeric",month:"short",hour:"numeric",minute:"2-digit"}); }
function fmtDay(ts){ return new Date(ts*1000).toLocaleDateString(undefined,{weekday:"short",day:"numeric",month:"short"}); }
function calDays(ts){
  const a = new Date(ts*1000), b = new Date();
  a.setHours(0,0,0,0); b.setHours(0,0,0,0);
  return Math.round((a-b)/(DAY*1000));
}
function plural(n,w){ return n + " " + w + (n === 1 ? "" : "s"); }
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
function courseColor(name){
  const names = [...new Set(S.items.map(i => i.course))].sort();
  return COLORS[Math.max(0, names.indexOf(name)) % COLORS.length];
}
const FACE = '';

/* ---------- rendering ---------- */
function card(it){
  const u = urgency(it), col = courseColor(it.course), n = nowS();
  const span = Math.max(1, it.due - it.start);
  let pct = Math.max(0, Math.min(1, (n - it.start)/span));
  if (u === "done") pct = 1;
  const x = Math.round(3 + pct*94);
  let note = "";
  if (u === "late"){
    const dLate = Math.max(1, Math.abs(calDays(it.due)));
    note = "Overdue by " + plural(dLate,"day") + ". Mark it done once it's submitted, or message your professor.";
  }
  else if (u === "done") note = it.gone && !it.done ? "It left your school portal's list, so it's probably submitted." : "Nicely done.";
  else if (u === "go") note = "Prep window is open. " + Math.round(pct*100) + "% of it is behind you.";
  else note = "Duey will nudge you " + rel(it.start) + " (" + fmtDay(it.start) + ").";
  const pill = u === "done" ? "done" : rel(it.due);
  const stickers = (it.fresh ? '<span class="sticker">New</span>' : "") + (it.changed && !it.fresh ? '<span class="sticker upd">Updated</span>' : "");
  const prepRow = (u === "done") ? "" : `
    <div class="prep">
      <span class="stepper" role="group" aria-label="Prep time">
        <button data-act="prep" data-id="${esc(it.id)}" data-d="-1" aria-label="One day less">−</button>
        <span>${plural(it.prep,"day")}</span>
        <button data-act="prep" data-id="${esc(it.id)}" data-d="1" aria-label="One day more">+</button>
      </span>
      <span class="why">${it.prep_manual ? 'You set this. <button class="linkbtn" data-act="prepreset" data-id="'+esc(it.id)+'">Use Duey\'s guess</button>' : esc(it.why || "")}</span>
    </div>`;
  return `<article class="card u-${u}">
    <div class="top">
      <span class="chip" style="background:var(--${col}-t)"><i style="background:var(--${col})"></i><span>${esc(it.course)}</span></span>
      <span class="kind">${esc(it.kind || "task")}</span>${stickers}
      <span class="pill">${esc(pill)}</span>
    </div>
    <h3>${esc(it.title)}</h3>
    <div class="when">Due ${esc(fmtDue(it.due))}</div>
    <div class="runway" aria-hidden="true">
      <div class="track"><div class="fill" style="width:${x}%"></div><div class="you" style="left:${x}%">${FACE}</div></div>
      <div class="ends"><span>Start by ${esc(fmtDay(it.start))}</span><span>Due ${esc(fmtDay(it.due))}</span></div>
    </div>
    <div class="note">${esc(note)}</div>
    ${prepRow}
    <div class="actions">
      ${u === "done" ? `<button class="btn small" data-act="undone" data-id="${esc(it.id)}">Undo</button>`
                     : `<button class="btn small" data-act="done" data-id="${esc(it.id)}">Mark done</button>`}
      <button class="btn small primary" data-act="help" data-id="${esc(it.id)}">Study help</button>
      ${u === "done" ? "" : `<button class="btn small" data-act="focus" data-id="${esc(it.id)}">Focus timer</button>`}
      ${it.url ? `<a class="btn small ghost" href="${esc(it.url)}" target="_blank" rel="noopener noreferrer">Open assignment</a>` : ""}
      ${it.focus_min ? `<span class="focusnote">Focused ${plural(it.focus_min,"min")} so far</span>` : ""}
    </div>
  </article>`;
}

function weekStrip(open){
  let out = "";
  for (let i = 0; i < 7; i++){
    const d = new Date(); d.setHours(0,0,0,0); d.setDate(d.getDate() + i);
    const items = open.filter(it => { const c = new Date(it.due*1000); c.setHours(0,0,0,0); return +c === +d; });
    const dots = items.map(it => `<i style="background:var(--${courseColor(it.course)})"></i>`).join("");
    const label = items.map(it => it.title).join(", ");
    out += `<div class="day${i===0?" today":""}${items.length?" has":""}" ${label ? `title="${esc(label)}"` : ""}>
      <div class="dn">${i===0 ? "Today" : d.toLocaleDateString(undefined,{weekday:"short"})}</div>
      <div class="dd">${d.getDate()}</div><div class="dots">${dots}</div></div>`;
  }
  return `<div class="week" aria-label="Next 7 days">${out}</div>`;
}

function group(title, sub, items){
  if (!items.length) return "";
  return `<section class="group"><h2>${esc(title)}</h2><p>${esc(sub)}</p><div class="cards">${items.map(card).join("")}</div></section>`;
}

function statStrip(open, late, go, st){
  const dueWeek = open.filter(i => i.due - nowS() < 7*DAY).length;
  const cells = [
    [late.length, "Overdue", late.length ? "warn" : ""],
    [go.length, "Start today", go.length ? "go" : ""],
    [dueWeek, "Due this week", ""],
    [st.streak, st.streak ? "Day streak" : "Day streak", st.streak ? "calm" : ""],
    [st.done_total, "Completed", ""],
  ];
  return `<div class="stats">${cells.map(c => `<div class="stat ${c[2]}"><b>${c[0]}</b><span>${esc(c[1])}</span></div>`).join("")}</div>`;
}

function render(){
  if (!S) return;
  const app = $("#app");
  const items = S.items;
  const open = items.filter(i => !i.done && !i.gone);
  const late = open.filter(i => urgency(i) === "late");
  const go = open.filter(i => urgency(i) === "go");
  const soon = open.filter(i => urgency(i) === "soon" || (urgency(i) === "calm" && i.due - nowS() < 7*DAY));
  const later = open.filter(i => !late.includes(i) && !go.includes(i) && !soon.includes(i));
  const doneList = items.filter(i => i.done || i.gone).sort((a,b) => b.due - a.due);
  let html = "";

  if (!S.configured){
    html = `<section class="hero"><h1>Let's connect Duey to your school portal</h1>
      <p class="sub">It takes about two minutes. You only need to do it once.</p></section>
      <div class="empty" style="margin-top:26px"><h3>Nothing to show yet</h3>
      <p>Open settings and paste your school portal's calendar link. Duey will pull in your deadlines, watch for changes, and remind you when it's time to start.</p>
      <button class="btn primary" data-act="settings">Open settings</button></div>`;
  } else {
    let h1;
    if (late.length && !go.length) h1 = plural(late.length,"thing") + " slipped past its deadline";
    else if (go.length) h1 = plural(go.length,"thing") + " to start today";
    else if (soon.length) h1 = plural(soon.length,"deadline") + " this week, nothing to start yet";
    else if (open.length) h1 = "Nothing pressing today";
    else h1 = "You're all caught up";
    const bits = [];
    if (late.length && go.length) bits.push(plural(late.length,"overdue item"));
    bits.push("Last checked " + ago(S.last_sync));
    html += `<section class="hero"><h1>${esc(h1)}</h1><p class="sub">${esc(bits.join(". "))}. Duey checks your school portal every ${Number(S.settings.sync_minutes) === 1 ? "minute" : S.settings.sync_minutes + " minutes"} while this window is open.</p></section>`;
    html += statStrip(open, late, go, S.stats);
    html += weekStrip(open);
    if (S.last_error) html += `<div class="banner" role="alert"><div><strong>Couldn't reach your school portal.</strong> ${esc(S.last_error)} Duey will try again in a couple of minutes.</div></div>`;
    if (S.email_error && S.settings.email_enabled) html += `<div class="banner" role="alert"><div><strong>Email isn't working.</strong> ${esc(S.email_error)}</div></div>`;

    const tabs = [["focus","Focus",late.length+go.length+soon.length],["all","Everything",open.length],["done","Done",doneList.length],["changes","Changes",S.changes.length]];
    html += `<div class="tabs" role="tablist">${tabs.map(t => `<button class="tab" role="tab" aria-selected="${tab===t[0]}" data-act="tab" data-tab="${t[0]}">${t[1]}<span class="ct">${t[2]}</span></button>`).join("")}</div>`;

    if (tab === "focus" || tab === "all"){
      const shown = tab === "focus" ? late.length+go.length+soon.length : open.length;
      if (!shown){
        html += `<div class="empty"><h3>${open.length ? "Nothing needs you right now" : "No upcoming deadlines"}</h3>
          <p>${open.length ? "Everything left is further away. Duey will nudge you when it's time to start." : "Either you're free, or your calendar link only covers a short window. Try a longer date range when you export it."}</p>
          ${open.length ? '<button class="btn" data-act="tab" data-tab="all">See everything</button>' : ""}</div>`;
      } else {
        html += group("Overdue","These slipped past the deadline.",late);
        html += group("Start these now","Their prep window has opened.",go);
        html += group("Due this week","Coming up fast, but you have a little time.",soon);
        if (tab === "all") html += group("Coming up","Duey will nudge you when it's time to start.",later);
      }
    } else if (tab === "done"){
      html += doneList.length ? `<div class="cards">${doneList.map(card).join("")}</div>`
        : `<div class="empty"><h3>Nothing ticked off yet</h3><p>Finished items land here.</p></div>`;
    } else {
      const ic = {due:"📅", desc:"📝", title:"✏️", gone:"👋", back:"↩️"};
      html += S.changes.length ? `<ul class="feed">${S.changes.map(c => `<li><span class="ic">${ic[c.kind]||"📌"}</span><div><strong>${esc(c.title || "Item")}</strong><br>${esc(c.text)}<br><small>${esc(ago(c.ts))}</small></div></li>`).join("")}</ul>`
        : `<div class="empty"><h3>No changes so far</h3><p>When a prof moves a date or edits instructions, it shows up here and you get a ping.</p></div>`;
    }
  }
  app.className = firstRender ? "" : "noanim";
  app.innerHTML = html;
  firstRender = false;
}

function renderHeader(){
  const b = $("#badge");
  b.hidden = !S.unread; b.textContent = S.unread > 99 ? "99+" : S.unread;
  $("#syncBtn").classList.toggle("spin", !!S.syncing);
}

function renderPanel(){
  const p = $("#notepanel");
  const canDesk = "Notification" in window && Notification.permission === "default";
  p.innerHTML = `<header><h3>Notifications</h3>${S.notifications.length ? '<button class="btn small ghost" data-act="markread">Mark all read</button>' : ""}</header>
    ${S.notifications.length ? `<ul class="nlist">${S.notifications.map(n => `<li class="${newIds.has(n.id)?"new":""}"><span style="font-size:20px">${ICON[n.kind]||"🔔"}</span><div><strong>${esc(n.title)}</strong><p>${esc(n.body)}</p><p>${esc(ago(n.ts))}</p></div></li>`).join("")}</ul>`
      : '<p style="color:var(--ink2)">All quiet. Reminders and changes will show up here.</p>'}
    ${canDesk ? '<div class="callout">Want pings even when this tab is in the background? <button class="linkbtn" data-act="desk">Turn on desktop notifications</button></div>' : ""}`;
}

/* ---------- toasts + desktop pings ---------- */
function toast(n){
  const box = $("#toasts");
  while (box.children.length >= 4) box.firstChild.remove();
  const el = document.createElement("div");
  el.className = "toast k-" + n.kind;
  el.innerHTML = `<div class="ti">${ICON[n.kind]||"🔔"}</div><div><strong>${esc(n.title)}</strong><p>${esc(n.body)}</p></div><button aria-label="Dismiss">×</button>`;
  el.querySelector("button").onclick = () => el.remove();
  box.appendChild(el);
  setTimeout(() => el.remove(), 14000);
}
function desktop(n){
  if ("Notification" in window && Notification.permission === "granted"){
    try { new Notification(n.title, {body:n.body}); } catch(e){}
  }
}

/* ---------- state loop ---------- */
async function load(force){
  let st;
  try { st = await api("/api/state"); } catch(e){ return; }
  S = st;
  const fresh = st.notifications.filter(n => !n.read && n.id > seenNote).sort((a,b) => a.id - b.id);
  if (seenNote < 0) fresh.slice(-3).forEach(toast);
  else fresh.forEach(n => { toast(n); desktop(n); });
  fresh.forEach(n => newIds.add(n.id));
  const ids = st.notifications.map(n => n.id);
  seenNote = Math.max(seenNote, 0, ...ids);
  renderHeader();
  if (!$("#notepanel").hidden) renderPanel();
  const s = JSON.stringify([st.items, st.changes, st.last_error, st.email_error, st.configured, st.last_sync, Math.floor(st.now/300), st.settings.sync_minutes, st.stats]);
  if (force || s !== sig){ sig = s; render(); }
  if (!st.configured && !opened){ opened = true; openSettings(); }
}

/* ---------- study help drawer ---------- */
async function openHelp(id, refresh){
  const it = S.items.find(i => i.id === id);
  $("#drawer").hidden = false;
  document.body.style.overflow = "hidden";
  $("#dbody").innerHTML = `<h2>${esc(it ? it.title : "Study help")}</h2><p style="color:var(--ink2)">Reading the assignment…</p><div class="skel"></div><div class="skel" style="width:80%"></div><div class="skel" style="width:60%"></div>`;
  let r;
  try { r = await api("/api/help/" + encodeURIComponent(id) + (refresh ? "?refresh=1" : "")); }
  catch(e){ r = {ok:false, error:"Couldn't reach Duey."}; }
  if (!r.ok){ $("#dbody").innerHTML = `<h2>Hmm</h2><p>${esc(r.error)}</p>`; return; }
  const h = r.help, col = it ? courseColor(it.course) : "grape";
  let out = `<span class="chip" style="background:var(--${col}-t);margin-top:14px"><i style="background:var(--${col})"></i><span>${esc(it ? it.course : "")}</span></span>
    <h2>${esc(it ? it.title : "")}</h2>`;
  if (!h.words) out += `<div class="callout">This one has no written brief on your school portal, so Duey is working from the title alone. Check your syllabus or ask your instructor for details.</div>`;
  if (h.summary) out += `<h4>The short version</h4><p>${esc(h.summary)}</p>`;
  if (h.ai_days && it && h.ai_days !== it.prep) out += `<div class="callout">Claude thinks this needs about <b>${plural(h.ai_days,"day")}</b> of prep. <button class="linkbtn" data-act="useai" data-id="${esc(id)}" data-d="${h.ai_days}">Use ${plural(h.ai_days,"day")}</button></div>`;
  if (h.steps && h.steps.length) out += `<h4>A gentle plan</h4><ol>${h.steps.map(s => `<li>${esc(s)}</li>`).join("")}</ol>`;
  if (h.asks && h.asks.length) out += `<h4>What they're asking for</h4><ul>${h.asks.map(s => `<li>${esc(s)}</li>`).join("")}</ul>`;
  if (h.topics && h.topics.length) out += `<h4>Ideas to get comfortable with</h4><div class="tags">${h.topics.map(t => `<a class="tag" target="_blank" rel="noopener noreferrer" href="https://www.youtube.com/results?search_query=${encodeURIComponent(t + " explained")}">${esc(t)}</a>`).join("")}</div>`;
  out += `<h4>Videos to watch</h4>`;
  if (h.videos && h.videos.length){
    out += `<div class="vids">${h.videos.map(v => `<a class="vid" target="_blank" rel="noopener noreferrer" href="https://www.youtube.com/watch?v=${esc(v.id)}">${v.thumb ? `<img loading="lazy" alt="" src="${esc(v.thumb)}">` : ""}<b>${esc(v.title)}</b><small>${esc(v.channel)}</small></a>`).join("")}</div>`;
  } else {
    out += `<div class="searches">${(h.queries||[]).map(qq => `<a class="btn small" target="_blank" rel="noopener noreferrer" href="https://www.youtube.com/results?search_query=${encodeURIComponent(qq)}">Search YouTube: ${esc(qq)}</a>`).join("")}</div>
      <div class="callout">Want the videos to show up right here? Add a free YouTube API key in settings.</div>`;
  }
  if (!h.ai) out += `<div class="callout">Add a Claude API key in settings for a smarter summary, a step-by-step plan and better time estimates.</div>`;
  (h.notes || []).forEach(n => out += `<div class="banner" style="margin-top:14px">${esc(n)}</div>`);
  out += `<p style="margin-top:22px"><button class="btn small" data-act="refreshhelp" data-id="${esc(id)}">Refresh suggestions</button></p>`;
  $("#dbody").innerHTML = out;
}
function closeHelp(){ $("#drawer").hidden = true; document.body.style.overflow = ""; }

/* ---------- focus timer ---------- */
let focusState = {id:null, remaining:25*60, length:25*60, running:false, timer:null, banked:0};
function fmtClock(sec){ const m = Math.floor(sec/60), s = sec%60; return String(m).padStart(2,"0") + ":" + String(s).padStart(2,"0"); }
function renderFocus(){
  const it = S && S.items.find(i => i.id === focusState.id);
  $("#focusTitle").textContent = it ? it.title : "";
  $("#focusTime").textContent = fmtClock(focusState.remaining);
  $("#focusToggle").textContent = focusState.running ? "Pause" : (focusState.remaining === focusState.length ? "Start" : "Resume");
  document.querySelectorAll("#focusLens button").forEach(b => b.setAttribute("aria-pressed", String(Number(b.dataset.min)*60 === focusState.length)));
}
function tickFocus(){
  if (!focusState.running) return;
  focusState.remaining--; focusState.banked++;
  if (focusState.remaining <= 0){
    stopFocusTimer(); focusState.remaining = 0; renderFocus(); saveFocus();
    toast({kind:"system", title:"Focus session complete", body:"Nice work. Stretch, then start another if you're on a roll."});
    return;
  }
  renderFocus();
}
function stopFocusTimer(){ focusState.running = false; if (focusState.timer) clearInterval(focusState.timer); focusState.timer = null; }
async function saveFocus(){
  if (focusState.banked > 0 && focusState.id){
    const seconds = focusState.banked; focusState.banked = 0;
    try { await api("/api/focus", {id: focusState.id, seconds}); await load(true); } catch(e){}
  }
}
function openFocus(id){
  stopFocusTimer();
  focusState = {id, remaining:25*60, length:25*60, running:false, timer:null, banked:0};
  renderFocus();
  $("#focusDlg").showModal();
}
function closeFocus(){ stopFocusTimer(); saveFocus(); if ($("#focusDlg").open) $("#focusDlg").close(); }

/* ---------- settings ---------- */
const F = id => document.getElementById(id);
function setMode(m){
  F("pane-ical").hidden = m !== "ical";
  F("pane-api").hidden = m !== "api";
  F("pane-ext").hidden = m !== "ext";
  document.querySelectorAll('input[name=mode]').forEach(r => r.checked = r.value === m);
}
function openSettings(){
  const s = S ? S.settings : {};
  setMode(s.mode || "ical");
  F("f_addr").value = (s.has_token && s.base_url) ? s.base_url : "";
  F("extCode").textContent = s.ext_code || "";
  F("extPath").textContent = s.ext_path || "the duey-extension folder that came with duey.py";
  F("f_cal").value = ""; F("f_key").value = "";
  F("f_cal").placeholder = s.has_ical_url ? "Saved. Leave blank to keep it." : "Paste your calendar / iCal link here";
  F("f_key").placeholder = s.has_token ? "Saved. Leave blank to keep it." : "";
  F("f_email_to").value = s.email_to || "";
  F("f_smtp_host").value = s.smtp_host || "";
  F("f_smtp_port").value = s.smtp_port || 587;
  F("f_smtp_user").value = s.smtp_user || "";
  F("f_smtp_pass").value = ""; F("f_smtp_pass").placeholder = s.has_smtp_pass ? "Saved. Leave blank to keep it." : "";
  F("f_minutes").value = String(s.sync_minutes || 5);
  F("f_yt").value = ""; F("f_yt").placeholder = s.has_youtube_key ? "Saved. Leave blank to keep it." : "";
  F("f_ai").value = ""; F("f_ai").placeholder = s.has_anthropic_key ? "Saved. Leave blank to keep it." : "";
  const u = F("f_user"), p = F("f_pass"); if (u){ u.value = ""; p.value = ""; }
  setStatus("");
  if (!F("settings").open) F("settings").showModal();
}
function setStatus(msg, cls){ const el = F("setStatus"); el.textContent = msg; el.className = "status " + (cls || ""); }
function collect(){
  const mode = document.querySelector('input[name=mode]:checked').value;
  const o = {mode, base_url:F("f_addr").value, ical_url:F("f_cal").value, token:F("f_key").value,
    email_enabled:!!F("f_email_to").value.trim(), email_to:F("f_email_to").value, smtp_host:F("f_smtp_host").value,
    smtp_port:F("f_smtp_port").value, smtp_user:F("f_smtp_user").value, smtp_pass:F("f_smtp_pass").value,
    sync_minutes:F("f_minutes").value, youtube_key:F("f_yt").value, anthropic_key:F("f_ai").value};
  if (F("f_user")){ o.username = F("f_user").value; o.password = F("f_pass").value; }
  return o;
}

/* ---------- clicks ---------- */
document.addEventListener("change", e => { if (e.target.name === "mode") setMode(e.target.value); });
document.addEventListener("click", async e => {
  const btnEl = e.target.closest("[data-act]");
  const np = $("#notepanel");
  if (!np.hidden && !e.target.closest(".notewrap")){ np.hidden = true; $("#bellBtn").setAttribute("aria-expanded","false"); }
  if (!btnEl) return;
  const act = btnEl.dataset.act, id = btnEl.dataset.id;
  if (act === "tab"){ tab = btnEl.dataset.tab; render(); }
  else if (act === "sync"){
    btnEl.disabled = true; btnEl.classList.add("spin");
    const r = await api("/api/sync", {}); await load(true);
    btnEl.disabled = false; btnEl.classList.remove("spin");
    if (!r.ok) toast({kind:"change", title:"Couldn't check your school portal", body:r.error});
  }
  else if (act === "bell"){
    np.hidden = !np.hidden; btnEl.setAttribute("aria-expanded", String(!np.hidden));
    if (!np.hidden){ renderPanel(); if (S.unread){ await api("/api/notifications/read", {}); S.unread = 0; renderHeader(); } }
  }
  else if (act === "markread"){ await api("/api/notifications/read", {}); newIds.clear(); await load(); renderPanel(); }
  else if (act === "desk"){ await Notification.requestPermission(); renderPanel(); }
  else if (act === "settings") openSettings();
  else if (act === "cancelset") F("settings").close();
  else if (act === "gotoext") setMode("ext");
  else if (act === "gmail"){ F("f_smtp_host").value = "smtp.gmail.com"; F("f_smtp_port").value = 587; if (!F("f_smtp_user").value) F("f_smtp_user").value = F("f_email_to").value; }
  else if (act === "saveset"){
    setStatus("Saving and checking your school portal…");
    btnEl.disabled = true;
    const r = await api("/api/settings", {settings:collect(), sync:true});
    btnEl.disabled = false;
    if (!r.ok){ setStatus(r.error || "Something went wrong.", "err"); await load(true); return; }
    F("settings").close(); await load(true);
    toast({kind:"system", title:"Saved", body: r.waiting ? "Now install the extension and enter your pairing code." : "Found " + plural(r.count || 0, "deadline") + "."});
  }
  else if (act === "testmail"){
    setStatus("Sending…");
    const s = await api("/api/settings", {settings:collect(), sync:false});
    if (!s.ok){ setStatus(s.error, "err"); return; }
    const r = await api("/api/test-email", {});
    setStatus(r.ok ? "Sent! Check your inbox (and spam folder)." : r.error, r.ok ? "ok" : "err");
  }
  else if (act === "done" || act === "undone"){ await api("/api/item", {id, done: act === "done"}); await load(true); }
  else if (act === "prep"){
    const it = S.items.find(i => i.id === id);
    await api("/api/item", {id, prep_days: Math.max(1, Math.min(21, it.prep + Number(btnEl.dataset.d)))}); await load(true);
  }
  else if (act === "prepreset"){ await api("/api/item", {id, prep_days:null}); await load(true); }
  else if (act === "useai"){ await api("/api/item", {id, prep_days:Number(btnEl.dataset.d)}); await load(true); btnEl.outerHTML = "<b>Done!</b>"; }
  else if (act === "help") openHelp(id, false);
  else if (act === "refreshhelp") openHelp(id, true);
  else if (act === "closehelp") closeHelp();
  else if (act === "focus") openFocus(id);
  else if (act === "focustoggle"){
    focusState.running = !focusState.running;
    if (focusState.running) focusState.timer = setInterval(tickFocus, 1000); else { stopFocusTimer(); saveFocus(); }
    renderFocus();
  }
  else if (act === "focusreset"){ stopFocusTimer(); saveFocus(); focusState.remaining = focusState.length; renderFocus(); }
  else if (act === "focuslen"){
    if (focusState.running) return;
    focusState.length = Number(btnEl.dataset.min) * 60; focusState.remaining = focusState.length; renderFocus();
  }
  else if (act === "closefocus") closeFocus();
});
$("#focusDlg").addEventListener("cancel", () => { stopFocusTimer(); saveFocus(); });
$("#drawer").addEventListener("click", e => { if (e.target.id === "drawer") closeHelp(); });
document.addEventListener("keydown", e => {
  if (e.key !== "Escape") return;
  if (!$("#drawer").hidden) closeHelp();
  const np = $("#notepanel"); if (!np.hidden){ np.hidden = true; $("#bellBtn").setAttribute("aria-expanded","false"); }
});

load(true);
setInterval(load, 20000);
</script>
</body>
</html>
"""


class Handler(BaseHTTPRequestHandler):
    server_version = "Duey"

    def log_message(self, *a):
        pass

    def _send(self, code, body, ctype="application/json; charset=utf-8"):
        if isinstance(body, (dict, list)):
            body = json.dumps(body)
        body = body.encode("utf-8")
        self.send_response(code)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Cache-Control", "no-store")
        self.send_header("X-Content-Type-Options", "nosniff")
        self.send_header("Referrer-Policy", "no-referrer")
        self.send_header("Content-Security-Policy",
                         "default-src 'self'; style-src 'self' 'unsafe-inline' https://fonts.googleapis.com; "
                         "font-src https://fonts.gstatic.com; img-src 'self' data: https://i.ytimg.com; "
                         "script-src 'self' 'unsafe-inline'; connect-src 'self'; frame-ancestors 'none'")
        self.end_headers()
        self.wfile.write(body)

    def _host_ok(self):
        host = (self.headers.get("Host") or "").rsplit(":", 1)[0].strip("[]")
        return host in ("127.0.0.1", "localhost", "::1")

    def do_GET(self):
        if not self._host_ok():
            return self._send(403, {"error": "forbidden"})
        u = urllib.parse.urlparse(self.path)
        if u.path == "/":
            return self._send(200, PAGE, "text/html; charset=utf-8")
        if u.path == "/api/state":
            return self._send(200, build_state())
        if u.path == "/privacy":
            return self._send(200, privacy_html(), "text/html; charset=utf-8")
        if u.path == "/api/ping":
            c = load_cfg()
            want = float(meta_get("ext_want", 0) or 0) > float(meta_get("last_sync", 0) or 0)
            return self._send(200, {"duey": True, "mode": c["mode"], "every": int(c["sync_minutes"]), "want": want})
        if u.path.startswith("/api/help/"):
            item_id = urllib.parse.unquote(u.path[len("/api/help/"):])
            refresh = "refresh=1" in (u.query or "")
            return self._send(200, help_for(item_id, refresh))
        self._send(404, {"error": "not found"})

    def do_POST(self):
        if not self._host_ok() or "application/json" not in (self.headers.get("Content-Type") or ""):
            return self._send(403, {"error": "forbidden"})
        try:
            n = int(self.headers.get("Content-Length") or 0)
            body = json.loads(self.rfile.read(n) or b"{}")
        except ValueError:
            return self._send(400, {"error": "bad request"})
        p = self.path
        if p == "/api/sync":
            if load_cfg()["mode"] == "ext":
                meta_set("ext_want", time.time())   # the extension polls this and refreshes within a minute
                return self._send(200, {"ok": True})
            return self._send(200, sync())
        if p == "/api/ingest":
            return self._send(200, ingest(body))
        if p == "/api/settings":
            err = apply_settings(body.get("settings"))
            if err:
                return self._send(200, {"ok": False, "error": err})
            cfg2 = load_cfg()
            if cfg2["mode"] == "ext" and not configured(cfg2):
                return self._send(200, {"ok": True, "count": 0, "waiting": True})
            res = sync() if body.get("sync") else {"ok": True}
            return self._send(200, res)
        if p == "/api/test-email":
            err = send_email([{"kind": "system", "title": "Test email from Duey",
                               "body": "If you can read this, deadline emails are working."}],
                             subject="[Duey] Test email")
            return self._send(200, {"ok": err is None, "error": err})
        if p == "/api/focus":
            iid, secs = body.get("id"), body.get("seconds")
            if not iid or not isinstance(secs, (int, float)) or secs <= 0:
                return self._send(200, {"ok": False, "error": "Nothing to save."})
            secs = min(int(secs), 4 * 3600)  # sanity cap per call
            x("UPDATE items SET focus_seconds = COALESCE(focus_seconds,0) + ? WHERE id=?", (secs, iid))
            x("INSERT INTO focus_log(item_id,ts,seconds) VALUES(?,?,?)", (iid, int(time.time()), secs))
            return self._send(200, {"ok": True})
        if p == "/api/item":
            iid = body.get("id")
            if "done" in body:
                now_ts = int(time.time())
                x("UPDATE items SET done=?, completed_ts=? WHERE id=?",
                  (1 if body["done"] else 0, now_ts if body["done"] else None, iid))
            if "prep_days" in body:
                v = body["prep_days"]
                x("UPDATE items SET prep_override=? WHERE id=?",
                  (None if v is None else max(1, min(21, int(v))), iid))
            return self._send(200, {"ok": True})
        if p == "/api/notifications/read":
            x("UPDATE notifications SET read=1")
            return self._send(200, {"ok": True})
        self._send(404, {"error": "not found"})


def main():
    server = None
    for port in range(DEFAULT_PORT, DEFAULT_PORT + 15):
        try:
            server = ThreadingHTTPServer(("127.0.0.1", port), Handler)
            break
        except OSError:
            continue
    if not server:
        sys.exit("Couldn't find a free port. Close other Duey windows and try again.")
    ensure_ext_code()
    threading.Thread(target=worker, daemon=True).start()
    url = "http://127.0.0.1:%d" % port
    print("Duey is running at %s" % url)
    print("Leave this window open so Duey can keep checking. Press Ctrl+C to stop.")
    try:
        webbrowser.open(url)
    except Exception:
        pass
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        print("\nBye! See you next time.")


if __name__ == "__main__":
    main()
