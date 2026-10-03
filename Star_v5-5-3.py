#!/usr/bin/env python3
"""STAR v5 — Multi-account Roblox auto-rejoin (Termux) + survival/Delta/boost"""
import gc, math, signal, json, os, re, sys, time, random, shlex, shutil, sqlite3, subprocess, tempfile, threading, unicodedata, uuid
from collections import deque

try:
    import requests
except ImportError:
    sys.exit("[!] pip install requests ก่อนนะ")

try:
    import termios, tty, select
    _TSAVE = termios.tcgetattr(sys.stdin.fileno())
    HAS_TTY = True
except Exception:
    termios = tty = select = None
    _TSAVE, HAS_TTY = None, False

def _argval(flag):
    if flag in sys.argv:
        i = sys.argv.index(flag)
        if i + 1 < len(sys.argv): return sys.argv[i + 1]
    return None

ONLY_LABEL = _argval("--only")   # จำกัดให้เฝ้าแค่บัญชีเดียว ใช้ตอนแยกจอ tmux

HERE    = os.path.dirname(os.path.abspath(__file__))
CONFIG  = os.path.join(HERE, "star_config.json")
STATS_F = os.path.join(HERE, "star_stats.json")
STOPF   = os.path.join(HERE, "STOP")
ROOTMAP = os.path.join(HERE, "star_root_map.json")
LOGF    = os.path.join(HERE, "star.log")
VERSION = "5.3.0"
UA      = "Mozilla/5.0 (Linux; Android 13) Termux"

IN_GAME     = 2
RETRY       = 3      # รอบ rejoin ต่อ 1 ชุดก่อนพัก
GRACE_MAX   = 80     # รอเข้าเกมสูงสุดต่อรอบ (วินาที) — เช็กทุก 7 วิ เข้าได้ก็ไปต่อทันที
MISS_NEEDED = 2      # presence หลุดกี่ครั้งติดถึงเริ่ม rejoin (กัน API สะดุด)
LAUNCH_GAP  = 6      # เว้นระยะเปิดแอปแต่ละตัว ไม่ให้เครื่องกระชากพร้อมกัน
COOL_MIN, COOL_MAX = 30, 300
COLORS_ON = not os.environ.get("NO_COLOR") and sys.stdout.isatty()

stop       = threading.Event()
slock      = threading.Lock()
CFG_LOCK   = threading.RLock()
LAUNCH_LOCK = threading.Lock()
LOGQ       = deque(maxlen=120)
STATES     = {}                       # key = account id
TOTALS     = {"rejoins": 0, "hops": 0, "alerts": 0}
SESSION    = {"t0": time.time()}
DASH       = {"on": False}
ROOT       = {"ok": None}
_notified  = {}
_base_up   = [0]

class Stopped(Exception): pass

# ════════════════════════════════════════════════════════════════
#  UI primitives
# ════════════════════════════════════════════════════════════════
RED_B, BLUE_L, GREEN_H = "38;2;255;75;75", "38;2;118;168;255", "38;2;80;220;110"
CYAN_S, GRAY_D = "38;2;90;220;220", "38;2;128;136;148"
GREEN, YELLOW, RED, GRAY = "92", "93", "91", "90"
CYAN, MAGENTA, BLUE = "96", "95", "94"
PALETTE = [CYAN, MAGENTA, GREEN, YELLOW, BLUE, RED]
ANSI = re.compile(r"\033\[[0-9;?]*[A-Za-z]")

def ac(t, code): return f"\033[{code}m{t}\033[0m" if COLORS_ON else str(t)
def _cw(ch): return 0 if unicodedata.category(ch) in ("Mn", "Me", "Cf") else 1
def vlen(s): return sum(_cw(c) for c in ANSI.sub("", s))
def pad(s, w): return s + " " * max(0, w - vlen(s))

def clip(s, w):
    """ตัดข้อความล้วน (ไม่มี ANSI) ให้พอดีความกว้างจอ นับสระ/วรรณยุกต์ไทยเป็น 0"""
    out, n = [], 0
    for ch in s:
        c = _cw(ch)
        if n + c > w: break
        out.append(ch); n += c
    return "".join(out)

def t_branch(last=False): return ac("└── " if last else "├── ", GRAY_D)
def t_ind(last=False):    return ac("    " if last else "│   ", GRAY_D)

def cls():
    """เคลียร์จอ + กลับไปบนสุด — ให้ทุกเมนูขึ้นสดใหม่ ไม่ทับกับข้อความ/คำสั่งเก่า"""
    if HAS_TTY and sys.stdout.isatty():
        sys.stdout.write("\033[H\033[2J\033[3J"); sys.stdout.flush()
    else:
        print("\n" * 2)

def sect(name, note="", last=False, width=46):
    dash = "─" * max(2, width - vlen(name) - vlen(note) - 6)
    return (t_branch(last) + ac(name, GREEN_H) + (ac(f" ({note})", "97") if note else "")
            + ac(" " + dash, GRAY_D))

def sym_line(sym, msg, color=BLUE_L): return f"{ac(sym, color)} {ac(msg, color)}"

SYM = {"ok": ("[+]", BLUE_L), "err": ("[x]", RED), "warn": ("[!]", YELLOW),
       "info": ("[*]", BLUE_L), "dim": ("[·]", GRAY)}
ST_COLOR = {"WATCH": GREEN, "REJOIN": YELLOW, "HOP": MAGENTA, "COOLDOWN": RED,
            "DEAD": RED, "NET": YELLOW, "INIT": GRAY, "OFF": GRAY}
ST_ICON  = {"WATCH": "●", "REJOIN": "◐", "HOP": "⇄", "COOLDOWN": "◌",
            "DEAD": "✖", "NET": "⚠", "INIT": "○", "OFF": "–"}

def inp(prompt="[?] "):
    if HAS_TTY and _TSAVE is not None:
        try: termios.tcsetattr(sys.stdin.fileno(), termios.TCSADRAIN, _TSAVE)
        except Exception: pass
    return input(prompt)

def flog(line):
    try:
        if os.path.exists(LOGF) and os.path.getsize(LOGF) > 1_000_000:
            os.replace(LOGF, LOGF + ".1")
        with open(LOGF, "a", encoding="utf-8") as f: f.write(line + "\n")
    except Exception: pass

def dlog(tag, msg, level="info"):
    ts = time.strftime("%H:%M:%S")
    LOGQ.append((ts, level, tag, msg))
    flog(f"{ts} {level:<4} {tag} {msg}")
    if not DASH["on"]:
        sym, col = SYM.get(level, SYM["info"])
        with slock:
            print(f"{ac(ts, GRAY_D)} {ac(sym, col)} {ac(tag, CYAN)} {msg}", flush=True)

# ════════════════════════════════════════════════════════════════
#  config / stats (เขียนแบบ atomic + มี .bak — config ไม่พังกลางคัน)
# ════════════════════════════════════════════════════════════════
DEFAULT = {"version": 2, "accounts": [], "apps": [], "webhook": "",
           "report_min": 60, "poll": 20, "restart_min": 0,
           "delta_dir": "", "trim_min": 10, "wake": True,
           "grid_locked": False, "grid_layout": {},
           "web": {"on": False, "port": 8787, "password": "", "tunnel": False}}

def _norm(c):
    base = json.loads(json.dumps(DEFAULT)); base.update(c if isinstance(c, dict) else {})
    for a in base["accounts"]:
        a.setdefault("id", uuid.uuid4().hex[:8]); a.setdefault("hop", False)
        a.setdefault("enabled", True); a.setdefault("place_id", None); a.setdefault("app_num", None)
        a.pop("_cfg", None); a.pop("_uid", None)
    return base

def load_cfg():
    for p in (CONFIG, CONFIG + ".bak"):
        try:
            with open(p, encoding="utf-8") as f: return _norm(json.load(f))
        except Exception: continue
    return _norm({})

def _atomic_write(path, text, mode=0o600):
    tmp = path + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f: f.write(text)
    try: os.chmod(tmp, mode)
    except Exception: pass
    os.replace(tmp, path)

def save_cfg(c):
    with CFG_LOCK:
        data = json.dumps(c, indent=2, ensure_ascii=False)     # dump ก่อน — พลาดก็ไม่แตะไฟล์เดิม
        if os.path.exists(CONFIG):
            try:
                shutil.copyfile(CONFIG, CONFIG + ".bak"); os.chmod(CONFIG + ".bak", 0o600)
            except Exception: pass
        _atomic_write(CONFIG, data)

def load_totals():
    try:
        with open(STATS_F) as f: d = json.load(f)
        for k in TOTALS: TOTALS[k] = int(d.get(k, 0))
        _base_up[0] = int(d.get("uptime_sec", 0))
    except Exception: pass

def save_totals():
    try:
        d = dict(TOTALS); d["uptime_sec"] = _base_up[0] + int(time.time() - SESSION["t0"])
        _atomic_write(STATS_F, json.dumps(d, indent=2), 0o644)
    except Exception: pass

# ════════════════════════════════════════════════════════════════
#  HTTP / Roblox API  (1 Session ต่อบัญชี · จัดการ CSRF อัตโนมัติ)
# ════════════════════════════════════════════════════════════════
class Resp:
    __slots__ = ("status", "data", "resp")
    def __init__(self, status, data=None, resp=None): self.status, self.data, self.resp = status, data, resp

class Http:
    def __init__(self, cookie=None):
        self.s = requests.Session()
        self.s.headers.update({"User-Agent": UA, "Accept": "application/json"})
        self.csrf = None
        if cookie: self.s.cookies.set(".ROBLOSECURITY", cookie, domain=".roblox.com")

    def req(self, method, url, **kw):
        kw.setdefault("timeout", (6, 12))
        for _ in range(2):
            hdr = {"X-CSRF-TOKEN": self.csrf} if self.csrf else {}
            try:
                r = self.s.request(method, url, headers=hdr, **kw)
            except Exception:
                return Resp(-1)                                   # เน็ต/timeout
            tok = r.headers.get("x-csrf-token")
            if r.status_code == 403 and tok and tok != self.csrf:
                self.csrf = tok; continue
            try: data = r.json()
            except Exception: data = None
            return Resp(r.status_code, data, r)
        return Resp(403)

    def cookie(self):
        for c in self.s.cookies:
            if c.name == ".ROBLOSECURITY" and c.value: return c.value
        return None

def whoami(cookie):
    r = Http(cookie).req("GET", "https://users.roblox.com/v1/users/authenticated")
    return r.data if r.status == 200 and isinstance(r.data, dict) and r.data.get("id") else None

def presence_of(http, uid):
    """คืน (kind, data): ok | net | auth | rate | err — แยกชัดว่า 'หลุดเกม' ต่างจาก 'API/เน็ตมีปัญหา'"""
    r = http.req("POST", "https://presence.roblox.com/v1/presence/users", json={"userIds": [uid]})
    if r.status == -1:  return "net", None
    if r.status == 401: return "auth", None
    if r.status == 429: return "rate", None
    if r.status == 200 and isinstance(r.data, dict):
        lst = r.data.get("userPresences") or []
        return "ok", (lst[0] if lst else {})
    return "err", None

def uid_by_username(name):
    r = Http().req("POST", "https://users.roblox.com/v1/usernames/users",
                   json={"usernames": [name], "excludeBannedUsers": False})
    d = (r.data or {}).get("data", []) if isinstance(r.data, dict) else []
    return d[0]["id"] if d else None

def pick_server(universe_id, exclude=None):
    if not universe_id: return None
    r = Http().req("GET", f"https://games.roblox.com/v1/games/{universe_id}/servers/Public",
                   params={"limit": 25, "sortOrder": "Asc"})
    if r.status != 200 or not isinstance(r.data, dict): return None
    room = [d for d in r.data.get("data", [])
            if d.get("playing", 999) < d.get("maxPlayers", 0) and d.get("id") != exclude]
    return random.choice(room[:5])["id"] if room else None

def logout_session(cookie):
    h = Http(cookie)
    r = h.req("POST", "https://auth.roblox.com/v2/logout")
    if r.status == 404: r = h.req("POST", "https://auth.roblox.com/v1/logout")
    return r.status in (200, 204), r.status

# ---------- Quick Login (ช่องทางทางการของ Roblox — ไม่ต้องใช้รหัสผ่าน ไม่ติด captcha) ----------
QL = "https://apis.roblox.com/auth-token-service/v1/login"

def quick_login(on_code, on_tick, timeout=300):
    h = Http()
    r = h.req("POST", f"{QL}/create", json={})
    if r.status != 200 or not isinstance(r.data, dict) or "code" not in r.data:
        return None, f"สร้างโค้ดไม่ได้ (HTTP {r.status})"
    code, key = r.data["code"], r.data["privateKey"]
    on_code(code)
    t0 = time.time()
    while time.time() - t0 < timeout:
        time.sleep(3)
        s = h.req("POST", f"{QL}/status", json={"code": code, "privateKey": key})
        st = s.data.get("status") if isinstance(s.data, dict) else None
        on_tick(int(timeout - (time.time() - t0)), st or s.status)
        if st == "Validated": break
        if st in ("Cancelled", "Expired") or s.status in (400, 404):
            return None, f"โค้ดถูกยกเลิก/หมดอายุ ({st or s.status})"
    else:
        return None, "หมดเวลา"
    r = h.req("POST", "https://auth.roblox.com/v2/login",
              json={"ctype": "AuthToken", "cvalue": code, "password": key})
    ck = h.cookie()
    if r.status == 200 and ck: return ck, None
    return None, f"แลก cookie ไม่ได้ (HTTP {r.status}) — ใช้ [2] วาง cookie แทน"

# ---------- cookie parsing ----------
def extract_cookie(text):
    m = re.search(r"_\|WARNING:-DO-NOT-SHARE-THIS[^\"'\s;]+", text or "")
    return m.group(0) if m else None

def parse_cookie_text(text):
    out = []
    for ln in text.splitlines():
        ln = ln.strip().strip(",")
        ck = extract_cookie(ln)
        if not ck: continue
        out.append(((ln.replace(ck, "").strip().strip("|:").strip()) or None, ck))
    return out

def parse_cookie_file(path):
    try:
        text = open(path, encoding="utf-8", errors="ignore").read()
    except Exception:
        return []
    pairs = []
    try:
        data = json.loads(text)
        if isinstance(data, dict):
            for k, v in data.items():
                ck = extract_cookie(v) if isinstance(v, str) else None
                if ck: pairs.append((k, ck))
        elif isinstance(data, list):
            for it in data:
                if isinstance(it, str):
                    ck = extract_cookie(it)
                    if ck: pairs.append((None, ck))
                elif isinstance(it, dict):
                    ck = extract_cookie(str(it.get("cookie", "")))
                    if ck: pairs.append((it.get("label"), ck))
        if pairs: return pairs
    except Exception: pass
    return parse_cookie_text(text)

def add_account(cfg, label, cookie, app_num=None):
    """คืน (me, is_new) — ถ้ามี user นี้อยู่แล้วจะอัปเดต cookie แทนการเพิ่มซ้ำ"""
    me = whoami(cookie)
    if not me: return None, False
    with CFG_LOCK:
        for a in cfg["accounts"]:
            if a.get("user_id") == me["id"]:
                a["cookie"] = cookie
                if app_num: a["app_num"] = app_num
                return me, False
        label = (label or "").strip() or me["name"]
        if any(a.get("label") == label for a in cfg["accounts"]):
            label = f"{label}#{len(cfg['accounts']) + 1}"
        cfg["accounts"].append({"id": uuid.uuid4().hex[:8], "label": label, "cookie": cookie,
                                "user_id": me["id"], "place_id": None, "app_num": app_num,
                                "hop": False, "enabled": True})
    return me, True

# ════════════════════════════════════════════════════════════════
#  Android: sh / root / launch
# ════════════════════════════════════════════════════════════════
class _R: returncode = 1; stdout = b""; stderr = b""

def su(cmd, timeout=120):
    try:
        return subprocess.run(["su", "-c", cmd], capture_output=True, stdin=subprocess.DEVNULL, timeout=timeout)
    except Exception:
        return _R()

def su_text(cmd, timeout=120): return (su(cmd, timeout).stdout or b"").decode(errors="ignore")

def has_root():
    if ROOT["ok"] is None:
        ROOT["ok"] = "uid=0" in su_text("id", timeout=10)
    return ROOT["ok"]

def sh(args, timeout=20, root=False):
    try:
        if root: args = ["su", "-c", shlex.join(args)]
        r = subprocess.run(args, capture_output=True, text=True, stdin=subprocess.DEVNULL, timeout=timeout)
        return r.returncode, (r.stdout or "") + (r.stderr or "")
    except subprocess.TimeoutExpired: return 124, "timeout"
    except Exception as e: return 127, str(e)

def pm_candidates():
    rc, out = sh(["pm", "list", "packages"])
    return sorted(p.replace("package:", "").strip() for p in out.splitlines() if "roblox" in p.lower())

def launch_game(app, place_id, job_id=None):
    """เปิดเกมผ่าน deep link — ล็อกคิวเว้นระยะ ไม่ให้หลายแอปเปิดพร้อมกันจนเครื่องค้าง"""
    suffix = f"&gameInstanceId={job_id}" if job_id else ""
    uris = [f"roblox://experiences/start?placeId={place_id}{suffix}",
            f"roblox://placeID={place_id}{suffix}",
            f"https://www.roblox.com/games/start?placeId={place_id}{suffix}"]
    pkg = (app or {}).get("package")
    root = has_root()
    ok = False
    with LAUNCH_LOCK:
        for uri in uris:
            for pk in ([pkg] if pkg else []) + [None]:
                args = ["am", "start", "-a", "android.intent.action.VIEW", "-d", uri]
                if pk: args += ["-p", pk]
                if root: args += ["--user", "0"]
                rc, out = sh(args, timeout=20, root=root)
                if rc == 0 and "error" not in out.lower():
                    ok = True; break
            if ok: break
        stop.wait(LAUNCH_GAP)
    return ok

def force_stop(pkg):
    if pkg:
        sh(["am", "force-stop", pkg], timeout=10, root=has_root())
        stop.wait(1.5)

def pid_alive(pkg):
    """root เท่านั้น: แอปยังรันอยู่ไหม — True เมื่อไม่แน่ใจ (กัน kill ผิดตัว)"""
    rc, out = sh(["sh", "-c", f"pidof {pkg} || ps -A -o PID,NAME | grep -w -F {pkg}"], timeout=10, root=True)
    if re.search(r"\d+", out): return True
    return not (rc in (0, 1) and not out.strip())

# ════════════════════════════════════════════════════════════════
#  แจ้งเตือน / รายงาน
# ════════════════════════════════════════════════════════════════
def fmt_up(sec):
    sec = int(sec)
    return f"{sec // 60}m{sec % 60:02d}s" if sec < 3600 else f"{sec // 3600}h{(sec % 3600) // 60:02d}m"

def _post_hook(url, payload):
    def _p():
        try: requests.post(url, json=payload, timeout=10)
        except Exception: pass
    threading.Thread(target=_p, daemon=True).start()

def _iso(): return time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())

def notify(cfg, key, title, desc, color=0xf1c40f, cooldown=60):
    now = time.time()
    with slock:
        if key and now - _notified.get(key, 0) < cooldown: return
        _notified[key] = now
        TOTALS["alerts"] += 1
    url = (cfg.get("webhook") or "").strip()
    if url:
        _post_hook(url, {"embeds": [{"title": title, "description": desc, "color": color, "timestamp": _iso()}]})
    if shutil.which("termux-notification"):
        threading.Thread(target=lambda: sh(["termux-notification", "-t", "STAR", "-c", f"{title}: {desc}"], 5),
                         daemon=True).start()

def send_report(cfg, reason="รายงานประจำ"):
    url = (cfg.get("webhook") or "").strip()
    if not url or not cfg["accounts"]: return
    fields, states = [], []
    for a in cfg["accounts"]:
        st = STATES.get(a["id"], {})
        s = st.get("state", "OFF" if not a.get("enabled", True) else "INIT")
        states.append(s)
        up = time.time() - st.get("start", time.time())
        stab = (st.get("in_ts", 0) / up * 100) if up > 5 else 0
        app = st.get("app")
        fields.append({"name": a.get("label", "?"), "inline": False,
                       "value": f"{s} · {'แอป #%s' % app['num'] if app else 'ไม่ผูกแอป'} · place {st.get('place', '-')} · "
                                f"rejoin {st.get('rejoins', 0)} · hop {st.get('hops', 0)} · นิ่ง {stab:.0f}% · up {fmt_up(up)}"})
    bad = any(s in ("DEAD", "COOLDOWN") for s in states)
    mid = any(s in ("REJOIN", "HOP", "NET") for s in states)
    _post_hook(url, {"embeds": [{"title": f"STAR · {reason}", "fields": fields,
                                 "description": f"rejoin {TOTALS['rejoins']} · hop {TOTALS['hops']} · alert {TOTALS['alerts']}",
                                 "color": 0xe74c3c if bad else (0xf1c40f if mid else 0x2ecc71),
                                 "footer": {"text": f"STAR v{VERSION}"}, "timestamp": _iso()}]})

# ════════════════════════════════════════════════════════════════
#  WORKER — หัวใจ: เฝ้า + rejoin แบบไม่ยอมตาย
# ════════════════════════════════════════════════════════════════
class Worker(threading.Thread):
    def __init__(self, acc, cfg, idx, color):
        super().__init__(daemon=True, name=f"w-{acc.get('label')}")
        self.acc, self.cfg, self.idx = acc, cfg, idx
        self.tag = acc.get("label", "acct")
        self.http = Http(acc["cookie"])
        self.uid = self.job = self.universe = None
        self.kick = threading.Event()
        self.app = next((a for a in cfg["apps"] if a.get("num") == acc.get("app_num")), None)
        self.launched_at = time.time()
        self.last_save = 0
        with slock:
            self.st = STATES[acc["id"]] = {
                "state": "INIT", "note": "", "color": color, "app": self.app,
                "place": acc.get("place_id") or "-", "rejoins": 0, "hops": 0,
                "in_ts": 0.0, "start": time.time()}

    # ---- helpers ----
    def set(self, **kw):
        with slock: self.st.update(kw)

    def nap(self, sec, kickable=False):
        end = time.time() + sec
        while True:
            if stop.is_set(): raise Stopped()
            left = end - time.time()
            if left <= 0 or (kickable and self.kick.is_set()): return
            stop.wait(min(left, 0.5))

    def presence(self): return presence_of(self.http, self.uid)
    def pkg(self): return (self.app or {}).get("package")

    def identify(self):
        n = 0
        while True:
            r = self.http.req("GET", "https://users.roblox.com/v1/users/authenticated")
            if r.status == 200 and isinstance(r.data, dict) and r.data.get("id"):
                self.uid = r.data["id"]
                if n: dlog(self.tag, "ต่อ session กลับมาแล้ว", "ok")
                return
            if r.status == 401:
                self.set(state="DEAD", note="cookie ตาย — ใส่ใหม่ที่ [4]")
                if n == 0:
                    dlog(self.tag, "cookie ตาย (รอลองซ้ำทุก 5 นาที)", "err")
                    notify(self.cfg, f"dead:{self.tag}", f"{self.tag}: cookie หมดอายุ", "ใส่ cookie ใหม่", 0xe74c3c, 600)
                n += 1; self.nap(300)
            else:
                self.set(state="NET", note="ต่อเน็ตไม่ได้")
                n += 1; self.nap(min(10 + n * 5, 60))

    def wait_net(self):
        n = 0
        while True:
            kind, _ = self.presence()
            if kind != "net": return
            n += 1
            self.set(state="NET", note="ไม่มีเน็ต — รอ...")
            self.nap(min(5 * n, 30))

    def wait_in_game(self, max_wait):
        end = time.time() + max_wait
        self.nap(10)
        while time.time() < end:
            kind, p = self.presence()
            if kind == "ok" and p.get("userPresenceType") == IN_GAME: return p
            self.nap(15 if kind == "rate" else 7)
        return None

    def joined(self, p, place, rounds, hop=False):
        pl = p.get("rootPlaceId") or p.get("placeId") or place
        self.job, self.universe = p.get("gameId"), p.get("universeId") or self.universe
        self.launched_at = time.time()
        with slock:
            TOTALS["rejoins"] += 1
            self.st.update(state="WATCH", note="", place=pl, rejoins=self.st.get("rejoins", 0) + 1)
        dlog(self.tag, "hop สำเร็จ" if hop else "กลับเข้าเกมแล้ว", "ok")
        if rounds: notify(self.cfg, f"back:{self.tag}", f"{self.tag}: กลับมาแล้ว", f"หลังพัก {rounds} รอบ", 0x2ecc71, 30)
        return True

    # ---- กู้เกม: ไต่ระดับ soft → kill+fresh → hop → พัก แล้ววนใหม่ ไม่เลิก ----
    def recover(self, reason):
        place = self.acc.get("place_id")
        if not place: return False
        dlog(self.tag, f"{reason} → rejoin", "warn")
        cool, rounds = COOL_MIN, 0
        forced = reason in ("แอปตาย", "รีเฟรชตามรอบ", "สั่งมือ")   # presence ยังค้าง IN_GAME ได้ → ห้ามเชื่อ
        def alive(p):   # root: ต้องเห็นโปรเซสแอปจริงด้วย ไม่งั้น presence ค้างหลอก
            return not (forced and self.pkg() and has_root() and not pid_alive(self.pkg()))
        while True:
            for n in range(1, RETRY + 1):
                self.wait_net()
                kind, p = self.presence()
                if kind == "ok" and p.get("userPresenceType") == IN_GAME and not (forced and rounds == 0 and n == 1):
                    return self.joined(p, place, rounds)          # กลับเองแล้ว / มีคนเข้าให้
                self.set(state="REJOIN", note=f"{reason} · ลอง {n}/{RETRY}")
                if n >= 2 or reason in ("แอปตาย", "รีเฟรชตามรอบ", "สั่งมือ"):
                    force_stop(self.pkg())
                job = self.job if (n == 1 and reason != "รีเฟรชตามรอบ") else None
                if not launch_game(self.app, place, job):
                    dlog(self.tag, "am start ไม่ติด", "warn")
                p = self.wait_in_game(GRACE_MAX)
                if p and alive(p): return self.joined(p, place, rounds)
                dlog(self.tag, f"ยังไม่เข้า ({n}/{RETRY})", "warn")
            if self.acc.get("hop") and self.universe:
                srv = pick_server(self.universe, self.job)
                if srv:
                    with slock:
                        TOTALS["hops"] += 1; self.st["hops"] = self.st.get("hops", 0) + 1
                    self.set(state="HOP", note="สลับเซิร์ฟเวอร์")
                    notify(self.cfg, f"hop:{self.tag}", f"{self.tag}: hop เซิร์ฟใหม่", f"place {place}", 0x3498db)
                    force_stop(self.pkg()); launch_game(self.app, place, srv)
                    p = self.wait_in_game(GRACE_MAX)
                    if p and alive(p): return self.joined(p, place, rounds, hop=True)
            rounds += 1
            self.set(state="COOLDOWN", note=f"พัก {cool}s แล้วลองใหม่")
            dlog(self.tag, f"rejoin ไม่สำเร็จ — พัก {cool}s (รอบที่ {rounds})", "err")
            notify(self.cfg, f"cool:{self.tag}", f"{self.tag}: rejoin ไม่สำเร็จ", f"พัก {cool}s แล้วลองต่อ", 0xe74c3c, 300)
            self.nap(cool)
            cool = min(cool * 2, COOL_MAX)

    # ---- ลูปเฝ้า ----
    def loop(self):
        acc = self.acc
        self.set(state="WATCH", note="")
        dlog(self.tag, f"เฝ้าดู (uid {self.uid})", "info")
        misses, dead_pid, last = MISS_NEEDED - 1, 0, time.time()   # ไม่อยู่ในเกมตั้งแต่เริ่ม → rejoin ทันที
        while True:
            if os.path.exists(STOPF):
                dlog(self.tag, "เจอไฟล์ STOP — หยุด", "warn"); stop.set(); raise Stopped()
            poll = max(10, int(self.cfg.get("poll", 20)))
            if self.kick.is_set():
                self.kick.clear(); self.recover("สั่งมือ"); last = time.time(); continue
            kind, p = self.presence()
            now = time.time(); dt = min(now - last, poll * 3); last = now
            if kind == "net":
                self.set(state="NET", note="ไม่มีเน็ต"); self.nap(15, True); continue
            if kind == "auth":
                self.identify(); continue
            if kind == "rate":
                self.nap(45, True); continue
            if kind != "ok":
                self.nap(poll, True); continue

            if p.get("userPresenceType") == IN_GAME:
                misses = 0
                place = p.get("rootPlaceId") or p.get("placeId") or acc.get("place_id")
                self.job = p.get("gameId") or self.job
                self.universe = p.get("universeId") or self.universe
                with slock:
                    self.st["in_ts"] = self.st.get("in_ts", 0) + dt
                    self.st.update(state="WATCH", note="", place=place or "-")
                if place and place != acc.get("place_id"):
                    with CFG_LOCK: acc["place_id"] = place
                    if now - self.last_save > 60:
                        self.last_save = now
                        try: save_cfg(self.cfg)
                        except Exception: pass
                if self.pkg() and has_root():
                    dead_pid = 0 if pid_alive(self.pkg()) else dead_pid + 1
                    if dead_pid >= 2:
                        dead_pid = 0; self.recover("แอปตาย"); last = time.time(); continue
                rm = int(self.cfg.get("restart_min", 0) or 0)
                if rm and self.pkg() and now - self.launched_at > rm * 60:
                    self.recover("รีเฟรชตามรอบ"); last = time.time(); continue
            elif not acc.get("place_id"):
                self.set(note="ยังไม่มีแมพ — ตั้งที่ [4]")
            else:
                misses += 1
                self.set(note=f"ไม่อยู่ในเกม {misses}/{MISS_NEEDED}")
                if misses >= MISS_NEEDED:
                    misses = 0; self.recover("หลุดเกม"); last = time.time(); continue
            self.nap(poll + random.uniform(0, 4), True)

    def run(self):
        try:
            self.nap(self.idx * 4)
            while True:
                try:
                    self.identify()
                    self.loop()
                except Stopped: raise
                except Exception as e:                      # ห้ามตาย: พลาดอะไรก็เริ่มลูปใหม่
                    dlog(self.tag, f"error {type(e).__name__}: {e} — รีสตาร์ท worker", "err")
                    self.nap(10)
        except Stopped:
            pass

# ════════════════════════════════════════════════════════════════
#  DASHBOARD  (alt-screen · วาดทับตำแหน่งเดิม · วาดเฉพาะเมื่อเฟรมเปลี่ยน → ไม่กะพริบไม่หน่วง)
# ════════════════════════════════════════════════════════════════
def _acc_rows(cfg):
    rows, now = [], time.time()
    for a in cfg["accounts"]:
        st = STATES.get(a["id"], {})
        state = st.get("state", "OFF" if not a.get("enabled", True) else "INIT")
        up = now - st.get("start", now)
        stab = (st.get("in_ts", 0) / up * 100) if up > 5 and state != "DEAD" else 0
        app = st.get("app")
        rows.append({"label": a.get("label", "?"), "state": state, "col": st.get("color", CYAN),
                     "app": f"#{app['num']}" if app else "-", "place": str(st.get("place", "-")),
                     "rj": st.get("rejoins", 0), "hp": st.get("hops", 0), "stab": stab,
                     "up": fmt_up(up) if st else "-", "note": st.get("note", "")})
    return rows

def build_frame(cfg, w, h):
    rows = _acc_rows(cfg)
    n = len(rows)
    L = [ac(" ★ STAR", RED_B) + ac(f" v{VERSION}", GREEN) + f"  {time.strftime('%H:%M:%S')}"
         + ac(f"  up {fmt_up(time.time() - SESSION['t0'])}  root {'✔' if ROOT['ok'] else '–'}", GRAY_D)]
    full = [("Account", 12), ("Status", 10), ("App", 5), ("Place", 11), ("RJ", 4), ("HP", 3), ("Stab", 5), ("Up", 7)]
    cols = None
    if w >= 72 and h - (7 + n) >= 4:
        cols = list(full)
        if w >= 96:
            used = sum(c[1] for c in cols) + 3 * (len(cols) + 1) + 1
            cols.append(("Note", max(8, w - used)))
    if cols:
        ws = [c[1] for c in cols]
        L.append("┌" + "┬".join("─" * (x + 2) for x in ws) + "┐")
        L.append("│ " + " │ ".join(pad(ac(c[0], GRAY), c[1]) for c in cols) + " │")
        L.append("├" + "┼".join("─" * (x + 2) for x in ws) + "┤")
        for r in rows:
            cells = [ac(clip(r["label"], 12), r["col"]),
                     ac(f"{ST_ICON.get(r['state'], '?')} {r['state']}", ST_COLOR.get(r["state"], GRAY)),
                     r["app"], clip(r["place"], 11), str(r["rj"]), str(r["hp"]), f"{r['stab']:.0f}%", r["up"]]
            if len(cols) == 9: cells.append(ac(clip(r["note"], ws[8]), GRAY_D))
            L.append("│ " + " │ ".join(pad(c, x) for c, x in zip(cells, ws)) + " │")
        L.append("└" + "┴".join("─" * (x + 2) for x in ws) + "┘")
    else:
        room = max(1, h - 6)
        for r in rows[:room]:
            s = (f"{ac(ST_ICON.get(r['state'], '?'), ST_COLOR.get(r['state'], GRAY))} "
                 f"{ac(clip(r['label'], 10), r['col'])} {r['state'][:4]} "
                 f"rj{r['rj']} hp{r['hp']} {r['stab']:.0f}% {clip(r['note'], max(0, w - 34))}")
            L.append(s)
        if n > room: L.append(ac(f"  +{n - room} บัญชี", GRAY_D))
    k = max(0, h - 1 - len(L) - 2)
    if k:
        L.append(ac("─ Log ", GREEN_H) + ac("─" * max(0, w - 6), GRAY_D))
        for ts, lv, tag, msg in list(LOGQ)[-k:]:
            sym, col = SYM.get(lv, SYM["info"])
            body = clip(f"{tag} {msg}", max(0, w - 15))
            L.append(f"{ac(ts, GRAY_D)} {ac(sym, col)} {body}")
    watching = sum(1 for s in STATES.values() if s.get("state") == "WATCH")
    L.append(ac(f" {TOTALS['rejoins']} rejoin · {TOTALS['hops']} hop · {TOTALS['alerts']} alert · "
                f"{watching}/{n} ในเกม", GREEN_H) + ac("   q หยุด · f บังคับ rejoin", GRAY_D))
    return L[:max(1, h - 1)]

def run_dashboard(cfg, workers):
    use_tty = HAS_TTY and sys.stdout.isatty() and not WEB["headless"]
    DASH["on"] = use_tty or WEB["headless"]
    fd = sys.stdin.fileno() if HAS_TTY else None
    last, last_size, last_paint, last_report = "", None, 0.0, time.time()
    if use_tty:
        sys.stdout.write("\033[?1049h\033[?25l\033[2J"); sys.stdout.flush()
        tty.setcbreak(fd)
    try:
        while not stop.is_set() and any(wk.is_alive() for wk in workers):
            if os.path.exists(STOPF): stop.set(); break
            if use_tty:
                r, _, _ = select.select([fd], [], [], 0.25)
                if r:
                    ch = os.read(fd, 1).decode(errors="ignore").lower()
                    if ch == "q": stop.set(); break
                    if ch == "f":
                        for wk in workers: wk.kick.set()
                        dlog("STAR", "สั่ง rejoin ทุกบัญชี", "warn")
            else:
                stop.wait(1)
            now = time.time()
            if now - last_paint >= 1.0:
                last_paint = now
                sz = shutil.get_terminal_size((100, 30))
                frame = "\033[H" + "".join(l + "\033[K\n" for l in build_frame(cfg, sz.columns, sz.lines)) + "\033[J"
                if use_tty and (frame != last or sz != last_size):
                    if sz != last_size: sys.stdout.write("\033[2J")
                    sys.stdout.write(frame); sys.stdout.flush()
                    last, last_size = frame, sz
            rm = int(cfg.get("report_min", 60) or 0)
            if rm and now - last_report >= rm * 60:
                last_report = now; send_report(cfg)
    finally:
        DASH["on"] = False
        if use_tty:
            try: termios.tcsetattr(fd, termios.TCSADRAIN, _TSAVE)
            except Exception: pass
            sys.stdout.write("\033[?25h\033[?1049l"); sys.stdout.flush()

def _start_session(cfg):
    accs = [a for a in cfg["accounts"] if a.get("enabled", True) and a.get("cookie")]
    if ONLY_LABEL:
        accs = [a for a in accs if a.get("label") == ONLY_LABEL]
    if not accs:
        print(sym_line("[x]", "ไม่มีบัญชีที่เปิดเฝ้า — เพิ่มที่ [1]/[2] หรือเปิดที่ [4]", RED)); return
    if any(a.get("app_num") for a in accs):
        print(sym_line("[*]", "เช็ก root..."))
        print(sym_line("[+]" if has_root() else "[·]",
                       "root พร้อม — ตรวจแอปตาย/force-stop ได้" if has_root() else "ไม่มี root — เฝ้าด้วย presence + deep link",
                       GREEN if has_root() else GRAY))
    for a in accs:
        if not a.get("place_id"):
            print(sym_line("[!]", f"{a['label']}: ยังไม่มีแมพ (จะเฝ้าอย่างเดียวจนกว่าจะเข้าเกมเอง)", YELLOW))
    if os.path.exists(STOPF): os.remove(STOPF)
    stop.clear(); STATES.clear(); _notified.clear()
    SESSION["t0"] = time.time()
    if cfg.get("wake", True): wake_lock(True)
    Maint(cfg).start()
    workers = [Worker(a, cfg, i, PALETTE[i % len(PALETTE)]) for i, a in enumerate(accs)]
    for wk in workers: wk.start()
    WORKERS[:] = workers
    try:
        run_dashboard(cfg, workers)
    except KeyboardInterrupt:
        pass
    stop.set()
    for wk in workers: wk.join(timeout=3)
    try: save_cfg(cfg)
    except Exception: pass
    save_totals()
    print(t_branch(True) + ac(f"จบเซสชัน · {TOTALS['rejoins']} rejoins, {TOTALS['hops']} hops, "
                              f"{TOTALS['alerts']} alerts", GREEN_H))
    stop.clear()

def start_session(cfg):
    if WEB["running"]:
        print(sym_line("[!]", "มี session รันอยู่แล้ว (สั่งจากเว็บ) — หยุดที่หน้าเว็บก่อน", YELLOW)); return
    WEB["running"] = True
    try: _start_session(cfg)
    finally: WEB["running"] = False; WORKERS.clear()

# ════════════════════════════════════════════════════════════════
#  REMOTE WEB — หน้าเว็บคุมเครื่องจากมือถือ/ไอแพด (stdlib ล้วน ไม่ต้องลงอะไรเพิ่ม)
#  ดูจอสด · สถานะรายบัญชี · Start/Stop · Rejoin · เพิ่ม cookie · Reboot
# ════════════════════════════════════════════════════════════════
import base64, hashlib, getpass, hmac, io, atexit, secrets, socket, string, urllib.parse
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

WEB_DEF = {"on": False, "port": 8787, "password": "", "tunnel": False, "hub": False, "key": "",
           "agent": {"on": False, "url": "", "key": "", "name": "", "id": ""}}
WEB     = {"server": None, "cfg": None, "headless": False, "running": False,
           "url": "", "tproc": None}
WORKERS = []
SHOT    = {"t": 0.0, "data": b"", "mime": "image/jpeg", "lock": threading.Lock()}
WEB_FAILS = {}

def web_cfg(cfg):
    w = cfg.setdefault("web", {})
    for k, v in WEB_DEF.items(): w.setdefault(k, dict(v) if isinstance(v, dict) else v)
    for k, v in WEB_DEF["agent"].items(): w["agent"].setdefault(k, v)
    return w

def lan_ip():
    try:
        s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        s.connect(("8.8.8.8", 80)); ip = s.getsockname()[0]; s.close(); return ip
    except Exception:
        return "127.0.0.1"

def web_shot(max_age=2.5):
    """จับภาพทั้งจอด้วย screencap (ต้อง root) · แคชไว้ ไม่ให้หลายคนเปิดพร้อมกันแล้วเครื่องหน่วง"""
    with SHOT["lock"]:
        if SHOT["data"] and time.time() - SHOT["t"] < max_age:
            return SHOT["data"], SHOT["mime"]
        if not has_root(): return None, ""
        raw = b""
        for cmd in ("screencap -j", "screencap -p"):
            d = su(cmd, timeout=15).stdout or b""
            if d[:2] == b"\xff\xd8" or d[:4] == b"\x89PNG": raw = d; break
        if not raw: return None, ""
        data, mime = raw, ("image/jpeg" if raw[:2] == b"\xff\xd8" else "image/png")
        try:                                            # มี Pillow → ย่อภาพให้เบา (ไม่มีก็ส่งตามเดิม)
            from PIL import Image
            im = Image.open(io.BytesIO(raw)).convert("RGB")
            if im.width > 720: im = im.resize((720, max(1, int(im.height * 720 / im.width))))
            b = io.BytesIO(); im.save(b, "JPEG", quality=55)
            data, mime = b.getvalue(), "image/jpeg"
        except Exception: pass
        SHOT.update(t=time.time(), data=data, mime=mime)
        return data, mime

def web_status(cfg):
    with CFG_LOCK:
        accs = list(cfg["accounts"])
    rows = _acc_rows(cfg)
    out = []
    for a, r in zip(accs, rows):
        out.append({"id": a["id"], "label": r["label"], "state": r["state"], "app": r["app"],
                    "place": r["place"], "rj": r["rj"], "hp": r["hp"], "stab": round(r["stab"]),
                    "up": r["up"], "note": r["note"], "enabled": a.get("enabled", True)})
    running = WEB["running"]
    enabled = sum(1 for x in out if x["enabled"])
    watching = sum(1 for x in out if x["state"] == "WATCH") if running else 0
    tot, av = mem_info()
    return {"version": VERSION, "host": socket.gethostname(), "running": running,
            "root": ROOT["ok"], "uptime": fmt_up(time.time() - SESSION["t0"]) if running else "-",
            "online": watching, "offline": max(0, enabled - watching) if running else 0,
            "rejoins": TOTALS["rejoins"], "hops": TOTALS["hops"], "alerts": TOTALS["alerts"],
            "ram_free": av, "ram_total": tot, "accounts": out,
            "log": [list(x) for x in list(LOGQ)[-25:]]}

def _web_run_session(cfg):
    WEB["headless"] = True
    try: start_session(cfg)
    except Exception as e: flog(f"web session {e!r}")
    finally: WEB["headless"] = False

def _web_reboot():
    time.sleep(1.5)
    try: save_totals(); save_cfg(WEB["cfg"])
    except Exception: pass
    su("reboot", timeout=10)

def web_action(cfg, d):
    """คืน (ok, ข้อความ)"""
    act = str(d.get("action", ""))
    wid = str(d.get("id", ""))
    if act == "start":
        if WEB["running"]: return False, "กำลังเฝ้าอยู่แล้ว"
        if not any(a.get("enabled", True) and a.get("cookie") for a in cfg["accounts"]):
            return False, "ไม่มีบัญชีที่เปิดเฝ้า"
        threading.Thread(target=_web_run_session, args=(cfg,), daemon=True, name="web-session").start()
        dlog("WEB", "สั่ง START จากเว็บ", "info")
        return True, "เริ่มเฝ้าแล้ว"
    if act == "stop":
        if not WEB["running"]: return False, "ยังไม่ได้เริ่ม"
        stop.set(); dlog("WEB", "สั่ง STOP จากเว็บ", "warn")
        return True, "สั่งหยุดแล้ว"
    if act == "rejoin_all":
        ws = list(WORKERS)
        if not ws: return False, "ยังไม่ได้เริ่มเฝ้า"
        for wk in ws: wk.kick.set()
        dlog("WEB", "สั่ง rejoin ทุกบัญชี", "warn")
        return True, f"สั่ง rejoin {len(ws)} บัญชี"
    if act == "rejoin":
        for wk in list(WORKERS):
            if wk.acc.get("id") == wid:
                wk.kick.set(); dlog("WEB", f"สั่ง rejoin {wk.tag}", "warn")
                return True, f"สั่ง rejoin {wk.tag}"
        return False, "ไม่เจอบัญชีนี้ในเซสชัน"
    if act == "toggle":
        with CFG_LOCK:
            for a in cfg["accounts"]:
                if a.get("id") == wid:
                    a["enabled"] = not a.get("enabled", True)
                    save_cfg(cfg)
                    return True, f"{a.get('label')}: {'เปิด' if a['enabled'] else 'ปิด'}เฝ้า" + (" (มีผลตอน START ใหม่)" if WEB["running"] else "")
        return False, "ไม่เจอบัญชี"
    if act == "add_cookie":
        ck = extract_cookie(str(d.get("cookie", "")))
        if not ck: return False, "ไม่พบ cookie (ต้องขึ้นต้น _|WARNING:-DO-NOT-SHARE-THIS...)"
        an = str(d.get("app_num", "")).strip()
        me, new = add_account(cfg, str(d.get("label", ""))[:24], ck, int(an) if an.isdigit() else None)
        if not me: return False, "cookie ใช้ไม่ได้ (Roblox ไม่ยอมรับ)"
        save_cfg(cfg)
        return True, f"{'เพิ่ม' if new else 'อัปเดต cookie'} {me.get('name')} แล้ว" + (" · START ใหม่เพื่อเฝ้าตัวนี้" if WEB["running"] else "")
    if act == "reboot":
        if d.get("confirm") is not True: return False, "ต้องยืนยันก่อน"
        if not has_root(): return False, "รีบูตต้องมี root"
        threading.Thread(target=_web_reboot, daemon=True).start()
        return True, "กำลังรีบูตเครื่อง..."
    return False, "คำสั่งไม่รู้จัก"

class WebHandler(BaseHTTPRequestHandler):
    timeout = 20
    def log_message(self, *a): pass

    def _send(self, code, body, ctype="application/json; charset=utf-8", extra=None):
        if isinstance(body, str): body = body.encode("utf-8")
        self.send_response(code)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Cache-Control", "no-store")
        self.send_header("X-Content-Type-Options", "nosniff")
        for k, v in (extra or {}).items(): self.send_header(k, v)
        self.end_headers(); self.wfile.write(body)

    def _auth(self):
        pw = web_cfg(WEB["cfg"]).get("password") or ""
        ip, now = self.client_address[0], time.time()
        fails = [t for t in WEB_FAILS.get(ip, []) if now - t < 60]
        if len(fails) >= 10:
            self._send(429, "too many attempts", "text/plain"); return False
        h = self.headers.get("Authorization", "")
        if pw and h.startswith("Basic "):
            try: given = base64.b64decode(h[6:]).decode("utf-8", "ignore").split(":", 1)[-1]
            except Exception: given = ""
            if hmac.compare_digest(given.encode(), pw.encode()): return True
            fails.append(now); WEB_FAILS[ip] = fails; time.sleep(1)
        self._send(401, "login", "text/plain", {"WWW-Authenticate": 'Basic realm="STAR", charset="UTF-8"'})
        return False

    def do_GET(self):
        if not self._auth(): return
        path, cfg = self.path.split("?", 1)[0], WEB["cfg"]
        try:
            w = web_cfg(cfg)
            if path == "/": self._send(200, HUB_HTML if w.get("hub") else WEB_HTML, "text/html; charset=utf-8")
            elif path == "/local": self._send(200, WEB_HTML, "text/html; charset=utf-8")
            elif path == "/api/hub/devices" and w.get("hub"):
                self._send(200, json.dumps({"version": VERSION, "devices": hub_devices(cfg)}, ensure_ascii=False))
            elif path == "/api/hub/shot" and w.get("hub"):
                q = urllib.parse.parse_qs(self.path.split("?", 1)[1] if "?" in self.path else "")
                data, mime = hub_shot((q.get("d") or [""])[0])
                if data: self._send(200, data, mime)
                else: self._send(404, "no screenshot", "text/plain")
            elif path == "/api/status": self._send(200, json.dumps(web_status(cfg), ensure_ascii=False))
            elif path == "/api/shot":
                data, mime = web_shot()
                if data: self._send(200, data, mime)
                else: self._send(404, "no screenshot", "text/plain")
            else: self._send(404, "not found", "text/plain")
        except (BrokenPipeError, ConnectionResetError, socket.timeout): pass
        except Exception as e:
            flog(f"web GET {e!r}")
            try: self._send(500, "error", "text/plain")
            except Exception: pass

    def _fail_key(self, ip):
        now = time.time(); WEB_FAILS[ip] = [t for t in WEB_FAILS.get(ip, []) if now - t < 60] + [now]

    def _hub_report(self):
        cfg = WEB["cfg"]; w = web_cfg(cfg); ip = self.client_address[0]
        try:
            if len([t for t in WEB_FAILS.get(ip, []) if time.time() - t < 60]) >= 10:
                self._send(429, "too many attempts", "text/plain"); return
            given = self.headers.get("X-Hub-Key", "")
            if not (w.get("hub") and w.get("key") and hmac.compare_digest(given.encode(), w["key"].encode())):
                self._fail_key(ip); time.sleep(1); self._send(401, "bad key", "text/plain"); return
            n = int(self.headers.get("Content-Length") or 0)
            if n <= 0 or n > 8_000_000:
                self._send(400, json.dumps({"ok": False})); return
            d = json.loads(self.rfile.read(n).decode("utf-8", "ignore"))
            self._send(200, json.dumps(hub_report(cfg, d if isinstance(d, dict) else {}), ensure_ascii=False))
        except (BrokenPipeError, ConnectionResetError, socket.timeout): pass
        except Exception as e:
            flog(f"hub report {e!r}")
            try: self._send(400, json.dumps({"ok": False}))
            except Exception: pass

    def do_POST(self):
        path = self.path.split("?", 1)[0]
        if path == "/hub/report": return self._hub_report()
        if not self._auth(): return
        try:
            if path not in ("/api/action", "/api/hub/action") or self.headers.get("X-Star") != "1":
                self._send(403, json.dumps({"ok": False, "msg": "forbidden"})); return
            n = int(self.headers.get("Content-Length") or 0)
            if n <= 0 or n > 65536:
                self._send(400, json.dumps({"ok": False, "msg": "bad size"})); return
            d = json.loads(self.rfile.read(n).decode("utf-8", "ignore"))
            d = d if isinstance(d, dict) else {}
            if path == "/api/hub/action":
                if not web_cfg(WEB["cfg"]).get("hub"): self._send(403, json.dumps({"ok": False, "msg": "hub off"})); return
                ok, msg = hub_action(WEB["cfg"], d)
            else:
                ok, msg = web_action(WEB["cfg"], d)
            self._send(200, json.dumps({"ok": ok, "msg": msg}, ensure_ascii=False))
        except (BrokenPipeError, ConnectionResetError, socket.timeout): pass
        except Exception as e:
            flog(f"web POST {e!r}")
            try: self._send(500, json.dumps({"ok": False, "msg": "server error"}))
            except Exception: pass

def web_start(cfg):
    w = web_cfg(cfg)
    if WEB["server"]: return True, ""
    if not w.get("password"): return False, "ยังไม่ได้ตั้งรหัสผ่าน"
    WEB["cfg"] = cfg
    try:
        srv = ThreadingHTTPServer(("0.0.0.0", int(w["port"])), WebHandler)
    except OSError as e:
        return False, f"เปิดพอร์ต {w['port']} ไม่ได้: {e}"
    srv.daemon_threads = True
    threading.Thread(target=srv.serve_forever, daemon=True, name="web").start()
    WEB["server"] = srv
    threading.Thread(target=has_root, daemon=True).start()      # เช็ก root ล่วงหน้า ไม่ให้หน้าเว็บรอ
    if w.get("tunnel"): web_tunnel_start(w["port"])
    return True, ""

def web_stop():
    web_tunnel_stop()
    srv, WEB["server"] = WEB["server"], None
    if srv:
        try: srv.shutdown(); srv.server_close()
        except Exception: pass

def web_tunnel_start(port):
    p = WEB["tproc"]
    if p and p.poll() is None: return True
    exe = shutil.which("cloudflared")
    if not exe: return False
    try:
        p = subprocess.Popen([exe, "tunnel", "--url", f"http://127.0.0.1:{port}", "--no-autoupdate"],
                             stdout=subprocess.PIPE, stderr=subprocess.STDOUT, stdin=subprocess.DEVNULL,
                             text=True, errors="ignore")
    except Exception: return False
    WEB["tproc"], WEB["url"] = p, ""
    def reader():
        for ln in p.stdout:
            m = re.search(r"https://[a-z0-9-]+\.trycloudflare\.com", ln)
            if m: WEB["url"] = m.group(0); flog(f"tunnel {WEB['url']}")
    threading.Thread(target=reader, daemon=True).start()
    return True

def web_tunnel_stop():
    p, WEB["tproc"], WEB["url"] = WEB["tproc"], None, ""
    if p and p.poll() is None:
        try: p.terminate()
        except Exception: pass

atexit.register(web_tunnel_stop)

# ════════ HUB (หน้ากลางรวมทุกเครื่อง) + AGENT (เครื่องลูกส่งข้อมูลเข้าหน้ากลาง) ════════
# เครื่องลูก "ส่งออก" ไปหาหน้ากลางเอง → ไม่ต้องเปิดพอร์ต/ลิงก์ที่เครื่องลูก มีลิงก์เดียวที่หน้ากลาง
HUB = {"devs": {}, "lock": threading.Lock()}
AGENT = {"thread": None, "stop": threading.Event(), "state": "ปิด", "results": [], "lock": threading.Lock()}
DEV_TTL = 15            # ไม่ส่งข้อมูลเกินกี่วินาทีถือว่า offline
CMD_TTL = 30            # คำสั่งค้างเกินกี่วินาทีทิ้ง (กัน reboot/stop ไปทำตอนเครื่องกลับมาทีหลัง)
HUB_ACTIONS = {"start", "stop", "rejoin_all", "rejoin", "toggle", "add_cookie", "reboot"}
HUB_KEYS = ("action", "id", "label", "app_num", "cookie", "confirm")
MENU_W_HASH = "cb35d449b919ec59f7ba64dd8592e76502d911072bfc41cd2bf38892966f2ba0"

def web_gate():
    """ถามรหัสผ่านก่อนเข้าเมนู Remote Web (เก็บเป็น hash ไม่ใช่ข้อความตรงๆ)"""
    for i in range(3):
        try: pw = getpass.getpass("[?] รหัสผ่านเมนู Remote Web: ")
        except (EOFError, KeyboardInterrupt): print(); return False
        if hmac.compare_digest(hashlib.sha256(pw.strip().encode()).hexdigest().encode(), MENU_W_HASH.encode()):
            return True
        print(sym_line("[x]", f"รหัสผ่านผิด ({i + 1}/3)", RED))
    time.sleep(1); return False

def _new_key(): return secrets.token_urlsafe(18)

# ---------- ฝั่งหน้ากลาง ----------
def hub_devices(cfg):
    now = time.time()
    local = {"id": "local", "name": (web_cfg(cfg)["agent"].get("name") or socket.gethostname()) + " (หน้ากลาง)",
             "online": True, "age": 0, "status": web_status(cfg), "msg": "", "msg_t": 0}
    out = [local]
    with HUB["lock"]:
        for d in sorted(HUB["devs"].values(), key=lambda x: x["name"].lower()):
            age = now - d["seen"]
            out.append({"id": d["id"], "name": d["name"], "online": age < DEV_TTL, "age": int(age),
                        "status": d["status"], "msg": d["msg"], "msg_t": d["msg_t"]})
    return out

def hub_shot(dev_id):
    if dev_id == "local": return web_shot()
    with HUB["lock"]:
        d = HUB["devs"].get(dev_id)
        if not d: return None, ""
        d["want_until"] = time.time() + 20          # มีคนดูอยู่ → บอกเครื่องลูกให้ส่งภาพมา
        return (d["shot"], d["mime"]) if d["shot"] else (None, "")

def hub_action(cfg, d):
    dev_id, act = str(d.get("device", "")), str(d.get("action", ""))
    if dev_id == "local":
        return web_action(cfg, {k: v for k, v in d.items() if k in HUB_KEYS})
    with HUB["lock"]:
        dev = HUB["devs"].get(dev_id)
        if not dev: return False, "ไม่เจอเครื่องนี้"
        if act == "forget":
            if time.time() - dev["seen"] < DEV_TTL: return False, "เครื่องยังออนไลน์อยู่"
            del HUB["devs"][dev_id]; return True, f"ลบ {dev['name']} ออกจากรายการแล้ว"
        if act not in HUB_ACTIONS: return False, "คำสั่งไม่รู้จัก"
        if time.time() - dev["seen"] >= DEV_TTL: return False, f"{dev['name']} offline"
        if len(dev["cmds"]) >= 20: return False, "คิวคำสั่งเต็ม"
        dev["cmds"].append((time.time(), {k: v for k, v in d.items() if k in HUB_KEYS}))
        return True, f"ส่งคำสั่งถึง {dev['name']} แล้ว (เครื่องรับภายใน ~3 วิ)"

def hub_report(cfg, d):
    """รับข้อมูลจากเครื่องลูก → คืน {cmds, want_shot}"""
    did = str(d.get("id", ""))
    if not re.fullmatch(r"[a-z0-9]{4,16}", did): raise ValueError("bad id")
    now = time.time()
    with HUB["lock"]:
        dev = HUB["devs"].get(did)
        if not dev:
            if len(HUB["devs"]) >= 200: raise ValueError("too many devices")
            dev = HUB["devs"][did] = {"id": did, "name": "?", "seen": 0, "status": {}, "shot": b"", "mime": "image/jpeg",
                                      "cmds": [], "want_until": 0, "msg": "", "msg_t": 0}
        dev["name"] = str(d.get("name") or did)[:32]
        dev["seen"] = now
        if isinstance(d.get("status"), dict): dev["status"] = d["status"]
        if d.get("shot"):
            try:
                raw = base64.b64decode(d["shot"])
                if raw[:2] == b"\xff\xd8" or raw[:4] == b"\x89PNG":
                    dev.update(shot=raw, mime="image/jpeg" if raw[:2] == b"\xff\xd8" else "image/png")
            except Exception: pass
        for r in (d.get("results") or [])[:10]:
            if isinstance(r, dict): dev["msg"], dev["msg_t"] = str(r.get("msg", ""))[:200], now
        cmds = [c for t, c in dev["cmds"] if now - t < CMD_TTL]
        dev["cmds"] = []
        return {"cmds": cmds, "want_shot": now < dev["want_until"]}

# ---------- ฝั่งเครื่องลูก ----------
def _agent_exec(cfg, cmd):
    try: ok, msg = web_action(cfg, cmd)
    except Exception as e: ok, msg = False, f"error {type(e).__name__}"
    with AGENT["lock"]: AGENT["results"].append({"ok": ok, "msg": msg})

def _agent_loop(cfg):
    a = web_cfg(cfg)["agent"]
    sess, want, fails = requests.Session(), False, 0
    while not AGENT["stop"].is_set():
        try:
            with AGENT["lock"]: res, AGENT["results"] = AGENT["results"], []
            body = {"id": a["id"], "name": a["name"], "status": web_status(cfg), "results": res}
            if want:
                data, _ = web_shot(max_age=1.5)
                if data: body["shot"] = base64.b64encode(data).decode()
            r = sess.post(a["url"].rstrip("/") + "/hub/report", json=body, headers={"X-Hub-Key": a["key"]}, timeout=(8, 25))
            if r.status_code == 200:
                j = r.json(); fails = 0; AGENT["state"] = "เชื่อมต่อแล้ว"
                want = bool(j.get("want_shot"))
                for c in (j.get("cmds") or [])[:10]:
                    if isinstance(c, dict): threading.Thread(target=_agent_exec, args=(cfg, c), daemon=True).start()
            elif r.status_code in (401, 403):
                AGENT["state"] = "key ไม่ถูก/หน้ากลางไม่ได้เปิด Hub"; fails += 1
            else:
                AGENT["state"] = f"หน้ากลางตอบ {r.status_code}"; fails += 1
        except Exception as e:
            AGENT["state"] = f"ต่อไม่ได้ ({type(e).__name__})"; fails += 1
        AGENT["stop"].wait(2 if want else min(3 + fails * 2, 30))
    AGENT["state"] = "ปิด"

def agent_start(cfg):
    a = web_cfg(cfg)["agent"]
    if not (a["url"] and a["key"]): return False
    t = AGENT["thread"]
    if t and t.is_alive(): return True
    AGENT["stop"].clear()
    AGENT["thread"] = threading.Thread(target=_agent_loop, args=(cfg,), daemon=True, name="agent")
    AGENT["thread"].start()
    threading.Thread(target=has_root, daemon=True).start()
    return True

def agent_stop():
    AGENT["stop"].set()

def agent_alive():
    t = AGENT["thread"]; return bool(t and t.is_alive() and not AGENT["stop"].is_set())

def web_autostart(cfg):
    w = web_cfg(cfg)
    if w.get("on") and w.get("password"):
        ok, msg = web_start(cfg)
        print(sym_line("[+]" if ok else "[x]", f"Remote web: http://{lan_ip()}:{w['port']}" + (" (Hub)" if w.get("hub") else "") if ok
                       else f"Remote web: {msg}", GREEN if ok else RED))
    if w["agent"].get("on") and agent_start(cfg):
        print(sym_line("[+]", f"Agent → {w['agent']['url']}", GREEN))

def _rand_pw(n=10):
    return "".join(secrets.choice(string.ascii_letters + string.digits) for _ in range(n))

def _ensure_web(cfg):
    """เปิดเว็บเซิร์ฟเวอร์ให้ (ตั้งรหัสผ่านให้ถ้ายังไม่มี) — คืน True ถ้าเปิดอยู่"""
    w = web_cfg(cfg)
    if not w["password"]: w["password"] = _rand_pw(); print(sym_line("[*]", f"สุ่มรหัสผ่านเว็บให้: {w['password']}"))
    ok, msg = web_start(cfg)
    if not ok: print(sym_line("[x]", msg, RED)); return False
    w["on"] = True; save_cfg(cfg); return True

def menu_web(cfg):
    w = web_cfg(cfg); a = w["agent"]
    while True:
        cls(); on = WEB["server"] is not None
        print(sect("Remote Web", "คุมจากมือถือ/ไอแพด"))
        print(t_ind() + f"เว็บ: {ac('เปิดอยู่', GREEN) if on else ac('ปิด', RED)} · พอร์ต {w['port']} · เปิดอัตโนมัติ: {'ใช่' if w['on'] else 'ไม่'}")
        print(t_ind() + f"รหัสผ่านเว็บ: {w['password'] or ac('(ยังไม่ตั้ง)', GRAY_D)}  (ชื่อผู้ใช้ใส่อะไรก็ได้)")
        if on:
            print(t_ind() + f"Wi-Fi เดียวกัน: http://{lan_ip()}:{w['port']}")
            print(t_ind() + "ลิงก์สาธารณะ: " + (ac(WEB["url"], GREEN_H) if WEB["url"] else ac("(ยังไม่เปิด)", GRAY_D)))
        print(t_ind() + f"Hub หน้ากลาง: {ac('เปิด', GREEN) if w['hub'] else ac('ปิด', GRAY_D)}" + (f" · key: {w['key']}" if w["hub"] else ""))
        print(t_ind() + f"Agent ส่งเข้าหน้ากลาง: {ac('เปิด', GREEN) if agent_alive() else ac('ปิด', GRAY_D)}"
              + (f" → {a['url']} · ชื่อ {a['name']} · {AGENT['state']}" if a["on"] else ""))
        print(t_ind() + "[1] เปิด/ปิดเว็บ   [2] ตั้ง/สุ่มรหัสผ่านเว็บ   [3] เปลี่ยนพอร์ต   [4] ลิงก์สาธารณะ (cloudflared)")
        print(t_ind() + "[5] เปิด/ปิด Hub (เครื่องนี้เป็นหน้ากลาง)   [6] เปิด/ปิด Agent (ส่งเครื่องนี้เข้าหน้ากลาง)   [0] กลับ")
        s = inp("[?] เลือก: ").strip()
        if s in ("", "0"): return
        if s == "1":
            if on:
                web_stop(); w["on"] = False; save_cfg(cfg); print(sym_line("[+]", "ปิดเว็บแล้ว"))
            elif _ensure_web(cfg): print(sym_line("[+]", f"เปิดแล้ว http://{lan_ip()}:{w['port']}", GREEN))
            inp("[Enter] ")
        elif s == "2":
            t = inp("[?] รหัสผ่านใหม่ (Enter=สุ่ม, อย่างน้อย 6 ตัว): ").strip()
            if not t: t = _rand_pw()
            if len(t) < 6: print(sym_line("[x]", "สั้นไป", RED))
            else: w["password"] = t; save_cfg(cfg); print(sym_line("[+]", f"ตั้งรหัสผ่านแล้ว: {t}"))
            inp("[Enter] ")
        elif s == "3":
            t = inp("[?] พอร์ต 1024-65535: ").strip()
            if t.isdigit() and 1024 <= int(t) <= 65535:
                was = on
                if was: web_stop()
                w["port"] = int(t); save_cfg(cfg)
                if was:
                    ok, msg = web_start(cfg); print(sym_line("[+]" if ok else "[x]", "เปลี่ยนแล้ว" if ok else msg, GREEN if ok else RED))
                else: print(sym_line("[+]", "บันทึกแล้ว"))
            else: print(sym_line("[x]", "ใส่ 1024-65535", RED))
            inp("[Enter] ")
        elif s == "4":
            if w["tunnel"] or WEB["tproc"]:
                web_tunnel_stop(); w["tunnel"] = False; save_cfg(cfg); print(sym_line("[+]", "ปิดลิงก์สาธารณะแล้ว"))
            elif not shutil.which("cloudflared"):
                print(sym_line("[x]", "ยังไม่มี cloudflared — พิมพ์ pkg install cloudflared ก่อน แล้วกลับมาเลือกใหม่", RED))
            elif on or _ensure_web(cfg):
                w["tunnel"] = True; save_cfg(cfg); web_tunnel_start(w["port"])
                print(sym_line("[*]", "กำลังขอลิงก์..."))
                for _ in range(50):
                    if WEB["url"]: break
                    time.sleep(0.5)
                print(sym_line("[+]", WEB["url"], GREEN) if WEB["url"] else sym_line("[!]", "ยังไม่ได้ลิงก์ — เข้าเมนูนี้ใหม่อีกครั้งแล้วดู", YELLOW))
            inp("[Enter] ")
        elif s == "5":
            if w["hub"]:
                w["hub"] = False; save_cfg(cfg); print(sym_line("[+]", "ปิด Hub แล้ว (เว็บกลับเป็นหน้าเครื่องเดียว)"))
            elif _ensure_web(cfg):
                if not w["key"]: w["key"] = _new_key()
                w["hub"] = True; save_cfg(cfg)
                print(sym_line("[+]", "เปิด Hub แล้ว — เปิดหน้าเว็บของเครื่องนี้จะเห็นทุกเครื่องรวมกัน", GREEN))
                print(t_ind() + "ที่เครื่องลูกแต่ละเครื่อง: เมนู w → [6] แล้วใส่")
                print(t_ind() + f"  URL หน้ากลาง = ลิงก์ของเครื่องนี้ (Wi-Fi เดียวกัน http://{lan_ip()}:{w['port']} หรือลิงก์ cloudflared [4])")
                print(t_ind() + ac(f"  key = {w['key']}", GREEN_H))
            inp("[Enter] ")
        elif s == "6":
            if a["on"] or agent_alive():
                agent_stop(); a["on"] = False; save_cfg(cfg); print(sym_line("[+]", "ปิด Agent แล้ว"))
            else:
                url = inp(f"[?] URL หน้ากลาง (Enter={a['url'] or 'ยกเลิก'}): ").strip() or a["url"]
                if not re.match(r"https?://[^\s/]+", url or ""): print(sym_line("[x]", "URL ต้องขึ้นต้น http:// หรือ https://", RED)); inp("[Enter] "); continue
                key = inp(f"[?] key จากหน้ากลาง (Enter={'ใช้ตัวเดิม' if a['key'] else 'ยกเลิก'}): ").strip() or a["key"]
                if not key: continue
                nm = inp(f"[?] ชื่อเครื่องนี้ที่จะโชว์ (Enter={a['name'] or socket.gethostname()}): ").strip() or a["name"] or socket.gethostname()
                if not a["id"]: a["id"] = uuid.uuid4().hex[:10]
                a.update(url=url.rstrip("/"), key=key, name=nm[:32], on=True); save_cfg(cfg)
                agent_start(cfg); print(sym_line("[+]", "เปิด Agent แล้ว — เครื่องนี้จะขึ้นในหน้ากลางภายในไม่กี่วินาที", GREEN))
            inp("[Enter] ")

WEB_HTML = r'''<!doctype html>
<html lang="th"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>STAR Remote</title>
<style>
:root{--bg:#0b0f17;--card:#111827;--line:#1f2937;--tx:#e5e7eb;--mut:#8b95a7;--blue:#2f9bff;--grn:#22c55e;--red:#ef4444;--yel:#eab308;--mag:#d946ef}
*{box-sizing:border-box}body{margin:0;background:var(--bg);color:var(--tx);font:14px/1.4 system-ui,sans-serif;padding:12px;max-width:1000px;margin:auto}
h1{font-size:17px;margin:0}header{display:flex;align-items:center;gap:10px;justify-content:space-between;margin-bottom:12px;flex-wrap:wrap}
.pill{border-radius:999px;padding:2px 10px;font-size:12px;border:1px solid}
.on{color:var(--grn);border-color:#14532d;background:#052e16}.off{color:var(--mut);border-color:var(--line)}
.card{background:var(--card);border:1px solid var(--line);border-radius:12px;padding:12px;margin-bottom:12px}
.shot{width:100%;display:block;border-radius:8px;background:#000;min-height:90px;object-fit:contain;max-height:60vh}
.meta{display:flex;justify-content:space-between;color:var(--mut);font-size:12px;margin-top:6px}
.stats{display:grid;grid-template-columns:repeat(5,1fr);gap:8px}
.st{background:#0d1320;border:1px solid var(--line);border-radius:10px;padding:8px;text-align:center}
.st b{display:block;font-size:18px}.st span{font-size:11px;color:var(--mut)}
.btns{display:grid;grid-template-columns:repeat(2,1fr);gap:8px}
button{font:inherit;color:var(--tx);background:#0d1320;border:1px solid var(--line);border-radius:10px;padding:11px;cursor:pointer}
button:active{filter:brightness(1.3)}.pri{background:var(--blue);border-color:var(--blue);color:#fff}.dng{color:#fca5a5;border-color:#7f1d1d;background:#2a0f12}
.row{display:flex;gap:10px;align-items:center;padding:10px 0;border-top:1px solid var(--line)}.row:first-child{border-top:0}
.dot{width:10px;height:10px;border-radius:50%;flex:none;background:var(--mut)}
.grow{flex:1;min-width:0}.nm{font-weight:600}.sub{color:var(--mut);font-size:12px;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.mini{padding:6px 10px;font-size:12px}.h{font-size:12px;color:var(--mut);margin:0 0 8px;letter-spacing:.05em}
pre{margin:0;font:11px/1.5 ui-monospace,monospace;white-space:pre-wrap;word-break:break-all;max-height:220px;overflow:auto;color:#cbd5e1}
dialog{background:var(--card);color:var(--tx);border:1px solid var(--line);border-radius:12px;width:min(92vw,420px)}
dialog::backdrop{background:#000a}input,textarea{width:100%;background:#0d1320;color:var(--tx);border:1px solid var(--line);border-radius:8px;padding:9px;font:inherit;margin:4px 0 10px}
#toast{position:fixed;left:50%;bottom:18px;transform:translateX(-50%);background:#1f2937;border-radius:10px;padding:10px 16px;display:none;z-index:9}
label.c{font-size:12px;color:var(--mut)}
</style></head><body>
<header><h1>★ STAR Remote <span class="sub" id="ver"></span></h1>
<div><span class="pill off" id="run">-</span> <span class="sub" id="ram"></span></div></header>

<div class="card"><img class="shot" id="shot" alt="">
<div class="meta"><span id="shotmsg">กำลังโหลดภาพ...</span><label><input type="checkbox" id="auto" checked style="width:auto;margin:0 4px 0 0">รีเฟรชอัตโนมัติ</label></div></div>

<div class="card"><div class="stats">
<div class="st"><b id="s_up">-</b><span>Active</span></div><div class="st"><b id="s_on" style="color:var(--grn)">0</b><span>Online</span></div>
<div class="st"><b id="s_off">0</b><span>Offline</span></div><div class="st"><b id="s_rj">0</b><span>Rejoin</span></div>
<div class="st"><b id="s_hp" style="color:var(--blue)">0</b><span>Hop</span></div></div></div>

<div class="card"><p class="h">DEVICE CONTROLS</p><div class="btns">
<button class="pri" onclick="api('start')">▶ Start tool</button><button onclick="api('stop')">■ Stop tool</button>
<button onclick="api('rejoin_all')">↻ Rejoin ทุกบัญชี</button><button onclick="$('#dlg').showModal()">＋ Add cookie</button>
<button class="dng" style="grid-column:1/-1" onclick="if(confirm('รีบูตเครื่องจริงๆ?'))api('reboot',{confirm:true})">⚡ Reboot</button></div></div>

<div class="card"><p class="h">ACCOUNTS</p><div id="accs"></div></div>
<div class="card"><p class="h">LOG</p><pre id="log"></pre></div>

<dialog id="dlg"><p class="h">ADD COOKIE</p>
<label class="c">ชื่อเรียก (ไม่ใส่ก็ได้)</label><input id="c_label" maxlength="24">
<label class="c">แอป # (ไม่ใส่ก็ได้)</label><input id="c_app" inputmode="numeric">
<label class="c">cookie</label><textarea id="c_ck" rows="4" placeholder="_|WARNING:-DO-NOT-SHARE-THIS..."></textarea>
<div class="btns"><button onclick="$('#dlg').close()">ยกเลิก</button><button class="pri" onclick="addCk()">เพิ่ม</button></div></dialog>
<div id="toast"></div>

<script>
const $=s=>document.querySelector(s);
const esc=s=>String(s==null?'':s).replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
const COL={WATCH:'#22c55e',REJOIN:'#eab308',HOP:'#d946ef',COOLDOWN:'#ef4444',DEAD:'#ef4444',NET:'#eab308',INIT:'#8b95a7',OFF:'#8b95a7'};
let tt;function toast(m,ok){const t=$('#toast');t.textContent=m;t.style.color=ok===false?'#fca5a5':'#e5e7eb';t.style.display='block';clearTimeout(tt);tt=setTimeout(()=>t.style.display='none',3200)}
async function api(a,extra){
  try{const r=await fetch('/api/action',{method:'POST',headers:{'Content-Type':'application/json','X-Star':'1'},body:JSON.stringify(Object.assign({action:a},extra||{}))});
  const j=await r.json();toast(j.msg,j.ok);load();return j}catch(e){toast('ต่อเครื่องไม่ได้',false)}}
async function addCk(){const j=await api('add_cookie',{label:$('#c_label').value,app_num:$('#c_app').value,cookie:$('#c_ck').value});if(j&&j.ok){$('#dlg').close();$('#c_ck').value=''}}
async function load(){
  let d;try{const r=await fetch('/api/status');if(!r.ok)throw 0;d=await r.json()}catch(e){$('#run').textContent='offline';$('#run').className='pill off';return}
  $('#ver').textContent='v'+d.version+' · '+d.host;
  $('#run').textContent=d.running?'Tool running':'Idle';$('#run').className='pill '+(d.running?'on':'off');
  $('#ram').textContent=d.ram_total?('RAM ว่าง '+d.ram_free+'/'+d.ram_total+' MB'):'';
  $('#s_up').textContent=d.uptime;$('#s_on').textContent=d.online;$('#s_off').textContent=d.offline;$('#s_rj').textContent=d.rejoins;$('#s_hp').textContent=d.hops;
  $('#accs').innerHTML=d.accounts.length?d.accounts.map(a=>`<div class="row"><span class="dot" style="background:${COL[a.state]||'#8b95a7'}"></span>
  <div class="grow"><div class="nm">${esc(a.label)} <span class="sub">${esc(a.app)} · ${esc(a.state)}</span></div>
  <div class="sub">rj ${a.rj} · hop ${a.hp} · stab ${a.stab}% · up ${esc(a.up)} · place ${esc(a.place)}</div>
  ${a.note?`<div class="sub" style="color:#eab308">${esc(a.note)}</div>`:''}</div>
  <button class="mini" onclick="api('rejoin',{id:'${esc(a.id)}'})">↻</button>
  <button class="mini" onclick="api('toggle',{id:'${esc(a.id)}'})">${a.enabled?'ON':'OFF'}</button></div>`).join(''):'<div class="sub">ยังไม่มีบัญชี — กด Add cookie</div>';
  const L=$('#log'),b=L.scrollTop+L.clientHeight>=L.scrollHeight-8;
  L.textContent=d.log.map(x=>x[0]+' '+x[2]+' '+x[3]).join('\n');if(b)L.scrollTop=L.scrollHeight}
function shot(){if(document.hidden||!$('#auto').checked)return;const im=new Image();
  im.onload=()=>{$('#shot').src=im.src;$('#shotmsg').textContent='อัปเดต '+new Date().toLocaleTimeString()};
  im.onerror=()=>{$('#shotmsg').textContent='ดึงภาพไม่ได้ (ต้องมี root)'};im.src='/api/shot?t='+Date.now()}
load();shot();setInterval(()=>{if(!document.hidden)load()},3000);setInterval(shot,4000);
</script></body></html>'''


HUB_HTML = r'''<!doctype html>
<html lang="th"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>STAR Hub</title>
<style>
:root{--bg:#0b0f17;--card:#111827;--line:#1f2937;--tx:#e5e7eb;--mut:#8b95a7;--blue:#2f9bff;--grn:#22c55e;--red:#ef4444;--yel:#eab308}
*{box-sizing:border-box}body{margin:0;background:var(--bg);color:var(--tx);font:14px/1.4 system-ui,sans-serif;padding:14px;max-width:1300px;margin:auto}
header{display:flex;align-items:center;justify-content:space-between;gap:10px;flex-wrap:wrap;margin-bottom:12px}
h1{font-size:18px;margin:0}.sub{color:var(--mut);font-size:12px}
.bulk{display:flex;gap:8px;align-items:center;flex-wrap:wrap;margin-bottom:12px;background:var(--card);border:1px solid var(--line);border-radius:12px;padding:10px}
.grid{display:grid;grid-template-columns:repeat(auto-fill,minmax(330px,1fr));gap:12px}
.card{background:var(--card);border:1px solid var(--line);border-radius:14px;padding:12px}
.top{display:flex;align-items:center;gap:8px;margin-bottom:10px;flex-wrap:wrap}.top b{font-size:16px}.sp{flex:1}
.dot{width:9px;height:9px;border-radius:50%;background:var(--mut)}.dot.on{background:var(--grn);box-shadow:0 0 6px var(--grn)}
.pill{border-radius:999px;padding:2px 10px;font-size:12px;border:1px solid var(--line);color:var(--mut)}.pill.on{color:var(--grn);border-color:#14532d;background:#052e16}.pill.bad{color:#fca5a5;border-color:#7f1d1d;background:#2a0f12}
.shot{width:100%;display:block;border-radius:8px;background:#000;aspect-ratio:16/9;object-fit:contain}
.stats{display:grid;grid-template-columns:repeat(5,1fr);gap:6px;margin:10px 0}
.st{background:#0d1320;border:1px solid var(--line);border-radius:10px;padding:6px 2px;text-align:center}.st b{display:block;font-size:16px}.st span{font-size:10px;color:var(--mut)}
.last{display:flex;justify-content:space-between;border-top:1px solid var(--line);border-bottom:1px solid var(--line);padding:8px 0;margin-bottom:10px;font-size:12px;color:var(--mut)}.last b{color:var(--tx)}
.h{font-size:11px;color:var(--mut);letter-spacing:.06em;margin:0 0 8px}
.btns{display:grid;grid-template-columns:1fr 1fr;gap:8px}.full{grid-column:1/-1}
button{font:inherit;color:var(--tx);background:#0d1320;border:1px solid var(--line);border-radius:10px;padding:10px 6px;cursor:pointer}button:active{filter:brightness(1.4)}button:disabled{opacity:.4}
.pri{background:var(--blue);border-color:var(--blue);color:#fff}.dng{color:#fca5a5;border-color:#7f1d1d;background:#2a0f12}.mini{padding:5px 9px;font-size:12px}
details{margin-top:10px}summary{cursor:pointer;color:var(--mut);font-size:12px}
.row{display:flex;gap:8px;align-items:center;padding:8px 0;border-top:1px solid var(--line)}.g{flex:1;min-width:0}.g div{overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.msg{margin-top:8px;font-size:12px;color:var(--yel);min-height:16px}
dialog{background:var(--card);color:var(--tx);border:1px solid var(--line);border-radius:12px;width:min(92vw,420px)}dialog::backdrop{background:#000a}
input[type=text],input:not([type]),textarea{width:100%;background:#0d1320;color:var(--tx);border:1px solid var(--line);border-radius:8px;padding:9px;font:inherit;margin:4px 0 10px}
#toast{position:fixed;left:50%;bottom:18px;transform:translateX(-50%);background:#1f2937;border-radius:10px;padding:10px 16px;display:none;z-index:9;max-width:90vw}
</style></head><body>
<header><h1>★ STAR Hub <span class="sub" id="ver"></span></h1><span class="sub" id="cnt"></span></header>
<div class="bulk"><label><input type="checkbox" id="all"> เลือกทั้งหมด</label><span class="sub" id="selc">0 เครื่อง</span><span class="sp" style="flex:1"></span>
<button class="mini pri" onclick="bulk('start')">▶ Start</button><button class="mini" onclick="bulk('stop')">■ Stop</button><button class="mini" onclick="bulk('rejoin_all')">↻ Rejoin</button></div>
<div class="grid" id="grid"></div>

<dialog id="dlg"><p class="h">ADD COOKIE → <span id="dname"></span></p>
<label class="sub">ชื่อเรียก (ไม่ใส่ก็ได้)</label><input id="c_label" maxlength="24">
<label class="sub">แอป # (ไม่ใส่ก็ได้)</label><input id="c_app" inputmode="numeric">
<label class="sub">cookie</label><textarea id="c_ck" rows="4" placeholder="_|WARNING:-DO-NOT-SHARE-THIS..."></textarea>
<div class="btns"><button onclick="$('#dlg').close()">ยกเลิก</button><button class="pri" onclick="addCk()">เพิ่ม</button></div></dialog>
<div id="toast"></div>

<script>
const $=s=>document.querySelector(s);
const esc=s=>String(s==null?'':s).replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
const COL={WATCH:'#22c55e',REJOIN:'#eab308',HOP:'#d946ef',COOLDOWN:'#ef4444',DEAD:'#ef4444',NET:'#eab308',INIT:'#8b95a7',OFF:'#8b95a7'};
const cards={},msgT={};let target=null,tt;
function toast(m,ok){const t=$('#toast');t.textContent=m;t.style.color=ok===false?'#fca5a5':'#e5e7eb';t.style.display='block';clearTimeout(tt);tt=setTimeout(()=>t.style.display='none',3500)}
async function hub(device,action,extra){
  try{const r=await fetch('/api/hub/action',{method:'POST',headers:{'Content-Type':'application/json','X-Star':'1'},body:JSON.stringify(Object.assign({device,action},extra||{}))});
  const j=await r.json();return j}catch(e){return{ok:false,msg:'ต่อหน้ากลางไม่ได้'}}}
async function act(device,action,extra){const j=await hub(device,action,extra);toast(j.msg,j.ok);if(j.ok)setTimeout(load,800);return j}
function selected(){return Object.keys(cards).filter(id=>cards[id].el.querySelector('.sel').checked)}
async function bulk(a){const ids=selected();if(!ids.length)return toast('ยังไม่ได้เลือกเครื่อง',false);
  const rs=await Promise.all(ids.map(id=>hub(id,a)));const ok=rs.filter(r=>r.ok).length;toast(a+': สำเร็จ '+ok+'/'+ids.length,ok===ids.length);setTimeout(load,800)}
function openCk(id,name){target=id;$('#dname').textContent=name;$('#dlg').showModal()}
async function addCk(){const j=await act(target,'add_cookie',{label:$('#c_label').value,app_num:$('#c_app').value,cookie:$('#c_ck').value});if(j.ok){$('#dlg').close();$('#c_ck').value=''}}
function make(d){
  const el=document.createElement('div');el.className='card';
  el.innerHTML=`<div class="top"><input type="checkbox" class="sel"><span class="dot"></span><b data-f="name"></b><span class="sp"></span><span class="pill" data-f="run"></span><span class="pill" data-f="net"></span></div>
  <img class="shot" alt=""><div class="sub" data-f="shotmsg" style="margin-top:4px"></div>
  <div class="stats"><div class="st"><b data-f="up">-</b><span>Active</span></div><div class="st"><b data-f="on" style="color:var(--grn)">0</b><span>Online</span></div>
  <div class="st"><b data-f="off">0</b><span>Offline</span></div><div class="st"><b data-f="rj">0</b><span>Rejoin</span></div><div class="st"><b data-f="hp" style="color:var(--blue)">0</b><span>Hop</span></div></div>
  <div class="last"><span>Last activity</span><b data-f="last">-</b></div>
  <p class="h">DEVICE CONTROLS</p><div class="btns">
  <button class="pri" data-a="start">▶ Start tool</button><button data-a="stop">■ Stop tool</button>
  <button data-a="rejoin_all">↻ Rejoin all</button><button data-a="cookie">＋ Add cookies</button>
  <button class="dng full" data-a="reboot">⚡ Reboot</button><button class="mini full" data-a="forget" style="display:none">ลบเครื่องนี้ออกจากรายการ</button></div>
  <details><summary data-f="accsum">บัญชี</summary><div data-f="accs"></div></details><div class="msg" data-f="msg"></div>`;
  el.querySelector('.sel').onchange=sel;
  el.querySelectorAll('[data-a]').forEach(b=>b.onclick=()=>{const a=b.dataset.a,n=cards[d.id].name;
    if(a==='cookie')return openCk(d.id,n);if(a==='reboot'){if(confirm('รีบูต '+n+' จริงๆ?'))act(d.id,'reboot',{confirm:true});return}
    if(a==='forget'){if(confirm('ลบ '+n+'?')){act(d.id,'forget').then(()=>{el.remove();delete cards[d.id]})}return}act(d.id,a)});
  $('#grid').appendChild(el);return cards[d.id]={el,name:d.name,img:el.querySelector('.shot'),f:k=>el.querySelector('[data-f='+k+']')}}
function sel(){$('#selc').textContent=selected().length+' เครื่อง'}
$('#all').onchange=e=>{Object.values(cards).forEach(c=>c.el.querySelector('.sel').checked=e.target.checked);sel()};
function ago(s){return s<60?s+' วิที่แล้ว':s<3600?Math.floor(s/60)+' นาทีที่แล้ว':Math.floor(s/3600)+' ชม.ที่แล้ว'}
function upsert(d){
  const c=cards[d.id]||make(d),s=d.status||{},run=!!s.running;c.name=d.name;
  c.f('name').textContent=d.name;c.el.querySelector('.dot').className='dot'+(d.online?' on':'');
  c.f('run').textContent=run&&d.online?'Tool running':'Idle';c.f('run').className='pill'+(run&&d.online?' on':'');
  c.f('net').textContent=d.online?'Online':'Offline';c.f('net').className='pill '+(d.online?'on':'bad');
  c.f('up').textContent=String(s.uptime||'-');c.f('on').textContent=s.online||0;c.f('off').textContent=s.offline||0;c.f('rj').textContent=s.rejoins||0;c.f('hp').textContent=s.hops||0;
  c.f('last').textContent=d.online?(d.id==='local'?'ตอนนี้':ago(d.age)):('Offline · '+ago(d.age));
  c.el.querySelector('[data-a=forget]').style.display=d.online||d.id==='local'?'none':'';
  c.el.querySelectorAll('[data-a]:not([data-a=forget])').forEach(b=>b.disabled=!d.online);
  const A=Array.isArray(s.accounts)?s.accounts:[];c.f('accsum').textContent='บัญชี ('+A.length+')';
  c.f('accs').innerHTML=A.map(a=>`<div class="row"><span class="dot" style="background:${COL[a.state]||'#8b95a7'}"></span><div class="g"><div><b>${esc(a.label)}</b> <span class="sub">${esc(a.app)} · ${esc(a.state)}</span></div>
  <div class="sub">rj ${esc(a.rj)} · hop ${esc(a.hp)} · stab ${esc(a.stab)}% · up ${esc(a.up)}</div>${a.note?`<div class="sub" style="color:#eab308">${esc(a.note)}</div>`:''}</div>
  <button class="mini" ${d.online?'':'disabled'} data-r="${esc(a.id)}">↻</button><button class="mini" ${d.online?'':'disabled'} data-t="${esc(a.id)}">${a.enabled?'ON':'OFF'}</button></div>`).join('')||'<div class="sub">ยังไม่มีบัญชี</div>';
  c.f('accs').querySelectorAll('[data-r]').forEach(b=>b.onclick=()=>act(d.id,'rejoin',{id:b.dataset.r}));
  c.f('accs').querySelectorAll('[data-t]').forEach(b=>b.onclick=()=>act(d.id,'toggle',{id:b.dataset.t}));
  if(d.msg_t&&d.msg_t!==msgT[d.id]){if(msgT[d.id]!==undefined)toast(d.name+': '+d.msg);msgT[d.id]=d.msg_t;c.f('msg').textContent=d.msg}
  else if(msgT[d.id]===undefined){msgT[d.id]=d.msg_t||0}}
async function load(){
  let L;try{const r=await fetch('/api/hub/devices');if(!r.ok)throw 0;L=await r.json()}catch(e){return}
  $('#ver').textContent='v'+(L.version||'');const D=L.devices;$('#cnt').textContent=D.filter(x=>x.online).length+'/'+D.length+' เครื่องออนไลน์';
  D.forEach(upsert)}
function shots(){if(document.hidden)return;Object.keys(cards).forEach(id=>{const c=cards[id];if(c.el.querySelector('.pill.bad'))return;
  const im=new Image();im.onload=()=>{c.img.src=im.src;c.f('shotmsg').textContent=''};im.onerror=()=>{if(!c.img.getAttribute('src'))c.f('shotmsg').textContent='ยังไม่มีภาพ (ต้องมี root หรือรอสักครู่)'};
  im.src='/api/hub/shot?d='+encodeURIComponent(id)+'&t='+Date.now()})}
load();setTimeout(shots,1500);setInterval(()=>{if(!document.hidden)load()},3000);setInterval(shots,4500);
</script></body></html>'''


# ════════════════════════════════════════════════════════════════
#  ROOT — Cookie Injector
# ════════════════════════════════════════════════════════════════
COOKIE_RE   = re.compile(rb"_\|WARNING:-DO-NOT-SHARE-THIS[^\"'\s;,]+")
COOKIE_RE_S = re.compile(COOKIE_RE.pattern.decode())

def root_fread(path):
    try:
        r = subprocess.run(["su", "-c", f"cat {shlex.quote(path)}"], capture_output=True,
                           stdin=subprocess.DEVNULL, timeout=180)
        return r.stdout or b""
    except Exception: return b""

def root_fwrite(path, data, perms, uid, gid):
    q = shlex.quote(path)
    try:
        p = subprocess.run(["su", "-c", f"cat > {q}"], input=data, capture_output=True, timeout=180)
        if p.returncode != 0: return False
    except Exception: return False
    su(f"chmod {perms} {q}"); su(f"chown {uid}:{gid} {q}"); su(f"restorecon {q} 2>/dev/null")
    return True

def root_fstat(path):
    out = su_text(f'stat -c "%a %u %g" {shlex.quote(path)}').split()
    return (out[0], out[1], out[2]) if len(out) == 3 else ("644", "0", "0")

def root_load_map():
    try:
        with open(ROOTMAP) as f: return json.load(f)
    except Exception: return {}

def root_save_map(m): _atomic_write(ROOTMAP, json.dumps(m, indent=2), 0o600)

def root_stream_scan(cmd, timeout):
    files = []
    try:
        proc = subprocess.Popen(["su", "-c", cmd], stdout=subprocess.PIPE,
                                stderr=subprocess.DEVNULL, stdin=subprocess.DEVNULL)
    except Exception: return files
    timer = threading.Timer(timeout, proc.kill); timer.start()      # timeout จริง แม้ grep ค้างไม่พ่นบรรทัด
    try:
        while True:
            ln = proc.stdout.readline()
            if not ln: break
            p = ln.decode(errors="ignore").strip()
            if not p or p.endswith(".starbak") or "com.termux" in p: continue
            files.append(p)
            print(f"{t_ind()}{t_ind()}{ac('เจอ:', GRAY_D)} {p}", flush=True)
    except KeyboardInterrupt:
        proc.kill(); print(sym_line("[!]", "ยกเลิกสแกน", YELLOW))
    finally:
        timer.cancel()
    proc.wait()
    return files

def root_roblox_pkgs():
    return sorted(p for p in su_text("ls /data/data").split() if "roblox" in p.lower())

def root_launch_app(pkg):
    su(f"am force-stop {pkg}")
    su(f"monkey -p {pkg} -c android.intent.category.LAUNCHER 1")

def root_inject_file(path, new_cookie):
    data = root_fread(path)
    if not data: return None, "อ่านไฟล์ไม่ได้"
    if not COOKIE_RE.search(data): return None, "ไม่พบ cookie เดิมในไฟล์"
    nb = new_cookie.encode()
    perms, uid, gid = root_fstat(path)
    q = shlex.quote(path)
    backup = f"[ -e {q}.starbak ] || cp -f {q} {q}.starbak"        # สำรองครั้งแรกเท่านั้น ไม่ทับต้นฉบับ

    if data[:15].startswith(b"SQLite format 3"):
        tmpdir = tempfile.mkdtemp(prefix="star_")
        tmpdb = os.path.join(tmpdir, "db.sqlite")
        try:
            with open(tmpdb, "wb") as f: f.write(data)
            for ext in ("-wal", "-shm"):
                wal = root_fread(path + ext)
                if wal:
                    with open(tmpdb + ext, "wb") as f: f.write(wal)
            con = sqlite3.connect(tmpdb); cur = con.cursor(); changed = 0
            try: tables = [r[0] for r in cur.execute("SELECT name FROM sqlite_master WHERE type='table'").fetchall()]
            except Exception: tables = []
            for t in tables:
                try: cols = [r[1] for r in cur.execute(f"PRAGMA table_info('{t}')").fetchall()]
                except Exception: continue
                for col in cols:
                    try:
                        rows = cur.execute(f'SELECT rowid, "{col}" FROM "{t}" WHERE "{col}" LIKE ?',
                                           ("%_|WARNING:-DO-NOT-SHARE-THIS%",)).fetchall()
                    except Exception: continue
                    for rowid, val in rows:
                        if isinstance(val, (bytes, memoryview)):
                            param = sqlite3.Binary(COOKIE_RE.sub(lambda m: nb, bytes(val)))
                        else:
                            param = COOKIE_RE_S.sub(lambda m: new_cookie, str(val))
                        try:
                            cur.execute(f'UPDATE "{t}" SET "{col}"=? WHERE rowid=?', (param, rowid)); changed += 1
                        except Exception: pass
            if not changed:
                con.close(); return None, "SQLite: ไม่พบแถวที่แก้ได้ (อาจถูกเข้ารหัส)"
            con.commit()
            try:
                cur.execute("PRAGMA wal_checkpoint(FULL)"); cur.execute("PRAGMA journal_mode=DELETE"); con.commit()
            except Exception: pass
            con.close()
            with open(tmpdb, "rb") as f: newdata = f.read()
        except Exception as e:
            return False, f"SQLite: {type(e).__name__}"
        finally:
            shutil.rmtree(tmpdir, ignore_errors=True)
        if nb not in newdata: return False, "SQLite: แก้แล้วแต่ไม่เจอ cookie ใหม่ในไฟล์"
        su(backup); su(f"rm -f {q}-wal {q}-shm")
        if not root_fwrite(path, newdata, perms, uid, gid): return False, "SQLite: ยัดกลับไม่สำเร็จ (สิทธิ์/SELinux)"
        return True, "สำเร็จ (SQLite)"

    su(backup)
    if not root_fwrite(path, COOKIE_RE.sub(lambda m: nb, data), perms, uid, gid):
        return False, "เขียนไม่สำเร็จ (สิทธิ์/SELinux)"
    if nb not in root_fread(path): return False, "เขียนแล้วแต่ตรวจไม่เจอ"
    return True, "สำเร็จ"

def root_setup():
    m = root_load_map()
    print(sect("Root Setup", "สแกนจุดเก็บ cookie"))
    print(t_ind() + ac("เงื่อนไข: ล็อกอินมือในแอปนั้นมาแล้ว ≥1 ครั้ง", GRAY_D))
    print(t_ind() + "[1] เร็ว — เฉพาะ roblox*   [2] ละเอียด — ทั้งเครื่อง (แอปโคลน)")
    if (inp("[?] เลือก (Enter=1): ").strip() or "1") == "2":
        print(sym_line("[!]", "ไล่ทั้งเครื่อง — รอจนขึ้น 'สแกนจบ'", YELLOW))
        files = root_stream_scan("grep -rla '_|WARNING:-DO-NOT-SHARE-THIS' /data/data/ 2>/dev/null", 900)
    else:
        pkgs = root_roblox_pkgs()
        if not pkgs:
            print(sym_line("[x]", "ไม่เจอ roblox* — ใช้แอปโคลน เลือก [2] แทน", RED)); return
        print(sym_line("[!]", f"สแกน {len(pkgs)} แอป", YELLOW))
        files = root_stream_scan("grep -rla '_|WARNING:-DO-NOT-SHARE-THIS' "
                                 + " ".join(f"/data/data/{p}/" for p in pkgs) + " 2>/dev/null", 600)
    print(sect("ผล", "สแกนจบ"))
    if not files:
        print(sym_line("[x]", "ไม่เจอ cookie → ล็อกอินมือในแอปก่อน 1 ครั้ง แล้วสแกนใหม่", RED)); return
    grouped = {}
    for p in files:
        mm = re.match(r"/data/data/([^/]+)/", p)
        if mm: grouped.setdefault(mm.group(1), []).append(p)
    for pkg, fs in grouped.items():
        m.setdefault(pkg, {})["files"] = fs
        print(sym_line("[+]", f"{pkg} → {len(fs)} จุด", GREEN))
    root_save_map(m)
    print(t_branch(True) + ac(f"บันทึกแผนที่ {len(grouped)} แอป", GREEN_H))

def _pick_multi(items, prompt):
    for i, it in enumerate(items, 1): print(f"{t_ind()}  [{i}] {it}")
    s = inp(prompt).strip().lower()
    if not s: return []
    if s == "a": return list(range(len(items)))
    idxs = []
    for tok in re.split(r"[,\s]+", s):
        if tok.isdigit() and 1 <= int(tok) <= len(items) and int(tok) - 1 not in idxs:
            idxs.append(int(tok) - 1)
    return idxs

def root_switch(cfg):
    m = root_load_map()
    if not m: print(sym_line("[x]", "ยังไม่มีแผนที่ — ทำ [1] ก่อน", RED)); return
    accs = [a for a in cfg["accounts"] if a.get("cookie")]
    if not accs: print(sym_line("[x]", "ไม่มีบัญชี", RED)); return
    pkgs = sorted(m.keys())
    print(sect("Root Switch", "ฉีด cookie"))
    ai = _pick_multi([a.get("label", "?") for a in accs], "[?] บัญชี (เลข/หลายเลข/a): ")
    if not ai: print(t_branch(True) + ac("ยกเลิก", GRAY_D)); return
    pi = _pick_multi(pkgs, "[?] แอป (เลข/หลายเลข/a): ")
    if not pi: print(t_branch(True) + ac("ยกเลิก", GRAY_D)); return
    sel_accs, sel_pkgs = [accs[i] for i in ai], [pkgs[i] for i in pi]
    pairs = [(sel_accs[j % len(sel_accs)], pkg) for j, pkg in enumerate(sel_pkgs)]
    for acc, pkg in pairs:
        print(f"{t_ind()}{ac('[+]', BLUE_L)} {ac(acc.get('label', '?'), CYAN)} → {ac(pkg, GREEN_H)}")
    if inp("[?] ยืนยันฉีด (ปิดแอป → ฉีด → เปิดใหม่ · ผูกแอปให้อัตโนมัติ)? (y/n): ").strip().lower() != "y":
        print(t_branch(True) + ac("ยกเลิก", GRAY_D)); return
    n_ok = n_fail = 0
    done = set()
    for acc, pkg in pairs:
        files = (m.get(pkg) or {}).get("files") or []
        if not files: print(sym_line("[!]", f"{pkg}: ไม่มีจุดเก็บ — ข้าม", YELLOW)); continue
        if pkg not in done:
            su(f"am force-stop {pkg}"); time.sleep(1.5); done.add(pkg)
        pkg_ok = False
        for f in files:
            st, msg = root_inject_file(f, acc["cookie"])
            if st: n_ok += 1; pkg_ok = True; print(sym_line("[+]", f"{pkg} · {os.path.basename(f)} ← {acc.get('label')} — {msg}", GREEN))
            elif st is False: n_fail += 1; print(sym_line("[x]", f"{pkg} · {os.path.basename(f)} — {msg}", RED))
            else: print(sym_line("[·]", f"{pkg} · {os.path.basename(f)} — {msg}", GRAY_D))
        if pkg_ok:                                                    # ผูกบัญชี↔แอปให้เอง ให้ START ใช้ถูกตัว
            app = next((a for a in cfg["apps"] if a.get("package") == pkg), None)
            if not app:
                num = max([a["num"] for a in cfg["apps"]] or [0]) + 1
                app = {"num": num, "name": f"Roblox #{num}", "package": pkg}; cfg["apps"].append(app)
            acc["app_num"] = app["num"]
    save_cfg(cfg)
    for pkg in done:
        root_launch_app(pkg); print(sym_line("[+]", f"{pkg} → เปิดใหม่แล้ว"))
    print(t_branch(True) + ac(f"เสร็จ — สำเร็จ {n_ok} · ล้มเหลว {n_fail}", GREEN_H))

def root_menu(cfg):
    cls(); print(sect("ROOT", "Injector"))
    if not has_root():
        print(sym_line("[x]", "root ไม่ผ่าน — กดอนุญาตใน Magisk แล้วลองใหม่", RED)); ROOT["ok"] = None; return
    print(sym_line("[+]", "root พร้อม ✔", GREEN))
    print(t_ind() + "[1] สแกนจุดเก็บ cookie   [2] ฉีด cookie   [3] ดูแผนที่   [0] กลับ")
    c = inp("[?] เลือก: ").strip()
    if c == "1": root_setup()
    elif c == "2": root_switch(cfg)
    elif c == "3":
        m = root_load_map()
        for pkg, v in m.items():
            print(f"{t_ind()}{ac('[+]', BLUE_L)} {pkg} → {len(v.get('files', []))} ไฟล์")
        if not m: print(t_ind() + ac("(ยังไม่มีแผนที่)", GRAY_D))

# ════════════════════════════════════════════════════════════════
#  เมนู
# ════════════════════════════════════════════════════════════════
def show_apps(cfg):
    if not cfg["apps"]: print(t_ind() + ac("(ยังไม่มีแอป)", GRAY_D)); return
    for a in cfg["apps"]:
        print(f"{t_ind()}{ac('[+]', BLUE_L)} #{a['num']} {ac(a.get('name', ''), CYAN)} — {ac(a.get('package', ''), GRAY_D)}")

def show_accounts(cfg):
    if not cfg["accounts"]: print(t_ind() + ac("(ยังไม่มีบัญชี)", GRAY_D)); return
    for i, a in enumerate(cfg["accounts"], 1):
        app = next((x for x in cfg["apps"] if x.get("num") == a.get("app_num")), None)
        at = f"แอป #{app['num']}" if app else ac("ไม่ผูกแอป", GRAY_D)
        on = ac("ON", GREEN) if a.get("enabled", True) else ac("OFF", GRAY)
        hop = ac("hop:ON", MAGENTA) if a.get("hop") else ac("hop:off", GRAY_D)
        print(f"{t_ind()}[{i}] {ac(a.get('label', '?'), CYAN)} {on} | place {a.get('place_id') or '-'} | {at} | {hop}")

def pick_app(cfg, prompt="[?] เลือกแอป #(เลข, Enter ไม่ผูก): "):
    if not cfg["apps"]:
        print(sym_line("[!]", "ยังไม่มีแอป — ไปสแกนที่ [3] ก่อน", YELLOW)); return None
    show_apps(cfg)
    s = inp(prompt).strip()
    return int(s) if s.isdigit() and any(a.get("num") == int(s) for a in cfg["apps"]) else None

def choose_app_map(cfg, count):
    if not cfg["apps"]:
        print(sym_line("[!]", "ยังไม่มีแอป — ไปสแกนที่ [3] ก่อน", YELLOW)); return [None] * count
    show_apps(cfg)
    print(ac("  1,2,1 = เลือกแอปตามลำดับ | a = หมุนเวียน | Enter = ไม่ผูก", GRAY))
    s = inp(f"[?] ผูกแอปให้ {count} ไอดี: ").strip().lower()
    valid = {a["num"] for a in cfg["apps"]}
    if not s: return [None] * count
    if s == "a": return [cfg["apps"][i % len(cfg["apps"])]["num"] for i in range(count)]
    nums = [int(x) for x in re.split(r"[,\s]+", s) if x.isdigit() and int(x) in valid]
    return [None] * count if not nums else [nums[i] if i < len(nums) else nums[-1] for i in range(count)]

def ask_place_for_missing(cfg):
    if all(a.get("place_id") for a in cfg["accounts"]): return
    pid = inp("[?] ตั้ง place id ให้ไอดีที่ยังไม่มีแมพ (Enter ข้าม): ").strip()
    if pid.isdigit():
        for a in cfg["accounts"]:
            if not a.get("place_id"): a["place_id"] = int(pid)
        save_cfg(cfg); print(sym_line("[+]", "ตั้งแมพแล้ว"))

def bulk_add(cfg, pairs):
    if not pairs: print(sym_line("[x]", "ไม่พบ cookie ที่ใช้ได้", RED)); return 0
    print(sym_line("[*]", f"พบ cookie {len(pairs)} ตัว — ตรวจกับ Roblox..."))
    appmap = choose_app_map(cfg, len(pairs))
    added = 0
    for i, (lb, ck) in enumerate(pairs):
        me, new = add_account(cfg, lb, ck, appmap[i])
        if me:
            added += 1
            print(f"  {ac('[+]', BLUE_L)} {ac(me['name'], GREEN)}{'' if new else ac(' (อัปเดต cookie เดิม)', GRAY_D)}")
        else:
            print(f"  {ac('[!]', YELLOW)} {lb or ck[:24] + '..'} cookie ใช้ไม่ได้ — ข้าม")
    if added: save_cfg(cfg); ask_place_for_missing(cfg)
    print(t_branch(True) + ac(f"สำเร็จ {added}/{len(pairs)}", GREEN_H))
    return added

def menu_add_quick(cfg):
    cls(); print(sect("Quick Login", "ช่องทางทางการ · ไม่ใช้รหัสผ่าน"))
    print(t_ind() + "บนเครื่องที่ล็อกอินบัญชีนั้นอยู่: Roblox → Settings → Quick Log In")
    print(t_ind() + "ใส่โค้ดที่ขึ้นด้านล่าง แล้วกดยืนยัน (Ctrl+C ยกเลิก)")
    try:
        ck, err = quick_login(
            lambda code: print(f"\n      {ac('CODE', GRAY_D)}  {ac(code, GREEN_H)}\n"),
            lambda left, st: print(f"\r{t_ind()}รอยืนยัน... {left:3d}s [{st}]  ", end="", flush=True))
    except KeyboardInterrupt:
        print(); print(t_branch(True) + ac("ยกเลิก", GRAY_D)); return
    print()
    if not ck: print(sym_line("[x]", err, RED)); return
    me, new = add_account(cfg, None, ck)
    if not me: print(sym_line("[x]", "cookie ที่ได้ใช้ไม่ได้", RED)); return
    cfg["accounts"][-1 if new else next(i for i, a in enumerate(cfg["accounts"]) if a.get("user_id") == me["id"])]["app_num"] = pick_app(cfg)
    save_cfg(cfg); ask_place_for_missing(cfg)
    print(sym_line("[+]", f"{me['name']} — เซฟแล้ว"))

def menu_add_cookie(cfg):
    cls(); print(t_ind() + "[a] วางเดี่ยว | [b] ไฟล์ | [c] หลายไอดี | [t] วิธีหา cookie")
    sub = inp("[?] เลือก: ").strip().lower()
    if sub == "t":
        print(t_ind() + ac("มือถือ: Kiwi Browser + Cookie-Editor → roblox.com → .ROBLOSECURITY → Copy", GREEN))
        print(t_ind() + ac("PC: F12 → Application → Cookies · ค่าต้องขึ้นต้น _|WARNING:...", GREEN))
    elif sub == "a":
        ck = extract_cookie(inp("[?] วาง cookie: ").strip().strip("\"'"))
        if not ck: print(sym_line("[x]", "ไม่ใช่ cookie — ลอง [t]", RED)); return
        me, new = add_account(cfg, None, ck)
        if not me: print(sym_line("[x]", "cookie ใช้ไม่ได้", RED)); return
        acc = next(a for a in cfg["accounts"] if a.get("user_id") == me["id"])
        acc["app_num"] = pick_app(cfg) or acc.get("app_num")
        save_cfg(cfg); ask_place_for_missing(cfg)
        print(sym_line("[+]", f"{'เพิ่ม' if new else 'อัปเดต'} {me['name']} แล้ว"))
    elif sub == "b":
        path = inp("[?] path ไฟล์: ").strip().strip("\"'")
        if not os.path.isfile(path): print(sym_line("[x]", "ไม่เจอไฟล์ (termux-setup-storage?)", RED)); return
        bulk_add(cfg, parse_cookie_file(path))
    elif sub == "c":
        print(t_ind() + "บรรทัดละตัว: ชื่อ|cookie — พิมพ์ . เพื่อจบ")
        lines = []
        while True:
            try: ln = inp()
            except (EOFError, KeyboardInterrupt): break
            if ln.strip() == ".": break
            if ln.strip(): lines.append(ln)
        bulk_add(cfg, parse_cookie_text("\n".join(lines)))

def menu_apps(cfg):
    cls(); print(sect("Apps")); show_apps(cfg)
    print(t_ind() + "[a] สแกน | [b] เพิ่มเอง | [r] แก้ชื่อ | [d] ลบ")
    sub = inp("[?] เลือก: ").strip().lower()
    nxt = lambda: max([a["num"] for a in cfg["apps"]] or [0]) + 1
    if sub == "a":
        found = [p for p in pm_candidates() if not any(a.get("package") == p for a in cfg["apps"])]
        if not found: print(sym_line("[x]", "ไม่เจอแอปใหม่ — เพิ่มเอง [b]", RED)); return
        for p in found:
            n = nxt(); nm = inp(f"[?] ชื่อ {p} [Roblox #{n}]: ").strip() or f"Roblox #{n}"
            cfg["apps"].append({"num": n, "name": nm, "package": p})
        save_cfg(cfg); print(sym_line("[+]", f"บันทึก {len(found)} แอป"))
    elif sub == "b":
        pkg = inp("[?] package: ").strip()
        if pkg:
            n = nxt(); nm = inp(f"[?] ชื่อ [Roblox #{n}]: ").strip() or f"Roblox #{n}"
            cfg["apps"].append({"num": n, "name": nm, "package": pkg}); save_cfg(cfg)
            print(sym_line("[+]", "บันทึกแล้ว"))
    elif sub in ("r", "d") and cfg["apps"]:
        s = inp("[?] แอป #(เลข): ").strip()
        app = next((a for a in cfg["apps"] if str(a["num"]) == s), None)
        if not app: return
        if sub == "r":
            nm = inp(f"[?] ชื่อใหม่ ({app['name']}): ").strip()
            if nm: app["name"] = nm; save_cfg(cfg); print(sym_line("[+]", "บันทึกแล้ว"))
        else:
            for a in cfg["accounts"]:
                if a.get("app_num") == app["num"]: a["app_num"] = None
            cfg["apps"].remove(app); save_cfg(cfg); print(sym_line("[+]", "ลบแล้ว"))

def manage_one(cfg, acc):
    while True:
        app = next((a for a in cfg["apps"] if a.get("num") == acc.get("app_num")), None)
        print(f"\n{t_ind()}▸ {ac(acc.get('label', '?'), CYAN)} | {('#%s %s' % (app['num'], app['name'])) if app else 'ไม่ผูกแอป'}"
              f" | hop {'ON' if acc.get('hop') else 'off'} | place {acc.get('place_id') or '-'} | {'เฝ้า' if acc.get('enabled', True) else 'ปิด'}")
        print(t_ind() + "[1] ชื่อ [2] แอป [3] แมพ [4] hop [5] เปิด/ปิดเฝ้า [6] cookie")
        print(t_ind() + "[7] จอยเพื่อน [8] ทดสอบเปิดเกม [9] logout [d] ลบ [0] กลับ")
        s = inp("[?] เลือก: ").strip().lower()
        if s == "0": return
        elif s == "1":
            nm = inp(f"[?] ชื่อใหม่ ({acc['label']}): ").strip()
            if not nm: continue
            if any(a is not acc and a.get("label") == nm for a in cfg["accounts"]): print(sym_line("[x]", "ชื่อซ้ำ", RED)); continue
            acc["label"] = nm; save_cfg(cfg); print(sym_line("[+]", "บันทึกแล้ว"))
        elif s == "2":
            acc["app_num"] = pick_app(cfg, "[?] แอป #(เลข, Enter ถอดผูก): "); save_cfg(cfg); print(sym_line("[+]", "บันทึกแล้ว"))
        elif s == "3":
            pid = inp(f"[?] place id ({acc.get('place_id') or '-'}): ").strip()
            if pid.isdigit(): acc["place_id"] = int(pid); save_cfg(cfg); print(sym_line("[+]", "บันทึกแล้ว"))
            else: print(sym_line("[x]", "ตัวเลขเท่านั้น", RED))
        elif s == "4":
            acc["hop"] = not acc.get("hop", False); save_cfg(cfg); print(sym_line("[+]", f"hop = {'ON' if acc['hop'] else 'off'}"))
        elif s == "5":
            acc["enabled"] = not acc.get("enabled", True); save_cfg(cfg); print(sym_line("[+]", "เฝ้า" if acc["enabled"] else "ปิดเฝ้า"))
        elif s == "6":
            ck = extract_cookie(inp("[?] วาง cookie ใหม่: ").strip().strip("\"'"))
            me = whoami(ck) if ck else None
            if not me: print(sym_line("[x]", "cookie ใช้ไม่ได้", RED)); continue
            acc["cookie"], acc["user_id"] = ck, me["id"]; save_cfg(cfg); print(sym_line("[+]", f"เปลี่ยนแล้ว ({me['name']})"))
        elif s == "7":
            me = whoami(acc["cookie"])
            fuid = uid_by_username(inp("[?] ชื่อเพื่อน: ").strip())
            if not me or not fuid: print(sym_line("[x]", "หาไม่เจอ/cookie ตาย", RED)); continue
            kind, p = presence_of(Http(acc["cookie"]), fuid)
            if kind != "ok" or p.get("userPresenceType") != IN_GAME: print(sym_line("[x]", "เพื่อนไม่ได้เล่นอยู่/ซ่อนสถานะ", RED)); continue
            place = p.get("rootPlaceId") or p.get("placeId")
            acc["place_id"] = place; save_cfg(cfg)
            launch_game(app, place, p.get("gameId")); print(sym_line("[+]", f"เข้าเซิร์ฟเพื่อน · place {place}"))
        elif s == "8":
            if not acc.get("place_id"): print(sym_line("[x]", "ยังไม่มี place id", RED)); continue
            ok = launch_game(app, acc["place_id"]); print(sym_line("[+]" if ok else "[x]", "สั่งเปิดแล้ว" if ok else "สั่งไม่ติด", GREEN if ok else RED))
        elif s == "9":
            if inp(f"[?] logout ปิด session ของ {acc['label']} ถาวร — พิมพ์ชื่อยืนยัน: ").strip() != acc["label"]:
                print(sym_line("[x]", "ยืนยันไม่ตรง", RED)); continue
            ok, code = logout_session(acc["cookie"])
            print(sym_line("[+]" if ok else "[x]", f"logout {'สำเร็จ' if ok else 'ไม่สำเร็จ'} (HTTP {code})", GREEN if ok else RED))
            if ok or inp("[?] ลบออกจาก config ไหม? (y/n): ").strip().lower() == "y":
                cfg["accounts"].remove(acc); save_cfg(cfg); return
        elif s == "d":
            if inp(f"[?] ลบ {acc['label']}? (y/n): ").strip().lower() == "y":
                cfg["accounts"].remove(acc); save_cfg(cfg); print(sym_line("[+]", "ลบแล้ว")); return

def manage_accounts(cfg):
    while True:
        cls(); show_accounts(cfg)
        if not cfg["accounts"]: return
        print("\n  [เลข] จัดการ 1 บัญชี · [h] เปิด/ปิด hop หลายบัญชี · [c] ตรวจ cookie ทุกไอดี · [0] กลับ")
        s = inp("[?] เลือก: ").strip().lower()
        if s == "0" or not s: return
        if s == "c":
            for a in cfg["accounts"]:
                me = whoami(a["cookie"])
                print(f"{t_ind()}{ac('[+]', BLUE_L) if me else ac('[x]', RED)} {ac(a.get('label', '?'), CYAN)} "
                      f"{ac(me['name'], GREEN) + ' มีชีวิต' if me else ac('cookie ตาย/เน็ตมีปัญหา', RED)}")
        elif s == "h":
            print(t_ind() + ac("hop = สลับเซิร์ฟเวอร์เองถ้า rejoin เดิมไม่ติดหลายรอบ", GRAY_D))
            labels = [f"{a.get('label', '?')} (hop:{'ON' if a.get('hop') else 'off'})" for a in cfg["accounts"]]
            idxs = _pick_multi(labels, "[?] เลือกบัญชี (เลข/หลายเลข คั่นด้วยช่องว่างหรือจุลภาค/a=ทั้งหมด): ")
            if not idxs: print(t_branch(True) + ac("ยกเลิก", GRAY_D)); continue
            mode = inp("[?] ตั้งเป็น [1] เปิด  [0] ปิด  [x] สลับค่าเดิม: ").strip().lower()
            for i in idxs:
                a = cfg["accounts"][i]
                a["hop"] = (not a.get("hop", False)) if mode == "x" else (mode == "1")
                print(f"{t_ind()}{ac(a.get('label', '?'), CYAN)} → hop {'ON' if a['hop'] else 'off'}")
            save_cfg(cfg)
        elif s.isdigit() and 1 <= int(s) <= len(cfg["accounts"]):
            manage_one(cfg, cfg["accounts"][int(s) - 1])

def menu_settings(cfg):
    cls(); print(sect("Settings"))
    print(t_ind() + f"webhook: {cfg.get('webhook') or ac('(ยังไม่ตั้ง)', GRAY_D)}")
    print(t_ind() + f"รายงานทุก {cfg['report_min']} นาที · เช็กทุก {cfg['poll']}s · รีเฟรชแอปทุก {cfg['restart_min'] or 'ปิด'} นาที")
    print(t_ind() + "[1] webhook [2] ทดสอบ/ส่งรายงาน [3] รอบรายงาน [4] ความถี่เช็ก(วิ) [5] รีเฟรชแอปทุก N นาที(0=ปิด)")
    print(t_ind() + "[6] backup config [7] สถิติ [8] ล้างข้อมูลทั้งหมด")
    s = inp("[?] เลือก: ").strip()
    def num(key, lo, hi, label):
        t = inp(f"[?] {label}: ").strip()
        if t.isdigit() and lo <= int(t) <= hi: cfg[key] = int(t); save_cfg(cfg); print(sym_line("[+]", "บันทึกแล้ว"))
        else: print(sym_line("[x]", f"ใส่ {lo}-{hi}", RED))
    if s == "1": cfg["webhook"] = inp("[?] URL: ").strip(); save_cfg(cfg); print(sym_line("[+]", "บันทึกแล้ว"))
    elif s == "2": send_report(cfg, "ทดสอบ"); notify(cfg, "", "STAR test", "ทำงานปกติ", 0x2ecc71); print(sym_line("[+]", "ส่งแล้ว"))
    elif s == "3": num("report_min", 0, 1440, "ทุกกี่นาที (0=ปิด)")
    elif s == "4": num("poll", 10, 120, "ทุกกี่วินาที")
    elif s == "5": num("restart_min", 0, 1440, "ทุกกี่นาที (0=ปิด)")
    elif s == "6":
        save_cfg(cfg); b = os.path.join(HERE, "star_config.backup.json"); shutil.copyfile(CONFIG, b)
        try: os.chmod(b, 0o600)
        except Exception: pass
        print(sym_line("[+]", f"บันทึก {b}"))
    elif s == "7": print(t_ind() + ac(f"{TOTALS['rejoins']} rejoins, {TOTALS['hops']} hops, {TOTALS['alerts']} alerts", GREEN_H))
    elif s == "8":
        if inp("[?] พิมพ์ RESET เพื่อลบ config ทั้งหมด: ").strip() == "RESET":
            for p in (CONFIG, CONFIG + ".bak", ROOTMAP):
                if os.path.exists(p): os.remove(p)
            cfg.clear(); cfg.update(_norm({})); print(sym_line("[*]", "ลบแล้ว"))

# ════════════════════════════════════════════════════════════════
#  TUNE — กันตาย / ประหยัดแรม / Delta AutoExec / ลดกราฟิก / Boost เครื่อง
# ════════════════════════════════════════════════════════════════
def rsh(cmd, timeout=30):
    """รันคำสั่ง shell — มี root ใช้ su ไม่มีก็รันธรรมดา"""
    if has_root(): return su_text(cmd, timeout)
    return sh(["sh", "-c", cmd], timeout=timeout)[1]

def mem_info():
    d = {}
    try:
        with open("/proc/meminfo") as f:
            for l in f:
                k, v = l.split(":", 1); d[k] = int(v.split()[0]) // 1024
    except Exception: pass
    return d.get("MemTotal", 0), d.get("MemAvailable", 0)

def mem_line():
    tot, av = mem_info()
    return f"RAM ว่าง {av} / {tot} MB" if tot else "อ่านแรมไม่ได้"

def wake_lock(on=True):
    exe = shutil.which("termux-wake-lock" if on else "termux-wake-unlock")
    if exe: sh([exe], timeout=10); return True
    return False

def harden_self():
    """ให้ตัวโปรแกรมเบา + ไม่ตายเพราะปิดเทอร์มินัล/pipe พัง"""
    for s in ("SIGHUP", "SIGPIPE"):
        try: signal.signal(getattr(signal, s), signal.SIG_IGN)
        except Exception: pass
    try: os.nice(5)
    except Exception: pass
    sys.setswitchinterval(0.05)
    gc.set_threshold(700, 10, 10)

def all_pkgs(cfg):
    return [a["package"] for a in cfg["apps"] if a.get("package")]

def protect(cfg):
    """root: ตั้ง oom_score_adj ให้ Termux/Roblox ถูก Android ฆ่าทีหลังสุด"""
    if not has_root(): return False
    items = [("com.termux", -900)] + [(p, -500) for p in all_pkgs(cfg)]
    script = "; ".join(f"for i in $(pidof {shlex.quote(p)}); do echo {adj} > /proc/$i/oom_score_adj; done" for p, adj in items)
    su(script, 20); return True

KEEP_HINT = ("roblox", "delta", "termux", "inputmethod", "keyboard", "launcher", "vending", "gms")

def bg_victims(cfg):
    out = rsh("pm list packages -3", 30)
    keep = set(all_pkgs(cfg))
    pk = [l.replace("package:", "").strip() for l in out.splitlines() if l.startswith("package:")]
    return [p for p in pk if p and p not in keep and not any(h in p.lower() for h in KEEP_HINT)]

def run_cmd(cmd, timeout=30):
    """รันคำสั่งเดียว → (returncode, ข้อความผลลัพธ์)"""
    if has_root():
        r = su(cmd, timeout)
        return r.returncode, ((r.stdout or b"").decode(errors="ignore") + (r.stderr or b"").decode(errors="ignore")).strip()
    rc, out = sh(["sh", "-c", cmd], timeout=timeout); return rc, out.strip()

def run_steps(steps, timeout=60, show_ok=True):
    """รันทีละคำสั่งแยกกัน + โชว์ผลแต่ละคำสั่ง → (สำเร็จ, พลาด)"""
    ok = bad = 0
    for label, cmd in steps:
        rc, out = run_cmd(cmd, timeout)
        first = (out.splitlines() or [""])[0][:34]
        if rc == 0 and "exception" not in out.lower() and not out.lower().startswith("error"):
            ok += 1
            if show_ok: print(sym_line("[+]", label, GREEN) + (ac(f"  {first}", GRAY_D) if first else ""))
        else:
            bad += 1; print(sym_line("[x]", label, RED) + ac(f"  {first or 'rc=' + str(rc)}", GRAY_D))
    return ok, bad

def free_ram(cfg, kill_bg=False, report=False):
    before = mem_info()[1]; killed = 0
    base = [("sync", "sync"), ("drop_caches", "echo 3 > /proc/sys/vm/drop_caches"),
            ("trim-caches", "pm trim-caches 99999999999")]
    kills = []
    if kill_bg:
        v = bg_victims(cfg); killed = len(v)
        kills = [(f"force-stop {p}", f"am force-stop {shlex.quote(p)}") for p in v]
    if report:
        run_steps(base, 120)
        if kills:
            ok, bad = run_steps(kills, 30, show_ok=len(kills) <= 8)
            print(sym_line("[+]", f"force-stop สำเร็จ {ok}/{len(kills)}" + (f" · พลาด {bad}" if bad else ""), GREEN if not bad else YELLOW))
    else:
        rsh("; ".join(c for _, c in base + kills), 120)
    gc.collect()
    return before, mem_info()[1], killed

def survival_setup(cfg, report=False):
    pk = ["com.termux"] + all_pkgs(cfg)
    steps = [("ปิด phantom monitor", "settings put global settings_enable_monitor_phantom_procs false"),
             ("ล็อก device_config", "device_config set_sync_disabled_for_tests persistent"),
             ("max_phantom_processes", "device_config put activity_manager max_phantom_processes 2147483647")]
    for p in pk:
        q = shlex.quote(p)
        steps += [(f"whitelist แบต {p}", f"dumpsys deviceidle whitelist +{p}"),
                  (f"RUN_IN_BACKGROUND {p}", f"cmd appops set {q} RUN_IN_BACKGROUND allow"),
                  (f"RUN_ANY_IN_BACKGROUND {p}", f"cmd appops set {q} RUN_ANY_IN_BACKGROUND allow")]
    if report:
        ok, bad = run_steps(steps, 30)
        print(sym_line("[+]" if not bad else "[!]", f"สำเร็จ {ok}/{len(steps)} คำสั่ง" + (f" · พลาด {bad}" if bad else ""), GREEN if not bad else YELLOW))
    else:
        rsh("; ".join(c for _, c in steps), 60)

def verify_survival(cfg):
    """อ่านค่ากลับมาให้เห็นว่าตั้งติดจริงไหม"""
    for label, cmd in [("phantom monitor", "settings get global settings_enable_monitor_phantom_procs"),
                       ("max_phantom_processes", "device_config get activity_manager max_phantom_processes")]:
        print(t_ind() + f"{label}: {run_cmd(cmd, 15)[1] or '-'}")
    for p in ["com.termux"] + all_pkgs(cfg):
        out = run_cmd(f"for i in $(pidof {shlex.quote(p)}); do cat /proc/$i/oom_score_adj; done", 10)[1]
        print(t_ind() + f"{p}: oom_adj {out.replace(chr(10), ', ') or 'ยังไม่รัน'}")

class Maint(threading.Thread):
    """เบื้องหลังระหว่างเฝ้า: ป้องกัน process ถูกฆ่า + ล้างแรมตามรอบ (เบา ไม่ฆ่าแอปอื่น)"""
    def __init__(self, cfg):
        super().__init__(daemon=True, name="maint"); self.cfg = cfg
    def run(self):
        tick = 0
        if stop.wait(20): return
        while not stop.is_set():
            try:
                protect(self.cfg); tick += 1
                tm = int(self.cfg.get("trim_min", 10) or 0)
                if tm and tick % tm == 0:
                    b, a, _ = free_ram(self.cfg)
                    dlog("MAINT", f"ล้างแคช {b}→{a} MB ว่าง", "dim")
            except Exception as e: flog(f"maint {e!r}")
            if stop.wait(60): return

# ---------- Delta AutoExec ----------
DELTA_CANDS = ["/storage/emulated/0/Delta/Autoexecute", "/storage/emulated/0/Delta/Autoexec",
               "/storage/emulated/0/Delta/autoexec", "/storage/emulated/0/Delta/AutoExecute",
               "/sdcard/Delta/Autoexecute", "/storage/emulated/0/Delta/Scripts/Autoexecute"]

def delta_dir(cfg):
    if cfg.get("delta_dir"): return cfg["delta_dir"]
    for p in DELTA_CANDS:
        if os.path.isdir(p): return p
    base = "/storage/emulated/0/Delta"
    try:
        for n in os.listdir(base):
            if "auto" in n.lower() and os.path.isdir(os.path.join(base, n)): return os.path.join(base, n)
    except Exception: pass
    return None

def put_file(path, text):
    try:
        os.makedirs(os.path.dirname(path), exist_ok=True)
        with open(path, "w", encoding="utf-8") as f: f.write(text)
        return True
    except Exception: pass
    if has_root():
        tmp = os.path.join(tempfile.gettempdir(), "star_" + uuid.uuid4().hex[:6])
        try:
            with open(tmp, "w", encoding="utf-8") as f: f.write(text)
            su(f"mkdir -p {shlex.quote(os.path.dirname(path))}; cp {tmp} {shlex.quote(path)}; chmod 666 {shlex.quote(path)}", 15)
            return True
        except Exception: pass
        finally:
            try: os.remove(tmp)
            except Exception: pass
    return False

def list_scripts(d):
    try: return sorted(n for n in os.listdir(d) if not n.startswith("."))
    except Exception:
        return sorted(n for n in su_text(f"ls {shlex.quote(d)}", 10).split() if n) if has_root() else []

def del_file(path):
    try: os.remove(path); return True
    except Exception: pass
    if has_root(): su(f"rm -f {shlex.quote(path)}", 10); return True
    return False

def safe_name(n):
    n = re.sub(r"[^\w.\-]", "_", n.strip()) or "script"
    return n if n.lower().endswith((".lua", ".txt")) else n + ".lua"

LUA_LITE = r'''-- STAR FPS Lite : ลดกราฟิกแบบปลอดภัย (ไม่ลบแมพ)
local RS = game:GetService("RunService")
pcall(function() settings().Rendering.QualityLevel = 1 end)
if setfpscap then pcall(setfpscap, 30) end
local L = game:GetService("Lighting")
pcall(function() L.GlobalShadows = false; L.FogEnd = 9e9; L.ShadowSoftness = 0 end)
for _, v in ipairs(L:GetChildren()) do
  if v:IsA("PostEffect") or v:IsA("Atmosphere") or v:IsA("Clouds") then pcall(function() v:Destroy() end) end
end
pcall(function()
  local T = workspace.Terrain
  T.WaterWaveSize, T.WaterWaveSpeed, T.WaterReflectance, T.WaterTransparency = 0, 0, 0, 1
  if sethiddenproperty then sethiddenproperty(T, "Decoration", false) end
end)
local function lite(v)
  if v:IsA("ParticleEmitter") or v:IsA("Trail") or v:IsA("Beam") or v:IsA("Smoke") or v:IsA("Fire") or v:IsA("Sparkles") then v.Enabled = false
  elseif v:IsA("BasePart") then v.CastShadow = false; v.Reflectance = 0; v.Material = Enum.Material.SmoothPlastic end
end
task.spawn(function()
  for i, v in ipairs(game:GetDescendants()) do pcall(lite, v); if i % 300 == 0 then task.wait() end end
end)
game.DescendantAdded:Connect(function(v) task.defer(pcall, lite, v) end)
'''

LUA_HEAVY = r'''-- STAR FPS Extreme : ลบภูเขา/เทอร์เรน/เท็กซ์เจอร์ ทุกอย่างที่กินแรม
local DISABLE_3D = __D3__   -- true = จอดำ ประหยัดสุด
local RS = game:GetService("RunService")
pcall(function() settings().Rendering.QualityLevel = 1 end)
if setfpscap then pcall(setfpscap, 15) end
local L = game:GetService("Lighting")
pcall(function() L.GlobalShadows = false; L.FogEnd = 9e9; L.Brightness = 1 end)
for _, v in ipairs(L:GetChildren()) do
  pcall(function() v:Destroy() end)
end
pcall(function() workspace.Terrain:Clear() end)   -- ลบภูเขา/พื้น Terrain ทั้งหมด
local function nuke(v)
  if v:IsA("ParticleEmitter") or v:IsA("Trail") or v:IsA("Beam") or v:IsA("Smoke") or v:IsA("Fire") or v:IsA("Sparkles") or v:IsA("Decal") or v:IsA("Texture") or v:IsA("SurfaceAppearance") or v:IsA("PostEffect") then
    v:Destroy()
  elseif v:IsA("MeshPart") then v.TextureID = ""; v.CastShadow = false; v.Material = Enum.Material.SmoothPlastic; v.Reflectance = 0
  elseif v:IsA("BasePart") then v.CastShadow = false; v.Material = Enum.Material.SmoothPlastic; v.Reflectance = 0 end
end
task.spawn(function()
  for i, v in ipairs(game:GetDescendants()) do pcall(nuke, v); if i % 300 == 0 then task.wait() end end
  if DISABLE_3D then pcall(function() RS:Set3dRenderingEnabled(false) end) end
end)
game.DescendantAdded:Connect(function(v) task.defer(pcall, nuke, v) end)
'''

LUA_CLAY = r'''-- STAR CLAY : กราฟิกดินน้ำมัน — ปิดเอฟเฟกต์/แอนิเมชัน/เท็กซ์เจอร์/เสียง ลดแลคสุด
local Players = game:GetService("Players")
local L = game:GetService("Lighting")
local LP = Players.LocalPlayer
local ANIM_SELF = __AS__   -- true = ปิดแอนิเมชันตัวเราด้วย
pcall(function() settings().Rendering.QualityLevel = 1 end)
pcall(function() settings().Rendering.MeshPartDetailLevel = Enum.MeshPartDetailLevel.Level04 end)
pcall(function()
  local g = UserSettings():GetService("UserGameSettings")
  g.SavedQualityLevel = Enum.SavedQualitySetting.QualityLevel1; g.MasterVolume = 0
end)
if setfpscap then pcall(setfpscap, 30) end
pcall(function() L.GlobalShadows = false; L.FogEnd = 9e9; L.Brightness = 2; L.ShadowSoftness = 0
  L.EnvironmentDiffuseScale = 0; L.EnvironmentSpecularScale = 0 end)
pcall(function() if sethiddenproperty then sethiddenproperty(L, "Technology", Enum.Technology.Compatibility) end end)
for _, v in ipairs(L:GetChildren()) do
  if v:IsA("PostEffect") or v:IsA("Atmosphere") or v:IsA("Clouds") or v:IsA("Sky") then pcall(function() v:Destroy() end) end
end
pcall(function()
  local T = workspace.Terrain
  T.WaterWaveSize, T.WaterWaveSpeed, T.WaterReflectance, T.WaterTransparency = 0, 0, 0, 1
  if sethiddenproperty then sethiddenproperty(T, "Decoration", false) end
end)
local function mine(v) return LP and LP.Character and v:IsDescendantOf(LP.Character) end
local function clay(v)
  if v:IsA("ParticleEmitter") or v:IsA("Trail") or v:IsA("Beam") or v:IsA("Smoke") or v:IsA("Fire")
    or v:IsA("Sparkles") or v:IsA("Decal") or v:IsA("Texture") or v:IsA("SurfaceAppearance")
    or v:IsA("PostEffect") or v:IsA("Clothing") or v:IsA("ShirtGraphic") or v:IsA("Highlight") then
    v:Destroy()
  elseif v:IsA("Light") then v.Enabled = false
  elseif v:IsA("Explosion") then v.Visible = false; v.BlastPressure = 0
  elseif v:IsA("Sound") then v.Volume = 0; v:Stop()
  elseif v:IsA("Accessory") then if not mine(v) then v:Destroy() end
  elseif v:IsA("Humanoid") then v.DisplayDistanceType = Enum.HumanoidDisplayDistanceType.None
  elseif v:IsA("Animator") then
    local own = LP and LP.Character and v:IsDescendantOf(LP.Character)
    if own and not ANIM_SELF then return end
    for _, t in ipairs(v:GetPlayingAnimationTracks()) do t:Stop(0) end
    v.AnimationPlayed:Connect(function(t) pcall(function() t:Stop(0) end) end)
  elseif v:IsA("BasePart") and not v:IsA("Terrain") then
    v.CastShadow = false; v.Reflectance = 0; v.Material = Enum.Material.SmoothPlastic
    if v:IsA("MeshPart") then v.TextureID = ""; v.RenderFidelity = Enum.RenderFidelity.Performance end
  end
end
task.spawn(function()
  for i, v in ipairs(game:GetDescendants()) do pcall(clay, v); if i % 300 == 0 then task.wait() end end
end)
game.DescendantAdded:Connect(function(v) task.defer(pcall, clay, v) end)
'''

LUA_FPSMETER = r'''-- STAR FPS Meter : ตัวเลข FPS มุมจอ ลากย้ายได้ แตะเพื่อย่อ/ขยาย
local Players = game:GetService("Players")
local RS = game:GetService("RunService")
local UIS = game:GetService("UserInputService")
local lp = Players.LocalPlayer
local gui = Instance.new("ScreenGui")
gui.Name = "STAR_FPSMeter"; gui.ResetOnSpawn = false; gui.IgnoreGuiInset = true
gui.DisplayOrder = 2147483647
gui.Parent = lp:WaitForChild("PlayerGui")

local box = Instance.new("TextButton")
box.Size = UDim2.new(0, 86, 0, 30)
box.Position = UDim2.new(1, -94, 0, 8)   -- มุมขวาบน ย้ายได้
box.BackgroundColor3 = Color3.new(0, 0, 0); box.BackgroundTransparency = 0.35
box.BorderSizePixel = 0; box.AutoButtonColor = false
box.Font = Enum.Font.GothamBold; box.TextSize = 16; box.TextColor3 = Color3.new(1, 1, 1)
box.Text = "FPS --"; box.ZIndex = 2147483647
box.Parent = gui
local corner = Instance.new("UICorner"); corner.CornerRadius = UDim.new(0, 8); corner.Parent = box

-- ลากย้ายตำแหน่ง
local dragging, dragStart, startPos = false, nil, nil
box.InputBegan:Connect(function(io)
  if io.UserInputType == Enum.UserInputType.MouseButton1 or io.UserInputType == Enum.UserInputType.Touch then
    dragging = true; dragStart = io.Position; startPos = box.Position
  end
end)
box.InputEnded:Connect(function(io)
  if io.UserInputType == Enum.UserInputType.MouseButton1 or io.UserInputType == Enum.UserInputType.Touch then dragging = false end
end)
UIS.InputChanged:Connect(function(io)
  if dragging and (io.UserInputType == Enum.UserInputType.MouseMovement or io.UserInputType == Enum.UserInputType.Touch) then
    local d = io.Position - dragStart
    box.Position = UDim2.new(startPos.X.Scale, startPos.X.Offset + d.X, startPos.Y.Scale, startPos.Y.Offset + d.Y)
  end
end)

-- สีเขียว/เหลือง/แดง ตามค่า FPS
local n, acc = 0, 0
RS.Heartbeat:Connect(function(dt)
  n = n + 1; acc = acc + dt
  if acc >= 0.5 then
    local fps = math.floor(n / acc + 0.5)
    box.Text = "FPS " .. fps
    box.TextColor3 = fps >= 45 and Color3.fromRGB(90, 230, 120)
                   or fps >= 25 and Color3.fromRGB(255, 210, 80)
                   or Color3.fromRGB(255, 90, 90)
    n, acc = 0, 0
  end
end)
'''

def menu_delta(cfg):
    while True:
        cls(); d = delta_dir(cfg)
        print(sect("Delta AutoExec", d or "ยังไม่พบโฟลเดอร์"))
        print(t_ind() + "[1] ตั้งโฟลเดอร์เอง [2] รายการสคริปต์ [3] วางโค้ด [4] จาก URL (loadstring) [5] จากไฟล์")
        print(t_ind() + "[6] FPS Lite (ลดกราฟิกปลอดภัย) [7] FPS Extreme (ลบภูเขา/เท็กซ์เจอร์)")
        print(t_ind() + "[f] ติดตั้งตัวโชว์ FPS มุมจอ (ลากย้ายได้)")
        print(t_ind() + "[8] ลบสคริปต์ 1 ไฟล์ [9] ลบทั้งหมด [0] กลับ")
        s = inp("[?] เลือก: ").strip()
        if s in ("", "0"): return
        if s == "1":
            p = inp("[?] path (Enter=auto): ").strip(); cfg["delta_dir"] = p; save_cfg(cfg); continue
        if not d:
            print(sym_line("[x]", "ไม่พบโฟลเดอร์ Delta — รัน termux-setup-storage แล้วเปิด Delta 1 ครั้ง หรือกด [1] ใส่ path เอง", RED)); continue
        if s == "2":
            ls = list_scripts(d)
            for i, n in enumerate(ls, 1): print(t_ind() + f"{i}. {n}")
            if not ls: print(t_ind() + ac("(ว่าง)", GRAY_D))
        elif s == "3":
            name = inp("[?] ชื่อไฟล์: ").strip(); print(sym_line("[*]", "วางโค้ด จบด้วยบรรทัดที่พิมพ์ EOF"))
            lines = []
            while True:
                l = inp("")
                if l.strip() == "EOF": break
                lines.append(l)
            ok = put_file(os.path.join(d, safe_name(name)), "\n".join(lines) + "\n")
            print(sym_line("[+]" if ok else "[x]", "เพิ่มแล้ว" if ok else "เขียนไม่ได้", BLUE_L if ok else RED))
        elif s == "4":
            url = inp("[?] URL สคริปต์: ").strip(); name = inp("[?] ชื่อไฟล์: ").strip() or "remote"
            if url.startswith("http"):
                ok = put_file(os.path.join(d, safe_name(name)), f'loadstring(game:HttpGet({json.dumps(url)}))()\n')
                print(sym_line("[+]" if ok else "[x]", "เพิ่มแล้ว" if ok else "เขียนไม่ได้", BLUE_L if ok else RED))
        elif s == "5":
            src = inp("[?] path ไฟล์ .lua/.txt: ").strip().strip("'\"")
            try:
                with open(src, encoding="utf-8", errors="ignore") as f: txt = f.read()
                ok = put_file(os.path.join(d, safe_name(os.path.basename(src))), txt)
                print(sym_line("[+]" if ok else "[x]", "เพิ่มแล้ว" if ok else "เขียนไม่ได้", BLUE_L if ok else RED))
            except Exception as e: print(sym_line("[x]", f"อ่านไฟล์ไม่ได้: {e}", RED))
        elif s == "6":
            ok = put_file(os.path.join(d, "star_fps_lite.lua"), LUA_LITE)
            print(sym_line("[+]" if ok else "[x]", "ติดตั้ง star_fps_lite.lua" if ok else "เขียนไม่ได้", BLUE_L if ok else RED))
        elif s == "7":
            print(sym_line("[!]", "Extreme ลบ Terrain ทั้งหมด — บางเกมตัวละครอาจตกเหว/รีเซ็ต ลองกับ 1 บัญชีก่อน", YELLOW))
            d3 = inp("[?] ปิดการเรนเดอร์ 3D ด้วย (จอดำ ประหยัดสุด)? y/N: ").strip().lower() == "y"
            ok = put_file(os.path.join(d, "star_fps_extreme.lua"), LUA_HEAVY.replace("__D3__", "true" if d3 else "false"))
            print(sym_line("[+]" if ok else "[x]", "ติดตั้ง star_fps_extreme.lua" if ok else "เขียนไม่ได้", BLUE_L if ok else RED))
        elif s == "f":
            ok = put_file(os.path.join(d, "star_fps_meter.lua"), LUA_FPSMETER)
            print(sym_line("[+]" if ok else "[x]", "ติดตั้ง star_fps_meter.lua — เปิดเกมแล้วจะมีเลข FPS มุมขวาบน ลากย้ายได้" if ok else "เขียนไม่ได้", BLUE_L if ok else RED))
        elif s == "8":
            ls = list_scripts(d)
            for i, n in enumerate(ls, 1): print(t_ind() + f"{i}. {n}")
            k = inp("[?] ลบเลขที่: ").strip()
            if k.isdigit() and 1 <= int(k) <= len(ls): del_file(os.path.join(d, ls[int(k) - 1])); print(sym_line("[+]", "ลบแล้ว"))
        elif s == "9":
            if inp("[?] พิมพ์ YES เพื่อลบสคริปต์ทั้งหมดในโฟลเดอร์: ").strip() == "YES":
                for n in list_scripts(d): del_file(os.path.join(d, n))
                print(sym_line("[+]", "ลบหมดแล้ว"))

# ---------- ลดกราฟิกระดับเครื่อง ----------
def menu_gfx(cfg):
    cls(); print(sect("ลดกราฟิก / ประหยัดแรม"))
    print(t_ind() + "[1] ลดความละเอียดจอ (เบาแรม+GPU มาก) [2] คืนความละเอียดเดิม")
    print(t_ind() + "[3] ปิดแอนิเมชันระบบ [4] ล้างแคชแอป Roblox [5] ติดตั้ง FPS Lite/Extreme (ไป Delta)")
    print(t_ind() + "[6] โหมดดินน้ำมัน (ภาพกากสุด ปิดเอฟเฟกต์/แอนิเมชัน/เท็กซ์เจอร์/เสียง ลดแลค)  [7] ถอนโหมดดินน้ำมัน")
    s = inp("[?] เลือก: ").strip()
    if s == "1":
        print(t_ind() + "a) 720x1280 dpi240  b) 540x960 dpi180  c) 360x640 dpi120 (ต่ำสุด)")
        pr = {"a": (720, 1280, 240), "b": (540, 960, 180), "c": (360, 640, 120)}.get(inp("[?] เลือก: ").strip().lower())
        if pr:
            rsh(f"wm size {pr[0]}x{pr[1]}; wm density {pr[2]}", 20)
            print(sym_line("[+]", "ตั้งแล้ว — ถ้าจอเพี้ยนกด [2] หรือพิมพ์: wm size reset; wm density reset"))
    elif s == "2": rsh("wm size reset; wm density reset", 20); print(sym_line("[+]", "คืนค่าแล้ว"))
    elif s == "3":
        rsh("settings put global window_animation_scale 0; settings put global transition_animation_scale 0; settings put global animator_duration_scale 0", 20)
        print(sym_line("[+]", "ปิดแอนิเมชันแล้ว"))
    elif s == "4":
        if not has_root(): print(sym_line("[x]", "ต้องมี root", RED)); return
        for p in all_pkgs(cfg):
            q = shlex.quote(p)
            su(f"rm -rf /data/data/{q}/cache/* /sdcard/Android/data/{q}/cache/*", 30)
        print(sym_line("[+]", "ล้างแคชแล้ว"))
    elif s == "5": menu_delta(cfg)
    elif s == "6":
        d = delta_dir(cfg)
        if not d:
            print(sym_line("[x]", "ไม่พบโฟลเดอร์ Delta — ตั้งที่ [8] Delta AutoExec → [1] ก่อน", RED)); inp("[Enter] "); return
        a_self = inp("[?] ปิดแอนิเมชันตัวเราเองด้วย (ยืนนิ่ง ลื่นสุด)? Y/n: ").strip().lower() != "n"
        ok = put_file(os.path.join(d, "star_clay.lua"), LUA_CLAY.replace("__AS__", "true" if a_self else "false"))
        print(sym_line("[+]" if ok else "[x]", "ติดตั้ง star_clay.lua — มีผลทุกครั้งที่เข้าเกม" if ok else "เขียนไม่ได้", BLUE_L if ok else RED))
        rsh("settings put global window_animation_scale 0; settings put global transition_animation_scale 0; settings put global animator_duration_scale 0", 20)
        print(sym_line("[+]", "ปิดแอนิเมชันระบบแล้ว"))
        if has_root():
            for p in all_pkgs(cfg):
                q = shlex.quote(p); su(f"rm -rf /data/data/{q}/cache/* /sdcard/Android/data/{q}/cache/*", 30)
            print(sym_line("[+]", "ล้างแคชแอปแล้ว"))
        print(t_ind() + ac("เปิดเกมใหม่ 1 รอบให้สคริปต์ทำงาน · อยากให้เบาขึ้นอีกใช้ข้อ [1] ลดความละเอียดจอ", GRAY_D)); inp("[Enter] ")
    elif s == "7":
        d = delta_dir(cfg)
        if d: del_file(os.path.join(d, "star_clay.lua"))
        rsh("settings put global window_animation_scale 1; settings put global transition_animation_scale 1; settings put global animator_duration_scale 1", 20)
        print(sym_line("[+]", "ถอนแล้ว (ลบสคริปต์ + คืนแอนิเมชันระบบ)")); inp("[Enter] ")

RUN_SH = '''#!/data/data/com.termux/files/usr/bin/sh
# STAR supervisor — เด้ง/ถูกฆ่า = เปิดใหม่เอง · กด q ออกปกติ = หยุด
termux-wake-lock 2>/dev/null
cd "$(dirname "$0")"
while true; do
  python "%s" --auto && break
  echo "[!] STAR ดับ (code $?) — เริ่มใหม่ใน 5 วิ"; sleep 5
done
'''

# ════════════════════════════════════════════════════════════════
#  จัดจอโคลนเป็นกริด — ย่อแต่ละแอปเป็นหน้าต่างเล็ก เรียงพร้อมกันหลายช่อง
# ════════════════════════════════════════════════════════════════
def screen_size():
    out = rsh("wm size", 10)
    m = re.findall(r"(\d+)\s*x\s*(\d+)", out)          # บรรทัดสุดท้าย = Override size (ถ้าเคยตั้งไว้)
    return (int(m[-1][0]), int(m[-1][1])) if m else (None, None)

def enable_freeform():
    rsh("settings put global development_settings_enabled 1; "
        "settings put global force_resizable_activities 1; "
        "settings put global enable_freeform_support 1", 15)

def resolve_activity(pkg):
    out = rsh(f"cmd package resolve-activity --brief {shlex.quote(pkg)}", 15)
    for l in reversed([x.strip() for x in out.splitlines() if x.strip()]):
        if "/" in l and "No activity" not in l: return l
    return None

GRID_DEF = {"auto": True,    # จัดกริดเองอัตโนมัติตอนกด START / --auto
            "lock": True,    # ล็อกไม่ให้ลาก/ขยายหน้าต่าง
            "cols": 0,       # 0 = คำนวณเอง
            "gap": 6,        # ช่องว่างระหว่างหน้าต่าง (px)
            "top": 3,        # เว้นขอบบน % (แถบสถานะ)
            "bottom": 35,    # เว้นขอบล่าง % ไว้ให้ dashboard ของ Termux
            "only_bound": False,  # True = จัดเฉพาะแอปที่ผูกกับบัญชี · False = จัดทุกแอปในรายการ
            "cw": 0, "ch": 0}  # ขนาดช่องคงที่ px (0 = คำนวณให้พอดีจอ) — ตั้งจากหน้าต่างช่อง 1 ได้

def grid_opts(cfg):
    g = dict(GRID_DEF); g.update(cfg.get("grid") or {}); return g

def grid_bounds(n, sw, sh, cols=0, gap=6, top=0, bottom=0, cw=0, ch=0):
    """แบ่งจอเป็นกริดช่องขนาดเท่ากันหมด · top/bottom เป็น % ของความสูงจอ
    cw/ch > 0 = ใช้ขนาดช่องคงที่ (เช่นเท่าหน้าต่างช่อง 1) เรียงต่อกัน แถวไม่พอจะซ้อนกันเล็กน้อยแทนล้นจอ"""
    if n <= 0: return []
    rt, rb = sh * top // 100, sh * bottom // 100
    uh = max(100, sh - rt - rb)
    out = []
    if cw and ch:
        cw = min(cw, sw - 2 * gap); ch = min(ch, uh - 2 * gap)
        cols = max(1, (sw - gap) // (cw + gap)); rows = math.ceil(n / cols)
        sy = ch + gap
        if rows > 1: sy = max(30, min(sy, (uh - ch - 2 * gap) // (rows - 1)))
        for i in range(n):
            r, c = divmod(i, cols)
            l = gap + c * (cw + gap); t = rt + gap + r * sy
            out.append((l, t, l + cw, t + ch))
        return out
    if not cols or cols < 1:
        cols = math.ceil(math.sqrt(n * sw / uh))
    cols = max(1, min(n, cols)); rows = math.ceil(n / cols)
    cw = (sw - gap * (cols + 1)) // cols
    ch = (uh - gap * (rows + 1)) // rows
    for i in range(n):
        r, c = divmod(i, cols)
        l = gap + c * (cw + gap); t = rt + gap + r * (ch + gap)
        out.append((l, t, l + cw, t + ch))
    return out

def grid_pkgs(cfg):
    """แพ็กเกจของแอปโคลนที่ใช้เฝ้าอยู่ (ถ้ายังไม่ผูกบัญชีเลย ใช้ทุกแอปที่มี)"""
    apps = [a for a in cfg["apps"] if a.get("package")]
    used = {a.get("app_num") for a in cfg["accounts"] if a.get("enabled", True) and a.get("cookie") and a.get("app_num")}
    sel = ([a for a in apps if a.get("num") in used] or apps) if grid_opts(cfg)["only_bound"] else apps
    seen, out = set(), []
    for a in sel:
        if a["package"] not in seen: seen.add(a["package"]); out.append(a["package"])
    return out

def make_layout(cfg, pkgs=None):
    sw, sh = screen_size()
    if not sw: return None, None, None
    pkgs = pkgs or grid_pkgs(cfg)
    g = grid_opts(cfg)
    boxes = grid_bounds(len(pkgs), sw, sh, g["cols"], g["gap"], g["top"], g["bottom"], g["cw"], g["ch"])
    return {p: list(b) for p, b in zip(pkgs, boxes)}, sw, sh

def task_info():
    """อ่าน dumpsys รอบเดียว → {package: (taskId, (l,t,r,b) หรือ None)} ของทุกหน้าต่างที่เปิดอยู่"""
    out = rsh("dumpsys activity activities", 20)
    res = {}
    for block in re.split(r"(?=Task\{)", out):
        if not block.startswith("Task{"): continue
        m_id = re.search(r"#(\d+)", block[:300]) or re.search(r"taskId=(\d+)", block[:800])
        m_pk = re.search(r"A=(?:\d+:)?([\w.]+)", block[:300]) or re.search(r"realActivity=([\w.]+)/", block[:800])
        if not (m_id and m_pk): continue
        head = block[:1500]
        m_b = re.search(r"bounds=\[(-?\d+),(-?\d+)\]\[(-?\d+),(-?\d+)\]", head) \
              or re.search(r"mBounds=Rect\((-?\d+), (-?\d+) - (-?\d+), (-?\d+)\)", head)
        bd = tuple(int(x) for x in m_b.groups()) if m_b else None
        res[m_pk.group(1)] = (m_id.group(1), bd)
    return res

def task_map():
    return {p: v[0] for p, v in task_info().items()}

def task_id_for(pkg):
    return task_map().get(pkg)

def set_bounds(task_id, l, t, r, b):
    rsh(f"am task resize {task_id} {l} {t} {r} {b}", 10)

def _near(a, b, tol=6):
    return a is not None and all(abs(x - y) <= tol for x, y in zip(a, b))

def apply_sizes(layout, info=None):
    """ปรับทุกหน้าต่างที่เปิดอยู่ให้เท่ากัน (เฉพาะอันที่ขนาด/ตำแหน่งไม่ตรง) ในคำสั่งเดียว
    → (จำนวนที่สั่งปรับ, [แพ็กเกจที่ปรับแล้วยังไม่ตรงจากรอบก่อน])"""
    info = info or task_info(); cmds = []; wrong = []
    for pkg, box in layout.items():
        if pkg not in info: continue
        tid, cur = info[pkg]
        if cur is not None and _near(cur, box): continue
        cmds.append(f"am task resize {tid} {box[0]} {box[1]} {box[2]} {box[3]}"); wrong.append(pkg)
    if cmds: rsh("; ".join(cmds), 20)
    return len(cmds), wrong

def launch_in_grid(pkg, box):
    act = resolve_activity(pkg)
    if not act: return False
    l, t, r, b = box
    out = rsh(f"am start --windowingMode 5 --activity-launch-bounds {l},{t},{r},{b} -n {shlex.quote(act)}", 20)
    return not ("Error" in out or "Exception" in out)

GRID = {"thread": None, "layout": {}}

class GridLock(threading.Thread):
    """กันหน้าต่างถูกลาก/ขยาย/ย้าย — เช็กขนาดจริงทุก 5 วิ ไม่ตรงก็ดึงกลับ
    ถ้า resize ไม่ติด 2 รอบติด จะสั่งเปิดซ้ำพร้อมขนาดช่อง (วิธีที่ ROM ส่วนใหญ่ยอมรับ)"""
    def __init__(self, cfg):
        super().__init__(daemon=True, name="gridlock"); self.cfg = cfg; self.fails = {}
    def run(self):
        while not stop.is_set() and self.cfg.get("grid_locked"):
            try:
                layout = GRID.get("layout") or self.cfg.get("grid_layout") or {}
                if layout:
                    _, wrong = apply_sizes(layout)
                    for pkg in layout:
                        if pkg not in wrong: self.fails.pop(pkg, None)
                    for pkg in wrong:
                        self.fails[pkg] = self.fails.get(pkg, 0) + 1
                        if self.fails[pkg] >= 2 and self.fails[pkg] % 3 == 2:
                            launch_in_grid(pkg, layout[pkg])
            except Exception as e: flog(f"gridlock {e!r}")
            if stop.wait(5): break
        GRID["thread"] = None

def start_lock(cfg):
    if not GRID["thread"] or not GRID["thread"].is_alive():
        GRID["thread"] = GridLock(cfg); GRID["thread"].start()

def auto_arrange(cfg, accs):
    """เรียกตอน START: คำนวณกริดให้ทุกแอป → ทุกครั้งที่ launch_game เปิดแอปจะเข้าช่องของตัวเอง + ล็อกขนาดให้เท่ากัน"""
    g = grid_opts(cfg)
    if not g["auto"]: return
    if not has_root():
        print(sym_line("[·]", "จัดกริดอัตโนมัติต้องใช้ root — ข้ามไป", GRAY)); return
    layout, sw, sh = make_layout(cfg)            # ใช้ทุกแอป → ช่องไม่ขยับแม้แยกจอ tmux ทีละบัญชี
    if not layout:
        print(sym_line("[!]", "จัดกริด: อ่านขนาดจอไม่ได้/ไม่มีแอป", YELLOW)); return
    mine = {a.get("app_num") for a in accs}
    mine_pk = {a["package"] for a in cfg["apps"] if a.get("num") in mine and a.get("package")}
    GRID["layout"] = {p: b for p, b in layout.items() if p in mine_pk} if (ONLY_LABEL and mine_pk) else layout
    enable_freeform()
    cfg["grid_layout"] = GRID["layout"]; cfg["grid_locked"] = bool(g["lock"]); save_cfg(cfg)
    if g["lock"]: start_lock(cfg)
    print(sym_line("[+]", f"จัดกริดอัตโนมัติ {len(GRID['layout'])} ช่อง ({sw}x{sh})"
                          f"{' · ล็อก' if g['lock'] else ''}", GREEN))

# ═════════ โซนเซ็ทจอ (กริด) ═════════
def screen_density():
    m = re.findall(r"density:\s*(\d+)", rsh("wm density", 10))
    return int(m[-1]) if m else None

def freeform_on():
    return rsh("settings get global enable_freeform_support", 10).strip() == "1"

def app_name(cfg, pkg):
    a = next((x for x in cfg["apps"] if x.get("package") == pkg), None)
    return (a or {}).get("name") or pkg

def tile_state(layout, info):
    """→ {pkg: ("ok"|"bad"|"closed"|"unk", ขนาดจริง หรือ None)}"""
    st = {}
    for pkg, box in layout.items():
        if pkg not in info: st[pkg] = ("closed", None); continue
        cur = info[pkg][1]
        st[pkg] = ("unk", None) if cur is None else (("ok" if _near(cur, box) else "bad"), cur)
    return st

def grid_preview(layout, sw, sh, bottom=0, W=44, H=14):
    """ภาพจำลองกริดแบบตัวอักษร: เลขในกรอบ = ลำดับช่อง = ลำดับแอป"""
    cv = [[" "] * W for _ in range(H)]
    X = lambda v: min(W - 1, max(0, round(v * (W - 1) / sw)))
    Y = lambda v: min(H - 1, max(0, round(v * (H - 1) / sh)))
    for i, (pkg, (l, t, r, b)) in enumerate(layout.items(), 1):
        x0, x1, y0, y1 = X(l), X(r), Y(t), Y(b)
        if x1 - x0 < 2: x1 = min(W - 1, x0 + 2)
        if y1 - y0 < 2: y1 = min(H - 1, y0 + 2)
        for x in range(x0, x1 + 1): cv[y0][x] = cv[y1][x] = "-"
        for y in range(y0, y1 + 1): cv[y][x0] = cv[y][x1] = "|"
        for y, x in ((y0, x0), (y0, x1), (y1, x0), (y1, x1)): cv[y][x] = "+"
        for k, ch in enumerate(str(i)):
            if x0 + 1 + k < x1: cv[y0 + 1][x0 + 1 + k] = ch
    if bottom:
        mid = (Y(sh * (100 - bottom) // 100) + H) // 2
        if mid < H and not "".join(cv[mid]).strip():
            txt = "Termux / dashboard"; s = max(0, (W - len(txt)) // 2)
            cv[mid][s:s + len(txt)] = list(txt)
    return ["".join(r) for r in cv]

def apply_now(cfg, layout):
    """จัดหน้าต่างที่เปิดอยู่เข้าช่อง → ตรวจผล → ตัวที่ดื้อสั่งเปิดซ้ำพร้อมขนาด → ตรวจผลอีกรอบ → คืนสถานะสุดท้าย"""
    enable_freeform(); GRID["layout"] = cfg["grid_layout"] = layout
    print(sym_line("[·]", "ขั้น 1/3 ปรับขนาดหน้าต่างที่เปิดอยู่...", GRAY))
    info = task_info(); n, _ = apply_sizes(layout, info)
    print(t_ind() + f"สั่งปรับ {n} หน้าต่าง"); time.sleep(2)
    info = task_info(); st = tile_state(layout, info)
    bad = [p for p, (s, _) in st.items() if s in ("bad", "unk")]
    if bad:
        print(sym_line("[·]", f"ขั้น 2/3 ยังไม่ตรง {len(bad)} ตัว → เปิดซ้ำพร้อมกำหนดขนาด", GRAY))
        for p in bad: launch_in_grid(p, layout[p])
        time.sleep(3); info = task_info(); st = tile_state(layout, info)
    else:
        print(sym_line("[·]", "ขั้น 2/3 ข้าม (ตรงหมดแล้ว)", GRAY))
    print(sym_line("[·]", "ขั้น 3/3 ตรวจผลสุดท้าย", GRAY))
    return st

def print_tiles(cfg, layout, st):
    mark = {"ok": ("[+]", GREEN, "ตรงช่อง"), "bad": ("[x]", RED, "ขนาดไม่ตรง"),
            "closed": ("[·]", GRAY_D, "ยังไม่เปิด"), "unk": ("[?]", YELLOW, "อ่านขนาดไม่ได้")}
    for i, (pkg, box) in enumerate(layout.items(), 1):
        s, cur = st.get(pkg, ("closed", None)); sym, col, txt = mark[s]
        extra = f" ตอนนี้ {cur[2]-cur[0]}x{cur[3]-cur[1]}" if s == "bad" and cur else ""
        print(t_ind() + ac(f"{sym} ช่อง {i:<2} {clip(app_name(cfg, pkg), 16):<16} {txt}{extra}", col))
    c = lambda k: sum(1 for v in st.values() if v[0] == k)
    print(sym_line("[+]" if not c("bad") else "[!]",
                   f"ตรง {c('ok')} · ไม่ตรง {c('bad') + c('unk')} · ยังไม่เปิด {c('closed')}",
                   GREEN if not c("bad") else YELLOW))

PRESETS = [("2 คอลัมน์ · ใหญ่ อ่านง่าย", dict(cols=2, gap=8, top=3, bottom=25)),
           ("3 คอลัมน์ · กลาง", dict(cols=3, gap=6, top=3, bottom=30)),
           ("4 คอลัมน์ · เล็ก", dict(cols=4, gap=4, top=3, bottom=35)),
           ("6 คอลัมน์ · จิ๋ว (แบบภาพตัวอย่าง)", dict(cols=6, gap=2, top=2, bottom=40)),
           ("เต็มจอ · ไม่เว้น dashboard", dict(cols=0, gap=4, top=3, bottom=0))]

def ask_int(label, cur, lo, hi):
    t = inp(f"[?] {label} {lo}-{hi} [{cur}]: ").strip()
    if t == "": return cur
    if t.isdigit() and lo <= int(t) <= hi: return int(t)
    print(sym_line("[x]", f"ต้องเป็นเลข {lo}-{hi} — ใช้ค่าเดิม", RED)); return cur

def menu_grid(cfg):
    while True:
        cls(); g = grid_opts(cfg); pkgs = grid_pkgs(cfg)
        print(sect("เซ็ทจอ · เรียงโคลนเป็นกริด"))
        if not has_root():
            print(sym_line("[x]", "ต้องมี root — สั่งปรับหน้าต่างระดับระบบไม่ได้", RED))
            print(t_ind() + "ถ้าไม่มี root: เปิด นักพัฒนา > บังคับให้ปรับขนาดได้ + หน้าต่างอิสระ แล้วลากเอง"); inp("[Enter] "); return
        if not pkgs:
            print(sym_line("[x]", "ยังไม่มีแอปโคลน — เพิ่มที่เมนู [3] แอป ก่อน", RED)); inp("[Enter] "); return
        layout, sw, sh = make_layout(cfg, pkgs)
        if not layout: print(sym_line("[x]", "อ่านขนาดจอไม่ได้", RED)); inp("[Enter] "); return
        info = task_info(); st = tile_state(layout, info)
        cnt = lambda k: sum(1 for v in st.values() if v[0] == k)
        b0 = next(iter(layout.values())); ncols = len({v[0] for v in layout.values()})
        locked = bool(cfg.get("grid_locked")) and GRID["thread"] is not None
        yn = lambda v: ac("ON", GREEN) if v else ac("off", GRAY_D)
        # ── สถานะ ──
        print(t_ind() + ac(f"จอ {sw}x{sh} · density {screen_density() or '?'} · freeform {'ON' if freeform_on() else 'ยังไม่เปิด (ปุ่ม [1] จะเปิดให้)'}", GRAY_D))
        print(t_ind() + f"{len(pkgs)} แอป · เปิดอยู่ {len(pkgs) - cnt('closed')} · ตรงช่อง {cnt('ok')} · ไม่ตรง {cnt('bad') + cnt('unk')}")
        print(t_ind() + f"ช่องละ {b0[2]-b0[0]}x{b0[3]-b0[1]} px · {ncols} คอลัมน์" + (ac(" · ขนาดคงที่", CYAN_S) if g["cw"] else " · อัตโนมัติ"))
        print(t_ind() + f"ล็อก {yn(locked)} · จัดเองตอน START {yn(g['auto'])} · จัดทุกแอป {yn(not g['only_bound'])}")
        for row in grid_preview(layout, sw, sh, g["bottom"]): print(t_ind() + ac(row, CYAN_S))
        # ── เมนู ──
        print(t_ind() + ac("▸ ทำเลย", YELLOW))
        print(t_ind() + "[1] จัดทั้งหมด + ล็อก (แนะนำ)    [2] ตรวจสถานะรายช่อง")
        print(t_ind() + ac("▸ เลือกรูปแบบ", YELLOW))
        print(t_ind() + "[3] พรีเซ็ต (2/3/4/6 คอลัมน์ · เต็มจอ)")
        print(t_ind() + "[4] ใช้ขนาดหน้าต่างช่อง 1 เป็นต้นแบบ    [5] ตั้งกว้าง×สูงเอง")
        print(t_ind() + "[6] ปรับละเอียด (คอลัมน์/ช่องว่าง/เว้นบน/เว้นล่าง)    [7] กลับเป็นอัตโนมัติ")
        print(t_ind() + ac("▸ ระบบ", YELLOW))
        print(t_ind() + "[8] จัดเองตอน START on/off    [9] ล็อกขนาด on/off    [u] ปลดล็อกเดี๋ยวนี้")
        print(t_ind() + "[a] จัดทุกแอป / เฉพาะที่ผูกบัญชี    [d] density (ขั้นสูง)    [r] รีเซ็ตทั้งหมด    [0] กลับ")
        s = inp("[?] เลือก: ").strip().lower()
        gg = cfg.setdefault("grid", {})
        def refresh_and_apply(ask=True):
            """หลังเปลี่ยนรูปแบบ → ถามว่าจัดเลยไหม"""
            if ask and inp("[?] จัดตามนี้เลย? Y/n: ").strip().lower() == "n": return
            ly, _, _ = make_layout(cfg, pkgs)
            cls(); print(sect("กำลังจัดจอ"))
            res = apply_now(cfg, ly); print_tiles(cfg, ly, res)
            if grid_opts(cfg)["lock"]: cfg["grid_locked"] = True; start_lock(cfg); print(sym_line("[+]", "ล็อกขนาดแล้ว (ตรวจซ้ำทุก 5 วิ)", GREEN))
            save_cfg(cfg)
            if cnt_closed(res): print(t_ind() + ac("ตัวที่ยังไม่เปิด จะเข้าช่องของตัวเองตอนกด START", GRAY_D))
            print(t_ind() + ac("บาง ROM ไม่ยอมให้ย่อหน้าต่าง/มีขนาดขั้นต่ำ — ถ้าไม่ตรงลองลด density [d]", GRAY_D))
            inp("[Enter] ")
        cnt_closed = lambda res: sum(1 for v in res.values() if v[0] == "closed")
        if s in ("0", ""): return
        elif s == "1": refresh_and_apply(ask=False)
        elif s == "2":
            cls(); print(sect("สถานะรายช่อง")); print_tiles(cfg, layout, st); inp("[Enter] ")
        elif s == "3":
            cls(); print(sect("พรีเซ็ต"))
            for i, (nm, _) in enumerate(PRESETS, 1): print(t_ind() + f"[{i}] {nm}")
            c = inp("[?] เลือก (Enter=ยกเลิก): ").strip()
            if c.isdigit() and 1 <= int(c) <= len(PRESETS):
                gg.update(PRESETS[int(c) - 1][1]); gg["cw"] = gg["ch"] = 0; save_cfg(cfg)
                ly, _, _ = make_layout(cfg, pkgs)
                for row in grid_preview(ly, sw, sh, grid_opts(cfg)["bottom"]): print(t_ind() + ac(row, CYAN_S))
                refresh_and_apply()
        elif s == "4":
            ref = next((p for p in pkgs if p in info and info[p][1]), None)
            if not ref:
                print(sym_line("[x]", "อ่านขนาดหน้าต่างช่อง 1 ไม่ได้ — เปิดแอปแรกเป็นหน้าต่างขนาดที่ต้องการก่อน หรือใช้ [5]", RED)); inp("[Enter] "); continue
            l, t, r, b = info[ref][1]; gg["cw"], gg["ch"] = r - l, b - t; save_cfg(cfg)
            print(sym_line("[+]", f"ใช้ขนาดของ {app_name(cfg, ref)} = {r-l}x{b-t} เป็นต้นแบบ", GREEN)); refresh_and_apply()
        elif s == "5":
            t = inp("[?] กว้าง×สูง px เช่น 255x255: ").strip().lower().replace("*", "x").replace("×", "x")
            m = re.match(r"^(\d{2,4})\s*x\s*(\d{2,4})$", t)
            if m: gg["cw"], gg["ch"] = int(m.group(1)), int(m.group(2)); save_cfg(cfg); refresh_and_apply()
            else: print(sym_line("[x]", "รูปแบบไม่ถูก", RED)); inp("[Enter] ")
        elif s == "6":
            gg["cols"] = ask_int("คอลัมน์ (0=auto)", g["cols"], 0, 12)
            gg["gap"] = ask_int("ช่องว่าง px", g["gap"], 0, 60)
            gg["top"] = ask_int("เว้นบน %", g["top"], 0, 40)
            gg["bottom"] = ask_int("เว้นล่าง % (ไว้ให้ dashboard)", g["bottom"], 0, 80)
            gg["cw"] = gg["ch"] = 0; save_cfg(cfg); refresh_and_apply()
        elif s == "7": gg["cw"] = gg["ch"] = 0; save_cfg(cfg)
        elif s == "8": gg["auto"] = not g["auto"]; save_cfg(cfg)
        elif s == "9": gg["lock"] = not g["lock"]; save_cfg(cfg)
        elif s == "a": gg["only_bound"] = not g["only_bound"]; save_cfg(cfg)
        elif s == "u":
            cfg["grid_locked"] = False; save_cfg(cfg); print(sym_line("[+]", "ปลดล็อกแล้ว — ลาก/ขยายได้อิสระ")); inp("[Enter] ")
        elif s == "d":
            cls(); print(sect("density (ขั้นสูง)"))
            print(t_ind() + f"ตอนนี้ {screen_density() or '?'} · เลขน้อย = UI เล็กลง หน้าต่างย่อได้เล็กขึ้น")
            print(t_ind() + "กระทบทั้งเครื่อง · พิมพ์ reset เพื่อคืนค่าเดิม")
            v = inp("[?] ใส่เลข 120-480 หรือ reset (Enter=ยกเลิก): ").strip().lower()
            if v == "reset": run_cmd("wm density reset"); print(sym_line("[+]", "คืนค่าเดิมแล้ว", GREEN)); inp("[Enter] ")
            elif v.isdigit() and 120 <= int(v) <= 480: run_cmd(f"wm density {int(v)}"); print(sym_line("[+]", f"ตั้ง density {v} แล้ว", GREEN)); inp("[Enter] ")
        elif s == "r":
            if inp("[?] รีเซ็ตค่ากริดทั้งหมด? y/N: ").strip().lower() == "y":
                cfg["grid"] = {}; cfg["grid_locked"] = False; cfg.pop("grid_layout", None); save_cfg(cfg)

def menu_phone(cfg):
    while True:
        cls(); print(sect("Phone / Cloudphone Boost", mem_line()))
        print(t_ind() + f"root: {'พร้อม' if has_root() else 'ไม่มี (บางข้อทำไม่ได้)'} · wake-lock: {'ON' if cfg.get('wake', True) else 'OFF'} · auto-trim: {cfg.get('trim_min', 10)} นาที")
        print(t_ind() + "[1] ล้างแรมเบา (แคช)   [2] ล้างแรมแรง (ปิดแอปพื้นหลังที่ไม่ใช่ Roblox/Termux)")
        print(t_ind() + "[3] กัน Termux+Roblox ไม่ให้ถูกฆ่า (ปิด phantom killer + whitelist แบต)")
        print(t_ind() + "[4] เปิด/ปิด wake-lock   [5] ตั้งรอบ auto-trim (0=ปิด)")
        print(t_ind() + "[6] สร้าง star_run.sh (ดับแล้วเปิดใหม่เอง)")
        print(t_ind() + "[0] กลับ")
        s = inp("[?] เลือก: ").strip()
        if s in ("", "0"): return
        cls(); did = True                      # เคลียร์ครั้งเดียวก่อนรัน แล้วคงผลไว้ให้อ่านจน Enter
        if s == "1":
            print(sect("ล้างแรมเบา", mem_line()))
            b, a, _ = free_ram(cfg, report=True)
            print(sym_line("[+]", f"RAM ว่าง {b} → {a} MB ({a - b:+d})" + ("" if has_root() else " · ไม่มี root ผลจะน้อย")))
        elif s == "2":
            v = bg_victims(cfg)
            print(sect("ล้างแรมแรง", f"{len(v)} แอปที่จะปิด"))
            print(t_ind() + ac(", ".join(v[:12]) + (" ..." if len(v) > 12 else "") if v else "ไม่มีแอปพื้นหลังให้ปิด", YELLOW))
            if inp("[?] ยืนยัน? y/N: ").strip().lower() == "y":
                b, a, k = free_ram(cfg, True, report=True)
                print(sym_line("[+]", f"ปิด {k} แอป · RAM ว่าง {b} → {a} MB ({a - b:+d})"))
            else: did = False
        elif s == "3":
            print(sect("กัน Termux+Roblox ไม่ให้ถูกฆ่า"))
            if has_root():
                survival_setup(cfg, report=True); protect(cfg)
                print(sect("ตรวจผลหลังตั้ง"))
                verify_survival(cfg)
                print(sym_line("[+]", "เสร็จ (Android 12+ ช่วยได้มากสุด)"))
            else:
                print(sym_line("[!]", "ไม่มี root — ทำเองได้: (1) ตั้งค่า > แอป > Termux > แบตเตอรี่ = ไม่จำกัด (2) ล็อกแอปใน Recents", YELLOW))
                print(t_ind() + "(3) ผ่าน adb: adb shell settings put global settings_enable_monitor_phantom_procs false")
        elif s == "4":
            cfg["wake"] = not cfg.get("wake", True); save_cfg(cfg)
            print(sym_line("[+]", f"wake-lock {'ON' if cfg['wake'] else 'OFF'}" + ("" if wake_lock(cfg['wake']) else " (ต้อง pkg install termux-api)")))
        elif s == "5":
            t = inp("[?] ทุกกี่นาที 0-120: ").strip()
            if t.isdigit() and 0 <= int(t) <= 120: cfg["trim_min"] = int(t); save_cfg(cfg); print(sym_line("[+]", f"บันทึกแล้ว — auto-trim {t} นาที"))
            else: print(sym_line("[x]", "ใส่ 0-120", RED))
        elif s == "6":
            p = os.path.join(HERE, "star_run.sh")
            with open(p, "w") as f: f.write(RUN_SH % os.path.basename(__file__))
            os.chmod(p, 0o755); print(sym_line("[+]", f"สร้างแล้ว — รันด้วย: sh {p}"))
        else: did = False
        if did: inp("[?] กด Enter เพื่อกลับเมนู ")

BANNER = ["  ███████╗████████╗ █████╗ ██████╗", "  ██╔════╝╚══██╔══╝██╔══██╗██╔══██╗",
          "  ███████╗   ██║   ███████║██████╔╝", "  ╚════██║   ██║   ██╔══██║██╔══██╗",
          "  ███████║   ██║   ██║  ██║██║  ██║", "  ╚══════╝   ╚═╝   ╚═╝  ╚═╝╚═╝  ╚═╝"]

# ════════════════════════════════════════════════════════════════
#  แยกจอ — 1 บัญชี 1 ช่อง tmux (กันดาวข้อความมั่วตอนเฝ้าหลายบัญชี)
# ════════════════════════════════════════════════════════════════
def tmux_ok():
    return shutil.which("tmux") is not None

def menu_tmux(cfg):
    cls()
    accs = [a for a in cfg["accounts"] if a.get("enabled", True) and a.get("cookie")]
    print(sect("แยกจอ (tmux)", f"{len(accs)} บัญชีเปิดเฝ้าอยู่"))
    if not accs:
        print(sym_line("[x]", "ไม่มีบัญชีที่เปิดเฝ้า — เพิ่ม/เปิดก่อนที่ [1]/[2]/[4]", RED)); return
    if not tmux_ok():
        print(sym_line("[x]", "ไม่มี tmux — ติดตั้งก่อน", RED))
        print(t_ind() + ac("pkg install tmux", CYAN)); return
    print(t_ind() + "แต่ละบัญชีจะได้หน้าจอ (pane) ของตัวเอง แยกจาก log ของบัญชีอื่นทั้งหมด")
    print(t_ind() + "สลับช่อง: กด Ctrl+b แล้วตามด้วยลูกศร · ออกทั้งชุด: Ctrl+b แล้วพิมพ์ :kill-session Enter")
    if inp("[?] เริ่มแยกจอเลย? y/N: ").strip().lower() != "y": return
    sess = "star"
    if subprocess.run(["tmux", "has-session", "-t", sess], capture_output=True).returncode == 0:
        if inp(f"[?] มีเซสชัน '{sess}' อยู่แล้ว ปิดแล้วเริ่มใหม่? y/N: ").strip().lower() == "y":
            subprocess.run(["tmux", "kill-session", "-t", sess], capture_output=True)
        else:
            return
    script = os.path.abspath(__file__)
    py = sys.executable or "python"
    first, rest = accs[0], accs[1:]
    subprocess.run(["tmux", "new-session", "-d", "-s", sess, "-n", first["label"],
                     py, script, "--auto", "--only", first["label"]])
    for a in rest:
        subprocess.run(["tmux", "split-window", "-t", sess, py, script, "--auto", "--only", a["label"]])
        subprocess.run(["tmux", "select-layout", "-t", sess, "tiled"])
    subprocess.run(["tmux", "select-layout", "-t", sess, "tiled"])
    print(sym_line("[+]", f"แยกจอแล้ว {len(accs)} ช่อง — กำลังเข้าสู่ tmux...", GREEN))
    time.sleep(1)
    os.execvp("tmux", ["tmux", "attach", "-t", sess])   # สลับ process ไปคุม tmux แทนเมนูนี้เลย

def menu_tree(cfg):
    cls()
    n = len(cfg["accounts"]); on = sum(1 for a in cfg["accounts"] if a.get("enabled", True))
    placed = sum(1 for a in cfg["accounts"] if a.get("place_id"))
    kv = lambda k, v: f"{t_ind()}{ac(f'{k:<9}', CYAN_S)}{ac(str(v), '97')}"
    print(); [print(ac(l, RED_B)) for l in BANNER]
    print("  Multi-Account Roblox Auto-Rejoin  " + ac(f"v{VERSION}", GREEN)); print()
    print(sect("Config", f"v{VERSION}"))
    print(kv("Accounts", f"{on}/{n} เฝ้า")); print(kv("Apps", len(cfg["apps"]))); print(kv("Maps", f"{placed}/{n}"))
    print(kv("Webhook", ac("live", GREEN) if cfg.get("webhook") else ac("off", RED)))
    print(kv("Web", (ac(f"on :{web_cfg(cfg)['port']}" + (" · Hub" if web_cfg(cfg)["hub"] else ""), GREEN) if WEB["server"] else ac("off", GRAY_D)) + (ac(" · Agent", GREEN) if agent_alive() else "")))
    print(sect("Operations"))
    for k, t, d in [("1", "เพิ่มบัญชี · Quick Login", "ไม่ต้องใช้รหัสผ่าน"), ("2", "เพิ่มบัญชี · Cookie", "วาง·ไฟล์·หลายไอดี"),
                    ("3", "แอป", "สแกน·เพิ่ม·แก้ชื่อ·ลบ"), ("4", "บัญชี", "แมพ·hop·จอยเพื่อน·ทดสอบ·logout"),
                    ("5", "ตั้งค่า", "webhook·รอบเช็ก·backup"), ("6", "ROOT ฉีด cookie", "หมุนเวียนหลายแอป"),
                    ("7", "START", "dashboard · q หยุด"),
                    ("8", "Delta AutoExec", "เพิ่ม·ลบสคริปต์·FPS boost"), ("9", "ลดกราฟิก", "ลบภูเขา·ลดจอ·ล้างแคช"),
                    ("a", "Phone Boost", "ล้างแรม·กันตาย·คาวโฟน"),
                    ("b", "แยกจอ (tmux)", "1 บัญชีต่อ 1 ช่อง ไม่มั่ว"),
                    ("w", "Remote Web", "คุมจากมือถือ·ดูจอสด·start/stop·เพิ่ม cookie")]:
        key, title = (ac("[7]", GREEN), ac(t, GREEN_H)) if k == "7" else (ac(f"[{k}]", CYAN), t)
        print(f"{t_ind()}{key} {title}{ac(' ← ' + d, GRAY_D) if d else ''}")
    print(t_branch(True) + ac("[0] ออก", "97"))

def resume_grid_lock(cfg):
    if cfg.get("grid_locked") and cfg.get("grid_layout") and has_root():
        GRID["layout"] = cfg["grid_layout"]; start_lock(cfg)

def main():
    harden_self(); load_totals()
    cfg = load_cfg(); c = ""
    web_autostart(cfg)
    while True:
        menu_tree(cfg)
        try:
            c = inp(f"{t_branch(True)}[?] เลือก: ").strip().lower()
            if c == "1": menu_add_quick(cfg)
            elif c == "2": menu_add_cookie(cfg)
            elif c == "3": menu_apps(cfg)
            elif c == "4": manage_accounts(cfg)
            elif c == "5": menu_settings(cfg)
            elif c == "6": root_menu(cfg)
            elif c == "7": start_session(cfg)
            elif c == "8": menu_delta(cfg)
            elif c == "9": menu_gfx(cfg)
            elif c == "a": menu_phone(cfg)
            elif c == "b": menu_tmux(cfg)
            elif c == "w":
                if web_gate(): menu_web(cfg)
            elif c == "0": break
        except (KeyboardInterrupt, EOFError):
            print(); 
            if c == "7": continue
            break
        except Exception as e:
            print(sym_line("[x]", f"error: {type(e).__name__}: {e}", RED)); flog(f"menu error {e!r}")
    save_totals()
    print(t_branch(True) + ac("bye", GREEN_H))

def auto_main():
    """--auto: เริ่มเฝ้าทันที ไม่ผ่านเมนู · พังกลางคันเริ่มใหม่เอง · q/STOP = ออกปกติ"""
    harden_self(); load_totals(); cfg = load_cfg()
    web_autostart(cfg)
    while True:
        try: start_session(cfg)
        except Exception as e:
            flog(f"auto crash {e!r}"); time.sleep(5); continue
        break
    if WEB["server"] or agent_alive():  # เปิดเว็บ/agent อยู่ → ไม่ออก ให้ START ใหม่จากเว็บได้ (Ctrl+C เพื่อออก)
        try:
            while True: time.sleep(3600)
        except KeyboardInterrupt: pass

if __name__ == "__main__":
    try:
        auto_main() if "--auto" in sys.argv else main()
    finally:
        save_totals()
