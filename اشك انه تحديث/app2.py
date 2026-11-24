import asyncio
import base64
import collections
import hashlib
import json
import os
import queue
import re
import subprocess
import sys
import shutil
import threading
import traceback
import time
import zlib
from concurrent.futures import ThreadPoolExecutor
from tkinter import filedialog, messagebox
from urllib.parse import quote

import aiohttp
import customtkinter as ctk

ctk.set_appearance_mode("Dark")
ctk.set_default_color_theme("blue")

BASE_DIR = os.path.dirname(os.path.abspath(sys.executable if getattr(sys, "frozen", False)
                                           else __file__))
STATE_FILE = os.path.join(BASE_DIR, "download_state.json")
OUTPUT_ROOT = os.path.join(BASE_DIR, "Downloaded_Files")  # <repo>/<type>/<N>/file
ERROR_LOG = os.path.join(BASE_DIR, "error_log.txt")
FOLDER_LIMIT = 1000                # أقصى عدد ملفات في المجلد الواحد
START_CONN = 100                   # عدد الاتصالات عند البداية (القيمة القديمة المجرّبة)
MAX_CONN = 400                     # أقصى عدد (بيزيد تلقائياً لحد ما GitHub يبطّئ)
MIN_CONN = 20                      # أقل عدد لو GitHub بدأ يرفض
TUNE_WINDOW = 5.0                  # ثواني بين كل قياس لإنتاجية التحميل
WRITE_THREADS = 32                 # خيوط كتابة الملفات على القرص
BIG_FILE = 8 * 1024 * 1024         # من الحجم ده يتعامل معاه كملف كبير (قناة منفصلة)
BIG_WORKERS = 4                    # أقصى عدد ملفات كبيرة بتتحمل مع بعض
SEG_MIN = 32 * 1024 * 1024         # من الحجم ده الملف بيتقسم لأجزاء متوازية
SEG_SIZE = 16 * 1024 * 1024        # حجم الجزء الواحد
SEG_CONN = 4                       # عدد الاتصالات للملف الكبير الواحد
CHUNK = 1024 * 1024                # حجم القراءة/الكتابة للملفات الكبيرة
INDEX_FILE = os.path.join(BASE_DIR, "download_index.json")
PARTIAL_DIR = os.path.join(OUTPUT_ROOT, ".partial")
LIST_BATCH = 500                   # عدد الفروع في كل طلب لقراءة قايمة الملفات

# Colors
BG, CARD, CARD2, BORDER = "#0a0e17", "#111827", "#1a2233", "#243049"
TEXT, MUTED = "#e5e7eb", "#8b95a9"
GREEN, GREEN_H = "#10b981", "#059669"
BLUE, BLUE_H = "#3b82f6", "#2563eb"
AMBER, AMBER_H = "#f59e0b", "#d97706"
RED, RED_H = "#ef4444", "#dc2626"

STATUS_COLORS = {
    "Ready": "#374151", "Scanning": BLUE, "Downloading": GREEN,
    "Paused": AMBER, "Stopped": RED, "Finished": "#8b5cf6", "Indexing": "#0ea5e9",
}


def id_key(name):
    """ترتيب الفروع: الأرقام الأول (بالقيمة) وبعدها الحروف."""
    return (0, int(name), name) if name.isdigit() else (1, 0, name)


def safe_name(name):
    name = re.sub(r'[<>:"|?*\\\x00-\x1f]', "_", name).rstrip(" .")
    return name or "_"


def parse_repo_input(val):
    """يرجّع owner/repo من رابط GitHub أو من الصيغة owner/repo، أو None."""
    val = val.strip()
    m = re.search(r"github\.com/([^/\s]+)/([^/\s#?]+)", val)
    if m:
        owner, repo = m.group(1), m.group(2)
    elif re.fullmatch(r"[\w.-]+/[\w.-]+", val):
        owner, repo = val.split("/")
    else:
        return None
    repo = repo[:-4] if repo.endswith(".git") else repo
    if not re.fullmatch(r"[\w.-]+", owner) or not re.fullmatch(r"[\w.-]+", repo):
        return None
    return f"{owner}/{repo}"


def blob_sha_bytes(data):
    """بصمة git للملف: sha1("blob <size>\\0" + content)."""
    return hashlib.sha1(b"blob %d\0" % len(data) + data).hexdigest()


def blob_sha_file(path):
    h = hashlib.sha1(b"blob %d\0" % os.path.getsize(path))
    with open(path, "rb") as f:
        while True:
            b = f.read(1 << 20)
            if not b:
                break
            h.update(b)
    return h.hexdigest()


def place_link(src, dst):
    """رابط صلب (من غير مساحة إضافية) أو نسخة محلية لو الرابط مش ممكن."""
    try:
        os.link(src, dst)
        return
    except OSError:
        pass
    tmp = dst + ".part"
    shutil.copyfile(src, tmp)
    os.replace(tmp, dst)


def extract_repos(line):
    """كل المستودعات في سطر واحد (رابط أو owner/repo)."""
    urls = re.findall(r"https?://github\.com/[^\s,;]+", line)
    found = [parse_repo_input(u) for u in urls] if urls else [parse_repo_input(line)]
    return found


def type_of(rel):
    ext = os.path.splitext(rel)[1].lstrip(".").lower()
    return re.sub(r"[^a-z0-9_-]", "", ext) or "other"


TYPE_NAMES = {1: b"commit", 2: b"tree", 3: b"blob", 4: b"tag"}


def pkt(text):
    data = text.encode() if isinstance(text, str) else text
    return b"%04x" % (len(data) + 4) + data


def build_fetch(wants):
    """طلب git protocol v2: كومتات + شجرة الملفات فقط (بدون محتوى الملفات)."""
    body = (pkt("command=fetch\n") + pkt("agent=git/2.43.0\n") + b"0001"
            + pkt("ofs-delta\n") + pkt("no-progress\n") + pkt("deepen 1\n")
            + pkt("filter blob:none\n"))
    body += b"".join(pkt(f"want {w}\n") for w in wants)
    return body + pkt("done\n") + b"0000"


def extract_pack(resp):
    """يفك pkt-lines ويرجّع بايتات الـ packfile."""
    pos, pack, in_pack = 0, bytearray(), False
    while pos + 4 <= len(resp):
        n = int(resp[pos:pos + 4], 16)
        if n in (0, 1, 2):
            pos += 4
            continue
        payload = resp[pos + 4:pos + n]
        pos += n
        if not in_pack:
            if payload.startswith(b"packfile"):
                in_pack = True
            elif payload.startswith(b"ERR"):
                raise RuntimeError(payload.decode(errors="replace"))
            continue
        band, chunk = payload[0], payload[1:]
        if band == 1:
            pack += chunk
        elif band == 3:
            raise RuntimeError(chunk.decode(errors="replace"))
    if not pack.startswith(b"PACK"):
        raise RuntimeError("no packfile in response")
    return bytes(pack)


def apply_delta(base, delta):
    pos = 0

    def varint():
        nonlocal pos
        v = shift = 0
        while True:
            b = delta[pos]
            pos += 1
            v |= (b & 0x7F) << shift
            shift += 7
            if not b & 0x80:
                return v

    varint()
    varint()
    out = bytearray()
    while pos < len(delta):
        op = delta[pos]
        pos += 1
        if op & 0x80:
            off = size = 0
            for i in range(4):
                if op & (1 << i):
                    off |= delta[pos] << (8 * i)
                    pos += 1
            for i in range(3):
                if op & (0x10 << i):
                    size |= delta[pos] << (8 * i)
                    pos += 1
            out += base[off:off + (size or 0x10000)]
        elif op:
            out += delta[pos:pos + op]
            pos += op
        else:
            raise ValueError("bad delta")
    return bytes(out)


def parse_pack(data):
    """يرجّع {sha_hex: (type_int, bytes)} لكل الكائنات في الـ pack."""
    count = int.from_bytes(data[8:12], "big")
    mv = memoryview(data)
    pos = 12
    by_off, by_sha, pending = {}, {}, []

    def store(off, typ, content):
        sha = hashlib.sha1(TYPE_NAMES[typ] + b" %d\0" % len(content) + content).hexdigest()
        by_off[off] = (typ, content)
        by_sha[sha] = (typ, content)

    for _ in range(count):
        start = pos
        b = data[pos]
        pos += 1
        typ, size, shift = (b >> 4) & 7, b & 15, 4
        while b & 0x80:
            b = data[pos]
            pos += 1
            size |= (b & 0x7F) << shift
            shift += 7
        base_off = base_sha = None
        if typ == 6:
            b = data[pos]
            pos += 1
            off = b & 0x7F
            while b & 0x80:
                b = data[pos]
                pos += 1
                off = ((off + 1) << 7) | (b & 0x7F)
            base_off = start - off
        elif typ == 7:
            base_sha = data[pos:pos + 20].hex()
            pos += 20
        d = zlib.decompressobj()
        out, p = [], pos
        step = max(size + (size >> 10) + 64, 256)
        while not d.eof:
            chunk = bytes(mv[p:p + step])
            if not chunk:
                raise ValueError("truncated pack")
            out.append(d.decompress(chunk))
            p += len(chunk)
        pos = p - len(d.unused_data)
        raw = b"".join(out)
        if typ in TYPE_NAMES:
            store(start, typ, raw)
        elif typ == 6:
            btyp, bdata = by_off[base_off]
            store(start, btyp, apply_delta(bdata, raw))
        elif typ == 7:
            pending.append((start, base_sha, raw))
    while pending:
        left = []
        for start, bsha, delta in pending:
            if bsha in by_sha:
                btyp, bdata = by_sha[bsha]
                store(start, btyp, apply_delta(bdata, delta))
            else:
                left.append((start, bsha, delta))
        if len(left) == len(pending):
            raise ValueError("unresolved delta")
        pending = left
    return by_sha


def parse_tree(content):
    i, out = 0, []
    while i < len(content):
        j = content.index(b" ", i)
        k = content.index(b"\0", j)
        out.append((content[i:j], content[j + 1:k].decode("utf-8", "replace"),
                    content[k + 1:k + 21].hex()))
        i = k + 21
    return out


def list_files(objs, commit_sha):
    """يرجّع قايمة مسارات كل الملفات في كومِت (أي نوع، أي مجلد فرعي)."""
    typ, content = objs[commit_sha]
    tree = content.split(b"\n", 1)[0].split(b" ", 1)[1].decode()
    files, stack = [], [("", tree)]
    while stack:
        prefix, sha = stack.pop()
        for mode, name, esha in parse_tree(objs[sha][1]):
            if mode == b"40000":
                stack.append((prefix + name + "/", esha))
            elif mode != b"160000":
                files.append((prefix + name, esha))
    return sorted(files)


def F(size=12, weight="normal", family="Segoe UI"):
    return ctk.CTkFont(family=family, size=size, weight=weight)


class ManifestHubApp(ctk.CTk):

    def __init__(self):
        super().__init__()
        self.title("Universal Pro Downloader")
        self.geometry("1100x700")
        self.minsize(820, 620)
        self.resizable(True, True)
        self.after(150, self.maximize)
        self.configure(fg_color=BG)

        self.is_running = False
        self.is_paused = False
        self.repo_url = ""        # المستودع اللي بيتحمل دلوقتي
        self.repos = []           # قايمة المستودعات المضافة
        self.last_repos = []
        self.out_dir = OUTPUT_ROOT
        self.index_cache, self.sha_to_path = {}, {}
        self.index_dirty = False
        self.idx_lock = threading.Lock()
        self.all_refs = {}
        self.token_logged = False
        self.ui_q = queue.Queue()
        self.choice_q = queue.Queue()
        self.branch_sha = {}
        self.token = ""
        self.token_ok = True
        self.repo_private = True
        self.log_lines = 0
        self.reset_stats()

        self.load_state_from_disk()
        self.build_ui()
        self.refresh_repo_label()
        self.log("System ready.")
        if not self.repos:
            self.log("Click 'Repositories' to add a repository first.")
        self.after(200, self.poll)

    # ------------------------------------------------------------------ UI
    def maximize(self):
        try:
            self.state("zoomed")
        except Exception:
            try:
                self.attributes("-zoomed", True)
            except Exception:
                pass

    def reset_stats(self):
        self.total = self.processed = self.ok = self.failed = self.files = self.bytes = 0
        self.types = set()
        self.start_time = None
        self.end_time = None
        self.paused_total, self.pause_started = 0.0, None
        self.samples = collections.deque()
        self.eta_ema = None
        self.big = {}                  # sha -> [الحجم, اللي نزل] للملفات الكبيرة
        self.net_total = self.net_done = 0
        self.small_bytes = self.small_done = 0
        self.reused = self.unverified = 0

    def build_ui(self):
        # Header
        header = ctk.CTkFrame(self, fg_color="transparent")
        header.pack(fill="x", padx=26, pady=(22, 10))
        ctk.CTkLabel(header, text="⚡", width=48, height=48, corner_radius=14,
                     fg_color=BLUE, font=F(24)).pack(side="left")
        tbox = ctk.CTkFrame(header, fg_color="transparent")
        tbox.pack(side="left", padx=14)
        ctk.CTkLabel(tbox, text="Universal Pro Downloader", font=F(21, "bold"),
                     text_color=TEXT).pack(anchor="w")
        ctk.CTkLabel(tbox, text="Fast bulk downloader for GitHub repositories",
                     font=F(12), text_color=MUTED).pack(anchor="w")
        self.btn_settings = ctk.CTkButton(
            header, text="⚙  Repositories", command=self.open_settings_popup,
            width=140, height=40, corner_radius=12, font=F(13, "bold"),
            fg_color=CARD2, hover_color=BORDER, border_width=1, border_color=BORDER)
        self.btn_settings.pack(side="right")

        # Repository card
        card = ctk.CTkFrame(self, fg_color=CARD, corner_radius=18,
                            border_width=1, border_color=BORDER)
        card.pack(fill="x", padx=26, pady=6)
        left = ctk.CTkFrame(card, fg_color="transparent")
        left.pack(side="left", padx=20, pady=16)
        ctk.CTkLabel(left, text="REPOSITORIES", font=F(10, "bold"),
                     text_color=MUTED).pack(anchor="w")
        self.lbl_repo = ctk.CTkLabel(left, text="", font=F(16, "bold"), text_color=TEXT)
        self.lbl_repo.pack(anchor="w", pady=(2, 0))
        right = ctk.CTkFrame(card, fg_color="transparent")
        right.pack(side="right", padx=20)
        self.chip_status = ctk.CTkLabel(right, text="Ready", width=120, height=30,
                                        corner_radius=15, fg_color=STATUS_COLORS["Ready"],
                                        font=F(12, "bold"))
        self.chip_status.pack(pady=(0, 6))
        self.chip_type = ctk.CTkLabel(right, text="Types: all files", width=170,
                                      height=26, corner_radius=13, fg_color=CARD2,
                                      font=F(11), text_color=MUTED)
        self.chip_type.pack()

        # App ID
        idcard = ctk.CTkFrame(self, fg_color=CARD, corner_radius=18,
                              border_width=1, border_color=BORDER)
        idcard.pack(fill="x", padx=26, pady=6)
        ctk.CTkLabel(idcard, text="APP ID  (optional)", font=F(10, "bold"),
                     text_color=MUTED).pack(anchor="w", padx=20, pady=(12, 0))
        idrow = ctk.CTkFrame(idcard, fg_color="transparent")
        idrow.pack(fill="x", padx=16, pady=(4, 14))
        self.entry_app = ctk.CTkEntry(
            idrow, height=40, corner_radius=10, fg_color=CARD2, border_color=BORDER,
            placeholder_text="Type an App ID (number or text) to get just that one — "
                             "leave empty to download everything")
        self.entry_app.pack(side="left", fill="x", expand=True)
        ctk.CTkButton(idrow, text="✕", width=40, height=40, corner_radius=10,
                      fg_color=CARD2, hover_color=BORDER,
                      command=lambda: self.entry_app.delete(0, "end")).pack(side="left", padx=(8, 0))

        # Stats
        stats = ctk.CTkFrame(self, fg_color="transparent")
        stats.pack(fill="x", padx=26, pady=6)
        stats.columnconfigure((0, 1, 2, 3), weight=1, uniform="s")
        self.v_done = self.stat_card(stats, 0, "Files saved", GREEN)
        self.v_left = self.stat_card(stats, 1, "Files left", AMBER)
        self.v_speed = self.stat_card(stats, 2, "Speed", BLUE)
        self.v_time = self.stat_card(stats, 3, "Elapsed", "#a78bfa")

        # Progress
        prog = ctk.CTkFrame(self, fg_color="transparent")
        prog.pack(fill="x", padx=26, pady=(8, 4))
        self.progress = ctk.CTkProgressBar(prog, height=14, corner_radius=7,
                                           fg_color=CARD2, progress_color=GREEN)
        self.progress.set(0)
        self.progress.pack(side="left", fill="x", expand=True)
        self.lbl_pct = ctk.CTkLabel(prog, text="0%", width=56, font=F(13, "bold"),
                                    text_color=TEXT)
        self.lbl_pct.pack(side="right", padx=(10, 0))

        # Buttons
        btns = ctk.CTkFrame(self, fg_color="transparent")
        btns.pack(fill="x", padx=26, pady=(10, 4))
        self.btn_start = ctk.CTkButton(
            btns, text="🚀  Start Download", command=self.start_download_thread,
            height=54, corner_radius=14, font=F(15, "bold"),
            fg_color=GREEN, hover_color=GREEN_H)
        self.btn_start.pack(fill="x", pady=(0, 8))
        row = ctk.CTkFrame(btns, fg_color="transparent")
        row.pack(fill="x")
        row.columnconfigure((0, 1, 2), weight=1, uniform="b")
        self.btn_pause = ctk.CTkButton(
            row, text="⏸  Pause", command=self.toggle_pause, height=44, corner_radius=12,
            font=F(13, "bold"), fg_color=AMBER, hover_color=AMBER_H, state="disabled")
        self.btn_pause.grid(row=0, column=0, sticky="ew", padx=(0, 5))
        self.btn_stop = ctk.CTkButton(
            row, text="⏹  Stop", command=self.stop_download, height=44, corner_radius=12,
            font=F(13, "bold"), fg_color=RED, hover_color=RED_H, state="disabled")
        self.btn_stop.grid(row=0, column=1, sticky="ew", padx=5)
        self.btn_open = ctk.CTkButton(
            row, text="📂  Open Folder", command=self.open_folder, height=44,
            corner_radius=12, font=F(13, "bold"), fg_color=CARD2, hover_color=BORDER,
            border_width=1, border_color=BORDER)
        self.btn_open.grid(row=0, column=2, sticky="ew", padx=(5, 0))

        # Activity log
        logcard = ctk.CTkFrame(self, fg_color=CARD, corner_radius=18,
                               border_width=1, border_color=BORDER)
        logcard.pack(fill="both", expand=True, padx=26, pady=(12, 22))
        ctk.CTkLabel(logcard, text="ACTIVITY", font=F(10, "bold"),
                     text_color=MUTED).pack(anchor="w", padx=18, pady=(12, 0))
        self.log_box = ctk.CTkTextbox(
            logcard, font=ctk.CTkFont(family="Consolas", size=12),
            fg_color="#0a0e17", text_color="#34d399", corner_radius=12)
        self.log_box.pack(fill="both", expand=True, padx=12, pady=12)
        self.log_box.configure(state="disabled")

    def stat_card(self, parent, col, title, color):
        c = ctk.CTkFrame(parent, fg_color=CARD, corner_radius=16,
                         border_width=1, border_color=BORDER)
        c.grid(row=0, column=col, sticky="ew", padx=4)
        v = ctk.CTkLabel(c, text="0", font=F(22, "bold"), text_color=color)
        v.pack(pady=(14, 0))
        t = ctk.CTkLabel(c, text=title, font=F(11), text_color=MUTED)
        t.pack(pady=(0, 14))
        v.title_lbl = t
        return v

    def refresh_repo_label(self):
        if not self.repos:
            txt = "No repository added"
        elif len(self.repos) == 1:
            txt = self.repos[0]
        else:
            txt = f"{len(self.repos)} repositories  ·  " + ", ".join(
                r.split("/")[1] for r in self.repos[:3]) + ("…" if len(self.repos) > 3 else "")
        self.lbl_repo.configure(text=txt)

    def set_status(self, name):
        self.chip_status.configure(text=name, fg_color=STATUS_COLORS.get(name, CARD2))

    def set_running(self, running):
        self.btn_start.configure(state="disabled" if running else "normal")
        self.btn_settings.configure(state="disabled" if running else "normal")
        self.btn_pause.configure(state="normal" if running else "disabled",
                                 text="⏸  Pause", fg_color=AMBER)
        self.btn_stop.configure(state="normal" if running else "disabled")

    def _write_log(self, message):
        self.log_box.configure(state="normal")
        self.log_box.insert("end", message + "\n")
        self.log_lines += 1
        if self.log_lines > 1000:
            self.log_box.delete("1.0", "201.0")
            self.log_lines -= 200
        self.log_box.see("end")
        self.log_box.configure(state="disabled")

    # ---------------------------------------- thread-safe UI messaging
    def log(self, message):
        self.ui_q.put(("log", f"[{time.strftime('%H:%M:%S')}] {message}"))

    def post(self, *msg):
        self.ui_q.put(msg)

    def poll(self):
        try:
            while True:
                m = self.ui_q.get_nowait()
                k = m[0]
                if k == "log":
                    self._write_log(m[1])
                elif k == "status":
                    self.set_status(m[1])
                elif k == "type":
                    self.chip_type.configure(text=m[1])
                elif k == "info":
                    messagebox.showinfo(m[1], m[2])
                elif k == "error":
                    messagebox.showerror("Error", m[1])
                elif k == "choose_types":
                    self.show_types_dialog(*m[1:])
                elif k == "ask_yesno":
                    self.choice_q.put(bool(messagebox.askyesno(m[1], m[2])))
                elif k == "repo_label":
                    self.lbl_repo.configure(text=m[1])
                elif k == "refresh_label":
                    self.refresh_repo_label()
                elif k == "finished":
                    self.set_running(False)
        except queue.Empty:
            pass
        self.refresh_stats()
        self.after(200, self.poll)

    def refresh_stats(self):
        t, p = self.total, self.processed
        self.progress.set(min(p / t, 1) if t else 0)
        self.lbl_pct.configure(text=f"{p / t * 100:.1f}%" if t else "0%")
        self.v_done.configure(text=f"{self.files:,}")
        if self.types:
            ts = sorted(self.types)
            self.chip_type.configure(text="Types: " + ", ".join(ts[:3]) + (f" +{len(ts) - 3}" if len(ts) > 3 else ""))
        self.v_left.configure(text=f"{max(t - p, 0):,}")
        now = time.time()
        el = 0.0
        if self.start_time:
            end = self.end_time or now
            paused = self.paused_total + ((now - self.pause_started) if self.pause_started else 0.0)
            el = max(end - self.start_time - paused, 0.0)
        self.v_speed.configure(text=f"{self.files / el:,.1f}/s" if el > 1 else "0/s")
        mb = self.bytes / 1048576
        self.v_speed.title_lbl.configure(
            text=f"Speed  ·  {mb / el:,.2f} MB/s" if el > 1 else "Speed")
        eta = ""
        if self.start_time and not self.end_time and p < t:
            if self.is_paused:
                eta = "  ·  paused"
            else:
                sec = self.estimate_eta(el)
                if sec is not None:
                    sec = int(sec)
                    eta = f"  ·  ETA ~{sec // 3600:d}:{sec % 3600 // 60:02d}:{sec % 60:02d}"
        self.v_time.title_lbl.configure(text="Elapsed" + eta)
        h, rem = divmod(int(el), 3600)
        m, s = divmod(rem, 60)
        self.v_time.configure(text=f"{h:02d}:{m:02d}:{s:02d}")

    def estimate_eta(self, el):
        """ETA من حجم البيانات المتبقي وسرعة آخر 40 ثانية (بيتجاهل فترات الإيقاف المؤقت)."""
        smp = self.samples
        if not smp or el - smp[-1][0] >= 1.0:
            smp.append((el, self.bytes, self.net_done))
        while len(smp) > 2 and el - smp[0][0] > 40:
            smp.popleft()
        if len(smp) < 2:
            return None
        dt = smp[-1][0] - smp[0][0]
        if dt < 5:
            return None
        byte_rate = (smp[-1][1] - smp[0][1]) / dt
        file_rate = (smp[-1][2] - smp[0][2]) / dt
        bigs = list(self.big.values())
        big_rem = sum(max(sz - dn, 0) for sz, dn in bigs)
        left = max(self.net_total - self.net_done - len(bigs), 0)
        if self.small_done >= 5 and byte_rate > 1024:
            sec = (left * (self.small_bytes / self.small_done) + big_rem) / byte_rate
        elif file_rate > 0 and not bigs:
            sec = left / file_rate
        else:
            return None
        self.eta_ema = sec if self.eta_ema is None else 0.7 * self.eta_ema + 0.3 * sec
        return self.eta_ema

    def show_types_dialog(self, counts, n, fast, preselect):
        win = ctk.CTkToplevel(self)
        win.title("File types found")
        win.geometry("540x600")
        win.minsize(460, 440)
        win.configure(fg_color=BG)
        win.transient(self)
        win.after(150, win.grab_set)
        win.after(200, win.lift)
        state = {"done": False}

        def finish(val):
            if state["done"]:
                return
            state["done"] = True
            self.choice_q.put(val)
            win.destroy()

        ctk.CTkLabel(win, text="File types in this database", font=F(19, "bold"),
                     text_color=TEXT).pack(pady=(22, 4))
        ctk.CTkLabel(
            win, justify="center", font=F(12), text_color=MUTED,
            text=(f"Found {len(counts)} file types across {n:,} branches.\n"
                  "Select the types you want, or select nothing to download EVERYTHING."),
        ).pack(padx=20)

        scroll = ctk.CTkScrollableFrame(win, fg_color=CARD, corner_radius=14,
                                        border_width=1, border_color=BORDER)
        scroll.pack(fill="both", expand=True, padx=22, pady=14)
        vars_ = {}
        for t, c in sorted(counts.items(), key=lambda kv: -kv[1]):
            var = ctk.BooleanVar(value=(t in preselect))
            vars_[t] = var
            label = "(no extension)" if t == "other" else f".{t}"
            ctk.CTkCheckBox(
                scroll, variable=var, font=F(13), text_color=TEXT,
                text=f"{label}     —     {c:,} files",
                fg_color=GREEN, hover_color=GREEN_H, corner_radius=6,
            ).pack(anchor="w", padx=14, pady=7)

        helpers = ctk.CTkFrame(win, fg_color="transparent")
        helpers.pack(fill="x", padx=22)
        ctk.CTkButton(helpers, text="Select all", width=110, height=32, corner_radius=10,
                      fg_color=CARD2, hover_color=BORDER,
                      command=lambda: [v.set(True) for v in vars_.values()]).pack(side="left")
        ctk.CTkButton(helpers, text="Clear", width=90, height=32, corner_radius=10,
                      fg_color=CARD2, hover_color=BORDER,
                      command=lambda: [v.set(False) for v in vars_.values()]
                      ).pack(side="left", padx=8)

        def start():
            chosen = [t for t, v in vars_.items() if v.get()]
            finish([] if len(chosen) == len(vars_) else chosen)  # [] = كل شيء

        bottom = ctk.CTkFrame(win, fg_color="transparent")
        bottom.pack(fill="x", padx=22, pady=(14, 20))
        bottom.columnconfigure((0, 1), weight=1, uniform="d")
        ctk.CTkButton(bottom, text="Cancel", height=44, corner_radius=12, font=F(13, "bold"),
                      fg_color=CARD2, hover_color=BORDER, border_width=1, border_color=BORDER,
                      command=lambda: finish(None)).grid(row=0, column=0, sticky="ew", padx=(0, 5))
        ctk.CTkButton(bottom, text="Start Download", height=44, corner_radius=12,
                      font=F(13, "bold"), fg_color=GREEN, hover_color=GREEN_H,
                      command=start).grid(row=0, column=1, sticky="ew", padx=(5, 0))
        win.protocol("WM_DELETE_WINDOW", lambda: finish(None))

    # -------------------------------------------------------- state / settings
    def read_state(self):
        if os.path.exists(STATE_FILE):
            try:
                with open(STATE_FILE, "r", encoding="utf-8") as f:
                    return json.load(f)
            except Exception:
                pass
        return {}

    def load_state_from_disk(self):
        d = self.read_state()
        self.repos = list(d.get("repos") or ([d["repo_url"]] if d.get("repo_url") else []))
        self.last_repos = list(d.get("last_repos", []))
        self.token = d.get("token", "")

    def write_state(self, **updates):
        data = self.read_state()
        data.update(updates)
        tmp = STATE_FILE + ".tmp"
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump(data, f)
        os.replace(tmp, STATE_FILE)

    def auth(self, kind):
        """هيدر التوكن. بيتبعت لمواقع GitHub فقط."""
        t = self.token if self.token_ok else ""
        if not t:
            return {}
        if kind == "git":
            cred = base64.b64encode(f"x-access-token:{t}".encode()).decode()
            return {"Authorization": f"Basic {cred}"}
        if kind == "api":
            return {"Authorization": f"Bearer {t}"}
        return {"Authorization": f"token {t}"}  # raw

    async def check_token(self):
        self.token_ok = True
        self.repo_private = True
        if not self.token:
            return
        hdr = {"User-Agent": "UniversalProDownloader/3.0",
               "Authorization": f"Bearer {self.token}"}
        try:
            async with aiohttp.ClientSession() as session:
                async with session.get("https://api.github.com/user", headers=hdr,
                                       timeout=aiohttp.ClientTimeout(total=15)) as r:
                    if r.status == 200:
                        if not self.token_logged:
                            who = (await r.json()).get("login", "")
                            self.log(f"GitHub token accepted ({who}).")
                            self.token_logged = True
                        # مستودع عام؟ التوكن مش محتاجه raw (ويمكن يعطّل الكاش)
                        async with session.get(
                                f"https://api.github.com/repos/{self.repo_url}", headers=hdr,
                                timeout=aiohttp.ClientTimeout(total=15)) as r2:
                            if r2.status == 200:
                                self.repo_private = bool((await r2.json()).get("private"))
                    elif r.status == 401:
                        self.token_ok = False
                        self.log("GitHub token was rejected — continuing without it.")
                    else:
                        self.log(f"Could not verify the GitHub token (HTTP {r.status}).")
        except Exception:
            self.log("Could not verify the GitHub token (network error).")

    def open_settings_popup(self):
        popup = ctk.CTkToplevel(self)
        popup.title("Repositories")
        popup.geometry("580x680")
        popup.minsize(500, 600)
        popup.configure(fg_color=BG)
        popup.transient(self)
        popup.after(150, popup.grab_set)

        ctk.CTkLabel(popup, text="Repositories", font=F(18, "bold"),
                     text_color=TEXT).pack(pady=(20, 2))
        ctk.CTkLabel(popup, text="Add GitHub links or  owner/repo.  Each repository gets its own folder.",
                     font=F(12), text_color=MUTED).pack()

        addrow = ctk.CTkFrame(popup, fg_color="transparent")
        addrow.pack(fill="x", padx=24, pady=(14, 8))
        entry = ctk.CTkEntry(addrow, height=40, corner_radius=10, fg_color=CARD2,
                             border_color=BORDER,
                             placeholder_text="https://github.com/owner/repo")
        entry.pack(side="left", fill="x", expand=True)

        def import_txt():
            path = filedialog.askopenfilename(
                parent=popup, title="Choose a .txt file (one repository link per line)",
                filetypes=[("Text files", "*.txt"), ("All files", "*.*")])
            if not path:
                return
            text = None
            for enc in ("utf-8-sig", "utf-16", "cp1256", "latin-1"):
                try:
                    with open(path, "r", encoding=enc) as f:
                        text = f.read()
                    break
                except (UnicodeError, OSError):
                    continue
            if text is None:
                messagebox.showerror("Error", "Could not read that file.", parent=popup)
                return
            known = {x.lower() for x in self.repos}
            added = dup = bad = 0
            for line in text.splitlines():
                line = line.strip()
                if not line or line.startswith("#"):
                    continue
                for repo in extract_repos(line):
                    if not repo:
                        bad += 1
                    elif repo.lower() in known:
                        dup += 1
                    else:
                        known.add(repo.lower())
                        self.repos.append(repo)
                        added += 1
            if added:
                self.write_state(repos=self.repos)
                self.refresh_repo_label()
            self.log(f"Imported {added} repositories from file.")
            render()
            messagebox.showinfo("Import finished",
                                f"Added: {added}\nAlready in list: {dup}\nInvalid lines: {bad}",
                                parent=popup)

        ctk.CTkButton(popup, text="📄  Import from .txt  (one link per line)", height=38,
                      corner_radius=10, font=F(13, "bold"), fg_color=CARD2, hover_color=BORDER,
                      border_width=1, border_color=BORDER, command=import_txt
                      ).pack(fill="x", padx=24, pady=(0, 6))

        listbox = ctk.CTkScrollableFrame(popup, fg_color=CARD, corner_radius=14,
                                         border_width=1, border_color=BORDER)
        listbox.pack(fill="both", expand=True, padx=24, pady=6)

        def render():
            for w in listbox.winfo_children():
                w.destroy()
            if not self.repos:
                ctk.CTkLabel(listbox, text="No repositories yet.", text_color=MUTED,
                             font=F(12)).pack(pady=20)
            for r in list(self.repos):
                row = ctk.CTkFrame(listbox, fg_color=CARD2, corner_radius=10)
                row.pack(fill="x", padx=6, pady=4)
                ctk.CTkLabel(row, text=r, font=F(13, "bold"), text_color=TEXT
                             ).pack(side="left", padx=12, pady=10)
                ctk.CTkButton(row, text="Remove", width=80, height=30, corner_radius=8,
                              fg_color=RED, hover_color=RED_H,
                              command=lambda r=r: remove(r)).pack(side="right", padx=8)

        def add():
            repo = parse_repo_input(entry.get())
            if not repo:
                messagebox.showerror("Error", "Invalid format. Use owner/repo or a GitHub link.",
                                     parent=popup)
                return
            if repo.lower() in [x.lower() for x in self.repos]:
                messagebox.showinfo("Already added", f"{repo} is already in the list.", parent=popup)
                return
            self.repos.append(repo)
            self.write_state(repos=self.repos)
            self.refresh_repo_label()
            self.log(f"Repository added: {repo}")
            entry.delete(0, "end")
            render()

        def remove(repo):
            self.repos = [x for x in self.repos if x != repo]
            self.last_repos = [x for x in self.last_repos if x != repo]
            self.write_state(repos=self.repos, last_repos=self.last_repos)
            self.refresh_repo_label()
            self.log(f"Repository removed: {repo}")
            render()

        ctk.CTkButton(addrow, text="Add", width=80, height=40, corner_radius=10,
                      font=F(13, "bold"), fg_color=GREEN, hover_color=GREEN_H,
                      command=add).pack(side="left", padx=(8, 0))
        entry.bind("<Return>", lambda e: add())
        render()

        ctk.CTkLabel(popup, text="GitHub token (optional)", font=F(13, "bold"),
                     text_color=TEXT).pack(pady=(10, 0))
        ctk.CTkLabel(popup, justify="center", font=F(11), text_color=MUTED,
                     text="Raises GitHub's limits and allows private repos. "
                          "Stored locally in download_state.json."
                     ).pack()
        tok = ctk.CTkEntry(popup, height=40, corner_radius=10, show="•", fg_color=CARD2,
                           border_color=BORDER, placeholder_text="ghp_xxxxxxxxxxxxxxxxxxxx")
        if self.token:
            tok.insert(0, self.token)
        tok.pack(fill="x", padx=24, pady=(8, 8))

        def close():
            self.token = tok.get().strip()
            self.token_logged = False
            self.write_state(token=self.token)
            popup.destroy()

        ctk.CTkButton(popup, text="Save & Close", command=close, height=42, corner_radius=12,
                      font=F(14, "bold"), fg_color=BLUE, hover_color=BLUE_H
                      ).pack(fill="x", padx=24, pady=(4, 18))
        popup.protocol("WM_DELETE_WINDOW", close)

    def show_repos_dialog(self, app_id, on_ok):
        """بيسأل: التحميل من أنهي مستودع (واحد أو أكتر)."""
        win = ctk.CTkToplevel(self)
        win.title("Choose repository")
        win.geometry("520x560")
        win.minsize(440, 420)
        win.configure(fg_color=BG)
        win.transient(self)
        win.after(150, win.grab_set)
        win.after(200, win.lift)

        ctk.CTkLabel(win, text="Download from which repository?", font=F(18, "bold"),
                     text_color=TEXT).pack(pady=(22, 4))
        sub = (f"App ID:  {app_id}" if app_id else "Everything in the selected repositories")
        ctk.CTkLabel(win, text=sub + "\nSelected repositories are downloaded one by one.",
                     font=F(12), text_color=MUTED, justify="center").pack(padx=20)
        scroll = ctk.CTkScrollableFrame(win, fg_color=CARD, corner_radius=14,
                                        border_width=1, border_color=BORDER)
        scroll.pack(fill="both", expand=True, padx=22, pady=14)
        pre = [r for r in self.last_repos if r in self.repos] or (
            list(self.repos) if len(self.repos) == 1 else [])
        vars_ = {}
        for r in self.repos:
            v = ctk.BooleanVar(value=(r in pre))
            vars_[r] = v
            ctk.CTkCheckBox(scroll, variable=v, text=r, font=F(13), text_color=TEXT,
                            fg_color=GREEN, hover_color=GREEN_H, corner_radius=6
                            ).pack(anchor="w", padx=14, pady=7)

        helpers = ctk.CTkFrame(win, fg_color="transparent")
        helpers.pack(fill="x", padx=22)
        ctk.CTkButton(helpers, text="Select all", width=110, height=32, corner_radius=10,
                      fg_color=CARD2, hover_color=BORDER,
                      command=lambda: [v.set(True) for v in vars_.values()]).pack(side="left")
        ctk.CTkButton(helpers, text="Clear", width=90, height=32, corner_radius=10,
                      fg_color=CARD2, hover_color=BORDER,
                      command=lambda: [v.set(False) for v in vars_.values()]
                      ).pack(side="left", padx=8)

        def go():
            chosen = [r for r in self.repos if vars_[r].get()]
            if not chosen:
                messagebox.showerror("Error", "Select at least one repository.", parent=win)
                return
            win.destroy()
            on_ok(chosen)

        bottom = ctk.CTkFrame(win, fg_color="transparent")
        bottom.pack(fill="x", padx=22, pady=(14, 20))
        bottom.columnconfigure((0, 1), weight=1, uniform="d")
        ctk.CTkButton(bottom, text="Cancel", height=44, corner_radius=12, font=F(13, "bold"),
                      fg_color=CARD2, hover_color=BORDER, border_width=1, border_color=BORDER,
                      command=win.destroy).grid(row=0, column=0, sticky="ew", padx=(0, 5))
        ctk.CTkButton(bottom, text="Start Download", height=44, corner_radius=12,
                      font=F(13, "bold"), fg_color=GREEN, hover_color=GREEN_H,
                      command=go).grid(row=0, column=1, sticky="ew", padx=(5, 0))

    # ---------------------------------------------------------------- controls
    def toggle_pause(self):
        if not self.is_paused:
            self.is_paused = True
            self.pause_started = time.time()
            self.btn_pause.configure(text="▶  Resume", fg_color=GREEN, hover_color=GREEN_H)
            self.set_status("Paused")
            self.log("Paused.")
        else:
            self.is_paused = False
            self.resume_clock()
            self.btn_pause.configure(text="⏸  Pause", fg_color=AMBER, hover_color=AMBER_H)
            self.set_status("Downloading")
            self.log("Resumed.")

    def resume_clock(self):
        if self.pause_started:
            self.paused_total += time.time() - self.pause_started
            self.pause_started = None

    def stop_download(self):
        self.is_running = False
        self.is_paused = False
        self.resume_clock()
        self.log("Stopping... progress will be saved.")

    def open_folder(self):
        os.makedirs(OUTPUT_ROOT, exist_ok=True)
        path = os.path.abspath(OUTPUT_ROOT)
        if sys.platform.startswith("win"):
            os.startfile(path)
        elif sys.platform == "darwin":
            subprocess.Popen(["open", path])
        else:
            subprocess.Popen(["xdg-open", path])

    def start_download_thread(self):
        if not self.repos:
            messagebox.showerror("Error", "Add a repository first (Repositories button).")
            return
        app_id = self.entry_app.get().strip()
        self.show_repos_dialog(app_id, lambda sel: self._begin(sel, app_id))

    def _begin(self, selected, app_id):
        self.last_repos = list(selected)
        self.write_state(last_repos=self.last_repos)
        self.is_running = True
        self.is_paused = False
        self.choice_q = queue.Queue()
        self.token_logged = False
        self.reset_stats()
        self.set_running(True)
        self.set_status("Scanning")
        threading.Thread(target=lambda: asyncio.run(self.run_pipeline(selected, app_id)),
                         daemon=True).start()

    def on_closing(self):
        self.is_running = False
        self.choice_q.put(None)
        self.destroy()

    # ------------------------------------------------------------ file layout
    def scan_existing(self, out_dir):
        """يرجّع (names, counts): أسماء الملفات الموجودة لكل نوع، وعدد ملفات كل مجلد."""
        names, counts = {}, {}
        if os.path.isdir(out_dir):
            for t in os.listdir(out_dir):
                tdir = os.path.join(out_dir, t)
                if not os.path.isdir(tdir):
                    continue
                for item in os.listdir(tdir):
                    p = os.path.join(tdir, item)
                    if not (os.path.isdir(p) and item.isdigit()):
                        continue
                    n = 0
                    with os.scandir(p) as it:
                        for e in it:
                            if not e.is_file():
                                continue
                            if e.name.endswith(".part"):  # ملف ناقص من تشغيل سابق
                                try:
                                    os.remove(e.path)
                                except OSError:
                                    pass
                                continue
                            names.setdefault(t, set()).add(e.name)
                            n += 1
                    counts[(t, int(item))] = n
        return names, counts

    # ------------------------------------------- قراءة قايمة ملفات كل فرع
    async def list_all(self, ids):
        """يرجّع {id: [paths]} لكل ملف متخزن في كل فرع (من غير ZIP ومن غير تحميل المحتوى)."""
        listing, failed_ids = {}, []
        have = [i for i in ids if i in self.branch_sha]
        failed_ids += [i for i in ids if i not in self.branch_sha]
        self.total, self.processed = len(ids), 0
        url = f"https://github.com/{self.repo_url}.git/git-upload-pack"
        hdr = {"User-Agent": "git/2.43.0", "Git-Protocol": "version=2",
               "Content-Type": "application/x-git-upload-pack-request",
               "Accept": "application/x-git-upload-pack-result", **self.auth("git")}
        sem = asyncio.Semaphore(6)
        connector = aiohttp.TCPConnector(limit=20)
        async with aiohttp.ClientSession(connector=connector) as session:

            async def do_batch(batch):
                async with sem:
                    for attempt in range(3):
                        if not self.is_running:
                            return
                        try:
                            body = build_fetch([self.branch_sha[i] for i in batch])
                            async with session.post(
                                    url, data=body, headers=hdr,
                                    timeout=aiohttp.ClientTimeout(total=180)) as r:
                                if r.status != 200:
                                    raise RuntimeError(f"HTTP {r.status}")
                                data = await r.read()

                            def work():
                                objs = parse_pack(extract_pack(data))
                                return {i: list_files(objs, self.branch_sha[i]) for i in batch}

                            listing.update(await asyncio.to_thread(work))
                            self.processed += len(batch)
                            return
                        except Exception:
                            await asyncio.sleep(1 + attempt)
                    failed_ids.extend(batch)

            await asyncio.gather(*[do_batch(have[i:i + LIST_BATCH])
                                   for i in range(0, len(have), LIST_BATCH)])

            # احتياطي: GitHub Tree API لأي فرع فشلت قراءته (له حد طلبات)
            if failed_ids and self.is_running:
                self.log(f"Reading {len(failed_ids):,} branches through the GitHub API...")
                api_sem = asyncio.Semaphore(10)

                async def api_one(aid):
                    ref = self.branch_sha.get(aid, str(aid))
                    u = (f"https://api.github.com/repos/{self.repo_url}"
                         f"/git/trees/{ref}?recursive=1")
                    async with api_sem:
                        async with session.get(
                                u, headers={"User-Agent": "UniversalProDownloader/3.0", **self.auth("api")},
                                timeout=aiohttp.ClientTimeout(total=30)) as r:
                            if r.status in (403, 429):
                                raise RuntimeError("GitHub API rate limit reached")
                            if r.status != 200:
                                return
                            d = await r.json()
                            listing[aid] = sorted(
                                (i["path"], i["sha"]) for i in d.get("tree", [])
                                if i.get("type") == "blob")
                            self.processed += 1

                await asyncio.gather(*[api_one(a) for a in failed_ids])
        self.total = self.processed = 0
        return listing

    # ----------------------------------------------------------- id discovery
    async def fetch_all_ids_flexible(self):
        """يقرأ كل الفروع (الاسم ← commit sha). يرجّع أسماء الفروع الرقمية."""
        numeric = set()
        self.all_refs = {}
        try:
            async with aiohttp.ClientSession() as session:
                ref_url = (f"https://github.com/{self.repo_url}.git/info/refs"
                           "?service=git-upload-pack")
                headers = {"User-Agent": "git/2.34.1",
                           "Accept": "application/x-git-upload-pack-advertisement, */*",
                           **self.auth("git")}
                async with session.get(ref_url, headers=headers,
                                       timeout=aiohttp.ClientTimeout(total=30)) as resp:
                    if resp.status == 200:
                        text = await resp.text()
                        for sha, name in re.findall(
                                r"([0-9a-f]{40}) refs/heads/([^\n\0]+)", text):
                            self.all_refs[name] = sha
                            if name.isdigit():
                                numeric.add(name)
        except Exception:
            pass
        return numeric

    def find_app_id(self, app_id):
        """يدوّر على الفرع بالاسم (بالظبط، وبعدها بدون حساسية للحروف)."""
        if app_id in self.all_refs:
            return app_id
        low = [n for n in self.all_refs if n.lower() == app_id.lower()]
        return low[0] if len(low) == 1 else None

    async def lookup_branch_api(self, name):
        """احتياطي لو قراءة الفروع فشلت: يسأل GitHub API عن فرع واحد."""
        try:
            async with aiohttp.ClientSession() as session:
                async with session.get(
                        f"https://api.github.com/repos/{self.repo_url}/branches/"
                        f"{quote(name, safe='')}",
                        headers={"User-Agent": "UniversalProDownloader/3.0", **self.auth("api")},
                        timeout=aiohttp.ClientTimeout(total=20)) as r:
                    if r.status == 200:
                        sha = (await r.json())["commit"]["sha"]
                        self.all_refs[name] = sha
                        return name
        except Exception:
            pass
        return None

    # --------------------------------------------------------------- pipeline
    async def wait_if_paused(self):
        while self.is_paused and self.is_running:
            await asyncio.sleep(0.1)

    async def run_pipeline(self, repos, app_id):
        results = []
        try:
            await self.maybe_migrate_legacy(repos[0])
            self.post("status", "Indexing")
            await asyncio.to_thread(self.scan_index)
            for i, repo in enumerate(repos, 1):
                if not self.is_running:
                    break
                self.post("repo_label", (f"{i}/{len(repos)}  ·  " if len(repos) > 1 else "") + repo)
                status, n = await self._pipeline_repo(repo, app_id)
                await asyncio.to_thread(self.save_index)
                results.append((repo, status, n))
                if status == "cancelled":
                    break
            stopped = (not self.is_running) or any(r[1] in ("stopped", "cancelled") for r in results)
            self.post("status", "Stopped" if stopped else "Finished")
            msgs = {"finished": "{n:,} files saved", "stopped": "stopped ({n:,} files saved)",
                    "cancelled": "cancelled", "not_found": "App ID not found",
                    "empty": "no branches found", "error": "could not read the file list",
                    "uptodate": "already up to date"}
            lines = [f"{r}:  {msgs.get(st, st).format(n=n)}" for r, st, n in results]
            if lines and not any(st == "cancelled" for _r, st, _n in results):
                if all(st in ("not_found", "empty", "error") for _r, st, _n in results):
                    self.post("error", "\n".join(lines))
                else:
                    self.post("info", "Stopped" if stopped else "Finished", "\n".join(lines))
        except Exception as e:
            self.log_error()
            self.post("error", f"Unexpected error:\n{e}\n\n(Details saved in error_log.txt)")
            self.post("status", "Stopped")
        finally:
            self.end_time = time.time()
            self.is_running = False
            try:
                await asyncio.to_thread(self.save_index)
            except Exception:
                pass
            self.post("refresh_label")
            self.post("finished")

    # ------------------------------------------- فهرس بصمات كل الملفات الموجودة
    def index_add(self, path, sha):
        try:
            st = os.stat(path)
        except OSError:
            return
        rel = os.path.relpath(path, OUTPUT_ROOT)
        with self.idx_lock:
            self.index_cache[rel] = [st.st_size, st.st_mtime_ns, sha]
            self.sha_to_path.setdefault(sha, path)
            self.index_dirty = True

    def save_index(self):
        if not self.index_dirty:
            return
        with self.idx_lock:
            data = dict(self.index_cache)
            self.index_dirty = False
        try:
            tmp = INDEX_FILE + ".tmp"
            with open(tmp, "w", encoding="utf-8") as f:
                json.dump(data, f, separators=(",", ":"))
            os.replace(tmp, INDEX_FILE)
        except OSError:
            self.index_dirty = True

    def scan_index(self):
        """يمسح Downloaded_Files كله ويحسب بصمة أي ملف جديد (مرة واحدة، وبعدها بيحدّث نفسه)."""
        try:
            with open(INDEX_FILE, "r", encoding="utf-8") as f:
                cache = json.load(f)
        except Exception:
            cache = {}
        new, sha_to_path, todo = {}, {}, []
        if os.path.isdir(OUTPUT_ROOT):
            for root, dirs, files in os.walk(OUTPUT_ROOT):
                dirs[:] = [d for d in dirs if d != ".partial"]
                for fn in files:
                    if fn.endswith(".part"):
                        continue
                    pth = os.path.join(root, fn)
                    try:
                        st = os.stat(pth)
                    except OSError:
                        continue
                    rel = os.path.relpath(pth, OUTPUT_ROOT)
                    c = cache.get(rel)
                    if c and c[0] == st.st_size and c[1] == st.st_mtime_ns:
                        new[rel] = c
                        sha_to_path.setdefault(c[2], pth)
                    else:
                        todo.append((rel, pth, st))
        if todo:
            self.total, self.processed = len(todo), 0
            if len(todo) > 200:
                self.log(f"Checking {len(todo):,} files already on disk (first time only)...")

            def hash_one(item):
                if not self.is_running:
                    return None
                rel, pth, st = item
                try:
                    sha = blob_sha_file(pth)
                except OSError:
                    return None
                self.processed += 1
                return rel, pth, st, sha

            with ThreadPoolExecutor(max_workers=8) as ex:
                for res in ex.map(hash_one, todo):
                    if res:
                        rel, pth, st, sha = res
                        new[rel] = [st.st_size, st.st_mtime_ns, sha]
                        sha_to_path.setdefault(sha, pth)
            self.total = self.processed = 0
        with self.idx_lock:
            self.index_cache, self.sha_to_path = new, sha_to_path
            self.index_dirty = bool(todo) or len(new) != len(cache)

    def log_error(self):
        try:
            with open(ERROR_LOG, "a", encoding="utf-8") as f:
                f.write(f"--- {time.strftime('%Y-%m-%d %H:%M:%S')} ---\n{traceback.format_exc()}\n")
        except OSError:
            pass

    async def maybe_migrate_legacy(self, first_repo):
        """ملفات النسخة القديمة (Downloaded_Files/<type>/...) تتنقل لمجلد المستودع لو المستخدم وافق."""
        st = self.read_state()
        if st.get("legacy_skipped") or not os.path.isdir(OUTPUT_ROOT):
            return
        legacy = []
        for t in os.listdir(OUTPUT_ROOT):
            tdir = os.path.join(OUTPUT_ROOT, t)
            if "__" in t or not os.path.isdir(tdir):
                continue
            if any(c.isdigit() and os.path.isdir(os.path.join(tdir, c)) for c in os.listdir(tdir)):
                legacy.append(t)
        if not legacy:
            return
        self.post("ask_yesno", "Existing files found",
                  f"Found files from the previous version in '{OUTPUT_ROOT}'\n"
                  f"(types: {', '.join(sorted(legacy))}).\n\n"
                  f"Were they downloaded from  {first_repo}  ?\n"
                  "Yes = move them into that repository's folder (so they are not downloaded again).\n"
                  "No = leave them as they are.")
        ans = await asyncio.to_thread(self.choice_q.get)
        if ans is None:
            return
        if not ans:
            self.write_state(legacy_skipped=True)
            return
        dest = os.path.join(OUTPUT_ROOT, first_repo.replace("/", "__"))

        def move():
            os.makedirs(dest, exist_ok=True)
            for t in legacy:
                src, dst = os.path.join(OUTPUT_ROOT, t), os.path.join(dest, t)
                if not os.path.exists(dst):
                    shutil.move(src, dst)
                    continue
                nums = [int(c) for c in os.listdir(dst) if c.isdigit()]
                nxt = (max(nums) if nums else 0) + 1
                for c in sorted((c for c in os.listdir(src) if c.isdigit()), key=int):
                    shutil.move(os.path.join(src, c), os.path.join(dst, str(nxt)))
                    nxt += 1

        await asyncio.to_thread(move)
        self.log(f"Moved existing files into {dest}")

    async def _pipeline_repo(self, repo, app_id):
        """يحمّل مستودع واحد. يرجّع (الحالة, عدد الملفات المحفوظة)."""
        self.repo_url = repo
        self.out_dir = os.path.join(OUTPUT_ROOT, repo.replace("/", "__"))
        self.reset_stats()
        self.post("status", "Scanning")
        self.post("type", "Types: all files")
        await self.check_token()
        self.log(f"Scanning repository: {repo}")
        numeric = await self.fetch_all_ids_flexible()
        self.branch_sha = self.all_refs
        if app_id:
            key = self.find_app_id(app_id)
            if key is None and not self.all_refs:
                key = await self.lookup_branch_api(app_id)
            if key is None:
                self.log(f"App ID '{app_id}' was not found in {repo}.")
                return "not_found", 0
            ids = [key]
            self.log(f"Found App ID: {key}")
        else:
            ids = sorted(numeric or self.all_refs, key=id_key)
            if not ids:
                self.log("No branches found. Check the repository link.")
                return "empty", 0

        # ---- قراءة كل الملفات المتخزنة في الفروع (من غير ZIP)
        if len(ids) > 1:
            self.log(f"Reading the file list of {len(ids):,} branches...")
        listing = await self.list_all(ids)
        if not self.is_running:
            self.log("Stopped.")
            return "stopped", 0
        if not listing:
            self.log("Could not read the file list from GitHub (blocked or rate limited).")
            return "error", 0
        type_counts = {}
        for paths in listing.values():
            for pth, _sha in paths:
                t = type_of(pth)
                type_counts[t] = type_counts.get(t, 0) + 1
        self.log(f"Found {sum(type_counts.values()):,} files in {len(listing):,} branches.")
        if not type_counts:
            self.log("These branches contain no files.")
            return "finished", 0

        # ---- اختيار المستخدم (التحميل لا يبدأ قبل كده أبداً)
        saved = self.read_state().get("type_choices", {})
        if len(type_counts) >= 2:
            self.log(f"Found {len(type_counts)} file types. Waiting for your choice...")
            self.post("choose_types", type_counts, len(listing), set(), saved.get(repo, []))
            choice = await asyncio.to_thread(self.choice_q.get)
            if choice is None:
                self.log("Cancelled.")
                return "cancelled", 0
        else:
            choice = []
        allowed = set(choice) or None
        saved[repo] = sorted(choice)
        self.write_state(type_choices=saved)
        self.log("Selected types: " + (", ".join("." + t for t in sorted(allowed))
                                          if allowed else "ALL types"))
        self.post("type", "Types: " + (", ".join(sorted(allowed)) if allowed else "all"))

        # ---- الملفات المطلوبة (اللي مش موجودة على القرص)
        existing, counts = self.scan_existing(self.out_dir)
        jobs, reuse = [], []
        for aid in ids:
            bid = aid.replace("/", "__")
            for pth, sha in listing.get(aid, []):
                typ = type_of(pth)
                if allowed and typ not in allowed:
                    continue
                own = "/" not in pth and os.path.splitext(pth)[0] == aid
                name = safe_name(pth if own else f"{bid}_{pth.replace('/', '__')}")
                if name in existing.get(typ, ()):
                    continue
                src = self.sha_to_path.get(sha)  # نفس الملف موجود في أي مجلد جوه Downloaded_Files؟
                if src and os.path.exists(src):
                    reuse.append((typ, name, src, sha))
                else:
                    jobs.append((aid, pth, typ, name, sha))
        self.total = len(jobs) + len(reuse)
        self.log(f"Files to download: {len(jobs):,}"
                 + (f"   (+{len(reuse):,} already on disk — no download)" if reuse else ""))
        if not jobs and not reuse:
            self.log("Everything is already downloaded.")
            return "uptodate", 0

        cur, made = {}, set()
        lock = threading.Lock()
        loop = asyncio.get_running_loop()
        pool = ThreadPoolExecutor(max_workers=WRITE_THREADS)
        out_dir = self.out_dir

        def reserve(typ, name):
            """يحدد مسار الملف (ويحجز مكانه). آمن للاستخدام من أكتر من خيط."""
            with lock:
                idx = cur.get(typ, 1)
                while counts.get((typ, idx), 0) >= FOLDER_LIMIT:
                    idx += 1
                cur[typ] = idx
                folder = os.path.join(out_dir, typ, str(idx))
                if folder not in made:
                    os.makedirs(folder, exist_ok=True)
                    made.add(folder)
                counts[(typ, idx)] = counts.get((typ, idx), 0) + 1
                return os.path.join(folder, name)

        def write_sync(path, data):
            with open(path + ".part", "wb") as f:
                f.write(data)
            os.replace(path + ".part", path)

        async def run_pooled(fn, *args):
            """يشغّل شغل تقيل في خيط، ولا يتلغي نص الطريق (عشان الملف ما يتكتبش ناقص)."""
            fut = loop.run_in_executor(pool, fn, *args)
            while not fut.done():
                try:
                    await asyncio.shield(fut)
                except asyncio.CancelledError:
                    pass
            return fut.result()

        # الملفات المتطابقة (نفس المحتوى في أكتر من فرع) تتحمل مرة واحدة وتتنسخ لباقي الأماكن
        dup_map, uniq, seen = {}, [], set()
        for j in jobs:
            if j[4] in seen:
                dup_map.setdefault(j[4], []).append(j)
            else:
                seen.add(j[4])
                uniq.append(j)
        jobs = uniq
        self.net_total = len(jobs)

        ptr = 0
        failed, active = [], set()
        retry = collections.deque()      # ملفات اتلغت بسبب الإيقاف المؤقت → تتكرر
        big_queue = collections.deque()  # ملفات كبيرة مستنية قناتها الخاصة
        main_done = [False]
        ctl = {"limit": START_CONN, "busy": 0, "r429": 0, "hold": 0.0}
        raw_hdr = self.auth("raw") if self.repo_private else {}
        file_timeout = aiohttp.ClientTimeout(total=120, sock_connect=10, sock_read=60)
        big_timeout = aiohttp.ClientTimeout(total=None, sock_connect=15, sock_read=90)
        connector = aiohttp.TCPConnector(limit=MAX_CONN + 50, force_close=False,
                                         keepalive_timeout=60, ttl_dns_cache=600)

        async def monitor():
            """عند الإيقاف المؤقت/الإيقاف: يلغي كل الطلبات الجارية فوراً."""
            while True:
                await asyncio.sleep(0.1)
                if (self.is_paused or not self.is_running) and active:
                    for t in list(active):
                        t.cancel()

        monitor_task = asyncio.create_task(monitor())
        self.start_time = time.time()
        self.post("status", "Downloading")
        self.log("Download started.")

        # ---- ملفات موجودة عندنا (من مستودع تاني): رابط من غير تحميل
        for i in range(0, len(reuse), 200):
            await self.wait_if_paused()
            if not self.is_running:
                break
            part = reuse[i:i + 200]

            def link_batch(part=part):
                for typ_, name_, src_, sha_ in part:
                    dst = reserve(typ_, name_)
                    place_link(src_, dst)
                    self.index_add(dst, sha_)

            await run_pooled(link_batch)
            for r_ in part:
                self.types.add(r_[0])
            self.files += len(part)
            self.ok += len(part)
            self.processed += len(part)
            self.reused += len(part)

        async with aiohttp.ClientSession(connector=connector) as session:

            async def fetch_job(job):
                aid, pth, typ, name, sha = job
                url = (f"https://raw.githubusercontent.com/{self.repo_url}/{quote(aid, safe='/')}/"
                       f"{quote(pth, safe='/')}")
                errs = waits = bad_hash = 0
                while errs < 3 and waits < 8:
                    status = data = None
                    is_big, size_hint = False, 0
                    try:
                        async with session.get(url, headers=raw_hdr,
                                               timeout=file_timeout) as r:
                            status = r.status
                            if status == 200:
                                cl = r.content_length
                                if cl is not None and cl >= BIG_FILE:
                                    is_big, size_hint = True, cl
                                elif cl is not None:
                                    data = await r.read()  # الملف زي ما هو
                                else:
                                    buf = bytearray()
                                    async for chunk in r.content.iter_chunked(CHUNK):
                                        buf += chunk
                                        if len(buf) >= BIG_FILE:
                                            is_big, size_hint = True, len(buf)
                                            break
                                    if not is_big:
                                        data = bytes(buf)
                    except Exception:
                        errs += 1
                        await asyncio.sleep(0.5)
                        continue
                    # الاتصال اتقفل هنا — الانتظار والكتابة برّاه
                    if is_big:
                        self.big[sha] = [size_hint, 0]
                        return "big"
                    if status == 200:
                        dests = [(typ, name)] + [(j[2], j[3]) for j in dup_map.get(sha, ())]
                        accept = bad_hash >= 1

                        def write_all(dests=dests, data=data, accept=accept):
                            good = blob_sha_bytes(data) == sha
                            if not good and not accept:
                                return None
                            for t_, n_ in dests:
                                pth_ = reserve(t_, n_)
                                write_sync(pth_, data)
                                if good:
                                    self.index_add(pth_, sha)
                            return good

                        good = await run_pooled(write_all)
                        if good is None:        # البصمة مش مطابقة → حاول مرة كمان
                            bad_hash += 1
                            continue
                        if not good:
                            self.unverified += len(dests)
                        for t_, _n in dests:
                            self.types.add(t_)
                        self.files += len(dests)
                        self.ok += len(dests) - 1
                        self.processed += len(dests) - 1
                        self.bytes += len(data)
                        self.small_bytes += len(data)
                        self.small_done += 1
                        return "ok"
                    elif status == 429:
                        waits += 1
                        ctl["r429"] += 1
                        await asyncio.sleep(1.0 + waits * 0.5)
                    elif status == 404:
                        return "not_found"
                    else:
                        errs += 1
                        await asyncio.sleep(0.3)
                return "failed"

            async def worker():
                nonlocal ptr
                while self.is_running:
                    await self.wait_if_paused()
                    if not self.is_running:
                        break
                    if ctl["busy"] >= ctl["limit"]:
                        await asyncio.sleep(0.02)
                        continue
                    if retry:
                        job = retry.popleft()
                    elif ptr < len(jobs):
                        job = jobs[ptr]
                        ptr += 1
                    else:
                        break
                    ctl["busy"] += 1
                    task = asyncio.ensure_future(fetch_job(job))
                    active.add(task)
                    try:
                        st = await task
                    except asyncio.CancelledError:
                        st = "cancelled"
                    finally:
                        active.discard(task)
                        ctl["busy"] -= 1
                    if st == "cancelled":
                        retry.append(job)
                        continue
                    if st == "big":              # ملف كبير → قناته الخاصة
                        big_queue.append(job)
                        continue
                    extra = len(dup_map.get(job[4], ()))
                    if st == "failed":
                        failed.append(job)
                        self.failed += 1
                        self.processed += extra
                    elif st == "ok":
                        self.ok += 1
                    else:
                        self.processed += extra
                    self.processed += 1
                    self.net_done += 1

            # ------------------------------------------------ الملفات الكبيرة
            async def write_chunk(fh, data, pos=None):
                def w():
                    if pos is not None:
                        fh.seek(pos)
                    fh.write(data)
                await run_pooled(w)

            def count(sha, n):
                self.bytes += n
                ent = self.big.get(sha)
                if ent:
                    ent[1] += n

            async def probe(url, hdr):
                """حجم الملف وهل السيرفر بيدعم Range."""
                async with session.get(url, headers={**hdr, "Range": "bytes=0-0"},
                                       timeout=file_timeout) as r:
                    if r.status == 206:
                        m = re.search(r"/(\d+)$", r.headers.get("Content-Range", ""))
                        return 206, int(m.group(1)) if m else None
                    if r.status == 200:
                        return 200, r.content_length
                    return r.status, None

            async def stream_single(url, hdr, part, total, ranges_ok, sha):
                have = os.path.getsize(part) if os.path.exists(part) else 0
                if have > total or (have and not ranges_ok):
                    have = 0
                h = dict(hdr)
                if have:
                    h["Range"] = f"bytes={have}-"
                self.big[sha] = [total, have]
                async with session.get(url, headers=h, timeout=big_timeout) as r:
                    if r.status not in (200, 206):
                        raise RuntimeError(f"HTTP {r.status}")
                    if have and r.status != 206:      # السيرفر تجاهل Range → من الأول
                        have = 0
                        self.big[sha][1] = 0
                    fh = open(part, "ab" if have else "wb")
                    try:
                        async for chunk in r.content.iter_chunked(CHUNK):
                            await write_chunk(fh, chunk)
                            count(sha, len(chunk))
                    finally:
                        fh.close()
                if os.path.getsize(part) != total:
                    raise RuntimeError("size mismatch")

            async def stream_segments(url, hdr, part, side, total, sha):
                nseg = -(-total // SEG_SIZE)
                done = set()
                try:
                    with open(side, "r", encoding="utf-8") as f:
                        meta = json.load(f)
                    if (meta.get("size") == total and os.path.exists(part)
                            and os.path.getsize(part) == total):
                        done = set(meta.get("done", []))
                except Exception:
                    pass
                if not done and not (os.path.exists(part) and os.path.getsize(part) == total):
                    with open(part, "wb") as f:
                        f.truncate(total)

                def seg_len(i):
                    return min(total, (i + 1) * SEG_SIZE) - i * SEG_SIZE

                self.big[sha] = [total, sum(seg_len(i) for i in done)]

                def save_side():
                    tmp = side + ".tmp"
                    with open(tmp, "w", encoding="utf-8") as f:
                        json.dump({"size": total, "done": sorted(done)}, f)
                    os.replace(tmp, side)

                sem = asyncio.Semaphore(SEG_CONN)

                async def seg(i):
                    start = i * SEG_SIZE
                    end = start + seg_len(i) - 1
                    async with sem:
                        for attempt in range(3):
                            counted = 0
                            try:
                                async with session.get(
                                        url, headers={**hdr, "Range": f"bytes={start}-{end}"},
                                        timeout=big_timeout) as r:
                                    if r.status != 206:
                                        raise RuntimeError(f"HTTP {r.status}")
                                    fh = open(part, "r+b")
                                    try:
                                        pos = start
                                        async for chunk in r.content.iter_chunked(CHUNK):
                                            await write_chunk(fh, chunk, pos)
                                            pos += len(chunk)
                                            counted += len(chunk)
                                            count(sha, len(chunk))
                                    finally:
                                        fh.close()
                                if pos != end + 1:
                                    raise RuntimeError("short segment")
                                done.add(i)
                                save_side()
                                return
                            except asyncio.CancelledError:
                                count(sha, -counted)
                                raise
                            except Exception:
                                count(sha, -counted)
                                await asyncio.sleep(1 + attempt)
                        raise RuntimeError("segment failed")

                res = await asyncio.gather(*[seg(i) for i in range(nseg) if i not in done],
                                           return_exceptions=True)
                for x in res:
                    if isinstance(x, asyncio.CancelledError):
                        raise x
                    if isinstance(x, BaseException):
                        raise x

            async def big_fetch(job):
                aid, pth, typ, name, sha = job
                url = (f"https://raw.githubusercontent.com/{self.repo_url}/{quote(aid, safe='/')}/"
                       f"{quote(pth, safe='/')}")
                hdr = {**raw_hdr, "Accept-Encoding": "identity"}
                os.makedirs(PARTIAL_DIR, exist_ok=True)
                part = os.path.join(PARTIAL_DIR, sha + ".part")
                side = part + ".json"
                for attempt in range(3):
                    if not self.is_running:
                        return "cancelled"
                    try:
                        status, total = await probe(url, hdr)
                        if status == 404:
                            return "not_found"
                        if status == 429:
                            ctl["r429"] += 1
                            await asyncio.sleep(2 + attempt * 2)
                            continue
                        if total is None or status not in (200, 206):
                            raise RuntimeError(f"HTTP {status}")
                        if total >= SEG_MIN and status == 206:
                            await stream_segments(url, hdr, part, side, total, sha)
                        else:
                            await stream_single(url, hdr, part, total, status == 206, sha)
                        good = await run_pooled(blob_sha_file, part) == sha
                        dests = [(typ, name)] + [(j[2], j[3]) for j in dup_map.get(sha, ())]

                        def place():
                            first = reserve(*dests[0])
                            os.replace(part, first)
                            if good:
                                self.index_add(first, sha)
                            for t_, n_ in dests[1:]:
                                p2 = reserve(t_, n_)
                                place_link(first, p2)
                                if good:
                                    self.index_add(p2, sha)

                        await run_pooled(place)
                        try:
                            os.remove(side)
                        except OSError:
                            pass
                        if not good:
                            self.unverified += len(dests)
                        for t_, _n in dests:
                            self.types.add(t_)
                        self.files += len(dests)
                        return "ok"
                    except asyncio.CancelledError:
                        raise
                    except Exception:
                        await asyncio.sleep(1 + attempt)
                return "failed"

            async def big_worker():
                while self.is_running:
                    await self.wait_if_paused()
                    if not self.is_running:
                        break
                    if big_queue:
                        job = big_queue.popleft()
                    elif main_done[0]:
                        break
                    else:
                        await asyncio.sleep(0.2)
                        continue
                    task = asyncio.ensure_future(big_fetch(job))
                    active.add(task)
                    try:
                        st = await task
                    except asyncio.CancelledError:
                        st = "cancelled"
                    finally:
                        active.discard(task)
                    if st == "cancelled":
                        big_queue.appendleft(job)
                        continue
                    dups = len(dup_map.get(job[4], ()))
                    self.big.pop(job[4], None)
                    if st == "ok":
                        self.ok += 1 + dups
                    elif st == "failed":
                        failed.append(job)
                        self.failed += 1
                    self.processed += 1 + dups
                    self.net_done += 1

            async def run_main():
                await asyncio.gather(*[worker() for _ in range(MAX_CONN)])
                main_done[0] = True

            async def tuner():
                """يدوّر على أعلى إنتاجية: يزوّد الاتصالات طالما السرعة بتزيد، ويثبّت عند
                أفضل رقم، ويقلل لو GitHub رفض (429)."""
                def work():
                    return self.bytes + 4096 * self.files

                last, best_thr, best_limit = work(), 0.0, ctl["limit"]
                last_probe = time.time()
                while True:
                    await asyncio.sleep(TUNE_WINDOW)
                    now = time.time()
                    w = work()
                    thr = (w - last) / TUNE_WINDOW
                    last = w
                    r429, ctl["r429"] = ctl["r429"], 0
                    if self.is_paused:
                        continue
                    if r429 >= 3:
                        new = max(MIN_CONN, int(min(ctl["limit"], max(ctl["busy"], MIN_CONN)) * 0.8))
                        if new < ctl["limit"]:
                            self.log(f"GitHub is throttling — using {new} connections.")
                        ctl["limit"], best_limit, best_thr = new, new, 0.0
                        ctl["hold"] = now + 10
                        continue
                    if now < ctl["hold"] or thr <= 0:
                        continue
                    if thr >= best_thr * 1.05 and ctl["busy"] >= ctl["limit"] * 0.9:
                        best_thr, best_limit = thr, ctl["limit"]       # لسه بتتحسن → زوّد
                        ctl["limit"] = min(MAX_CONN, int(ctl["limit"] * 1.25) + 5)
                    elif thr < best_thr * 0.8 and ctl["limit"] > best_limit:
                        ctl["limit"] = best_limit                         # الزيادة ما فادتش → ارجع
                        ctl["hold"] = now + 30
                        best_thr = thr
                    elif now - last_probe > 45 and ctl["limit"] < MAX_CONN:
                        last_probe = now                                  # جرّب تزوّد تاني شوية
                        best_thr = max(best_thr, thr)
                        ctl["limit"] = min(MAX_CONN, int(ctl["limit"] * 1.15) + 5)

            if self.is_running:
                helpers = [asyncio.create_task(tuner())]
                await asyncio.gather(run_main(), *[big_worker() for _ in range(BIG_WORKERS)])
                for h in helpers:
                    h.cancel()
        monitor_task.cancel()
        pool.shutdown(wait=True)

        self.end_time = time.time()
        if not self.is_running and self.processed < self.total:
            self.log("Download stopped. Progress saved — press Start to resume.")
            return "stopped", self.files
        if failed:
            self.log(f"{len(failed):,} files failed. Press Start again to retry them.")
        if self.reused:
            self.log(f"Reused {self.reused:,} files already on disk (no download).")
        if self.unverified:
            self.log(f"{self.unverified:,} files do not match their git hash (Git LFS pointers?).")
        self.log(f"Download finished. Files saved: {self.files:,}")
        return "finished", self.files


if __name__ == "__main__":
    app = ManifestHubApp()
    def _tk_error(exc, val, tb):
        try:
            with open(ERROR_LOG, "a", encoding="utf-8") as f:
                f.write(f"--- {time.strftime('%Y-%m-%d %H:%M:%S')} ---\n"
                        + "".join(traceback.format_exception(exc, val, tb)) + "\n")
        except OSError:
            pass
    app.report_callback_exception = _tk_error
    app.protocol("WM_DELETE_WINDOW", app.on_closing)
    app.mainloop()
