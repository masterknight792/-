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
import threading
import time
import zlib
from concurrent.futures import ThreadPoolExecutor
from tkinter import messagebox
from urllib.parse import quote

import aiohttp
import customtkinter as ctk

ctk.set_appearance_mode("Dark")
ctk.set_default_color_theme("blue")

STATE_FILE = "download_state.json"
OUTPUT_ROOT = "Downloaded_Files"   # الجذر: Downloaded_Files/<type>/<N>/file
LEGACY_DIR = "Downloaded_Lua"      # مجلد النسخ القديمة (يُفحص فقط لتجنب إعادة التنزيل)
FOLDER_LIMIT = 1000                # أقصى عدد ملفات في المجلد الواحد
START_CONN = 100                   # عدد الاتصالات عند البداية (القيمة القديمة المجرّبة)
MAX_CONN = 400                     # أقصى عدد (بيزيد تلقائياً لحد ما GitHub يبطّئ)
MIN_CONN = 20                      # أقل عدد لو GitHub بدأ يرفض
TUNE_WINDOW = 5.0                  # ثواني بين كل قياس لإنتاجية التحميل
WRITE_THREADS = 32                 # خيوط كتابة الملفات على القرص
LIST_BATCH = 500                   # عدد الفروع في كل طلب لقراءة قايمة الملفات
BULK_MODE = False                  # تحميل جماعي بـ git pack: طلع أبطأ من ملف-ملف في تجربتك، فمقفول
PACK_START = 200                   # عدد الملفات في أول طلب تحميل جماعي (بعدها بيتظبط تلقائياً)
PACK_MIN, PACK_MAX = 20, 600       # أقل/أكبر عدد ملفات في الطلب الواحد
PACK_TARGET = 24 * 1024 * 1024     # حجم الطلب المستهدف (يحمي الذاكرة لو الملفات كبيرة)
PACK_CONC = 6                      # عدد طلبات التحميل الجماعي المتزامنة

# Colors
BG, CARD, CARD2, BORDER = "#0a0e17", "#111827", "#1a2233", "#243049"
TEXT, MUTED = "#e5e7eb", "#8b95a9"
GREEN, GREEN_H = "#10b981", "#059669"
BLUE, BLUE_H = "#3b82f6", "#2563eb"
AMBER, AMBER_H = "#f59e0b", "#d97706"
RED, RED_H = "#ef4444", "#dc2626"

STATUS_COLORS = {
    "Ready": "#374151", "Scanning": BLUE, "Downloading": GREEN,
    "Paused": AMBER, "Stopped": RED, "Finished": "#8b5cf6",
}


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


def build_fetch_blobs(wants):
    """طلب git protocol v2 لتحميل ملفات (blobs) محددة بالـ sha في طلب واحد."""
    body = (pkt("command=fetch\n") + pkt("agent=git/2.43.0\n") + b"0001"
            + pkt("ofs-delta\n") + pkt("no-progress\n"))
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
        self.minsize(820, 560)
        self.resizable(True, True)
        self.after(150, self.maximize)
        self.configure(fg_color=BG)

        self.is_running = False
        self.is_paused = False
        self.repo_url = ""
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
        if not self.repo_url:
            self.log("Click 'Repository' to set the target repository first.")
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
            header, text="⚙  Repository", command=self.open_settings_popup,
            width=140, height=40, corner_radius=12, font=F(13, "bold"),
            fg_color=CARD2, hover_color=BORDER, border_width=1, border_color=BORDER)
        self.btn_settings.pack(side="right")

        # Repository card
        card = ctk.CTkFrame(self, fg_color=CARD, corner_radius=18,
                            border_width=1, border_color=BORDER)
        card.pack(fill="x", padx=26, pady=6)
        left = ctk.CTkFrame(card, fg_color="transparent")
        left.pack(side="left", padx=20, pady=16)
        ctk.CTkLabel(left, text="TARGET REPOSITORY", font=F(10, "bold"),
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
            btns, text="🚀  Start / Resume Smart Download", command=self.start_download_thread,
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
        self.lbl_repo.configure(text=self.repo_url or "No repository selected")

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
        el = 0
        if self.start_time:
            el = (self.end_time or time.time()) - self.start_time
        self.v_speed.configure(text=f"{self.files / el:,.1f}/s" if el > 1 else "0/s")
        mb = self.bytes / 1048576
        self.v_speed.title_lbl.configure(
            text=f"Speed  ·  {mb / el:,.2f} MB/s" if el > 1 else "Speed")
        left = max(t - p, 0)
        eta = ""
        if el > 5 and self.processed > 0 and left and not self.end_time:
            sec = int(left / (self.processed / el))
            eta = f"  ·  ETA {sec // 3600:d}:{sec % 3600 // 60:02d}:{sec % 60:02d}"
        self.v_time.title_lbl.configure(text="Elapsed" + eta)
        h, rem = divmod(int(el), 3600)
        m, s = divmod(rem, 60)
        self.v_time.configure(text=f"{h:02d}:{m:02d}:{s:02d}")

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
        self.repo_url = d.get("repo_url", "")
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
        try:
            async with aiohttp.ClientSession() as session:
                async with session.get(
                        "https://api.github.com/user",
                        headers={"User-Agent": "UniversalProDownloader/3.0",
                                 "Authorization": f"Bearer {self.token}"},
                        timeout=aiohttp.ClientTimeout(total=15)) as r:
                    if r.status == 200:
                        who = (await r.json()).get("login", "")
                        self.log(f"GitHub token accepted ({who}).")
                        # مستودع عام؟ التوكن مش محتاجه raw (ويمكن يعطّل الكاش)
                        async with session.get(
                                f"https://api.github.com/repos/{self.repo_url}",
                                headers={"User-Agent": "UniversalProDownloader/3.0",
                                         "Authorization": f"Bearer {self.token}"},
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
        popup.title("Repository")
        popup.geometry("500x430")
        popup.resizable(False, False)
        popup.configure(fg_color=BG)
        popup.transient(self)
        popup.after(150, popup.grab_set)

        ctk.CTkLabel(popup, text="Target repository", font=F(16, "bold"),
                     text_color=TEXT).pack(pady=(22, 2))
        ctk.CTkLabel(popup, text="Paste a GitHub link or type  owner/repo",
                     font=F(12), text_color=MUTED).pack()
        entry = ctk.CTkEntry(popup, width=420, height=40, corner_radius=10,
                             fg_color=CARD2, border_color=BORDER,
                             placeholder_text="https://github.com/owner/repo")
        if self.repo_url:
            entry.insert(0, self.repo_url)
        entry.pack(pady=(14, 8))

        ctk.CTkLabel(popup, text="GitHub token (optional)", font=F(13, "bold"),
                     text_color=TEXT).pack(pady=(10, 0))
        ctk.CTkLabel(popup, justify="center", font=F(11), text_color=MUTED,
                     text="Raises GitHub's request limits and lets you download private repos.\n"
                          "Stored locally in download_state.json. Leave empty to skip."
                     ).pack()
        tok = ctk.CTkEntry(popup, width=420, height=40, corner_radius=10, show="•",
                           fg_color=CARD2, border_color=BORDER,
                           placeholder_text="ghp_xxxxxxxxxxxxxxxxxxxx")
        if self.token:
            tok.insert(0, self.token)
        tok.pack(pady=(8, 8))

        def save_repo():
            val = entry.get().strip()
            m = re.search(r"github\.com/([^/\s]+)/([^/\s#?]+)", val)
            if m:
                owner, repo = m.group(1), m.group(2)
            elif re.fullmatch(r"[\w.-]+/[\w.-]+", val):
                owner, repo = val.split("/")
            else:
                messagebox.showerror(
                    "Error", "Invalid format. Use owner/repo or a GitHub link.", parent=popup)
                return
            repo = repo[:-4] if repo.endswith(".git") else repo
            self.repo_url = f"{owner}/{repo}"
            self.token = tok.get().strip()
            self.write_state(repo_url=self.repo_url, token=self.token)
            self.refresh_repo_label()
            self.log(f"Repository saved: {self.repo_url}"
                     + ("  (token set)" if self.token else ""))
            popup.destroy()

        ctk.CTkButton(popup, text="Save & Use", command=save_repo, width=420, height=42,
                      corner_radius=12, font=F(14, "bold"),
                      fg_color=GREEN, hover_color=GREEN_H).pack(pady=(10, 0))

    # ---------------------------------------------------------------- controls
    def toggle_pause(self):
        if not self.is_paused:
            self.is_paused = True
            self.btn_pause.configure(text="▶  Resume", fg_color=GREEN, hover_color=GREEN_H)
            self.set_status("Paused")
            self.log("Paused.")
        else:
            self.is_paused = False
            self.btn_pause.configure(text="⏸  Pause", fg_color=AMBER, hover_color=AMBER_H)
            self.set_status("Downloading")
            self.log("Resumed.")

    def stop_download(self):
        self.is_running = False
        self.is_paused = False
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
        if not self.repo_url:
            messagebox.showerror("Error", "Please set the repository first (Repository button).")
            return
        self.is_running = True
        self.is_paused = False
        self.choice_q = queue.Queue()
        self.reset_stats()
        self.set_running(True)
        self.set_status("Scanning")
        threading.Thread(target=lambda: asyncio.run(self.run_pipeline()),
                         daemon=True).start()

    def on_closing(self):
        self.is_running = False
        self.choice_q.put(None)
        self.destroy()

    # ------------------------------------------------------------ file layout
    def scan_existing(self):
        """يرجّع (names, counts): أسماء الملفات الموجودة لكل نوع، وعدد ملفات كل مجلد."""
        names, counts = {}, {}
        if os.path.isdir(OUTPUT_ROOT):
            for t in os.listdir(OUTPUT_ROOT):
                tdir = os.path.join(OUTPUT_ROOT, t)
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

        # المجلد القديم: للفحص فقط حتى لا يعاد تنزيل ما هو موجود
        def legacy(folder, t):
            with os.scandir(folder) as it:
                for e in it:
                    if e.is_file():
                        names.setdefault(t, set()).add(e.name)

        if os.path.isdir(LEGACY_DIR):
            legacy(LEGACY_DIR, "lua")
            for item in os.listdir(LEGACY_DIR):
                p = os.path.join(LEGACY_DIR, item)
                if not os.path.isdir(p):
                    continue
                if item.isdigit():
                    legacy(p, "lua")
                else:
                    for sub in os.listdir(p):
                        sp = os.path.join(p, sub)
                        if os.path.isdir(sp) and sub.isdigit():
                            legacy(sp, item)
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
        """جلب المعرفات سواء من الفروع أو من هيكل المشروع (Tree API)"""
        fetched_ids = set()
        async with aiohttp.ClientSession() as session:
            try:
                ref_url = (f"https://github.com/{self.repo_url}.git/info/refs"
                           "?service=git-upload-pack")
                headers = {"User-Agent": "git/2.34.1",
                           "Accept": "application/x-git-upload-pack-advertisement, */*",
                           **self.auth("git")}
                async with session.get(ref_url, headers=headers,
                                       timeout=aiohttp.ClientTimeout(total=15)) as resp:
                    if resp.status == 200:
                        text = await resp.text()
                        matches = re.findall(r"refs/heads/(\d+)", text)
                        if matches:
                            fetched_ids.update([int(m) for m in matches])
                        for sha, bid in re.findall(
                                r"([0-9a-f]{40}) refs/heads/(\d+)(?=[\n\0])", text):
                            self.branch_sha[int(bid)] = sha
            except Exception:
                pass

            if not fetched_ids:
                try:
                    tree_url = (f"https://api.github.com/repos/{self.repo_url}"
                                "/git/trees/main?recursive=1")
                    async with session.get(tree_url, headers=self.auth("api"),
                                           timeout=aiohttp.ClientTimeout(total=15)) as resp:
                        if resp.status == 200:
                            data = await resp.json()
                            for item in data.get("tree", []):
                                path = item.get("path", "")
                                match = (re.search(r"(\d+)\.[A-Za-z0-9]+$", path)
                                         or re.search(r"^(\d+)$", path))
                                if match:
                                    fetched_ids.add(int(match.group(1)))
                except Exception:
                    pass
        return fetched_ids

    # --------------------------------------------------------------- pipeline
    async def wait_if_paused(self):
        while self.is_paused and self.is_running:
            await asyncio.sleep(0.1)

    async def run_pipeline(self):
        try:
            await self._pipeline()
        except Exception as e:
            self.post("error", f"Unexpected error:\n{e}")
            self.post("status", "Stopped")
        finally:
            self.end_time = time.time()
            self.is_running = False
            self.post("finished")

    async def _pipeline(self):
        await self.check_token()
        self.log(f"Scanning repository: {self.repo_url}")
        self.branch_sha = {}
        fetched = await self.fetch_all_ids_flexible()
        if not fetched:
            self.log("No files found. Check the repository link.")
            self.post("status", "Stopped")
            self.post("error", "No files were found in this repository.")
            return
        ids = sorted(fetched)

        # ---- قراءة كل الملفات المتخزنة في كل الفروع (من غير ZIP)
        self.log(f"Reading the file list of {len(ids):,} branches...")
        listing = await self.list_all(ids)
        if not self.is_running:
            self.log("Stopped.")
            self.post("status", "Stopped")
            return
        if not listing:
            self.log("Could not read the file list from GitHub.")
            self.post("status", "Stopped")
            self.post("error", "Could not read the file list from GitHub (blocked or rate limited).")
            return
        type_counts = {}
        for paths in listing.values():
            for pth, _sha in paths:
                t = type_of(pth)
                type_counts[t] = type_counts.get(t, 0) + 1
        total_files = sum(type_counts.values())
        self.log(f"Found {total_files:,} files in {len(listing):,} branches.")

        # ---- اختيار المستخدم (التحميل لا يبدأ قبل كده أبداً)
        state = self.read_state()
        preselect = state.get("type_choice", []) if state.get("repo_url") == self.repo_url else []
        if len(type_counts) >= 2:
            self.log(f"Found {len(type_counts)} file types. Waiting for your choice...")
            self.post("choose_types", type_counts, len(listing), set(), preselect)
            choice = await asyncio.to_thread(self.choice_q.get)
            if choice is None:
                self.log("Cancelled.")
                self.post("status", "Stopped")
                return
        else:
            choice = []
        allowed = set(choice) or None
        self.write_state(repo_url=self.repo_url, type_choice=sorted(choice))
        self.log("Selected types: " + (", ".join("." + t for t in sorted(allowed))
                                          if allowed else "ALL types"))
        self.post("type", "Types: " + (", ".join(sorted(allowed)) if allowed else "all"))

        # ---- الملفات المطلوبة (اللي مش موجودة على القرص)
        existing, counts = self.scan_existing()
        jobs = []
        for aid in ids:
            for pth, sha in listing.get(aid, []):
                typ = type_of(pth)
                if allowed and typ not in allowed:
                    continue
                own = "/" not in pth and os.path.splitext(pth)[0] == str(aid)
                name = pth if own else f"{aid}_{pth.replace('/', '__')}"
                if name in existing.get(typ, ()):
                    continue
                jobs.append((aid, pth, typ, name, sha))
        self.total = len(jobs)
        self.log(f"Files to download: {len(jobs):,}")
        if not jobs:
            self.log("Download finished — everything is already downloaded.")
            self.post("status", "Finished")
            self.post("info", "Finished", "All files are already downloaded.")
            return

        cur, made = {}, set()
        lock = threading.Lock()
        loop = asyncio.get_running_loop()
        pool = ThreadPoolExecutor(max_workers=WRITE_THREADS)

        def reserve(typ, name):
            """يحدد مسار الملف (ويحجز مكانه). آمن للاستخدام من أكتر من خيط."""
            with lock:
                idx = cur.get(typ, 1)
                while counts.get((typ, idx), 0) >= FOLDER_LIMIT:
                    idx += 1
                cur[typ] = idx
                folder = os.path.join(OUTPUT_ROOT, typ, str(idx))
                if folder not in made:
                    os.makedirs(folder, exist_ok=True)
                    made.add(folder)
                counts[(typ, idx)] = counts.get((typ, idx), 0) + 1
                return os.path.join(folder, name)

        def write_sync(path, data):
            with open(path + ".part", "wb") as f:
                f.write(data)
            os.replace(path + ".part", path)

        ptr = 0
        failed, active = [], set()
        retry = collections.deque()  # ملفات اتلغت بسبب الإيقاف المؤقت → تتكرر
        ctl = {"limit": START_CONN, "busy": 0, "r429": 0, "hold": 0.0}
        raw_hdr = self.auth("raw") if self.repo_private else {}
        file_timeout = aiohttp.ClientTimeout(total=120, sock_connect=10, sock_read=60)
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

        # ---- المرحلة 1: تحميل جماعي بالبروتوكول الأصلي (مئات الملفات في طلب واحد)
        by_sha = {}
        for j in jobs:
            by_sha.setdefault(j[4], []).append(j)
        shas = list(by_sha) if BULK_MODE else []
        bsize = [PACK_START]
        fallback, pack_state, pack_dead = [], {"ok": 0, "fail": 0}, [False]
        stat_lock = threading.Lock()
        pack_url = f"https://github.com/{self.repo_url}.git/git-upload-pack"
        pack_hdr = {"User-Agent": "git/2.43.0", "Git-Protocol": "version=2",
                    "Content-Type": "application/x-git-upload-pack-request",
                    "Accept": "application/x-git-upload-pack-result", **self.auth("git")}
        pack_timeout = aiohttp.ClientTimeout(total=900, sock_connect=15, sock_read=120)

        def process_batch(data, batch):
            """يفك الـ pack ويكتب كل ملف زي ما هو (نفس بايتات القاعدة). يرجّع اللي ناقص."""
            objs = parse_pack(extract_pack(data))
            missing = []
            for sha in batch:
                ent = objs.get(sha)
                if ent is None or ent[0] != 3:
                    missing.append(sha)
                    continue
                content = ent[1]
                for (_a, _p, typ, name, _s) in by_sha[sha]:
                    write_sync(reserve(typ, name), content)
                    with stat_lock:
                        self.types.add(typ)
                        self.files += 1
                        self.ok += 1
                        self.processed += 1
                        self.bytes += len(content)
            return missing

        sptr = 0
        retry_b = collections.deque()
        pack_connector = aiohttp.TCPConnector(limit=PACK_CONC * 2, keepalive_timeout=60)
        async with aiohttp.ClientSession(connector=pack_connector) as psession:

            async def fetch_batch(batch):
                body = build_fetch_blobs(batch)
                for attempt in range(3):
                    try:
                        async with psession.post(pack_url, data=body, headers=pack_hdr,
                                                 timeout=pack_timeout) as r:
                            if r.status != 200:
                                raise RuntimeError(f"HTTP {r.status}")
                            data = await r.read()
                    except Exception:
                        await asyncio.sleep(1 + attempt)
                        continue
                    avg = max(len(data) / max(len(batch), 1), 1)
                    bsize[0] = int(min(PACK_MAX, max(PACK_MIN, PACK_TARGET / avg)))
                    fut = loop.run_in_executor(pool, process_batch, data, batch)
                    while not fut.done():  # الكتابة لا تتلغي نص الطريق
                        try:
                            await asyncio.shield(fut)
                        except asyncio.CancelledError:
                            pass
                    try:
                        missing = fut.result()
                    except Exception:
                        await asyncio.sleep(1 + attempt)
                        continue
                    for sha in missing:
                        fallback.extend(by_sha[sha])
                    return "ok"
                return "failed"

            async def pack_worker():
                nonlocal sptr
                while self.is_running and not pack_dead[0]:
                    await self.wait_if_paused()
                    if not self.is_running:
                        break
                    if retry_b:
                        batch = retry_b.popleft()
                    elif sptr < len(shas):
                        batch = shas[sptr:sptr + bsize[0]]
                        sptr += len(batch)
                    else:
                        break
                    task = asyncio.ensure_future(fetch_batch(batch))
                    active.add(task)
                    try:
                        st = await task
                    except asyncio.CancelledError:
                        st = "cancelled"
                    finally:
                        active.discard(task)
                    if st == "cancelled":
                        retry_b.append(batch)
                        continue
                    if st == "ok":
                        pack_state["ok"] += 1
                    else:
                        pack_state["fail"] += 1
                        for sha in batch:
                            fallback.extend(by_sha[sha])
                        if pack_state["ok"] == 0 and pack_state["fail"] >= 2:
                            pack_dead[0] = True
                            self.log("Bulk mode unavailable — using direct downloads.")

            await asyncio.gather(*[pack_worker() for _ in range(PACK_CONC)])
        if pack_dead[0]:
            for sha in [x for b in retry_b for x in b] + shas[sptr:]:
                fallback.extend(by_sha[sha])
        if BULK_MODE:
            jobs = fallback  # اللي فشل في التحميل الجماعي يتحمل مباشرة من raw

        # الملفات المتطابقة (نفس المحتوى في أكتر من فرع) تتحمل مرة واحدة وتتنسخ لباقي الأماكن
        dup_map, uniq, seen = {}, [], set()
        for j in jobs:
            if j[4] in seen:
                dup_map.setdefault(j[4], []).append(j)
            else:
                seen.add(j[4])
                uniq.append(j)
        jobs = uniq

        async with aiohttp.ClientSession(connector=connector) as session:

            async def fetch_job(job):
                aid, pth, typ, name, sha = job
                url = (f"https://raw.githubusercontent.com/{self.repo_url}/{aid}/"
                       f"{quote(pth, safe='/')}")
                errs = waits = 0
                while errs < 3 and waits < 8:
                    status = data = None
                    try:
                        async with session.get(url, headers=raw_hdr,
                                               timeout=file_timeout) as r:
                            status = r.status
                            if status == 200:
                                data = await r.read()  # الملف زي ما هو
                    except Exception:
                        errs += 1
                        await asyncio.sleep(0.5)
                        continue
                    # الاتصال اتقفل هنا — الانتظار والكتابة برّاه
                    if status == 200:
                        dests = [(typ, name)] + [(j[2], j[3]) for j in dup_map.get(sha, ())]

                        def write_all(dests=dests, data=data):
                            for t_, n_ in dests:
                                write_sync(reserve(t_, n_), data)

                        fut = loop.run_in_executor(pool, write_all)
                        while not fut.done():  # الكتابة لا تتلغي نص الطريق
                            try:
                                await asyncio.shield(fut)
                            except asyncio.CancelledError:
                                pass
                        fut.result()
                        for t_, _n in dests:
                            self.types.add(t_)
                        self.files += len(dests)
                        self.ok += len(dests) - 1
                        self.processed += len(dests) - 1
                        self.bytes += len(data)
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

            if jobs and self.is_running:
                helpers = [asyncio.create_task(tuner())]
                await asyncio.gather(*[worker() for _ in range(MAX_CONN)])
                for h in helpers:
                    h.cancel()
        monitor_task.cancel()
        pool.shutdown(wait=True)

        self.end_time = time.time()
        if not self.is_running and self.processed < self.total:
            self.log("Download stopped. Progress saved — press Start to resume.")
            self.post("status", "Stopped")
            return
        if failed:
            self.log(f"{len(failed):,} files failed. Press Start again to retry them.")
        self.log(f"Download finished. Files saved: {self.files:,}")
        self.post("status", "Finished")
        self.post("info", "Finished", f"Download finished.\nFiles saved: {self.files:,}")


if __name__ == "__main__":
    app = ManifestHubApp()
    app.protocol("WM_DELETE_WINDOW", app.on_closing)
    app.mainloop()
