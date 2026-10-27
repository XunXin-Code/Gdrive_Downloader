#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Google 网盘批量下载器（仅使用 Python 标准库）
版本：1.0.0

功能：
  * 每行粘贴一个链接即可批量下载（支持 /file/d/ID、open?id=ID、uc?id=ID、纯文件 ID）
  * 批量下载并重命名：左边贴链接，右边写新文件名；支持从谷歌表格一键粘贴（A 列链接、B 列新文件名）
  * 多线程并发下载（线程数可调），大文件自动处理“病毒扫描”确认页
  * 断点续传（.part 临时文件）、失败自动重试、已存在文件自动跳过
  * 支持 Google 文档 / 表格 / 幻灯片（导出为 docx / xlsx / pptx）
  * 图形界面（Tkinter），浅色 / 深色主题一键切换（自动记住选择）
  * 命令行模式

重命名规则：
  * 新文件名不带扩展名 → 自动沿用原文件的扩展名（如 视频01 → 视频01.mp4）
  * 新文件名已带原扩展名 → 原样使用
  * 新文件名留空 → 保持原文件名

注意：
  * 仅适用于“知道链接的任何人可查看”的公开分享文件
  * 文件夹链接无法在不使用 API 的情况下列出内容，会被标记为不支持

用法：
  GUI：    python gdrive_downloader.py
  命令行： python gdrive_downloader.py -f links.txt -o downloads -t 6
           （links.txt 每行一个链接；如需重命名，用 Tab 分隔：链接<Tab>新文件名）
"""

import argparse
import csv
import http.client
import http.cookiejar
import io
import json
import os
import queue
import re
import subprocess
import sys
import threading
import time
import unicodedata
import urllib.error
import urllib.parse
import urllib.request
from concurrent.futures import ThreadPoolExecutor
from html.parser import HTMLParser

APP_NAME = "Google 网盘批量下载器"
__version__ = "1.0.0"

UA = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
      "(KHTML, like Gecko) Chrome/124.0 Safari/537.36")
CHUNK = 256 * 1024
DOC_EXPORT = {
    "document": ("docx", ".docx"),
    "spreadsheets": ("xlsx", ".xlsx"),
    "presentation": ("pptx", ".pptx"),
}


class Cancelled(Exception):
    pass


class DriveError(Exception):
    pass


# --------------------------------------------------------------------------
# 工具函数
# --------------------------------------------------------------------------
def fmt_size(n):
    n = float(n)
    for unit in ("B", "KB", "MB", "GB", "TB"):
        if n < 1024 or unit == "TB":
            return f"{n:.0f} {unit}" if unit == "B" else f"{n:.2f} {unit}"
        n /= 1024


WIN_RESERVED = {"CON", "PRN", "AUX", "NUL",
                *(f"COM{i}" for i in range(1, 10)), *(f"LPT{i}" for i in range(1, 10))}
MAX_NAME = 150
MAX_THREADS = 32      # 线程数上限
DEFAULT_THREADS = 32  # 默认线程数
# 只允许访问 Google 自己的域名（防止被重定向/伪造的确认页带到其他地址）
ALLOWED_HOST_SUFFIXES = ("google.com", "googleusercontent.com", "googleapis.com")
FILE_ID_RE = re.compile(r"[\w-]{10,200}")


def host_allowed(url):
    """仅允许 https 且主机属于 Google 域名。"""
    try:
        u = urllib.parse.urlparse(url)
        host = (u.hostname or "").lower()
    except ValueError:
        return False
    return u.scheme == "https" and any(
        host == s or host.endswith("." + s) for s in ALLOWED_HOST_SUFFIXES)


def sanitize(name, default="file"):
    """清理文件名：去控制/不可见字符、非法字符、Windows 保留名，并限制长度。"""
    # 去掉控制字符与不可见格式字符（含 RTL 覆盖符，防止扩展名伪装）
    name = "".join(ch for ch in name if unicodedata.category(ch) not in ("Cc", "Cf"))
    name = re.sub(r'[\\/:*?"<>|]', "_", name).strip(" .")
    if not name:
        return default
    stem, ext = os.path.splitext(name)
    ext = ext[:20]
    if stem.upper() in WIN_RESERVED:
        stem = "_" + stem
    if len(stem) + len(ext) > MAX_NAME:
        stem = stem[:max(1, MAX_NAME - len(ext))]
    return (stem + ext).strip(" .") or default


def apply_rename(new, orig):
    """按规则把用户填写的新文件名应用到服务器返回的原文件名上。"""
    new = sanitize(new, "")
    if not new:
        return orig
    oext = os.path.splitext(orig)[1]
    if oext and os.path.splitext(new)[1].lower() == oext.lower():
        return new
    return sanitize(new + oext, orig)


def parse_link(line):
    """返回 (kind, id/url)；无法识别返回 None。"""
    line = line.strip()
    if not line:
        return None
    if re.fullmatch(r"[\w-]{25,200}", line):  # 纯文件 ID
        return ("file", line)
    try:
        u = urllib.parse.urlparse(line)
        host = (u.hostname or "").lower()  # 精确主机名，避免 drive.google.com.evil.com 之类的仿冒
        path = u.path
        qs = urllib.parse.parse_qs(u.query)
    except ValueError:
        return None
    if u.scheme not in ("http", "https"):
        return None
    if host in ("drive.google.com", "drive.usercontent.google.com"):
        if "/folders/" in path:
            return ("folder", line)
        m = re.search(r"/file/d/([\w-]{10,200})(?:/|$)", path)
        if m:
            return ("file", m.group(1))
        if "id" in qs and FILE_ID_RE.fullmatch(qs["id"][0]):  # 校验 ID，防止参数注入
            return ("file", qs["id"][0])
    if host == "docs.google.com":
        m = re.search(r"/(document|spreadsheets|presentation)/d/([\w-]{10,200})(?:/|$)", path)
        if m:
            return (m.group(1), m.group(2))
    return None


def build_jobs(lines, names=None):
    """
    把文本行解析为任务列表。names 与 lines 按行号一一对应（可为空）。
    返回 [(kind, ident, raw, newname)]；kind 为 None 表示无法识别的链接。
    """
    jobs, seen = [], set()
    for i, raw in enumerate(lines):
        raw = raw.strip()
        if not raw:
            continue
        newname = None
        if names and i < len(names):
            newname = names[i].strip() or None
        parsed = parse_link(raw)
        if parsed is None:
            jobs.append((None, None, raw, newname))
            continue
        key = (parsed, newname)
        if key in seen:
            continue
        seen.add(key)
        jobs.append((parsed[0], parsed[1], raw, newname))
    return jobs


def parse_sheet_text(text):
    """
    解析从谷歌表格复制的内容（Tab 分隔）：A 列 = 链接，B 列 = 新文件名。
    返回 (links, names, skipped_header)。
    """
    rows = []
    try:
        for row in csv.reader(io.StringIO(text), delimiter="\t"):
            if row and any(c.strip() for c in row):
                rows.append(row)
    except csv.Error:  # 例如单元格超长、引号不匹配
        return [], [], False
    skipped = False
    if rows and parse_link(rows[0][0]) is None:  # 第一行不是链接 → 当作表头
        rows = rows[1:]
        skipped = True
    # 单元格内可能含换行（Alt+Enter）或多余空白：链接去掉所有空白，文件名折叠为单个空格，
    # 否则换行会让左右两列的行号错位，导致文件被改成别的名字
    links = ["".join(r[0].split()) for r in rows]
    names = [" ".join(r[1].split()) if len(r) > 1 else "" for r in rows]
    return links, names, skipped


class FormParser(HTMLParser):
    """解析 Google 的“无法扫描病毒”确认页中的下载表单。"""

    def __init__(self):
        super().__init__()
        self.action = None
        self.fields = {}
        self._in_form = False

    def handle_starttag(self, tag, attrs):
        a = dict(attrs)
        if tag == "form" and "download" in (a.get("action") or "") and self.action is None:
            self.action = a["action"]
            self._in_form = True
        elif tag == "input" and self._in_form and a.get("name"):
            self.fields[a["name"]] = a.get("value") or ""

    def handle_endtag(self, tag):
        if tag == "form":
            self._in_form = False


def filename_from_headers(headers, default):
    cd = headers.get("Content-Disposition", "") or ""
    m = re.search(r"filename\*\s*=\s*([^']*)'[^']*'([^;]+)", cd, re.I)
    if m:
        try:
            return urllib.parse.unquote(m.group(2).strip(), encoding=m.group(1) or "utf-8")
        except LookupError:
            return urllib.parse.unquote(m.group(2).strip())
    m = re.search(r'filename\s*=\s*"([^"]+)"', cd, re.I) or \
        re.search(r"filename\s*=\s*([^;]+)", cd, re.I)
    if m:
        name = m.group(1).strip()
        try:
            name = name.encode("latin-1").decode("utf-8")
        except (UnicodeEncodeError, UnicodeDecodeError):
            pass
        return name
    return default


def explain_html(html):
    low = html.lower()
    if "quota" in low or "too many users" in low or "download quota" in low:
        return "下载次数过多，Google 已临时限制（配额超限），请稍后再试"
    if "accounts.google.com" in low or "servicelogin" in low or "sign in" in low:
        return "文件未公开：请把分享权限设为“知道链接的任何人可查看”"
    if "not found" in low or "404" in low:
        return "文件不存在或已被删除"
    return "Google 返回了网页而不是文件，请检查链接与权限"


# --------------------------------------------------------------------------
# 下载核心
# --------------------------------------------------------------------------
class SafeRedirectHandler(urllib.request.HTTPRedirectHandler):
    """只跟随跳转到 Google 域名的 https 地址，拒绝 http/ftp/其他主机。"""

    def redirect_request(self, req, fp, code, msg, headers, newurl):
        target = urllib.parse.urljoin(req.full_url, newurl)
        if not host_allowed(target):
            raise DriveError("拒绝跳转到非 Google 域名的地址")
        return super().redirect_request(req, fp, code, msg, headers, newurl)


def open_part(path, append):
    """打开 .part 临时文件；拒绝符号链接，防止被诱导写入其他位置。"""
    if os.path.islink(path):
        raise DriveError("临时文件是符号链接，已拒绝写入")
    flags = os.O_WRONLY | os.O_CREAT | (os.O_APPEND if append else os.O_TRUNC)
    flags |= getattr(os, "O_BINARY", 0) | getattr(os, "O_NOFOLLOW", 0)
    return os.fdopen(os.open(path, flags, 0o644), "ab" if append else "wb")


class Downloader:
    def __init__(self, save_dir, stop_event, report, retries=3):
        self.save_dir = save_dir
        self.stop = stop_event
        self.report = report  # report(idx, **fields)
        self.retries = retries
        self.lock = threading.Lock()
        self.active = set()

    @staticmethod
    def _make_opener():
        return urllib.request.build_opener(
            SafeRedirectHandler(),
            urllib.request.HTTPCookieProcessor(http.cookiejar.CookieJar()))

    @staticmethod
    def _open(opener, url, headers=None):
        if not host_allowed(url):
            raise DriveError("拒绝访问非 Google 域名的地址")
        h = {"User-Agent": UA}
        if headers:
            h.update(headers)
        return opener.open(urllib.request.Request(url, headers=h), timeout=30)

    @staticmethod
    def _is_html(resp):
        return "text/html" in (resp.headers.get("Content-Type", "") or "").lower()

    def _reserve(self, name, ident):
        with self.lock:
            path = os.path.join(self.save_dir, name)
            if path in self.active:
                stem, ext = os.path.splitext(name)
                name = f"{stem}_{ident[:6]}{ext}"
                path = os.path.join(self.save_dir, name)
            self.active.add(path)
            return name, path

    def _release(self, path):
        with self.lock:
            self.active.discard(path)

    # ---- 单个任务（含重试） ----
    def run(self, idx, kind, ident, newname=None):
        if self.stop.is_set():
            self.report(idx, status="已取消")
            return
        if kind is None:
            self.report(idx, status="无法识别的链接")
            return
        if kind == "folder":
            self.report(idx, status="不支持文件夹链接")
            return
        opener = self._make_opener()
        last = None
        for attempt in range(1, self.retries + 1):
            try:
                self.report(idx, status="连接中" if attempt == 1
                            else f"重试 {attempt}/{self.retries}")
                self._download(idx, kind, ident, opener, newname)
                return
            except Cancelled:
                self.report(idx, status="已取消")
                return
            except DriveError as e:
                self.report(idx, status=f"失败：{e}")
                return
            except urllib.error.HTTPError as e:
                if e.code in (401, 403):
                    self.report(idx, status="失败：无权限访问（需设为公开分享）")
                    return
                if e.code == 404:
                    self.report(idx, status="失败：文件不存在")
                    return
                if e.code == 429:
                    self.report(idx, status="失败：请求过于频繁/配额超限")
                    return
                last = e
            except (urllib.error.URLError, OSError, http.client.HTTPException) as e:
                last = e
            except Exception as e:  # 兜底，避免线程静默退出
                self.report(idx, status=f"失败：{e}")
                return
            if self.stop.wait(min(2 * attempt, 6)):
                self.report(idx, status="已取消")
                return
        self.report(idx, status=f"失败：{last}")

    # ---- 一次下载尝试 ----
    def _download(self, idx, kind, ident, opener, newname):
        qid = urllib.parse.quote(ident, safe="")
        if kind == "file":
            url = ("https://drive.usercontent.google.com/download"
                   f"?id={qid}&export=download&confirm=t")
            default = ident
        else:
            fmt, ext = DOC_EXPORT[kind]
            url = f"https://docs.google.com/{kind}/d/{qid}/export?format={fmt}"
            default = ident + ext

        resp = self._open(opener, url)
        if self._is_html(resp):
            html = resp.read(2 * 1024 * 1024).decode("utf-8", "replace")
            resp.close()
            parser = FormParser()
            parser.feed(html)
            if not parser.action:
                raise DriveError(explain_html(html))
            action = urllib.parse.urljoin(url, parser.action)
            if not host_allowed(action):
                raise DriveError("确认页返回了非 Google 域名的下载地址，已拒绝")
            url = action + ("&" if "?" in action else "?") + urllib.parse.urlencode(parser.fields)
            resp = self._open(opener, url)
            if self._is_html(resp):
                html = resp.read(2 * 1024 * 1024).decode("utf-8", "replace")
                resp.close()
                raise DriveError(explain_html(html))

        name = sanitize(filename_from_headers(resp.headers, default), default)
        if newname:
            name = apply_rename(newname, name)
        name, dest = self._reserve(name, ident)
        try:
            if os.path.exists(dest):
                resp.close()
                self.report(idx, name=name, status="已存在，跳过", progress="100%")
                return
            self._stream(idx, opener, url, resp, name, dest)
        finally:
            self._release(dest)

    def _stream(self, idx, opener, url, resp, name, dest):
        part = dest + ".part"
        done, mode = 0, "wb"
        remaining = int(resp.headers.get("Content-Length") or 0)

        # 断点续传
        if os.path.exists(part):
            size = os.path.getsize(part)
            if size > 0 and remaining and size < remaining:
                resp.close()
                resp2 = self._open(opener, url, {"Range": f"bytes={size}-"})
                if resp2.status == 206:
                    done, mode = size, "ab"
                resp = resp2
                remaining = int(resp.headers.get("Content-Length") or 0)
        full = done + remaining if remaining else 0

        self.report(idx, name=name, status="下载中", size=fmt_size(full) if full else "未知")
        last_t, last_b = time.time(), done
        with open_part(part, append=(mode == "ab")) as f:
            while True:
                if self.stop.is_set():
                    resp.close()
                    raise Cancelled()
                buf = resp.read(CHUNK)
                if not buf:
                    break
                f.write(buf)
                done += len(buf)
                now = time.time()
                if now - last_t >= 0.5:
                    speed = (done - last_b) / (now - last_t)
                    prog = f"{done * 100 / full:.1f}%" if full else fmt_size(done)
                    self.report(idx, progress=prog, speed=fmt_size(speed) + "/s")
                    last_t, last_b = now, done
        resp.close()
        if full and done < full:
            raise OSError("下载不完整，将重试")
        os.replace(part, dest)
        self.report(idx, status="完成", progress="100%", speed="", size=fmt_size(done))


def run_batch(jobs, save_dir, threads, stop, report):
    try:
        threads = max(1, min(MAX_THREADS, int(threads)))
    except (TypeError, ValueError):
        threads = DEFAULT_THREADS
    try:
        os.makedirs(save_dir, exist_ok=True)
    except OSError as e:
        for i in range(len(jobs)):
            report(i, status=f"失败：无法创建保存目录（{e.strerror or e}）")
        return
    dl = Downloader(save_dir, stop, report)
    with ThreadPoolExecutor(max_workers=threads) as ex:
        futures = [ex.submit(dl.run, i, k, ident, newname)
                   for i, (k, ident, _raw, newname) in enumerate(jobs)]
        for f in futures:
            f.result()


# --------------------------------------------------------------------------
# 图形界面
# --------------------------------------------------------------------------
def minimize_console():
    """Windows 下把后面的黑色控制台窗口最小化（其他系统无操作）。"""
    if not sys.platform.startswith("win"):
        return
    try:
        import ctypes
        hwnd = ctypes.windll.kernel32.GetConsoleWindow()
        if hwnd:
            ctypes.windll.user32.ShowWindow(hwnd, 6)  # 6 = SW_MINIMIZE
    except Exception:
        pass


def run_gui():
    import tkinter as tk
    import tkinter.font as tkfont
    from tkinter import filedialog, messagebox, ttk

    try:  # Windows 高分屏清晰度
        import ctypes
        ctypes.windll.shcore.SetProcessDpiAwareness(1)
    except Exception:
        pass

    LIGHT = dict(bg="#f4f5f7", surface="#ffffff", text="#1f2328", muted="#6b7280",
                 border="#d9dde3", accent="#2563eb", accent_hover="#1d4ed8",
                 accent_fg="#ffffff", btn="#e8ebf0", btn_hover="#dbdfe6",
                 select="#dbe7ff", head="#eef0f4", odd="#f8f9fb",
                 ok="#15803d", err="#dc2626", warn="#b45309", run="#2563eb")
    DARK = dict(bg="#14161a", surface="#1e2127", text="#e6e8eb", muted="#9aa1ac",
                border="#30343d", accent="#3b82f6", accent_hover="#5b9bff",
                accent_fg="#ffffff", btn="#2a2e37", btn_hover="#353a45",
                select="#2b4575", head="#262a32", odd="#23272e",
                ok="#4ade80", err="#f87171", warn="#fbbf24", run="#60a5fa")
    SETTINGS = os.path.join(os.path.expanduser("~"), ".gdrive_downloader.json")

    def load_settings():
        try:
            with open(SETTINGS, encoding="utf-8") as f:
                data = json.load(f)
                return data if isinstance(data, dict) else {}
        except (OSError, ValueError):
            return {}

    def save_settings(data):
        tmp = SETTINGS + ".tmp"
        try:  # 先写临时文件再替换，避免程序中途退出时把配置写坏
            with open(tmp, "w", encoding="utf-8") as f:
                json.dump(data, f, ensure_ascii=False, indent=2)
            os.replace(tmp, SETTINGS)
        except OSError:
            try:
                os.remove(tmp)
            except OSError:
                pass

    def alive(w):
        try:
            return bool(w.winfo_exists())
        except tk.TclError:
            return False

    def tag_for(status):
        if status in ("完成", "已存在，跳过"):
            return "ok"
        if status.startswith(("失败", "不支持", "无法识别")):
            return "err"
        if status == "已取消":
            return "warn"
        if status.startswith(("下载中", "连接中", "重试")):
            return "run"
        return ""

    class App:
        def __init__(self, root):
            self.root = root
            self.cfg = load_settings()
            self.dark = bool(self.cfg.get("dark", False))
            self.c = DARK if self.dark else LIGHT
            self.q = queue.Queue()
            self.stop = threading.Event()
            self.running = False
            self.jobs = []
            self.states = {}
            self.rename_win = None
            self.texts, self.cards, self.tops = [], [], [root]

            fams = set(tkfont.families())
            self.ui = next((f for f in ("Microsoft YaHei UI", "PingFang SC", "Noto Sans CJK SC",
                                        "Source Han Sans SC", "WenQuanYi Micro Hei", "Segoe UI")
                            if f in fams), "TkDefaultFont")
            self.style = ttk.Style(root)

            root.title(f"{APP_NAME} v{__version__}")
            root.geometry("960x700")
            root.minsize(800, 560)

            outer = ttk.Frame(root, padding=(20, 16, 20, 16))
            outer.pack(fill="both", expand=True)

            # ---- 顶部标题栏 ----
            head = ttk.Frame(outer)
            head.pack(fill="x")
            tb = ttk.Frame(head)
            tb.pack(side="left")
            ttk.Label(tb, text=APP_NAME, style="Title.TLabel").pack(anchor="w")
            ttk.Label(tb, text=f"v{__version__} · 多线程 · 断点续传 · 批量重命名",
                      style="Muted.TLabel").pack(anchor="w")
            self.theme_btn = ttk.Button(head, command=self.toggle_theme, width=9)
            self.theme_btn.pack(side="right", anchor="n")

            # ---- 链接输入 ----
            lab = ttk.Frame(outer)
            lab.pack(fill="x", pady=(16, 6))
            ttk.Label(lab, text="下载链接", style="Sub.TLabel").pack(side="left")
            ttk.Label(lab, text="  每行一个", style="Muted.TLabel").pack(side="left")
            card = self.make_card(outer)
            card.pack(fill="x")
            self.text = self.make_text(card, height=8)
            sb = ttk.Scrollbar(card, command=self.text.yview)
            self.text.configure(yscrollcommand=sb.set)
            sb.pack(side="right", fill="y")
            self.text.pack(side="left", fill="both", expand=True)

            # ---- 选项 ----
            opt = ttk.Frame(outer)
            opt.pack(fill="x", pady=(14, 0))
            ttk.Label(opt, text="保存到").grid(row=0, column=0, sticky="w")
            saved_dir = self.cfg.get("dir")  # 配置文件内容不可信，需校验类型
            self.dir_var = tk.StringVar(
                value=saved_dir if isinstance(saved_dir, str) and saved_dir.strip()
                else os.path.join(os.path.expanduser("~"), "Downloads", "GDrive"))
            ttk.Entry(opt, textvariable=self.dir_var).grid(row=0, column=1, sticky="ew", padx=(10, 8))
            ttk.Button(opt, text="浏览…", command=self.choose_dir).grid(row=0, column=2)
            ttk.Label(opt, text="线程数").grid(row=0, column=3, padx=(20, 8))
            try:
                thr = max(1, min(MAX_THREADS, int(self.cfg.get("threads", DEFAULT_THREADS))))
            except (TypeError, ValueError):
                thr = DEFAULT_THREADS
            self.thr_var = tk.IntVar(value=thr)
            # 上限 32：点箭头加到 32 就不能再加；手动输入超出范围的数字，回车或离开输入框时自动改回 32（或 1）
            spin = ttk.Spinbox(opt, from_=1, to=MAX_THREADS, width=4, textvariable=self.thr_var)
            spin.grid(row=0, column=4)
            spin.bind("<FocusOut>", lambda _e: self.fix_threads())
            spin.bind("<Return>", lambda _e: self.fix_threads())
            opt.columnconfigure(1, weight=1)

            # ---- 按钮 ----
            btns = ttk.Frame(outer)
            btns.pack(fill="x", pady=(14, 0))
            self.start_btn = ttk.Button(btns, text="开始下载", style="Accent.TButton", command=self.start)
            self.start_btn.pack(side="left")
            self.rename_btn = ttk.Button(btns, text="批量下载并重命名", command=self.open_rename)
            self.rename_btn.pack(side="left", padx=8)
            self.stop_btn = ttk.Button(btns, text="停止", command=self.on_stop, state="disabled")
            self.stop_btn.pack(side="left")
            ttk.Button(btns, text="打开文件夹", command=self.open_dir).pack(side="right")
            ttk.Button(btns, text="清空链接",
                       command=lambda: self.text.delete("1.0", "end")).pack(side="right", padx=8)

            # ---- 总进度 ----
            pf = ttk.Frame(outer)
            pf.pack(fill="x", pady=(16, 8))
            self.prog = ttk.Progressbar(pf, maximum=1.0, value=0.0)
            self.prog.pack(side="left", fill="x", expand=True)
            self.summary = tk.StringVar(value="就绪")
            ttk.Label(pf, textvariable=self.summary, style="Muted.TLabel").pack(side="left", padx=(12, 0))

            # ---- 任务表 ----
            tcard = self.make_card(outer)
            tcard.pack(fill="both", expand=True)
            cols = ("no", "name", "status", "progress", "speed", "size")
            self.tree = ttk.Treeview(tcard, columns=cols, show="headings", height=10)
            for c, t, w in (("no", "#", 44), ("name", "文件名", 330), ("status", "状态", 210),
                            ("progress", "进度", 84), ("speed", "速度", 100), ("size", "大小", 96)):
                self.tree.heading(c, text=t)
                self.tree.column(c, width=w, anchor="w" if c in ("name", "status") else "center",
                                 stretch=c in ("name", "status"))
            tsb = ttk.Scrollbar(tcard, command=self.tree.yview)
            self.tree.configure(yscrollcommand=tsb.set)
            tsb.pack(side="right", fill="y")
            self.tree.pack(side="left", fill="both", expand=True)

            self.apply_theme()
            root.protocol("WM_DELETE_WINDOW", self.on_close)
            root.after(100, self.poll)

        # ---------------- 主题 ----------------
        def make_card(self, parent):
            f = tk.Frame(parent, highlightthickness=1, bd=0)
            self.cards.append(f)
            return f

        def make_text(self, parent, **kw):
            t = tk.Text(parent, wrap="none", undo=True, font=(self.ui, 11), relief="flat",
                        bd=0, highlightthickness=0, padx=10, pady=8, **kw)
            self.texts.append(t)
            return t

        def set_titlebar(self, win):
            if not sys.platform.startswith("win"):
                return
            try:
                import ctypes
                win.update_idletasks()
                hwnd = ctypes.windll.user32.GetParent(win.winfo_id())
                val = ctypes.c_int(1 if self.dark else 0)
                for attr in (20, 19):
                    ctypes.windll.dwmapi.DwmSetWindowAttribute(
                        hwnd, attr, ctypes.byref(val), ctypes.sizeof(val))
            except Exception:
                pass

        def apply_theme(self):
            c = self.c = DARK if self.dark else LIGHT
            ui, st = self.ui, self.style
            st.theme_use("clam")
            self.cards = [w for w in self.cards if alive(w)]
            self.texts = [w for w in self.texts if alive(w)]
            self.tops = [w for w in self.tops if alive(w)]

            st.configure(".", background=c["bg"], foreground=c["text"], font=(ui, 10),
                         bordercolor=c["border"], lightcolor=c["bg"], darkcolor=c["bg"],
                         troughcolor=c["btn"], focuscolor=c["bg"])
            st.configure("TFrame", background=c["bg"])
            st.configure("TLabel", background=c["bg"], foreground=c["text"])
            st.configure("Title.TLabel", font=(ui, 17, "bold"))
            st.configure("Sub.TLabel", font=(ui, 10, "bold"))
            st.configure("Muted.TLabel", foreground=c["muted"])

            st.configure("TButton", background=c["btn"], foreground=c["text"], padding=(14, 7),
                         borderwidth=0, bordercolor=c["btn"], lightcolor=c["btn"],
                         darkcolor=c["btn"], focuscolor=c["btn"], relief="flat")
            st.map("TButton",
                   background=[("disabled", c["btn"]), ("active", c["btn_hover"])],
                   foreground=[("disabled", c["muted"])])
            st.configure("Accent.TButton", background=c["accent"], foreground=c["accent_fg"],
                         bordercolor=c["accent"], lightcolor=c["accent"], darkcolor=c["accent"],
                         focuscolor=c["accent"], font=(ui, 10, "bold"))
            st.map("Accent.TButton",
                   background=[("disabled", c["btn"]), ("active", c["accent_hover"])],
                   foreground=[("disabled", c["muted"])])

            for name in ("TEntry", "TSpinbox"):
                st.configure(name, fieldbackground=c["surface"], foreground=c["text"],
                             insertcolor=c["text"], padding=6, bordercolor=c["border"],
                             lightcolor=c["border"], darkcolor=c["border"],
                             background=c["btn"], arrowcolor=c["text"])
                st.map(name, bordercolor=[("focus", c["accent"])],
                       lightcolor=[("focus", c["accent"])], darkcolor=[("focus", c["accent"])])

            st.configure("Treeview", background=c["surface"], fieldbackground=c["surface"],
                         foreground=c["text"], rowheight=30, borderwidth=0, font=(ui, 10))
            st.map("Treeview", background=[("selected", c["select"])],
                   foreground=[("selected", c["text"])])
            st.configure("Treeview.Heading", background=c["head"], foreground=c["text"],
                         relief="flat", padding=(8, 7), borderwidth=0, font=(ui, 10, "bold"))
            st.map("Treeview.Heading", background=[("active", c["head"])])

            st.configure("TScrollbar", background=c["btn"], troughcolor=c["surface"],
                         bordercolor=c["surface"], lightcolor=c["btn"], darkcolor=c["btn"],
                         arrowcolor=c["muted"], gripcount=0, relief="flat")
            st.map("TScrollbar", background=[("active", c["btn_hover"])])
            st.configure("Horizontal.TProgressbar", troughcolor=c["btn"], background=c["accent"],
                         bordercolor=c["btn"], lightcolor=c["accent"], darkcolor=c["accent"],
                         thickness=8)

            for w in self.tops:
                w.configure(bg=c["bg"])
            for f in self.cards:
                f.configure(bg=c["surface"], highlightbackground=c["border"],
                            highlightcolor=c["border"])
            for t in self.texts:
                t.configure(bg=c["surface"], fg=c["text"], insertbackground=c["text"],
                            selectbackground=c["select"], selectforeground=c["text"])
            for tag in ("ok", "err", "warn", "run"):
                self.tree.tag_configure(tag, foreground=c[tag])
            self.tree.tag_configure("odd", background=c["odd"])
            self.theme_btn.config(text="☀ 浅色" if self.dark else "☾ 深色")
            for w in self.tops:
                self.set_titlebar(w)

        def toggle_theme(self):
            self.dark = not self.dark
            self.apply_theme()
            self.save_cfg()

        def get_threads(self):
            try:
                return max(1, min(MAX_THREADS, int(self.thr_var.get())))
            except (tk.TclError, ValueError):
                return DEFAULT_THREADS

        def fix_threads(self):
            """把输入框里的线程数规范到 1–32 范围内。"""
            self.thr_var.set(self.get_threads())

        def save_cfg(self):
            save_settings({"dark": self.dark, "dir": self.dir_var.get(),
                           "threads": self.get_threads()})

        def on_close(self):
            self.save_cfg()
            self.root.destroy()

        # ---------------- 通用 ----------------
        def choose_dir(self):
            d = filedialog.askdirectory(initialdir=self.dir_var.get())
            if d:
                self.dir_var.set(d)

        def save_path(self):
            """规范化保存目录：展开 ~、转为绝对路径（也避免以 - 开头的相对路径被当成命令选项）。"""
            return os.path.abspath(os.path.expanduser(self.dir_var.get().strip() or "."))

        def open_dir(self):
            d = self.save_path()
            try:
                os.makedirs(d, exist_ok=True)
            except OSError as e:
                messagebox.showerror("无法打开文件夹", str(e))
                return
            if not os.path.isdir(d):
                return
            if sys.platform.startswith("win"):
                os.startfile(d)
            elif sys.platform == "darwin":
                subprocess.Popen(["open", d])
            else:
                subprocess.Popen(["xdg-open", d])

        # ---------------- 普通批量下载 ----------------
        def start(self):
            jobs = build_jobs(self.text.get("1.0", "end").splitlines())
            if not jobs:
                messagebox.showinfo("提示", "请先粘贴下载链接（每行一个）")
                return
            self.launch(jobs)

        def launch(self, jobs):
            if self.running:
                messagebox.showinfo("提示", "当前还有下载任务在进行，请等待完成或先点击“停止”")
                return False
            self.jobs = jobs
            self.states = {i: "等待中" for i in range(len(jobs))}
            self.tree.delete(*self.tree.get_children())
            for i, (k, ident, raw, newname) in enumerate(jobs):
                if newname:
                    shown = newname
                elif k in ("file", "document", "spreadsheets", "presentation"):
                    shown = ident
                else:
                    shown = raw
                self.tree.insert("", "end", iid=str(i), tags=("odd",) if i % 2 else (),
                                 values=(i + 1, shown, "等待中", "", "", ""))
            self.stop.clear()
            self.running = True
            self.start_btn.config(state="disabled")
            self.rename_btn.config(state="disabled")
            self.stop_btn.config(state="normal")
            self.prog.config(value=0.0)
            self.summary.set(f"共 {len(jobs)} 个任务")
            self.root.title(f"{APP_NAME} v{__version__}")
            self.save_cfg()
            threading.Thread(target=self.worker, daemon=True,
                             args=(jobs, self.save_path(), self.get_threads())).start()
            return True

        def worker(self, jobs, save_dir, threads):
            def report(idx, **kw):
                self.q.put((idx, kw))
            try:
                run_batch(jobs, save_dir, threads, self.stop, report)
            finally:
                self.q.put((-1, {}))

        def on_stop(self):
            self.stop.set()
            self.stop_btn.config(state="disabled")

        def counts(self):
            ok = bad = cancel = 0
            for s in self.states.values():
                t = tag_for(s)
                if t == "ok":
                    ok += 1
                elif t == "err":
                    bad += 1
                elif t == "warn":
                    cancel += 1
            return ok, bad, cancel

        def update_summary(self):
            total = len(self.jobs) or 1
            ok, bad, cancel = self.counts()
            self.prog.config(value=(ok + bad + cancel) / total)
            text = f"成功 {ok} · 失败 {bad} · 共 {len(self.jobs)}"
            if cancel:
                text += f" · 已取消 {cancel}"
            self.summary.set(text)

        def finish(self):
            self.running = False
            self.start_btn.config(state="normal")
            self.rename_btn.config(state="normal")
            self.stop_btn.config(state="disabled")
            self.update_summary()
            ok, bad, _ = self.counts()
            self.root.title(f"{APP_NAME} v{__version__} — 完成 {ok}/{len(self.jobs)}")

        def poll(self):
            dirty = False
            try:
                while True:
                    idx, kw = self.q.get_nowait()
                    if idx == -1:
                        self.finish()
                        continue
                    iid = str(idx)
                    if not self.tree.exists(iid):
                        continue
                    for k, v in kw.items():
                        self.tree.set(iid, k, v)
                    if "status" in kw:
                        self.states[idx] = kw["status"]
                        tag = tag_for(kw["status"])
                        self.tree.item(iid, tags=((tag,) if tag else ()) +
                                       (("odd",) if idx % 2 else ()))
                        dirty = True
            except queue.Empty:
                pass
            if dirty:
                self.update_summary()
            self.root.after(100, self.poll)

        # ---------------- 批量下载并重命名窗口 ----------------
        def open_rename(self):
            if alive(self.rename_win) if self.rename_win is not None else False:
                self.rename_win.lift()
                self.rename_win.focus_force()
                return
            win = tk.Toplevel(self.root)
            self.rename_win = win
            self.tops.append(win)
            win.title("批量下载并重命名")
            win.geometry("900x600")
            win.minsize(680, 460)
            win.transient(self.root)

            frm = ttk.Frame(win, padding=(20, 16, 20, 16))
            frm.pack(fill="both", expand=True)

            top = ttk.Frame(frm)
            top.pack(fill="x")
            ttk.Button(top, text="从谷歌表格粘贴链接和重命名", style="Accent.TButton",
                       command=lambda: paste_from_sheet()).pack(side="left")
            ttk.Button(top, text="清空", command=lambda: clear_all()).pack(side="left", padx=8)
            ttk.Label(top, text="先在谷歌表格选中 A、B 两列并复制，再点左侧按钮",
                      style="Muted.TLabel").pack(side="left", padx=6)

            body = ttk.Frame(frm)
            body.columnconfigure(0, weight=3, uniform="col")
            body.columnconfigure(1, weight=2, uniform="col")
            body.rowconfigure(1, weight=1)
            ttk.Label(body, text="下载链接（每行一个）", style="Sub.TLabel").grid(
                row=0, column=0, sticky="w", pady=(0, 6))
            ttk.Label(body, text="新文件名（与左侧同一行对应）", style="Sub.TLabel").grid(
                row=0, column=1, sticky="w", padx=(10, 0), pady=(0, 6))

            lcard = self.make_card(body)
            lcard.grid(row=1, column=0, sticky="nsew")
            rcard = self.make_card(body)
            rcard.grid(row=1, column=1, sticky="nsew", padx=(10, 0))
            left = self.make_text(lcard, width=10, height=8)
            right = self.make_text(rcard, width=10, height=8)
            left.pack(fill="both", expand=True)
            right.pack(fill="both", expand=True)
            sb = ttk.Scrollbar(body)
            sb.grid(row=1, column=2, sticky="ns", padx=(6, 0))

            def yview(*a):
                left.yview(*a)
                right.yview(*a)

            def on_scroll(first, last):
                sb.set(first, last)
                left.yview_moveto(first)
                right.yview_moveto(first)

            sb.configure(command=yview)
            left.configure(yscrollcommand=on_scroll)
            right.configure(yscrollcommand=on_scroll)

            hint = ttk.Label(frm, text="新文件名不写扩展名时会自动沿用原文件的扩展名；留空则保持原文件名。"
                                       "保存目录和线程数使用主窗口中的设置。",
                             style="Muted.TLabel", wraplength=820)
            bottom = ttk.Frame(frm)
            # 先固定底部按钮栏和提示，再让文本区占用剩余空间；
            # 这样无论窗口多小或系统缩放多大，“开始下载并重命名”按钮都不会被挤出去
            bottom.pack(side="bottom", fill="x")
            hint.pack(side="bottom", anchor="w", pady=(10, 8))
            body.pack(fill="both", expand=True, pady=(14, 0))
            info = tk.StringVar()
            ttk.Label(bottom, textvariable=info, style="Muted.TLabel").pack(side="left")
            ttk.Button(bottom, text="开始下载并重命名", style="Accent.TButton",
                       command=lambda: go()).pack(side="right")
            ttk.Button(bottom, text="取消", command=win.destroy).pack(side="right", padx=8)

            def lines_of(widget):
                return widget.get("1.0", "end-1c").split("\n")

            def refresh_info(_e=None):
                n = sum(1 for s in lines_of(left) if s.strip())
                m = sum(1 for s in lines_of(right) if s.strip())
                info.set(f"链接 {n} 条，已填写新文件名 {m} 条")

            left.bind("<KeyRelease>", refresh_info)
            right.bind("<KeyRelease>", refresh_info)

            def clear_all():
                left.delete("1.0", "end")
                right.delete("1.0", "end")
                refresh_info()

            def paste_from_sheet():
                try:
                    data = win.clipboard_get()
                except tk.TclError:
                    data = ""
                if not data.strip():
                    messagebox.showinfo("提示", "剪贴板里没有内容。\n请先在谷歌表格选中 A、B 两列并复制。",
                                        parent=win)
                    return
                links, names, skipped = parse_sheet_text(data)
                if not links:
                    messagebox.showinfo("提示", "没有识别到数据，请确认复制的是表格单元格。", parent=win)
                    return
                left.delete("1.0", "end")
                right.delete("1.0", "end")
                left.insert("1.0", "\n".join(links))
                right.insert("1.0", "\n".join(names))
                refresh_info()
                if skipped:
                    info.set(info.get() + "（已自动跳过表头行）")

            def go():
                links = lines_of(left)
                names = lines_of(right)
                jobs = build_jobs(links, names)
                if not jobs:
                    messagebox.showinfo("提示", "请先填写下载链接", parent=win)
                    return
                n_links = sum(1 for s in links if s.strip())
                n_names = sum(1 for s in names if s.strip())
                if n_names > n_links:
                    if not messagebox.askyesno(
                            "确认", f"右侧文件名（{n_names} 个）比链接（{n_links} 条）多，"
                                    "多出的文件名将被忽略。\n是否继续？", parent=win):
                        return
                if self.launch(jobs):
                    win.destroy()
                    self.root.lift()

            self.apply_theme()
            refresh_info()
            left.focus_set()

    root = tk.Tk()
    App(root)
    root.mainloop()


# --------------------------------------------------------------------------
# 命令行
# --------------------------------------------------------------------------
def printable(text):
    """去掉控制字符（含终端转义序列的 ESC），防止链接文件或服务器返回的内容篡改终端显示。"""
    return "".join(ch for ch in str(text) if unicodedata.category(ch) not in ("Cc", "Cf"))


def run_cli(args):
    links, names = [], []
    try:
        with open(args.file, encoding="utf-8") as f:
            for line in f.read().splitlines():
                parts = line.split("\t", 1)
                links.append(parts[0])
                names.append(parts[1] if len(parts) > 1 else "")
    except (OSError, UnicodeDecodeError) as e:
        print(f"无法读取链接文件：{e}")
        return
    jobs = build_jobs(links, names)
    if not jobs:
        print("链接文件为空")
        return
    state = {}
    lock = threading.Lock()

    def report(idx, **kw):
        with lock:
            s = state.setdefault(idx, {})
            old = s.get("status")
            s.update(kw)
            if "status" in kw and kw["status"] != old:
                label = s.get("name") or jobs[idx][3] or jobs[idx][1] or jobs[idx][2]
                print(printable(f"[{idx + 1}/{len(jobs)}] {label} -> {kw['status']}"), flush=True)

    stop = threading.Event()
    try:
        run_batch(jobs, os.path.abspath(os.path.expanduser(args.out)), args.threads, stop, report)
    except KeyboardInterrupt:
        stop.set()
        print("已中断（未完成的文件保留为 .part，下次可续传）")
    ok = sum(1 for s in state.values() if s.get("status") in ("完成", "已存在，跳过"))
    print(f"全部结束：成功 {ok} / 共 {len(jobs)}")


def main():
    ap = argparse.ArgumentParser(description=f"{APP_NAME} v{__version__}")
    ap.add_argument("-V", "--version", action="version", version=f"{APP_NAME} {__version__}")
    ap.add_argument("-f", "--file", help="链接文件（每行一个，可用 Tab 分隔新文件名），提供后进入命令行模式")
    ap.add_argument("-o", "--out", default="downloads", help="保存目录")
    ap.add_argument("-t", "--threads", type=int, default=DEFAULT_THREADS,
                    help=f"并发线程数，默认 {DEFAULT_THREADS}，最大 {MAX_THREADS}")
    args = ap.parse_args()
    if args.file:
        run_cli(args)
    else:
        minimize_console()
        run_gui()


if __name__ == "__main__":
    main()
