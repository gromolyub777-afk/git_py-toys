#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Git Committer v2 — GUI-приложение (Tkinter) для двусторонней синхронизации
папки и git-репозитория + авто-режимы по таймеру.

Возможности:
  * Большая кнопка «КОММИТ»            — папка → репозиторий (add/commit/push).
  * Кнопка «ВЫГРУЗИТЬ ИЗ РЕПО»         — репозиторий → папка (download_folder).
  * Поля: Папка, Ссылка репо (кнопка «…» — вставить из буфера), Папка выгрузки.
  * Выбор ветки из списка (git branch -r), счётчик изменений на кнопке.
  * Авто-режимы с индивидуальными интервалами, расписанием, watcher'ом, паузой.
  * Dry-run, автобэкап перед выгрузкой, проверка remote, откат коммита, теги.
  * Лог в файл с ротацией, звук по окончании, трей, компактный вид.
  * Конфиг генерируется сам, пишется атомарно, битый файл бэкапится.

Запуск:  python git_committer_v2.py
Зависимости: стандартная библиотека Python + установленный git.
Необязательные: pystray + Pillow (трей), watchdog (watcher файлов).
"""

import hashlib
import json
import logging
import os
import queue
import re
import shutil
import subprocess
import sys
import tempfile
import threading
import traceback
import zipfile
from datetime import datetime, timedelta
from logging.handlers import RotatingFileHandler
from pathlib import Path

try:
    import tkinter as tk
    from tkinter import filedialog, messagebox, ttk
    _TK_ERROR_TEXT = ""
except Exception as _tk_exc:                       # noqa: BLE001
    tk = None
    _TK_ERROR_TEXT = str(_tk_exc)


__version__ = "2.1.0"
APP_TITLE = f"Git Committer v{__version__}"
CONFIG_NAME = "config.json"
LOG_NAME = "git_committer.log"


# --------------------------------------------------------------------------- #
#  Лог в файл (всегда, рядом с config.json; ротация 1 МБ × 3)                 #
# --------------------------------------------------------------------------- #

def _setup_file_logging() -> logging.Logger:
    logger = logging.getLogger("git_committer")
    if logger.handlers:                     # повторный вызов — не дублируем
        return logger
    logger.setLevel(logging.DEBUG)
    try:
        handler = RotatingFileHandler(
            str(config_path().parent / LOG_NAME),
            maxBytes=1_000_000, backupCount=3, encoding="utf-8")
        handler.setFormatter(logging.Formatter(
            "%(asctime)s [%(levelname)s] %(message)s"))
        logger.addHandler(handler)
    except OSError:
        pass                                # нет прав на запись — не роняем
    return logger


def log_to_file(msg: str, level: int = logging.INFO):
    """Запись сообщения GUI-лога в файл (пишется ВСЕГДА)."""
    _setup_file_logging().log(level, msg)


# --------------------------------------------------------------------------- #
#  Проверка git при старте                                                     #
# --------------------------------------------------------------------------- #

GIT_MIN_VERSION = (2, 20)


def check_git():
    """Возвращает (ok, версия_или_текст_ошибки). ok=False — git не найден."""
    try:
        out = subprocess.run(["git", "--version"], capture_output=True,
                             text=True, timeout=15).stdout or ""
    except (FileNotFoundError, OSError, subprocess.TimeoutExpired):
        return False, ""
    m = re.search(r"(\d+)\.(\d+)", out)
    if not m:
        return True, out.strip() or "неизвестно"
    return True, (int(m.group(1)), int(m.group(2)))


# --------------------------------------------------------------------------- #
#  Placeholder-поле ввода                                                      #
# --------------------------------------------------------------------------- #

class PlaceholderEntry(ttk.Entry):
    """Поле ввода с подсказкой (placeholder), если оно пустое и не в фокусе."""

    GRAY = "#999999"
    BLACK = "#000000"

    def __init__(self, master=None, placeholder="", **kwargs):
        super().__init__(master, **kwargs)
        self.placeholder = placeholder
        self._showing_ph = False
        self.var = tk.StringVar(master=self)
        self.configure(textvariable=self.var)
        self.bind("<FocusIn>", self._on_focus_in)
        self.bind("<FocusOut>", self._on_focus_out)
        self._show_placeholder()

    # ---- value API ---------------------------------------------------- #
    def get(self):
        if self._showing_ph:
            return ""
        return self.var.get()

    def set(self, value):
        value = value or ""
        if value:
            self._hide_placeholder()
            self.var.set(value)
            self.configure(foreground=self.BLACK)
        else:
            self._show_placeholder()

    def _show_placeholder(self):
        self._showing_ph = True
        self.var.set(self.placeholder)
        self.configure(foreground=self.GRAY)

    def _hide_placeholder(self):
        self._showing_ph = False
        self.var.set("")
        self.configure(foreground=self.BLACK)

    def _on_focus_in(self, _e):
        self._hide_placeholder()

    def _on_focus_out(self, _e):
        if not self.var.get():
            self._show_placeholder()


# --------------------------------------------------------------------------- #
#  Конфигурация                                                               #
# --------------------------------------------------------------------------- #

def config_dir() -> Path:
    """Каталог, где живёт конфиг (рядом со скриптом / exe)."""
    if getattr(sys, "frozen", False):        # PyInstaller: рядом с exe
        return Path(sys.executable).resolve().parent
    try:
        base = Path(__file__).resolve().parent
    except NameError:                        # интерактивный режим
        base = Path.cwd()
    return base


def config_path() -> Path:
    return config_dir() / CONFIG_NAME


HISTORY_LIMIT = 50


def default_config() -> dict:
    """Конфиг по умолчанию — генерируется сам, без вмешательства пользователя."""
    return {
        "source_folder": str(Path.home()),           # папка, откуда коммитим
        "repository": "",                            # ССЫЛКА на репозиторий (URL)
        "branch": "main",                            # ветка для коммита
        "commit_message": "Автокоммит: {datetime}",  # подстрока {datetime} подставится сама
        "author_name": "Git Committer",              # локальный автор коммита
        "author_email": "committer@local",
        "push": False,                               # пушить ли после коммита (ручной КОММИТ)
        "delete_extra": True,                        # удалять в репо файлы, отсутствующие в источнике
        "history": [],                               # последние удачные операции (до 50)
        # ---- v2: авто-режимы и выгрузка ---------------------------------
        "auto_commit": False,                        # авто-коммит по таймеру
        "auto_clone": False,                         # авто-выгрузка из репо по таймеру
        "auto_interval_min": 5,                      # общий интервал авто-режимов, минут
        "auto_commit_interval_min": 0,               # 0 = использовать общий
        "auto_clone_interval_min": 0,                # 0 = использовать общий
        "download_folder": "",                       # куда выгружать из репо ('' = source_folder)
        # ---- v2.1 --------------------------------------------------------
        "version": 2,                                # схема конфига
        "last_version": __version__,                 # версия приложения при записи (миграции)
        "git_timeout_min": 30,                       # таймаут сетевых git-команд, мин (1–60)
        "auto_schedule": {"enabled": False, "from": "09:00", "to": "18:00",
                          "days": [1, 2, 3, 4, 5]},  # Пн=1 … Вс=7
        "dry_run": False,                            # только показать, ничего не писать
        "backup_before_download": True,              # ZIP-бэкап целевой папки перед выгрузкой
        "backup_keep_last": 10,                      # хранить последних N бэкапов
        "confirm_delete_extras": True,               # спрашивать перед удалением лишних
        "sound_on_finish": False,                    # звук по окончании задачи
        "tray_on_close": False,                      # сворачивать в трей при закрытии
        "compact_view": False,                       # мини-режим интерфейса
        "watch_source": False,                       # авто-коммит по изменению файлов
        "auto_push": False,                          # push после АВТО-коммита
    }


def load_config() -> dict:
    """Читает конфиг; если файла нет — создаёт его автоматически."""
    path = config_path()
    if not path.exists():
        cfg = default_config()
        save_config(cfg)
        return cfg
    try:
        with open(path, "r", encoding="utf-8") as f:
            data = json.load(f)
        if not isinstance(data, dict):
            raise json.JSONDecodeError("конфиг должен быть объектом JSON", "", 0)
    except (json.JSONDecodeError, OSError, UnicodeDecodeError):
        # Повреждённый конфиг — не роняем приложение, пересоздаём,
        # а битый файл сохраняем рядом для отладки.
        try:
            backup = path.with_suffix(".broken.json")
            path.replace(backup)
        except OSError:
            pass
        cfg = default_config()
        save_config(cfg)
        return cfg
    # Добиваем отсутствующие ключи значениями по умолчанию
    base = default_config()
    for key, value in base.items():
        data.setdefault(key, value)
    sched = data.get("auto_schedule")
    if not isinstance(sched, dict):
        sched = dict(base["auto_schedule"])
    else:
        for k, v in base["auto_schedule"].items():
            sched.setdefault(k, v if not isinstance(v, list) else list(v))
    days = [d for d in sched.get("days", []) if isinstance(d, int) and 1 <= d <= 7]
    sched["days"] = sorted(set(days))
    data["auto_schedule"] = sched
    return data


def save_config(cfg: dict) -> None:
    """Атомарная запись конфига: mkstemp + os.replace; tmp/fd чистятся при ошибке."""
    path = config_path()
    cfg = dict(cfg)
    cfg["last_version"] = __version__
    tmp_fd, tmp_name = tempfile.mkstemp(dir=str(path.parent), suffix=".tmp")
    fd_owned = False
    try:
        f = os.fdopen(tmp_fd, "w", encoding="utf-8")
        fd_owned = True
        with f:
            json.dump(cfg, f, ensure_ascii=False, indent=2)
        os.replace(tmp_name, path)
    except Exception:
        # Если os.fdopen бросил исключение — fd всё ещё наш, закрываем сами.
        if not fd_owned:
            try:
                os.close(tmp_fd)
            except OSError:
                pass
        try:
            if os.path.exists(tmp_name):
                os.remove(tmp_name)
        except OSError:
            pass
        raise


def open_config_in_editor(path: Path) -> None:
    """Открыть конфиг во внешнем редакторе/просмотрщике (кроссплатформенно)."""
    try:
        if sys.platform.startswith("win"):
            os.startfile(str(path))                          # type: ignore[attr-defined]
        elif sys.platform == "darwin":
            subprocess.Popen(["open", "-t", str(path)])
        else:
            for opener in ("xdg-open", "gnome-open", "kde-open"):
                try:
                    subprocess.Popen([opener, str(path)])
                    return
                except FileNotFoundError:
                    continue
            # Если графических открывальщиков нет — печатаем путь
            raise FileNotFoundError("не найден системный открывальщик файлов")
    except Exception as exc:                                 # noqa: BLE001
        messagebox.showwarning(APP_TITLE,
                               f"Не удалось открыть конфиг автоматически.\n"
                               f"Файл лежит здесь:\n{path}\n\n({exc})")


# --------------------------------------------------------------------------- #
#  Git-операции                                                               #
# --------------------------------------------------------------------------- #

class GitError(Exception):
    pass


# Таймаут одной локальной git-команды, сек
GIT_TIMEOUT = 300
# Сетевые команды (clone/fetch/pull/push/ls-remote) на больших репо могут идти
# долго — базовый увеличенный таймаут; пользователь может задать свой
# (git_timeout_min в конфиге, см. net_timeout).
GIT_NET_TIMEOUT = 1800


def run_git(args, cwd=None, timeout=GIT_TIMEOUT):
    """Запуск git с захватом вывода. Бросает GitError при ненулевом коде/таймауте."""
    env = os.environ.copy()
    # Никаких интерактивных запросов паролей и редакторов из-под GUI
    env["GIT_TERMINAL_PROMPT"] = "0"
    env["GIT_EDITOR"] = "true"
    env["GCM_INTERACTIVE"] = "never"        # Git Credential Manager
    try:
        proc = subprocess.run(
            ["git", *args],
            cwd=str(cwd) if cwd else None,
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
            timeout=timeout,
            env=env,
        )
    except FileNotFoundError:
        raise GitError("Команда «git» не найдена в системе. Установите git.")
    except subprocess.TimeoutExpired:
        label = f"{timeout} с" if timeout else "неограниченно долго"
        raise GitError(f"Команда «git {' '.join(args)}» не завершилась за {label}.")
    if proc.returncode != 0:
        raise GitError((proc.stderr or proc.stdout or "")
                       .strip() or f"git {' '.join(args)} завершился с ошибкой")
    return (proc.stdout or "").strip()


def net_timeout(cfg: dict) -> int:
    """Таймаут сетевых git-команд из конфига (git_timeout_min, спинбокс 1–60)."""
    try:
        minutes = int(cfg.get("git_timeout_min", 30))
    except (TypeError, ValueError):
        minutes = 30
    minutes = min(max(minutes, 1), 60)
    return minutes * 60


def is_repo_url(repo: str) -> bool:
    """Похожа ли строка на ссылку git-репозитория?"""
    if not repo:
        return False
    lowered = repo.lower()
    if lowered.startswith(("http://", "https://", "git://", "ssh://",
                           "git@", "file://")):
        return True
    # scp-подобный формат: user@host:path/repo.git (без пробелов)
    if re.match(r"^[\w.-]+@[\w.-]+:(?!/)[\w./~@-]+$", repo):
        return True
    # путь, заканчивающийся на .git — тоже считаем ссылкой на репозиторий
    if lowered.endswith(".git"):
        return True
    return False


def local_clone_dir(repo_url: str) -> Path:
    """Стабильная локальная папка для клонирования (по хешу ссылки)."""
    digest = hashlib.sha1(repo_url.encode("utf-8")).hexdigest()[:12]
    name = re.sub(r"[^\w.-]", "_", Path(repo_url.rstrip("/")).name) or "repo"
    if name.endswith(".git"):
        name = name[:-4]
    return config_dir() / f"repo_{name}_{digest}"


def ensure_repo_layout(cfg: dict, *, need_source: bool = True) -> Path:
    """
    Подготавливает рабочую область по ССЫЛКЕ на репозиторий:
      * repository — URL (https/git/ssh/file:// или путь .git);
      * клонируем в подпапку ./repo_<имя>_<hash>, если её ещё нет;
      * если есть — fetch/checkout/pull, чтобы быть в актуальном состоянии.
    need_source=True дополнительно требует существующую папку-источник
    (для прямого процесса КОММИТ).
    Возвращает Path к рабочей копии репозитория.
    """
    repo = str(cfg.get("repository", "") or "").strip()
    source = str(cfg.get("source_folder", "") or "").strip()
    if not repo:
        raise GitError("Вставьте ссылку на репозиторий (ключ «repository» в конфиге), "
                       "например https://github.com/user/repo.git")
    if need_source and (not source or not Path(source).is_dir()):
        raise GitError(f"Папка-источник не существует: {source}")

    if not is_repo_url(repo):
        raise GitError(
            f"«{repo}» не похоже на ссылку на репозиторий.\n"
            "Поддерживаются: https://…, http://…, git://…, ssh://…, "
            "git@host:user/repo.git, file:///… или путь, оканчивающийся на .git")

    local = local_clone_dir(repo)
    branch = cfg.get("branch", "main") or "main"
    nt = net_timeout(cfg)

    if not (local / ".git").is_dir():
        run_git(["clone", repo, str(local)], timeout=nt)
    else:
        run_git(["fetch", "origin"], cwd=local, timeout=nt)

    # ---- безопасное переключение на нужную ветку (без сброса -B) --------- #
    def ref_exists(ref: str) -> bool:
        """Есть ли ref (rev-parse --verify: код 0 = есть, иначе — нет)."""
        try:
            run_git(["rev-parse", "--verify", "--quiet", ref], cwd=local)
            return True
        except GitError:
            return False

    current = ""
    try:
        current = run_git(["rev-parse", "--abbrev-ref", "HEAD"], cwd=local)
    except GitError:
        pass  # например, пустой клон (unborn HEAD)

    if current != branch:
        if ref_exists(f"refs/heads/{branch}"):
            run_git(["checkout", branch], cwd=local)
        elif ref_exists(f"refs/remotes/origin/{branch}"):
            # ветка есть на remote — создаём локальную-трек без сброса чего-либо
            run_git(["checkout", "-b", branch, "--track",
                     f"origin/{branch}"], cwd=local)
        else:
            # ветки нигде нет — создаём новую от текущего коммита.
            # В пустом репозитории (unborn HEAD) checkout просто переключает HEAD.
            run_git(["checkout", "-b", branch], cwd=local)

    # Подтягиваем изменения с remote только если рабочая копия чистая —
    # иначе наши прошлые незапушенные коммиты/файлы останутся как есть.
    if not run_git(["status", "--porcelain"], cwd=local):
        try:
            run_git(["pull", "--ff-only", "origin", branch], cwd=local,
                    timeout=nt)
        except GitError:
            pass

    # Если в репозитории вообще нет ни одного коммита (пустой клон),
    # git commit не сможет определить HEAD — заводим пустой коммит.
    try:
        run_git(["rev-parse", "--verify", "--quiet", "HEAD"], cwd=local)
    except GitError:
        run_git(["commit", "--allow-empty", "-m", "Initial empty commit"],
                cwd=local)
    return local


# Папки/файлы, которые никогда не копируются в репозиторий
SYNC_IGNORE = {".git", ".venv", "venv", "node_modules", "__pycache__",
               ".idea", ".vscode", ".mypy_cache", ".pytest_cache"}


def _ignore_dirs(_dir: str, names: list) -> set:
    """shutil.copytree(ignore): отсекаем служебные каталоги и *.egg-info."""
    ignored = {n for n in names if n in SYNC_IGNORE or n.endswith(".egg-info")}
    return ignored


def sync_source_into_repo(source: Path, workdir: Path, delete_extra: bool = True) -> int:
    """
    Копирует содержимое папки-источника в рабочую копию репозитория.
      * пропускает служебные папки (SYNC_IGNORE);
      * при delete_extra удаляет в рабочей копии файлы/папки, которых нет
        в источнике (кроме .git), чтобы дерево точно отражало источник.
    Возвращает число синхронизированных верхнеуровневых объектов.
    """
    count = 0
    source_names = set()
    for item in sorted(source.iterdir()):
        if item.name in SYNC_IGNORE:
            continue
        source_names.add(item.name)
        dest = workdir / item.name
        if item.is_dir():
            if dest.exists():
                shutil.rmtree(dest)
            shutil.copytree(item, dest, ignore=_ignore_dirs)
        else:
            shutil.copy2(item, dest)
        count += 1

    if delete_extra:
        for old in sorted(workdir.iterdir()):
            if old.name in SYNC_IGNORE or old.name in source_names:
                continue
            if old.is_dir():
                shutil.rmtree(old)
            else:
                old.unlink()

    return count


def count_files(tree: Path) -> int:
    """Рекурсивное число файлов в дереве (служебные папки не считаем)."""
    total = 0
    for root_dir, dirs, files in os.walk(tree):
        dirs[:] = [d for d in dirs if d not in SYNC_IGNORE]
        total += len(files)
    return total


def append_history(cfg: dict, entry: dict) -> None:
    """Добавляет запись в историю (максимум HISTORY_LIMIT).

    Пишется напрямую в config.json read-modify-write: рабочий конфиг может
    быть снапшотом, сделанным до других изменений GUI, — прямая запись их
    не затрёт.
    """
    try:
        disk_cfg = load_config()
    except Exception as exc:                               # noqa: BLE001
        # Не глушим молча: fallback на снимок, но предупреждаем в stderr.
        print(f"append_history: не удалось прочитать конфиг с диска ({exc}), "
              "использую снимок", file=sys.stderr)
        disk_cfg = dict(cfg)
    history = disk_cfg.get("history")
    if not isinstance(history, list):
        history = []
    history.append(entry)
    del history[:-HISTORY_LIMIT]
    disk_cfg["history"] = history
    cfg["history"] = history          # держим снимок в курсе
    save_config(disk_cfg)


def make_commit_message(cfg: dict) -> str:
    message = str(cfg.get("commit_message") or "Автокоммит: {datetime}")
    return message.replace("{datetime}",
                           datetime.now().strftime("%Y-%m-%d %H:%M:%S"))


def porcelain_plan(workdir: Path, staged: bool = False) -> tuple:
    """Разбор git status --porcelain: ([добавляется/меняется], [удаляется])."""
    out = run_git(["status", "--porcelain"], cwd=workdir)
    added, deleted = [], []
    for line in out.splitlines():
        if not line.strip():
            continue
        x, y = line[0], line[1]
        name = line[3:]
        if staged:
            if x in "AMRC":
                added.append(name)
            elif x == "D":
                deleted.append(name)
        else:
            if y in "AMRCD" or (y == "?" and x == "?"):
                added.append(name)
            elif y == "D":
                deleted.append(name)
    return added, deleted


def commit_all(cfg: dict, log, auto: bool = False) -> str:
    """Прямой процесс: синхронизация + add + commit (+ push при желании).

    auto=True — запуск из авто-режима: dry-run не применяется, push
    определяется отдельным флагом auto_push (а не ручным push).
    """
    do_dry = bool(cfg.get("dry_run")) and not auto
    workdir = ensure_repo_layout(cfg, need_source=True)
    source = Path(cfg["source_folder"]).expanduser()

    # Не копируем репозиторий сам в себя (защита от ручного конфига).
    try:
        same = source.resolve() == workdir.resolve()
    except OSError:
        same = False
    if same:
        raise GitError("Папка-источник и рабочая копия репозитория совпадают. "
                       "Укажите отдельную папку для файлов.")

    if do_dry:
        # Dry-run: НЕ пишем на диск — только план по git status.
        pre_added, pre_deleted = porcelain_plan(workdir, staged=False)
        log("DRY-RUN: изменения на диск не применяются.")
        return "\n".join(
            [f"РЕЖИМ DRY-RUN (только просмотр) — ветка {cfg.get('branch') or 'main'}:",
             "",
             f"Файлов в источнике будет добавлено/обновлено: {len(pre_added)}",
             *(f"  + {n}" for n in pre_added[:100]),
             f"Файлов в рабочей копии будет удалено: {len(pre_deleted)}",
             *(f"  - {n}" for n in pre_deleted[:100]),
             "",
             "Коммит и push НЕ выполнялись; файлы на диске не изменялись."])

    n = sync_source_into_repo(source, workdir,
                              delete_extra=bool(cfg.get("delete_extra", True)))
    log(f"Синхронизировано объектов из папки: {n}")

    # Ветка уже подготовлена в ensure_repo_layout (безопасный checkout/создание).
    branch = cfg.get("branch", "main") or "main"

    run_git(["add", "-A"], cwd=workdir)

    status = run_git(["status", "--porcelain"], cwd=workdir)
    if not status:
        log("Нечего коммитить — изменений нет.")
        return ""

    message = make_commit_message(cfg)

    author = str(cfg.get("author_name", "")).strip()
    email = str(cfg.get("author_email", "")).strip()
    git_args = ["commit", "-m", message]
    if author and email:
        git_args += ["--author", f"{author} <{email}>"]
    out = run_git(git_args, cwd=workdir)
    log(out.splitlines()[-1] if out else "Коммит создан.")

    sha = run_git(["rev-parse", "--short", "HEAD"], cwd=workdir)

    # Записываем историю и фиксируем успех ДО push — чтобы ошибка/неудача
    # пуша не маскировала уже созданный коммит.
    append_history(cfg, {
        "type": "commit",
        "time": datetime.now().isoformat(timespec="seconds"),
        "sha": sha,
        "branch": branch,
        "message": message,
    })
    log(f"Коммит {sha} создан в ветке {branch}")

    # push: ручной КОММИТ — флаг push; авто-коммит — отдельный флаг auto_push.
    should_push = bool(cfg.get("auto_push")) if auto else bool(cfg.get("push"))
    if should_push and sha:
        remote_exists = False
        try:
            remotes = run_git(["remote"], cwd=workdir)
            remote_exists = "origin" in remotes.split()
        except GitError:
            pass
        if not remote_exists:
            log("ВНИМАНИЕ: push не выполнен — в рабочей копии нет remote 'origin'.")
        else:
            try:
                run_git(["push", "-u", "origin", branch], cwd=workdir,
                        timeout=net_timeout(cfg))
                log(f"Запушено в origin/{branch}")
            except GitError as exc:
                # Коммит уже создан и записан в историю — push-ошибка некритична.
                log(f"ВНИМАНИЕ: push не выполнен: {exc}")

    return sha


def backups_dir() -> Path:
    return config_dir() / "backups"


def backup_target_folder(target: Path, log) -> Path:
    """ZIP-бэкап содержимого папки в ./backups/<имя>_<YYYYMMDD_HHMMSS>.zip.

    Служебные папки (SYNC_IGNORE, включая .git) в архив не кладём.
    Хранятся последние backup_keep_last (по умолчанию 10).
    """
    keep = 10
    try:
        keep = int(load_config().get("backup_keep_last", 10))
    except Exception:                                        # noqa: BLE001
        pass
    keep = min(max(keep, 1), 100)
    bdir = backups_dir()
    bdir.mkdir(parents=True, exist_ok=True)
    stamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    safe_name = re.sub(r"[^\w.-]", "_", target.name) or "target"
    zip_path = bdir / f"{safe_name}_{stamp}.zip"
    with zipfile.ZipFile(zip_path, "w", zipfile.ZIP_DEFLATED) as zf:
        for root_dir, dirs, files in os.walk(target):
            dirs[:] = [d for d in dirs if d not in SYNC_IGNORE]
            for fname in files:
                full = Path(root_dir) / fname
                try:
                    rel = full.relative_to(target)
                except ValueError:
                    continue
                try:
                    zf.write(full, arcname=str(rel))
                except OSError:
                    pass                                   # пропущен/нет прав
    # ротация бэкапов: оставляем самые свежие N
    try:
        all_backups = sorted(bdir.glob(f"{safe_name}_*.zip"),
                             key=lambda p: p.stat().st_mtime, reverse=True)
        for old in all_backups[keep:]:
            try:
                old.unlink()
            except OSError:
                pass
    except OSError:
        pass
    log(f"Бэкап целевой папки: {zip_path.name}")
    return zip_path


def download_from_repo(cfg: dict, log, confirm=None) -> str:
    """
    Обратный процесс: клон/fetch/checkout/pull →
    копирование рабочей копии (без .git) в download_folder (или source_folder) →
    удаление лишних файлов (с подтверждением confirm в GUI, безусловно в авто).
    Возвращает sha HEAD выгруженной ветки либо текст плана (dry-run).
    """
    do_dry = bool(cfg.get("dry_run"))
    workdir = ensure_repo_layout(cfg, need_source=False)
    branch = cfg.get("branch", "main") or "main"
    sha = run_git(["rev-parse", "--short", "HEAD"], cwd=workdir)

    target = str(cfg.get("download_folder", "") or "").strip()
    if not target:
        target = str(cfg.get("source_folder", "") or "").strip()
    if not target:
        raise GitError("Не указана папка выгрузки («Папка выгрузки» или «Папка»).")
    target_path = Path(target).expanduser()

    # Защита: нельзя выгружать поверх рабочей копии репозитория или внутрь неё.
    try:
        wd_resolved = workdir.resolve()
        tg_resolved = target_path.resolve()
        if tg_resolved == wd_resolved or wd_resolved in tg_resolved.parents:
            raise GitError("Папка выгрузки совпадает с рабочей копией репозитория "
                           "или находится внутри неё — выберите другую папку.")
    except OSError:
        pass

    repo_names = {item.name for item in workdir.iterdir()
                  if item.name not in SYNC_IGNORE}
    nfiles = count_files(workdir)

    if do_dry:
        # Dry-run: НЕ трогаем диск — только план.
        try:
            existing = {p.name for p in target_path.iterdir()} \
                if target_path.is_dir() else set()
        except OSError:
            existing = set()
        will_copy = sorted(repo_names & existing)
        will_add = sorted(repo_names - existing)
        extras = sorted(n for n in existing
                        if n not in repo_names and n not in SYNC_IGNORE)
        lines = [f"РЕЖИМ DRY-RUN (только просмотр) — {branch}@{sha} → {target_path}",
                 "",
                 f"Будет обновлено файлов/папок: {len(will_copy)}",
                 *(f"  ~ {n}" for n in will_copy[:100]),
                 f"Будет добавлено: {len(will_add)}",
                 *(f"  + {n}" for n in will_add[:100]),
                 f"Лишних объектов будет удалено: {len(extras)}",
                 *(f"  - {n}" for n in extras[:100]),
                 "",
                 "Файлы на диске НЕ изменялись."]
        log("DRY-RUN: выгрузка не выполнялась, диск не тронут.")
        return "\n".join(lines)

    target_path.mkdir(parents=True, exist_ok=True)

    # Очистка лишнего (файлов, которых нет в репо) — с подтверждением (GUI)
    # или безусловно в авто-режиме (confirm=None). Служебные объекты
    # (SYNC_IGNORE: .git целевой папки и т.п.) не удаляем никогда.
    extras = [p for p in sorted(target_path.iterdir())
              if p.name not in repo_names and p.name not in SYNC_IGNORE] \
        if target_path.is_dir() else []
    do_clean = bool(extras)
    if extras and confirm is not None:
        do_clean = bool(confirm(target_path))
        if not do_clean:
            log(f"Удаление лишних файлов в «{target_path}» отменено "
                f"(осталось {len(extras)} объектов).")
    if extras and do_clean:
        # Автобэкап целевой папки ПЕРЕД любыми изменениями на диске.
        if cfg.get("backup_before_download", True):
            try:
                backup_target_folder(target_path, log)
            except Exception as exc:                         # noqa: BLE001
                raise GitError(f"Не удалось создать бэкап целевой папки "
                               f"({exc}) — выгрузка прервана, диск не тронут.")
    elif target_path.is_dir() and cfg.get("backup_before_download", True) \
            and any(target_path.iterdir()):
        # Даже без удаления лишнего файлы репо перезаписываются — бэкапим.
        try:
            backup_target_folder(target_path, log)
        except Exception as exc:                             # noqa: BLE001
            raise GitError(f"Не удалось создать бэкап целевой папки "
                           f"({exc}) — выгрузка прервана, диск не тронут.")

    # Копируем содержимое рабочей копии (без .git и служебных папок) поверх
    # целевой папки — файлы репозитория всегда актуальны.
    copied = 0
    for item in sorted(workdir.iterdir()):
        if item.name in SYNC_IGNORE:
            continue
        dest = target_path / item.name
        if item.is_dir():
            if dest.exists():
                shutil.rmtree(dest)
            shutil.copytree(item, dest, ignore=_ignore_dirs)
        else:
            shutil.copy2(item, dest)
        copied += 1

    if extras and do_clean:
        for old_item in extras:
            if old_item.is_dir() and not old_item.is_symlink():
                shutil.rmtree(old_item)
            else:
                old_item.unlink()
        log(f"Удалено лишних объектов в «{target_path}»: {len(extras)}")

    tgt_files = count_files(target_path)
    append_history(cfg, {
        "type": "download",
        "time": datetime.now().isoformat(timespec="seconds"),
        "sha": sha,
        "branch": branch,
        "message": f"Выгружено в {target_path}",
    })
    log(f"Выгружено из {branch}@{sha}: {copied} объектов, {tgt_files} файлов → {target_path}")
    return sha


# --------------------------------------------------------------------------- #
#  Звук по окончании (кроссплатформенно)                                      #
# --------------------------------------------------------------------------- #

def play_beep():
    def _run():
        try:
            if sys.platform.startswith("win"):
                import winsound
                winsound.Beep(880, 250)
            elif sys.platform == "darwin":
                subprocess.run(["afplay", "/System/Library/Sounds/Glass.aiff"],
                               timeout=5)
            else:
                wav = "/usr/share/sounds/freedesktop/stereo/complete.oga"
                if os.path.exists(wav) and shutil.which("paplay"):
                    subprocess.run(["paplay", wav], timeout=5)
                else:
                    dev = "/dev/snd/beeper"
                    if os.path.exists(dev):                  # last resort
                        with open(dev, "w") as _f:
                            pass
        except Exception:                                    # noqa: BLE001
            pass                                             # звук — не критично
    threading.Thread(target=_run, daemon=True).start()


# --------------------------------------------------------------------------- #
#  Тултип                                                                     #
# --------------------------------------------------------------------------- #

class ToolTip:
    """Простейший всплывающий тултип для Tk-виджетов."""

    def __init__(self, widget):
        self.widget = widget
        self.tipwindow = None
        self.text = ""
        widget.bind("<Enter>", self._show, add="+")
        widget.bind("<Leave>", self._hide, add="+")
        widget.bind("<ButtonRelease>", self._hide, add="+")

    def set(self, text):
        self.text = text or ""
        if text and self.tipwindow:
            self._hide()
            self._show()

    def _show(self, _e=None):
        if not self.text:
            return
        self._hide()
        x = self.widget.winfo_rootx() + 12
        y = self.widget.winfo_rooty() + self.widget.winfo_height() + 2
        self.tipwindow = tw = tk.Toplevel(self.widget)
        tw.wm_overrideredirect(True)
        tw.wm_geometry(f"+{x}+{y}")
        tk.Label(tw, text=self.text, background="#fffbe6", relief="solid",
                 borderwidth=1, font=("Segoe UI", 9), justify="left",
                 padx=6, pady=3).pack()

    def _hide(self, _e=None):
        if self.tipwindow:
            self.tipwindow.destroy()
            self.tipwindow = None


# --------------------------------------------------------------------------- #
#  GUI                                                                        #
# --------------------------------------------------------------------------- #

class CommitterApp:
    def __init__(self, root):
        self.root = root
        self.cfg = load_config()
        self.busy = False          # занята ли фоновая git-задача
        self.current_task = None   # "commit" | "download" | ... | None

        # очередь сообщений из фонового потока (worker -> GUI)
        self.msg_queue = queue.Queue()

        # --- состояние авто-режимов --------------------------------------- #
        self.auto_enabled = {"commit": False, "download": False}
        self.next_run_at = {"commit": None, "download": None}
        self.paused_until = None                 # «Пауза 1 ч»
        self._pause_lbl_shown = False
        if self.cfg.get("auto_commit"):
            self._schedule_auto("commit", now=datetime.now())
        if self.cfg.get("auto_clone"):
            self._schedule_auto("download", now=datetime.now())

        # --- служебное ----------------------------------------------------- #
        self.change_count = None                 # счётчик изменений на кнопке
        self._count_dirty = True                 # пересчитать после задач
        self._last_status_sig = None
        self._status_job = None
        self._last_watch_event = 0.0             # дебаунс watcher'а
        self._watch_stop = None                  # Event остановки observer'а
        self._watch_thread = None
        self._tray_icon = None
        self._force_quit = False
        self._tt = {}                            # тултипы полей

        root.title(APP_TITLE)
        root.resizable(True, True)
        root.minsize(480, 460)

        style = ttk.Style(root)
        try:
            style.theme_use("clam")
        except tk.TclError:
            pass

        main = ttk.Frame(root, padding=14)
        main.pack(fill="both", expand=True)
        # спецификации раскладки — для compact-режима (grid_forget/grid)
        self._layout_spec = {}

        def _g(widget, **kw):
            """grid с сохранением спецификации (для compact-режима)."""
            widget.grid(**kw)
            self._layout_spec[widget] = ("grid", kw)
            return widget

        def _p(widget, **kw):
            """pack с сохранением спецификации (для compact-режима)."""
            widget.pack(**kw)
            self._layout_spec[widget] = ("pack", kw)
            return widget

        # --- верхняя строка: пути + кнопки "…" ----------------------------- #
        top = ttk.Frame(main)
        top.pack(fill="x")

        self._w_folder_label = _g(ttk.Label(top, text="Папка:"),
                                  row=0, column=0, sticky="w")
        self.var_folder = tk.StringVar(value=self.cfg.get("source_folder", ""))
        self._w_folder = _g(ttk.Entry(top, textvariable=self.var_folder),
                            row=0, column=1, sticky="ew", padx=(6, 2))
        self._w_folder_btn = _g(ttk.Button(top, text="…", width=3,
                                           command=self.pick_folder),
                                row=0, column=2)

        self._w_repo_label = _g(ttk.Label(top, text="Ссылка репо:"),
                                row=1, column=0, sticky="w", pady=(6, 0))
        self.var_repo = PlaceholderEntry(top, placeholder="https://github.com/user/repo.git")
        if self.cfg.get("repository"):
            self.var_repo.set(self.cfg["repository"])
        self._w_repo = self.var_repo
        _g(self.var_repo, row=1, column=1, sticky="ew", padx=(6, 2), pady=(6, 0))
        self._w_repo_btn = _g(ttk.Button(top, text="…", width=3,
                                         command=self.paste_repo_url),
                              row=1, column=2, pady=(6, 0))

        # Тест соединения + таймаут сетевых операций — под полем репо
        self._w_tools_row = _g(ttk.Frame(top), row=2, column=1, columnspan=2,
                               sticky="w", pady=(4, 0))
        self.btn_test_conn = ttk.Button(self._w_tools_row, text="Тест соединения",
                                       command=self.on_test_connection)
        self.btn_test_conn.pack(side="left")
        ttk.Label(self._w_tools_row, text="  Таймаут, мин:").pack(side="left")
        self.var_timeout = tk.IntVar(value=self._clamp_timeout(
            self.cfg.get("git_timeout_min", 30)))
        self.spn_timeout = ttk.Spinbox(self._w_tools_row, from_=1, to=60, width=4,
                                       textvariable=self.var_timeout,
                                       command=self._on_settings_change)
        self.spn_timeout.pack(side="left", padx=(2, 0))

        self._w_download_label = _g(ttk.Label(top, text="Папка выгрузки:"),
                                    row=3, column=0, sticky="w", pady=(6, 0))
        self.var_download = tk.StringVar(value=self.cfg.get("download_folder", ""))
        self._w_download = _g(ttk.Entry(top, textvariable=self.var_download),
                              row=3, column=1, sticky="ew", padx=(6, 2), pady=(6, 0))
        self._w_download_btn = _g(ttk.Button(top, text="…", width=3,
                                             command=self.pick_download_folder),
                                  row=3, column=2, pady=(6, 0))

        # --- доп. поля: ветка (combobox) / сообщение / push ----------------- #
        self.var_branch = tk.StringVar(value=self.cfg.get("branch", "main"))
        self._w_branch_label = _g(ttk.Label(top, text="Ветка:"),
                                  row=4, column=0, sticky="w", pady=(6, 0))
        self._w_branch_row = _g(ttk.Frame(top), row=4, column=1, columnspan=2,
                                sticky="ew", padx=(6, 0), pady=(6, 0))
        self.cmb_branch = ttk.Combobox(self._w_branch_row, textvariable=self.var_branch,
                                       values=[], width=16)
        self.cmb_branch.pack(side="left")
        self.btn_branches = ttk.Button(self._w_branch_row, text="Обновить", width=9,
                                       command=self.on_refresh_branches)
        self.btn_branches.pack(side="left", padx=(4, 0))

        self.var_message = tk.StringVar(value=self.cfg.get("commit_message", ""))
        self._w_message_label = _g(ttk.Label(top, text="Сообщение:"),
                                   row=5, column=0, sticky="w", pady=(6, 0))
        self._w_message = _g(ttk.Entry(top, textvariable=self.var_message),
                             row=5, column=1, columnspan=2, sticky="ew",
                             padx=(6, 0), pady=(6, 0))

        self.var_push = tk.BooleanVar(value=bool(self.cfg.get("push")))
        self._w_push_chk = _g(ttk.Checkbutton(top, text="push после коммита",
                                              variable=self.var_push,
                                              command=self._on_settings_change),
                              row=6, column=1, sticky="w", padx=(6, 0), pady=(6, 0))

        top.columnconfigure(1, weight=1)

        # --- большая кнопка КОММИТ ------------------------------------------ #
        btn_frame = ttk.Frame(main)
        btn_frame.pack(fill="both", expand=True, pady=(14, 7))

        self.btn_commit = tk.Button(
            btn_frame,
            text="КОММИТ",
            font=("Segoe UI", 24, "bold"),
            bg="#1f8b4c",
            fg="white",
            activebackground="#17703d",
            activeforeground="white",
            relief="flat",
            cursor="hand2",
            command=self.on_commit,
        )
        self.btn_commit.pack(fill="both", expand=True)

        # --- кнопка ВЫГРУЗИТЬ ИЗ РЕПО + доп. git-действия -------------------- #
        self.btn_download = tk.Button(
            main,
            text="ВЫГРУЗИТЬ ИЗ РЕПО",
            font=("Segoe UI", 12, "bold"),
            bg="#2b6cb0",
            fg="white",
            activebackground="#22558c",
            activeforeground="white",
            relief="flat",
            cursor="hand2",
            command=self.on_download,
        )
        _p(self.btn_download, fill="x", pady=(0, 7))

        tools_row = ttk.Frame(main)
        _p(tools_row, fill="x")
        self._w_tools_git = tools_row
        ttk.Button(tools_row, text="Откатить последний",
                   command=self.on_revert_last).pack(side="left")
        ttk.Button(tools_row, text="Создать тег",
                   command=self.on_create_tag).pack(side="left", padx=(6, 0))

        # --- авто-режимы ------------------------------------------------------ #
        auto_frame = ttk.LabelFrame(main, text="Авто-режимы", padding=8)
        auto_frame.pack(fill="x", pady=(7, 0))

        self.var_auto_commit = tk.BooleanVar(value=bool(self.cfg.get("auto_commit")))
        self.var_auto_clone = tk.BooleanVar(value=bool(self.cfg.get("auto_clone")))

        self.lbl_next_commit = ttk.Label(auto_frame, text="—", width=22)
        self.lbl_next_download = ttk.Label(auto_frame, text="—", width=22)

        ttk.Checkbutton(auto_frame, text="Авто-коммит",
                        variable=self.var_auto_commit,
                        command=lambda: self._toggle_auto("commit"))\
            .grid(row=0, column=0, sticky="w")
        self.lbl_next_commit.grid(row=0, column=1, sticky="w", padx=8)
        ttk.Button(auto_frame, text="Сейчас", width=7,
                   command=lambda: self._run_auto_now("commit"))\
            .grid(row=0, column=2, sticky="e")
        ttk.Label(auto_frame, text="интервал, мин:").grid(row=0, column=3, sticky="e")
        self.var_ci = tk.IntVar(value=self._clamp_interval(
            self.cfg.get("auto_commit_interval_min")
            or self.cfg.get("auto_interval_min", 5)))
        ttk.Spinbox(auto_frame, from_=1, to=60, width=4, textvariable=self.var_ci,
                    command=lambda: self._on_interval_change("commit"))\
            .grid(row=0, column=4, sticky="w", padx=(2, 0))

        ttk.Checkbutton(auto_frame, text="Авто-клон",
                        variable=self.var_auto_clone,
                        command=lambda: self._toggle_auto("download"))\
            .grid(row=1, column=0, sticky="w", pady=(4, 0))
        self.lbl_next_download.grid(row=1, column=1, sticky="w", padx=8, pady=(4, 0))
        ttk.Button(auto_frame, text="Сейчас", width=7,
                   command=lambda: self._run_auto_now("download"))\
            .grid(row=1, column=2, sticky="e", pady=(4, 0))
        ttk.Label(auto_frame, text="интервал, мин:").grid(row=1, column=3,
                                                          sticky="e", pady=(4, 0))
        self.var_cl = tk.IntVar(value=self._clamp_interval(
            self.cfg.get("auto_clone_interval_min")
            or self.cfg.get("auto_interval_min", 5)))
        ttk.Spinbox(auto_frame, from_=1, to=60, width=4, textvariable=self.var_cl,
                    command=lambda: self._on_interval_change("download"))\
            .grid(row=1, column=4, sticky="w", padx=(2, 0), pady=(4, 0))

        # общий интервал (fallback)
        ttk.Label(auto_frame, text="общий интервал, мин:").grid(
            row=2, column=3, sticky="e", pady=(4, 0))
        self.var_ai = tk.IntVar(value=self._clamp_interval(
            self.cfg.get("auto_interval_min", 5)))
        ttk.Spinbox(auto_frame, from_=1, to=60, width=4, textvariable=self.var_ai,
                    command=lambda: self._on_interval_change(None))\
            .grid(row=2, column=4, sticky="w", padx=(2, 0), pady=(4, 0))

        # Пауза авто + Push после авто-коммита + Watcher
        pause_row = ttk.Frame(auto_frame)
        pause_row.grid(row=2, column=0, columnspan=3, sticky="w", pady=(4, 0))
        self.btn_pause = ttk.Button(pause_row, text="Пауза 1 ч", width=10,
                                   command=self.toggle_pause)
        self.btn_pause.pack(side="left")
        self.lbl_pause = ttk.Label(pause_row, text="", width=18)
        self.lbl_pause.pack(side="left", padx=(6, 0))
        self.var_auto_push = tk.BooleanVar(value=bool(self.cfg.get("auto_push")))
        ttk.Checkbutton(pause_row, text="Push после авто-коммита",
                        variable=self.var_auto_push,
                        command=self._on_settings_change)\
            .pack(side="left", padx=(10, 0))

        self.var_watch = tk.BooleanVar(value=bool(self.cfg.get("watch_source")))
        ttk.Checkbutton(auto_frame, text="Реагировать на изменения файлов",
                        variable=self.var_watch,
                        command=self._on_toggle_watch)\
            .grid(row=3, column=0, columnspan=3, sticky="w", pady=(4, 0))

        # Расписание авто-задач
        sched = self.cfg.get("auto_schedule", default_config()["auto_schedule"])
        sched_frame = ttk.LabelFrame(auto_frame, text="Расписание", padding=6)
        sched_frame.grid(row=4, column=0, columnspan=5, sticky="ew", pady=(6, 0))
        self.var_sched = tk.BooleanVar(value=bool(sched.get("enabled")))
        ttk.Checkbutton(sched_frame, text="включено", variable=self.var_sched,
                        command=self._on_settings_change).grid(row=0, column=0,
                                                               sticky="w")
        ttk.Label(sched_frame, text="с").grid(row=0, column=1, sticky="e", padx=(8, 2))
        self.var_sched_from = tk.StringVar(value=str(sched.get("from", "09:00")))
        ttk.Entry(sched_frame, textvariable=self.var_sched_from, width=6)\
            .grid(row=0, column=2)
        ttk.Label(sched_frame, text="до").grid(row=0, column=3, sticky="e", padx=(8, 2))
        self.var_sched_to = tk.StringVar(value=str(sched.get("to", "18:00")))
        ttk.Entry(sched_frame, textvariable=self.var_sched_to, width=6)\
            .grid(row=0, column=4)
        self.day_vars = []
        days = sched.get("days") or [1, 2, 3, 4, 5]
        day_row = ttk.Frame(sched_frame)
        day_row.grid(row=1, column=0, columnspan=5, sticky="w", pady=(4, 0))
        for i, name in enumerate(["Пн", "Вт", "Ср", "Чт", "Пт", "Сб", "Вс"]):
            v = tk.BooleanVar(value=(i + 1) in days)
            self.day_vars.append(v)
            ttk.Checkbutton(day_row, text=name, variable=v,
                            command=self._on_settings_change).grid(row=0, column=i,
                                                                   padx=2)

        auto_frame.columnconfigure(1, weight=1)

        # --- блок чекбоксов безопасности/вида ------------------------------- #
        self._w_checks = _p(ttk.LabelFrame(main, text="Режимы", padding=8),
                            fill="x", pady=(7, 0))
        grid_checks = [
            ("dry_run", "Только показать (dry-run)"),
            ("backup_before_download", "Бэкап целевой папки"),
            ("confirm_delete_extras", "Спрашивать перед удалением лишних"),
            ("sound_on_finish", "Звук после задачи"),
            ("tray_on_close", "В трей при закрытии"),
            ("compact_view", "Компактный вид"),
        ]
        self.var_checks = {}
        for i, (key, label) in enumerate(grid_checks):
            v = tk.BooleanVar(value=bool(self.cfg.get(key)))
            self.var_checks[key] = v
            extra = {"command": lambda: self._apply_compact()} \
                if key == "compact_view" else {"command": self._on_settings_change}
            ttk.Checkbutton(self._w_checks, text=label, variable=v, **extra)\
                .grid(row=i // 2, column=i % 2, sticky="w", padx=6, pady=2)

        # --- нижняя строка: статус + маленькая кнопка "..." (открыть конфиг) #
        bottom = ttk.Frame(main)
        bottom.pack(fill="x", pady=(10, 0))

        self.var_status = tk.StringVar(value="Готов.")
        ttk.Label(bottom, textvariable=self.var_status,
                  foreground="#555").pack(side="left", fill="x", expand=True)

        ttk.Button(bottom, text="…", width=4,
                   command=self.open_config).pack(side="right")

        # лог последних действий
        self.log_box = tk.Text(main, height=7, state="disabled", wrap="word",
                               font=("Consolas", 9))
        _p(self.log_box, fill="x", pady=(10, 0))
        self._w_log = self.log_box

        # контекстные меню на полях ввода (ПКМ)
        self._entry_menu = self._build_entry_menu()
        for w in (self._w_folder, self.var_repo, self._w_download,
                  self.cmb_branch):
            w.bind("<Button-3>", self._show_entry_menu)

        # валидация в реальном времени
        self._setup_validation()

        # WM_DELETE_WINDOW — трей/выход
        root.protocol("WM_DELETE_WINDOW", self._on_close_window)

        # применяем сохранённый компактный вид
        self._apply_compact()

        # единый таймер главного потока (1 раз в секунду)
        self.root.after(1000, self._tick)
        # периодический счётчик изменений (30 с)
        self.root.after(5000, self._maybe_count_changes)

        if self.var_watch.get():
            self._start_watcher()

    # ------------------------------------------------------------------ #
    #  Лог / статус / конфиг                                              #
    # ------------------------------------------------------------------ #

    def log(self, text: str):
        stamp = datetime.now().strftime("%H:%M:%S")
        line = f"[{stamp}] {text}"
        self.log_box.configure(state="normal")
        self.log_box.insert("end", line + "\n")
        self.log_box.see("end")
        self.log_box.configure(state="disabled")
        for part in str(text).splitlines():
            if part.strip():
                log_to_file(part)

    def set_status(self, text: str):
        self.var_status.set(text)

    def _interval_minutes(self, mode: str = None) -> int:
        # Интервалы читаем с диска — ручные правки в config.json
        # подхватываются без перезапуска приложения.
        try:
            disk = load_config()
        except Exception:                                    # noqa: BLE001
            disk = self.cfg
        def _val(key, default):
            try:
                v = int(disk.get(key, default))
            except (TypeError, ValueError):
                v = default
            return v
        if mode == "commit":
            v = _val("auto_commit_interval_min", 0)
            if v > 0:
                return min(v, 60)
        elif mode == "download":
            v = _val("auto_clone_interval_min", 0)
            if v > 0:
                return min(v, 60)
        return max(1, _val("auto_interval_min", 5))

    @staticmethod
    def _clamp_interval(v) -> int:
        try:
            v = int(v)
        except (TypeError, ValueError):
            v = 5
        return min(max(v, 1), 60)

    @staticmethod
    def _clamp_timeout(v) -> int:
        try:
            v = int(v)
        except (TypeError, ValueError):
            v = 30
        return min(max(v, 1), 60)

    def _collect_cfg(self):
        """Сохраняем пользовательские поля обратно в конфиг (атомарно)."""
        self.cfg["source_folder"] = self.var_folder.get().strip()
        self.cfg["repository"] = self.var_repo.get().strip()
        self.cfg["download_folder"] = self.var_download.get().strip()
        self.cfg["branch"] = self.var_branch.get().strip() or "main"
        self.cfg["commit_message"] = self.var_message.get() or "Автокоммит: {datetime}"
        self.cfg["push"] = bool(self.var_push.get())
        self.cfg["auto_commit"] = bool(self.var_auto_commit.get())
        self.cfg["auto_clone"] = bool(self.var_auto_clone.get())
        self.cfg["git_timeout_min"] = self._clamp_timeout(self.var_timeout.get())
        self.cfg["auto_interval_min"] = self._clamp_interval(self.var_ai.get())
        self.cfg["auto_commit_interval_min"] = self._clamp_interval(self.var_ci.get())
        self.cfg["auto_clone_interval_min"] = self._clamp_interval(self.var_cl.get())
        for key, var in self.var_checks.items():
            self.cfg[key] = bool(var.get())
        self.cfg["watch_source"] = bool(self.var_watch.get())
        self.cfg["auto_push"] = bool(self.var_auto_push.get())
        self.cfg["auto_schedule"] = {
            "enabled": bool(self.var_sched.get()),
            "from": self.var_sched_from.get().strip() or "09:00",
            "to": self.var_sched_to.get().strip() or "18:00",
            "days": [i + 1 for i, v in enumerate(self.day_vars) if v.get()],
        }
        save_config(self.cfg)

    def _on_settings_change(self):
        try:
            self._collect_cfg()
        except Exception as exc:                             # noqa: BLE001
            self.log(f"Не удалось сохранить настройки: {exc}")

    def pick_folder(self):
        folder = filedialog.askdirectory(title="Папка, откуда коммитим",
                                         initialdir=self.var_folder.get() or ".")
        if folder:
            self.var_folder.set(folder)
            self._collect_cfg()

    def pick_download_folder(self):
        folder = filedialog.askdirectory(title="Папка выгрузки из репо",
                                         initialdir=self.var_download.get()
                                         or self.var_folder.get() or ".")
        if folder:
            self.var_download.set(folder)
            self._collect_cfg()

    def paste_repo_url(self):
        """Кнопка «…» у поля репозитория — вставить ссылку из буфера обмена."""
        try:
            clip = self.root.clipboard_get().strip()
        except tk.TclError:
            clip = ""
        if clip and is_repo_url(clip.splitlines()[0]):
            self.var_repo.set(clip.splitlines()[0])
            self._collect_cfg()
            self.set_status("Ссылка вставлена из буфера обмена")
        else:
            messagebox.showinfo(
                APP_TITLE,
                "В буфере обмена нет ссылки на репозиторий.\n\n"
                "Скопируйте ссылку (например https://github.com/user/repo.git)\n"
                "и нажмите «…» ещё раз — либо вставьте её в поле вручную (Ctrl+V).")

    def open_config(self):
        """Маленькая кнопка с троеточием внизу — открыть файл конфига."""
        self._collect_cfg()
        path = config_path()
        if not path.exists():
            save_config(self.cfg)
        open_config_in_editor(path)
        self.set_status(f"Конфиг открыт: {path.name}")

    # ------------------------------------------------------------------ #
    #  Валидация в реальном времени (38)                                  #
    # ------------------------------------------------------------------ #

    def _setup_validation(self):
        self._tt = {}
        for kind, widget in (("folder", self._w_folder),
                             ("repo", self.var_repo),
                             ("download", self._w_download)):
            var = {"folder": self.var_folder, "repo": self.var_repo.var,
                   "download": self.var_download}[kind]
            var.trace_add("write", lambda *_a, k=kind: self._validate_field(k))
            widget.bind("<FocusOut>", lambda *_a, k=kind: self._validate_field(k))
            self._tt[kind] = ToolTip(widget)
            self._validate_field(kind)

    def _field_value(self, kind):
        if kind == "folder":
            return self.var_folder.get().strip()
        if kind == "repo":
            return self.var_repo.get().strip()
        if kind == "download":
            return self.var_download.get().strip()
        return ""

    def _field_widget(self, kind):
        if kind == "folder":
            return self._w_folder
        if kind == "repo":
            return self.var_repo
        return self._w_download

    def _validate_field(self, kind):
        """Красная рамка + тултип, если значение некорректно."""
        value = self._field_value(kind)
        widget = self._field_widget(kind)
        tip = self._tt.get(kind)
        reason = ""
        if kind in ("folder", "download"):
            if value and not Path(value).expanduser().is_dir():
                reason = "Папка не существует"
        elif kind == "repo":
            if value and not is_repo_url(value):
                reason = "Не похоже на ссылку git-репозитория"
        try:
            if kind == "repo":
                widget.configure(
                    foreground="#c62828" if reason else
                    (PlaceholderEntry.GRAY if widget._showing_ph
                     else PlaceholderEntry.BLACK))
            else:
                widget.configure(
                    foreground="#c62828" if reason else PlaceholderEntry.BLACK)
        except tk.TclError:
            pass
        if tip:
            tip.set(reason)
        return not reason

    # ------------------------------------------------------------------ #
    #  Компактный вид (35)                                                #
    # ------------------------------------------------------------------ #

    def _apply_compact(self):
        """Мини-режим: скрывает «Папку выгрузки», «Сообщение», «Ветку», лог.

        Остаются: Папка, Репо, КОММИТ, ВЫГРУЗИТЬ, авто-блок.
        Спецификации раскладки сохранены в self._layout_spec — при возврате
        к обычному виду виджеты восстанавливаются на свои места.
        """
        compact = bool(self.var_checks["compact_view"].get())
        hidden_attrs = ("_w_download_label", "_w_download", "_w_download_btn",
                        "_w_message_label", "_w_message",
                        "_w_branch_label", "_w_branch_row",
                        "_w_log")
        for attr in hidden_attrs:
            w = getattr(self, attr, None)
            if w is None:
                continue
            spec = self._layout_spec.get(w)
            manager = str(w.winfo_manager())
            if compact:
                if manager:                      # виджет сейчас отображён
                    w.grid_forget() if manager == "grid" else w.pack_forget()
            elif not manager and spec:           # был скрыт — вернуть
                kind, kw = spec
                if kind == "grid":
                    w.grid(**kw)
                else:
                    w.pack(**kw)
        try:
            self._collect_cfg()
        except Exception:                                        # noqa: BLE001
            pass

    # ------------------------------------------------------------------ #
    #  Контекстное меню полей (36)                                        #
    # ------------------------------------------------------------------ #

    def _build_entry_menu(self):
        menu = tk.Menu(self.root, tearoff=0)
        menu.add_command(label="Вставить", command=self._ctx_paste)
        menu.add_command(label="Копировать путь", command=self._ctx_copy)
        menu.add_command(label="Открыть в проводнике", command=self._ctx_open)
        menu.add_command(label="Очистить", command=self._ctx_clear)
        return menu

    def _show_entry_menu(self, event):
        w = event.widget
        try:
            if isinstance(w, PlaceholderEntry):
                self._ctx_target = w
            else:
                self._ctx_target = w
            self._entry_menu.tk_popup(event.x_root, event.y_root)
        finally:
            self._entry_menu.grab_release()

    def _ctx_get(self):
        return self._ctx_target.get()

    def _ctx_set(self, value):
        self._ctx_target.set(value)
        self._on_settings_change()

    def _ctx_paste(self):
        try:
            text = self.root.clipboard_get()
        except tk.TclError:
            return
        cur = self._ctx_get()
        self._ctx_set(cur + text.strip())

    def _ctx_copy(self):
        text = self._ctx_get()
        if text:
            self.root.clipboard_clear()
            self.root.clipboard_append(text)
            self.set_status("Скопировано в буфер обмена")

    def _ctx_open(self):
        path = self._ctx_get()
        if not path:
            return
        p = Path(path)
        target = p if p.is_dir() else p.parent
        if not target.exists():
            self.set_status("Папка не существует")
            return
        try:
            if sys.platform.startswith("win"):
                os.startfile(str(target))                    # type: ignore
            elif sys.platform == "darwin":
                subprocess.Popen(["open", str(target)])
            else:
                subprocess.Popen(["xdg-open", str(target)])
        except Exception as exc:                             # noqa: BLE001
            self.log(f"Не удалось открыть папку: {exc}")

    def _ctx_clear(self):
        self._ctx_set("")

    # ------------------------------------------------------------------ #
    #  Фоновые задачи (queue.Queue вместо разделяемых флагов-списков)     #
    # ------------------------------------------------------------------ #

    def _start_bg(self, kind: str, fn, *args) -> bool:
        """Запускает git-задачу в фоновом потоке. False, если уже занято."""
        if self.busy:
            return False
        # Фоновые задачи (кроме интерактивных commit/download) выполняются
        # молча: не трогают кнопки и статус, чтобы не мешать авто-режимам.
        quiet = kind in ("count", "branches", "test-conn")
        if not quiet:
            self._set_busy_status("Выполняется задача…")
        self.busy = True
        self.current_task = kind
        cfg_snapshot = dict(self.cfg)      # не делим мутабельный dict с потоком
        # история пишется read-modify-write поверх файла, поэтому снимок
        # дополнительно подтягивает актуальные значения ключей с диска —
        # иначе рабочий поток затёр бы свежие настройки GUI.
        try:
            disk_cfg = load_config()
        except Exception:                                   # noqa: BLE001
            disk_cfg = {}
        for key in default_config():
            if key == "history":
                continue
            if key in disk_cfg:
                cfg_snapshot[key] = disk_cfg[key]
        # Лог-колбэк для фоновой задачи: пишет в очередь, GUI печатает в главном потоке.
        log = lambda msg: self.msg_queue.put(("log", msg))     # noqa: E731
        threading.Thread(target=self._bg_worker,
                         args=(fn, cfg_snapshot, log, *args), daemon=True).start()
        self._poll_results()
        return True

    def _bg_worker(self, fn, cfg: dict, log, *args):
        """Работает в фоновом потоке; в GUI пишет только через queue.Queue."""
        try:
            result = fn(cfg, log, *args)
            self.msg_queue.put(("done", result))
        except GitError as exc:
            self.msg_queue.put(("error", str(exc)))
        except Exception as exc:                               # noqa: BLE001
            # Полный traceback — в лог, краткая ошибка — в статус.
            self.msg_queue.put(("log", traceback.format_exc()))
            self.msg_queue.put(("error", f"Ошибка: {exc}"))

    def _poll_results(self):
        """Выбирает сообщения из очереди и печатает их в главном потоке Tk."""
        finished = None  # ("done"|"error", text)
        while True:
            try:
                kind, text = self.msg_queue.get_nowait()
            except queue.Empty:
                break
            if kind == "log":
                self.log(text)
            elif kind == "watch":
                self._handle_watch()           # watcher обслуживается и здесь
            elif kind in ("done", "error"):
                finished = (kind, text)
                break
            elif kind == "branches":
                self._apply_branch_list(text)
                continue
        if finished is not None:
            kind, text = finished
            interactive = self.current_task in ("commit", "download",
                                                "test-conn", "branches",
                                                "revert", "tag")
            self._finish(kind, text, interactive=interactive)
            # Дочитываем оставшиеся сообщения (например log-и, пришедшие
            # в ту же порцию, что и done/error) — иначе они зависнут до
            # следующей задачи.
            self.root.after(0, self._poll_results)
        elif self.busy:
            self.root.after(100, self._poll_results)

    def _finish(self, kind: str, text, interactive: bool):
        task = self.current_task
        self.busy = False
        self.current_task = None
        self._refresh_buttons()
        if kind == "error":
            if task == "count":                 # фоновый счётчик — молча
                return
            self.set_status(f"Ошибка: {task or 'задача'}")
            self.log(str(text))
            if interactive and task in ("commit", "download", "revert", "tag",
                                        "test-conn"):
                messagebox.showerror(APP_TITLE, str(text))
        else:
            if task == "commit":
                if isinstance(text, str) and text.startswith("РЕЖИМ DRY-RUN"):
                    self.set_status("Dry-run: план готов (диск не тронут)")
                    messagebox.showinfo(APP_TITLE + " — dry-run", text)
                elif text:
                    msg = f"Готово: коммит {text}"
                    self.set_status(msg)
                    self.log(msg)
                else:
                    msg = "Готово: изменений нет."
                    self.set_status(msg)
                    self.log(msg)
            elif task == "download":
                if isinstance(text, str) and text.startswith("РЕЖИМ DRY-RUN"):
                    self.set_status("Dry-run: план готов (диск не тронут)")
                    messagebox.showinfo(APP_TITLE + " — dry-run", text)
                else:
                    msg = f"Готово: выгружено ({text})" if text else "Выгрузка пропущена."
                    self.set_status(msg)
                    self.log(msg)
            elif task == "branches":
                self._apply_branch_list(text)
            elif task == "test-conn":
                self.set_status("Связь с репозиторием OK")
                self.log(f"Тест соединения: OK — {text}")
            elif task == "count":
                self._apply_change_count(text)  # счётчик на кнопке — без статуса
            elif task in ("revert", "tag"):
                msg = f"Готово: {text}" if text else "Готово."
                self.set_status(msg)
                self.log(msg)
            elif task in ("auto-commit", "auto-download"):
                msg = f"Готово: {text}" if text else "Готово."
                self.log(f"{self.AUTO_LABELS['commit' if task == 'auto-commit' else 'download']}: {msg}")
            else:
                msg = f"Готово: {text}" if text else "Готово."
                self.set_status(msg)
                self.log(msg)
            if task in ("commit", "download", "revert", "auto-commit",
                        "auto-download"):
                self._count_dirty = True
                if self.cfg.get("sound_on_finish"):
                    play_beep()

    def _refresh_buttons(self):
        state = "normal" if not self.busy else "disabled"
        self.btn_commit.configure(
            state=state,
            bg="#1f8b4c" if not self.busy else "#9e9e9e",
            fg="white")
        self.btn_download.configure(
            state=state,
            bg="#2b6cb0" if not self.busy else "#9e9e9e",
            fg="white")
        for b in (getattr(self, "btn_test_conn", None),
                  getattr(self, "btn_branches", None)):
            if b is not None:
                b.configure(state=state)

    # ------------------------------------------------------------------ #
    #  Прямые процессы                                                     #
    # ------------------------------------------------------------------ #

    def on_commit(self):
        if self.busy:
            return
        self._collect_cfg()
        if not self.cfg.get("repository"):
            messagebox.showinfo(
                APP_TITLE,
                "Вставьте ссылку на репозиторий (поле «Ссылка репо» или кнопка «…» — из буфера)\n"
                "и папку-источник, затем нажмите КОММИТ.\n\n"
                "Кнопка «…» справа внизу открывает файл config.json.")
            return
        # dry-run ничего не пишет — можно запускать даже когда он «занят»
        self._start_bg("commit", commit_all)

    def on_download(self):
        if self.busy:
            return
        self._collect_cfg()
        if not self.cfg.get("repository"):
            messagebox.showinfo(
                APP_TITLE,
                "Укажите ссылку на репозиторий (поле «Ссылка репо» или кнопка «…» — из буфера), "
                "затем нажмите «ВЫГРУЗИТЬ ИЗ РЕПО».")
            return
        if not (self.cfg.get("download_folder") or self.cfg.get("source_folder")):
            messagebox.showinfo(
                APP_TITLE,
                "Укажите «Папку выгрузки» (или «Папку») — куда выложить содержимое репозитория.")
            return
        # Подтверждение нужно только если в целевой папке есть файлы, которых
        # нет в репозитории (их придётся удалить) И стоит флаг confirm_delete_extras.
        target = str(self.cfg.get("download_folder") or "").strip() \
            or str(self.cfg.get("source_folder") or "").strip()
        extras = 0
        try:
            tp = Path(target)
            if tp.is_dir():
                extras = sum(1 for p in tp.iterdir()
                             if p.name not in SYNC_IGNORE)
        except OSError:
            pass
        if extras and self.cfg.get("confirm_delete_extras", True) \
                and not messagebox.askyesno(
                APP_TITLE,
                f"В целевой папке {extras} объектов, которых нет в репозитории — "
                "они будут удалены.\nФайлы репозитория будут выгружены поверх.\n\n"
                "Продолжить?"):
            self.log("Выгрузка отменена пользователем.")
            return
        self._set_busy_status("Выгружаем из репо…")
        # confirm=None: решение уже принято выше; лишнее чистим безусловно.
        self._start_bg("download", download_from_repo, None)

    def _set_busy_status(self, text: str):
        # Только статус/кнопки; флаг self.busy ставит _start_bg.
        self.set_status(text)
        self._refresh_buttons()

    # ------------------------------------------------------------------ #
    #  Тест соединения (19) / список веток (4)                            #
    # ------------------------------------------------------------------ #

    def on_test_connection(self):
        if self.busy:
            return
        self._collect_cfg()
        repo = self.cfg.get("repository", "").strip()
        if not is_repo_url(repo):
            messagebox.showinfo(APP_TITLE,
                                "Сначала укажите корректную ссылку на репозиторий.")
            return
        self._set_busy_status("Проверяю соединение с репозиторием…")
        timeout_s = min(net_timeout(self.cfg), 30)

        def _test(cfg, log):
            out = run_git(["ls-remote", "--heads", repo], timeout=timeout_s)
            branches = [ln.split("refs/heads/")[-1]
                        for ln in out.splitlines() if "refs/heads/" in ln]
            return (f"{len(branches)} веток: "
                    + ", ".join(branches[:10]) if branches else "репозиторий доступен (веток пока нет)")
        self._start_bg("test-conn", _test)

    def on_refresh_branches(self):
        if self.busy:
            return
        self._collect_cfg()
        if not is_repo_url(self.cfg.get("repository", "").strip()):
            messagebox.showinfo(APP_TITLE,
                                "Сначала укажите корректную ссылку на репозиторий.")
            return
        self._set_busy_status("Читаю список веток…")

        def _branches(cfg, log):
            workdir = ensure_repo_layout(cfg, need_source=False)
            out = run_git(["branch", "-r"], cwd=workdir)
            names = []
            for line in out.splitlines():
                name = line.strip()
                if "->" in name or not name:
                    continue
                name = name.split("/", 1)[-1] if name.startswith("origin/") else name
                if name not in names:
                    names.append(name)
            return names
        self._start_bg("branches", _branches)

    def _apply_branch_list(self, names):
        try:
            current = self.var_branch.get()
            values = list(names)
            if current and current not in values:
                values.insert(0, current)
            self.cmb_branch.configure(values=values)
            self.log(f"Ветки: {', '.join(values) if values else 'нет'}")
            self.set_status(f"Список веток обновлён ({len(values)})")
        except Exception as exc:                             # noqa: BLE001
            self.log(f"Не удалось применить список веток: {exc}")

    # ------------------------------------------------------------------ #
    #  Откат последнего коммита (41) / теги (42)                          #
    # ------------------------------------------------------------------ #

    def on_revert_last(self):
        if self.busy:
            return
        self._collect_cfg()
        if not is_repo_url(self.cfg.get("repository", "").strip()):
            messagebox.showinfo(APP_TITLE, "Сначала укажите ссылку на репозиторий.")
            return
        choice = messagebox.askyesnocancel(
            APP_TITLE,
            "Откатить ПОСЛЕДНИЙ локальный коммит?\n\n"
            "«Да»   — SOFT: коммит откатывается, изменения остаются в рабочей копии.\n"
            "«Нет»  — HARD: коммит и изменения удаляются безвозвратно.\n"
            "«Отмена» — ничего не делать.\n\n"
            "(Откат возможен только для незапушенного коммита.)")
        if choice is None:
            return
        mode = "soft" if choice else "hard"

        def _revert(cfg, log):
            workdir = ensure_repo_layout(cfg, need_source=False)
            branch = cfg.get("branch", "main") or "main"
            try:
                ahead = int(run_git(["rev-list", "--count",
                                     f"origin/{branch}..HEAD"], cwd=workdir) or "0")
            except GitError:
                ahead = 1  # remote-ветки нет — коммит точно локальный
            if ahead < 1:
                raise GitError("Коммит уже запушен в origin — откат запрещён. "
                               "Используйте git revert вручную.")
            last = run_git(["log", "-1", "--pretty=%h %s"], cwd=workdir)
            run_git(["reset", f"--{mode}", "HEAD~1"], cwd=workdir)
            return f"Откат {mode}: убрали коммит «{last}»"
        self._set_busy_status(f"Откатываю последний коммит ({mode})…")
        self._start_bg("revert", _revert)

    def on_create_tag(self):
        if self.busy:
            return
        self._collect_cfg()
        if not is_repo_url(self.cfg.get("repository", "").strip()):
            messagebox.showinfo(APP_TITLE, "Сначала укажите ссылку на репозиторий.")
            return
        dlg = self._tag_dialog()
        if dlg is None:
            return
        name, annotation, push_tag = dlg

        def _tag(cfg, log):
            workdir = ensure_repo_layout(cfg, need_source=False)
            args = ["tag", "-a", name]
            if annotation:
                args += ["-m", annotation]
            else:
                args += ["-m", name]
            run_git(args, cwd=workdir)
            result = f"Тег {name} создан"
            if push_tag:
                try:
                    run_git(["push", "origin", name], cwd=workdir,
                            timeout=net_timeout(cfg))
                    result += ", запушен в origin"
                except GitError as exc:
                    result += f"; ВНИМАНИЕ: push тега не выполнен: {exc}"
            return result
        self._set_busy_status(f"Создаю тег {name}…")
        self._start_bg("tag", _tag)

    def _tag_dialog(self):
        """Модальное окно: имя, аннотация, чекбокс push тега."""
        win = tk.Toplevel(self.root)
        win.title("Создать тег")
        win.transient(self.root)
        win.grab_set()
        win.resizable(False, False)
        result = {}
        frm = ttk.Frame(win, padding=12)
        frm.pack(fill="both", expand=True)
        ttk.Label(frm, text="Имя тега:").grid(row=0, column=0, sticky="w")
        var_name = tk.StringVar(value=f"v{__version__}")
        ttk.Entry(frm, textvariable=var_name, width=32).grid(row=0, column=1,
                                                             sticky="ew", padx=(6, 0))
        ttk.Label(frm, text="Аннотация:").grid(row=1, column=0, sticky="w",
                                               pady=(6, 0))
        var_msg = tk.StringVar(value="")
        ttk.Entry(frm, textvariable=var_msg, width=32).grid(row=1, column=1,
                                                            sticky="ew",
                                                            padx=(6, 0), pady=(6, 0))
        var_push = tk.BooleanVar(value=True)
        ttk.Checkbutton(frm, text="push тега в origin", variable=var_push)\
            .grid(row=2, column=1, sticky="w", pady=(6, 0))

        def ok(_e=None):
            name = var_name.get().strip()
            if not name or not re.match(r"^[\w][\w./-]*$", name):
                messagebox.showwarning(APP_TITLE, "Некорректное имя тега.",
                                       parent=win)
                return
            result["value"] = (name, var_msg.get().strip(), bool(var_push.get()))
            win.destroy()

        def cancel(_e=None):
            result["value"] = None
            win.destroy()

        btns = ttk.Frame(frm)
        btns.grid(row=3, column=0, columnspan=2, sticky="e", pady=(10, 0))
        ttk.Button(btns, text="Создать", command=ok).pack(side="right", padx=(4, 0))
        ttk.Button(btns, text="Отмена", command=cancel).pack(side="right")
        win.bind("<Return>", ok)
        win.bind("<Escape>", cancel)
        self.root.wait_window(win)
        return result.get("value")

    # ------------------------------------------------------------------ #
    #  Счётчик изменений на кнопке (8)                                    #
    # ------------------------------------------------------------------ #

    def _maybe_count_changes(self):
        """Периодически (раз в ~30 с) считает git status --porcelain в фоне."""
        try:
            if (self._count_dirty and not self.busy
                    and is_repo_url(self.cfg.get("repository", "").strip())):
                self._count_dirty = False
                self._start_bg("count", self._count_worker)
        finally:
            self.root.after(30000, self._maybe_count_changes)

    @staticmethod
    def _count_worker(cfg, log):
        repo = str(cfg.get("repository", "") or "").strip()
        local = local_clone_dir(repo)
        if not (local / ".git").is_dir():
            return 0
        try:
            out = run_git(["status", "--porcelain"], cwd=local)
        except GitError:
            return 0
        return len([ln for ln in out.splitlines() if ln.strip()])

    def _apply_change_count(self, n):
        try:
            n = int(n)
        except (TypeError, ValueError):
            n = 0
        self.change_count = n
        base = "КОММИТ"
        text = f"{base} ({n})" if n > 0 else base
        if self.var_checks["dry_run"].get():
            text = "DRY-RUN" + text[len(base):]
        self.btn_commit.configure(text=text)

    # ------------------------------------------------------------------ #
    #  Авто-режимы                                                         #
    # ------------------------------------------------------------------ #

    AUTO_LABELS = {"commit": "Авто-коммит", "download": "Авто-клон"}

    def _toggle_auto(self, mode: str):
        """Чекбокс включён — планируем (НЕ запускаем сразу); выключен — сброс."""
        var = self.var_auto_commit if mode == "commit" else self.var_auto_clone
        enabled = bool(var.get())
        self.auto_enabled[mode] = enabled
        if enabled:
            self._schedule_auto(mode, now=datetime.now())
            self.log(f"{self.AUTO_LABELS[mode]}: включён, "
                     f"интервал {self._interval_minutes(mode)} мин.")
        else:
            self.next_run_at[mode] = None
            lbl = (self.lbl_next_commit if mode == "commit"
                   else self.lbl_next_download)
            lbl.configure(text="—")
            self.log(f"{self.AUTO_LABELS[mode]}: выключен.")
        try:
            self._collect_cfg()
        except Exception as exc:                               # noqa: BLE001
            self.log(f"Не удалось сохранить настройки: {exc}")

    def _on_interval_change(self, mode):
        """Спинбоксы интервалов: общий и индивидуальные (26/27)."""
        try:
            self._collect_cfg()
        except Exception as exc:                               # noqa: BLE001
            self.log(f"Не удалось сохранить настройки: {exc}")
            return
        for m in (("commit", "download") if mode is None else (mode,)):
            if self.auto_enabled[m]:
                self._schedule_auto(m, now=datetime.now(), enable=False)
        self.log(f"Интервалы: общий {self.var_ai.get()} мин, "
                 f"коммит {self.var_ci.get()}, клон {self.var_cl.get()}.")

    def _schedule_auto(self, mode: str, now: datetime, enable: bool = True):
        """Планирует следующий запуск; enable=False — только сдвиг таймера
        (кнопка «Сейчас» при снятом чекбоксе НЕ включает авто-режим)."""
        if enable:
            self.auto_enabled[mode] = True
        self.next_run_at[mode] = now + timedelta(
            minutes=self._interval_minutes(mode))

    def _run_auto_now(self, mode: str):
        """Кнопка «Сейчас» — немедленный запуск в фоне + перепланировка."""
        now = datetime.now()
        if self.busy:
            self.log(f"{self.AUTO_LABELS[mode]}: пропуск — другая задача выполняется.")
            if self.auto_enabled[mode]:
                self._schedule_auto(mode, now=now, enable=False)   # сдвигаем
            return
        self._collect_cfg()
        if not self._auto_can_run(mode):
            self.log(f"{self.AUTO_LABELS[mode]}: пропуск — нет ссылки на репо или папки.")
            if self.auto_enabled[mode]:
                self._schedule_auto(mode, now=now, enable=False)
            return
        # «Сейчас» НЕ включает авто-режим: перепланируем таймер только если
        # он уже включён чекбоксом (enable=False при выключенном).
        self._schedule_auto(mode, now=now, enable=self.auto_enabled[mode])
        if mode == "commit":
            self.set_status("Авто-коммит: выполняем…")
            self._start_bg("auto-commit", commit_all, True)
        else:
            self.set_status("Авто-клон: выполняем…")
            self._start_bg("auto-download", download_from_repo, None)

    def _auto_can_run(self, mode: str) -> bool:
        cfg = self.cfg
        if not str(cfg.get("repository", "") or "").strip():
            return False
        if mode == "commit":
            src = str(cfg.get("source_folder", "") or "").strip()
            return bool(src) and Path(src).is_dir()
        # download (авто-клон): опасный дефолт — выгружать можно ТОЛЬКО в
        # явно заданный download_folder. source_folder (дефолт — домашняя
        # папка) как цель авто-клона не используется.
        target = str(cfg.get("download_folder", "") or "").strip()
        return bool(target)

    # ---- расписание (28) ---------------------------------------------- #

    @staticmethod
    def _parse_hm(text, default):
        m = re.match(r"^(\d{1,2}):(\d{2})$", str(text).strip())
        if not m:
            return default
        hh, mm = int(m.group(1)), int(m.group(2))
        if 0 <= hh <= 23 and 0 <= mm <= 59:
            return hh * 60 + mm
        return default

    def _in_schedule(self, now: datetime) -> bool:
        sched = self.cfg.get("auto_schedule") or {}
        if not sched.get("enabled"):
            return True
        days = sched.get("days")
        if days is not None and now.isoweekday() not in days:
            return False
        frm = self._parse_hm(sched.get("from"), 9 * 60)
        to = self._parse_hm(sched.get("to"), 18 * 60)
        cur = now.hour * 60 + now.minute
        return frm <= cur <= to if frm <= to else (cur >= frm or cur <= to)

    # ---- пауза (30) ---------------------------------------------------- #

    def toggle_pause(self):
        if self.paused_until and self.paused_until > datetime.now():
            self.paused_until = None
            self.log("Пауза авто-режимов снята.")
        else:
            self.paused_until = datetime.now() + timedelta(hours=1)
            self.log(f"Авто-режимы на паузе до "
                     f"{self.paused_until.strftime('%H:%M')}.")
        self._update_pause_button()

    def _update_pause_button(self):
        active = bool(self.paused_until and self.paused_until > datetime.now())
        try:
            self.btn_pause.configure(text="Снять паузу" if active else "Пауза 1 ч")
        except tk.TclError:
            pass

    # ---- watcher файлов (29) -------------------------------------------- #

    def _on_toggle_watch(self):
        if self.var_watch.get():
            try:
                import watchdog  # noqa: F401
            except ImportError:
                self.var_watch.set(False)
                messagebox.showinfo(
                    APP_TITLE,
                    "Для watcher'а нужна библиотека watchdog:\n\n"
                    "    pip install watchdog")
                return
            self._start_watcher()
        else:
            self._stop_watcher()
        self._on_settings_change()

    def _start_watcher(self):
        self._stop_watcher()
        self._watch_stop = threading.Event()
        stop = self._watch_stop

        def _thread():
            try:
                from watchdog.observers import Observer
                from watchdog.events import FileSystemEventHandler

                class Handler(FileSystemEventHandler):
                    def __init__(self, cb):
                        self.cb = cb

                    def on_any_event(self, event):
                        if event.is_directory:
                            return
                        parts = set(str(event.src_path).split(os.sep))
                        if parts & SYNC_IGNORE:
                            return
                        self.cb()

                obs = Observer()
                src = str(self.cfg.get("source_folder", "") or "").strip()
                if not src or not Path(src).is_dir():
                    return
                obs.schedule(Handler(self._on_watch_event), src, recursive=True)
                obs.daemon = True
                obs.start()
                while not stop.is_set():
                    stop.wait(1)
                obs.stop()
                obs.join(timeout=5)
            except Exception as exc:                         # noqa: BLE001
                self.msg_queue.put(("log", f"Watcher остановлен: {exc}"))
        self._watch_thread = threading.Thread(target=_thread, daemon=True)
        self._watch_thread.start()
        self.log("Watcher за файлами папки запущен (дебаунс 30 с).")

    def _stop_watcher(self):
        if self._watch_stop is not None:
            self._watch_stop.set()
            self._watch_stop = None
        self._watch_thread = None

    def _on_watch_event(self):
        # Из фонового потока observer'а — только в очередь GUI.
        self.msg_queue.put(("watch", None))

    def _handle_watch(self):
        """Событие watcher'а: старт дебаунс-окна (30 с тишины).

        Watcher приоритетнее таймера: из-за активности файлов таймер
        авто-коммита постоянно сдвигается, а коммит выполняется после
        30 секунд тишины (_tick_inner -> _fire_watch_commit).
        """
        self._last_watch_event = datetime.now().timestamp()
        if self.auto_enabled["commit"]:
            # сдвигаем плановый запуск таймера — приоритет у watcher'а
            self._schedule_auto("commit", now=datetime.now(), enable=False)

    def _fire_watch_commit(self):
        """Дебаунс-окно закрыто (30 с без изменений) — авто-коммит."""
        if self.busy or not self.var_watch.get():
            return
        self._collect_cfg()
        if not self._auto_can_run("commit"):
            return
        if not self._in_schedule(datetime.now()):
            return
        self.log("Watcher: изменения файлов (30 с тишины) — авто-коммит.")
        self._schedule_auto("commit", now=datetime.now(),
                            enable=self.auto_enabled["commit"])
        self.set_status("Watcher: авто-коммит…")
        self._start_bg("auto-commit", commit_all, True)

    # ---- основной тик --------------------------------------------------- #

    def _tick(self):
        """Единый таймер главного потока: 1 раз в секунду."""
        try:
            self._drain_events()
            self._tick_inner()
        finally:
            self.root.after(1000, self._tick)

    def _drain_events(self):
        """Выборка неблокирующих событий из очереди (watch и др.)."""
        pending_logs = []
        while True:
            try:
                kind, payload = self.msg_queue.get_nowait()
            except queue.Empty:
                break
            if kind == "watch":
                self._handle_watch()
            elif kind == "log":
                pending_logs.append(payload)
            else:  # done/error — вернуть в очередь, обработает _poll_results
                self.msg_queue.put((kind, payload))
                break
        for text in pending_logs:
            self.log(text)

    def _tick_inner(self):
        now = datetime.now()

        # дебаунс watcher'а: 30 с тишины -> авто-коммит
        if (self.var_watch.get() and self._last_watch_event
                and now.timestamp() - self._last_watch_event >= 30):
            self._last_watch_event = 0.0
            self._fire_watch_commit()

        # пауза (30)
        paused = bool(self.paused_until and now < self.paused_until)
        self._update_pause_button()
        if paused:
            self.lbl_pause.configure(
                text=f"пауза до {self.paused_until.strftime('%H:%M')}")
        elif self._pause_lbl_shown:
            self.lbl_pause.configure(text="")
        self._pause_lbl_shown = paused

        # индикаторы «следующий через MM:SS» / «вне расписания»
        in_sched = self._in_schedule(now)
        for mode, lbl in (("commit", self.lbl_next_commit),
                          ("download", self.lbl_next_download)):
            nxt = self.next_run_at.get(mode)
            if paused:
                lbl.configure(text="пауза")
            elif not self.auto_enabled[mode] or not nxt:
                lbl.configure(text="—")
            elif not in_sched:
                lbl.configure(text="вне расписания")
            else:
                secs = max(0, int((nxt - now).total_seconds()))
                lbl.configure(text=f"следующий через {secs // 60:02d}:{secs % 60:02d}")

        if paused or not in_sched:
            return

        due = [m for m in ("download", "commit")   # приоритет: авто-клон первый
               if self.auto_enabled[m] and self.next_run_at.get(m)
               and now >= self.next_run_at[m]]
        for mode in due:
            if self.busy:
                # задача идёт — пропускаем и сдвигаем запуск
                self._schedule_auto(mode, now=now, enable=False)
                self.log(f"{self.AUTO_LABELS[mode]}: пропуск (занято), сдвиг таймера.")
                continue
            self._collect_cfg()
            if not self._auto_can_run(mode):
                self.log(f"{self.AUTO_LABELS[mode]}: пропуск — нет ссылки на репо или папки.")
                self._schedule_auto(mode, now=now, enable=False)
                continue
            self._schedule_auto(mode, now=now, enable=False)
            if mode == "commit":
                self.set_status("Авто-коммит: выполняем…")
                self._start_bg("auto-commit", commit_all, True)
            else:
                self.set_status("Авто-клон: выполняем…")
                self._start_bg("auto-download", download_from_repo, None)
            break  # один запуск за тик; второй авто — следующим тиком/по плану

    # ------------------------------------------------------------------ #
    #  Трейд-менеджер окна / трей (34)                                    #
    # ------------------------------------------------------------------ #

    def _on_close_window(self):
        if self.var_checks["tray_on_close"].get():
            if self._ensure_tray():
                self.root.withdraw()
                self.log("Приложение свёрнуто в трей (клик по иконке — развернуть).")
                return
        self._quit_app()

    def _ensure_tray(self) -> bool:
        """Ленивый запуск pystray; False, если библиотека недоступна."""
        if self._tray_icon is not None:
            return True
        try:
            import pystray
            from PIL import Image, ImageDraw
        except ImportError:
            messagebox.showinfo(
                APP_TITLE,
                "Для работы в трее нужны библиотеки pystray и Pillow:\n\n"
                "    pip install pystray Pillow\n\n"
                "Приложение будет закрыто обычным способом.")
            self.var_checks["tray_on_close"].set(False)
            return False
        try:
            img = Image.new("RGB", (64, 64), "#1f8b4c")
            d = ImageDraw.Draw(img)
            d.rectangle((14, 14, 50, 50), outline="white", width=6)
            icon = pystray.Icon("git_committer", img, APP_TITLE,
                                menu=pystray.Menu(
                                    pystray.MenuItem("Показать окно",
                                                     self._tray_show, default=True),
                                    pystray.MenuItem("Выход",
                                                     self._tray_quit)))
            threading.Thread(target=icon.run, daemon=True).start()
            self._tray_icon = icon
            return True
        except Exception as exc:                             # noqa: BLE001
            self.log(f"Не удалось запустить трей: {exc}")
            return False

    def _tray_show(self, icon=None, item=None):
        def _do():
            self.root.deiconify()
            self.root.lift()
            if icon is not None:
                try:
                    icon.stop()
                except Exception:                            # noqa: BLE001
                    pass
                self._tray_icon = None
        self.root.after(0, _do)

    def _tray_quit(self, icon=None, item=None):
        self.root.after(0, self._quit_app)

    def _quit_app(self):
        self._force_quit = True
        if self._tray_icon is not None:
            try:
                self._tray_icon.stop()
            except Exception:                                # noqa: BLE001
                pass
        self._stop_watcher()
        try:
            self._collect_cfg()
        except Exception:                                    # noqa: BLE001
            pass
        self.root.destroy()


def main():
    if tk is None:
        sys.exit(
            "Tkinter недоступен (" + _TK_ERROR_TEXT + ").\n"
            "Установите tk/tcl: Linux — «apt install python3-tk» / «pacman -S tk», "
            "на Windows и macOS tkinter входит в официальный установщик Python."
        )
    _setup_file_logging()
    root = tk.Tk()
    app = CommitterApp(root)
    # Проверка git при старте (15)
    ok, ver = check_git()
    if not ok:
        messagebox.showerror(APP_TITLE,
                             "Git не найден в системе.\n\n"
                             "Установите git (https://git-scm.com) и перезапустите "
                             "приложение.")
        sys.exit(1)
    if isinstance(ver, tuple):
        if ver < GIT_MIN_VERSION:
            app.log(f"ВНИМАНИЕ: версия git {ver[0]}.{ver[1]} ниже рекомендованной "
                    f"{GIT_MIN_VERSION[0]}.{GIT_MIN_VERSION[1]} — возможны проблемы.")
        else:
            app.log(f"git {ver[0]}.{ver[1]} — OK")
    elif ver:
        app.log(ver)
    root.mainloop()


if __name__ == "__main__":
    main()
