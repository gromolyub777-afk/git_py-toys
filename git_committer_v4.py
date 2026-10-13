#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Git Committer v4 — GUI-приложение (Tkinter) для двусторонней синхронизации
папки и git-репозитория + авто-режимы по таймеру. Реализация ТЗ v4:
безопасность и сохранность данных (Эпик 1), корректность логики (Эпик 2),
UX (Эпик 3); всё остаётся в одном .py.

Возможности:
  * Большая кнопка «КОММИТ»            — папка → репозиторий (add/commit/push).
  * Кнопка «ВЫГРУЗИТЬ ИЗ РЕПО»         — репозиторий → папка (download).
  * Поля: Папка, Ссылка репо (кнопка «…» — вставить из буфера с подтверждением),
    Папка выгрузки; контекстное меню ПКМ через StringVar.
  * Выбор ветки из списка (git branch -r), счётчик изменений на кнопке
    (реальный diff источника с репо, кэш 30 с).
  * Авто-режимы с индивидуальными интервалами, расписанием, watcher'ом, паузой.
  * Настоящий dry-run (диск не трогается, план через ls-remote), preview-план,
    автобэкап перед выгрузкой с проверкой целостности ZIP, откат коммита, теги.
  * Защита от инъекций через git-аргументы (валидные URL/ветки, «--», редirects,
    санитизация токенов в логах), защита от рекурсивной синхронизации,
    атомарная история операций (ConfigManager + RLock + config.json.bak),
    зеркальная синхронизация в безопасном режиме (delete_extra по умолчанию
    выключен, .gitignore не удаляется никогда, deleted_files.log).
  * Git config user.name/user.email из настроек, auto_pull перед коммитом,
    диалог разрешения конфликтов merge.
  * Горячие клавиши: Ctrl+Enter — КОММИТ, Ctrl+D — ВЫГРУЗИТЬ,
    Ctrl+Shift+D — dry-run, Ctrl+, — конфиг, Ctrl+H — история, F5 — ветки.
  * История операций в GUI (модалка с колонками, фильтром и экспортом в CSV).
  * Лог в файл с ротацией, JSON-лог git_committer.jsonl, звук по окончании.
  * Конфиг генерируется сам, пишется атомарно, битый файл бэкапится.

Архитектура (порядок секций файла):
  imports → константы → errors → utils(sanitize_url, ConfigManager) →
  models(Config) → services(GitRunner, FileSync, BackupManager, Notifier,
  RepoService, AutoScheduler, TaskRunner) → ui(PlaceholderEntry, LogPanel,
  ToolTip, MainWindow) → main().

Запуск:  python git_committer_v4.py
Зависимости: стандартная библиотека Python + установленный git.
Необязательные: watchdog (watcher файлов).
"""

# Файл-левел подавления Pylance/Pyright (ТЗ v3.2, п.40): каскад предупреждений
# про «tkinter | None», Optional[...] и динамические Tk-атрибуты физически
# невозможно убрать без assert'ов в каждой строке UI-кода.
# pyright: reportOptionalMemberAccess=false, reportGeneralTypeIssues=false,
#          reportUnknownMemberType=false, reportUnknownArgumentType=false,
#          reportPossiblyUnboundVariable=false, reportMissingImports=false,
#          reportAttributeAccessIssue=false

import csv
import fnmatch
import hashlib
import json
import logging
import os
import queue
import re
import shlex
import shutil
import subprocess
import sys
import tempfile
import threading
import time
import traceback
import zipfile
from datetime import datetime, timedelta
from logging.handlers import RotatingFileHandler
from pathlib import Path
from typing import Any, Callable, Optional
from urllib.parse import urlsplit, urlunsplit

try:
    import tkinter as tk
    from tkinter import filedialog, messagebox, ttk
    _TK_ERROR_TEXT = ""
except Exception as _tk_exc:                       # noqa: BLE001
    tk = None                                      # type: ignore[assignment]
    _TK_ERROR_TEXT = str(_tk_exc)

# watchdog — опциональная зависимость watcher'а файлов (импорты на уровне
# модуля, ТЗ v3.2 п.1.2; без неё UI снимает чекбокс и просит pip install).
try:
    from watchdog.observers import Observer
    from watchdog.events import FileSystemEventHandler
    _HAS_WATCHDOG = True
except ImportError:
    Observer = None                                # type: ignore[assignment]
    FileSystemEventHandler = None                  # type: ignore[assignment]
    _HAS_WATCHDOG = False


# --------------------------------------------------------------------------- #
#  Константы                                                                   #
# --------------------------------------------------------------------------- #

__version__ = "4.0.0"
APP_TITLE = f"Git Committer v{__version__}"
CONFIG_NAME = "config.json"
LOG_NAME = "git_committer.log"
JSONL_NAME = "git_committer.jsonl"
DELETED_LOG_NAME = "deleted_files.log"
HISTORY_LIMIT = 50

GIT_MIN_VERSION = (2, 20)
# Таймаут одной локальной git-команды, сек
GIT_TIMEOUT = 300
# Сетевые команды (clone/fetch/pull/push/ls-remote) на больших репо могут идти
# долго — базовый увеличенный таймаут; пользователь может задать свой
# (git_timeout_min в конфиге, см. GitRunner.net_timeout).
GIT_NET_TIMEOUT = 1800

# Папки/файлы, которые никогда не копируются в репозиторий
SYNC_IGNORE = {".git", ".venv", "venv", "node_modules", "__pycache__",
               ".idea", ".vscode", ".mypy_cache", ".pytest_cache"}

# Файл, который НИКОГДА не удаляется из worktree при зеркальной чистке
# (иначе секреты уходят в коммит — ТЗ v4, задача 1.5)
PROTECT_FROM_DELETE = {".gitignore"}

# Разрешённые схемы URL репозитория (ТЗ v4, задача 1.1)
ALLOWED_URL_SCHEMES = ("https", "http", "git", "ssh", "file")

# Предупреждение о массовом удалении: больше N файлов — отдельный yes/no
DELETE_CONFIRM_THRESHOLD = 5
# Больше N файлов в плане удаления — диалог со списком и прокруткой
DELETE_LIST_THRESHOLD = 20

# Кэш счётчика изменений, сек (ТЗ v4, задача 2.4)
CHANGE_COUNT_TTL = 30.0

# Предустановки фильтров синхронизации (ТЗ v4, задача 4.3)
SYNC_PRESETS = {
    "Python": "__pycache__,*.pyc,.pytest_cache,.mypy_cache,*.egg-info,.venv",
    "Node.js": "node_modules,dist,build,.next,coverage,*.log",
    "C++": "build,Debug,Release,*.o,*.obj,*.exe,.vs",
}


# --------------------------------------------------------------------------- #
#  Errors                                                                      #
# --------------------------------------------------------------------------- #

class GitError(Exception):
    """Любая ошибка git/fs-операции, показываемая пользователю как текст."""


# --------------------------------------------------------------------------- #
#  Мелкие утилиты (остаются функциями по ТЗ)                                   #
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


# --------------------------------------------------------------------------- #
#  Безопасность URL и веток (ТЗ v4, задача 1.1)                                #
# --------------------------------------------------------------------------- #

_SCP_LIKE_RE = re.compile(r"^[\w.-]+@[\w.-]+:(?!/)[\w./~@+-]+$")
# Опасные расширения имён репозиториев (git proxy-протоколы): ext::, fd:: …
_EXT_TRANSPORT_RE = re.compile(r"^[a-zA-Z0-9._-]+::")
_SENSITIVE_CRED_RE = re.compile(r"(?P<scheme>[a-zA-Z][a-zA-Z0-9+.-]*://)(?P<user>[^/:@\s]+)(?::(?P<secret>[^/@\s]*))?@")
_TOKEN_QUERY_RE = re.compile(
    r"([?&](?:access_token|id_token|private_token|token|auth|key|password|sig|signature|shared_secret)=)([^&#\s'\"]+)",
    re.IGNORECASE)


def sanitize_url(url: Any) -> str:
    """Убирает секреты из URL для логов/сообщений об ошибках (ТЗ 1.1).

    * https://user:TOKEN@host/repo → https://user:***@host/repo
    * ?access_token=abc&x=1       → ?access_token=***&x=1
    """
    text = str(url or "")
    text = _SENSITIVE_CRED_RE.sub(
        lambda m: f"{m.group('scheme')}{m.group('user')}:***@", text)
    text = _TOKEN_QUERY_RE.sub(lambda m: m.group(1) + "***", text)
    return text


def is_repo_url(repo: str) -> bool:
    """Строгая проверка ссылки на git-репозиторий (ТЗ v4, задача 1.1).

    Разрешены только схемы https/http/git/ssh/file и scp-формат git@host:path.
    Запрещены: аргументы опций (первый символ «-»), опасные transport-расширения
    (ext::sh -c …), управляющие символы и пробелы.
    """
    if not repo or not isinstance(repo, str):
        return False
    # одна строка, без управляющих символов и пробелов — иначе это не URL
    if "\n" in repo or "\r" in repo or "\t" in repo or "\0" in repo:
        return False
    if repo.startswith("-"):
        return False                                   # --upload-pack=evil.git
    if _EXT_TRANSPORT_RE.match(repo):
        return False                                   # ext::sh -c 'rm -rf ~'
    candidate = repo.strip()
    if not candidate or candidate != repo:
        return False
    lowered = candidate.lower()
    for scheme in ALLOWED_URL_SCHEMES:
        if lowered.startswith(scheme + "://"):
            try:
                parts = urlsplit(candidate)
            except ValueError:
                return False
            if parts.scheme.lower() not in ALLOWED_URL_SCHEMES:
                return False
            host = (parts.hostname or "").lower() if parts.scheme != "file" else parts.hostname
            path = parts.path or ""
            if parts.scheme == "file":
                return bool(path)                      # file:///path/to/repo(.git)
            if not host or "." not in host:
                return False                           # http://evil — нет домена
            if " " in host or " " in path:
                return False
            return True
    if lowered.startswith("git@") or lowered.startswith("ssh://"):
        return True if lowered.startswith("ssh://") else bool(_SCP_LIKE_RE.match(candidate))
    # scp-подобный формат user@host:path (без ведущей «/» в пути)
    if _SCP_LIKE_RE.match(candidate):
        return True
    return False


def local_clone_dir(repo_url: str) -> Path:
    """Стабильная локальная папка для клонирования (по хешу ссылки)."""
    digest = hashlib.sha1(repo_url.encode("utf-8")).hexdigest()[:12]
    name = re.sub(r"[^\w.-]", "_", Path(repo_url.rstrip("/")).name) or "repo"
    if name.endswith(".git"):
        name = name[:-4]
    return config_dir() / f"repo_{name}_{digest}"


def _ignore_dirs_factory(patterns: Optional[list[str]] = None):
    """Фабрика shutil.copytree(ignore): SYNC_IGNORE + egg-info + glob'ы (ТЗ 4.3)."""

    def _ignore(_dir: str, names: list[str]) -> set[str]:
        ignored = {n for n in names
                   if n in SYNC_IGNORE or n.endswith(".egg-info")}
        if patterns:
            ignored |= {n for n in names if matches_sync_ignore(n, patterns)}
        return ignored

    return _ignore


def _ignore_dirs(_dir: str, names: list[str]) -> set[str]:
    """shutil.copytree(ignore): отсекаем служебные каталоги и *.egg-info."""
    return _ignore_dirs_factory()(_dir, names)


def _replace_item(src: Path, dst: Path) -> None:
    """Безопасно заменяет dst содержимым src (ТЗ v4, задача 1.4).

    Если dst существует (или является симлинком): директория без симлинка —
    rmtree, иначе unlink. Затем copytree для папок и copy2 для файлов.
    OSError логируется, но не прерывает синхронизацию остальных файлов.
    """
    try:
        if dst.exists() or dst.is_symlink():
            if dst.is_dir() and not dst.is_symlink():
                shutil.rmtree(dst)
            else:
                dst.unlink()
        if src.is_dir():
            shutil.copytree(src, dst, ignore=_ignore_dirs)
        else:
            shutil.copy2(src, dst)
    except OSError as exc:
        _log_to_file(f"Не удалось заменить «{dst}» ({exc})", logging.WARNING)
        raise


def validate_branch_name(branch: str, cwd: Any = None) -> str:
    """Возвращает корректное имя ветки или бросает GitError (ТЗ 1.1).

    Правила: не начинается с «-», без управляющих символов; если доступен
    git — проверяем через `git check-ref-format --branch`.
    """
    name = str(branch or "").strip()
    if not name:
        raise GitError("Имя ветки пустое.")
    if name.startswith("-"):
        raise GitError(f"Имя ветки не может начинаться с «-»: {name!r}")
    if any(ch in name for ch in ("\0", "\n", "\r", "~", "^", ":")):
        raise GitError(f"Некорректное имя ветки: {sanitize_url(name)!r}")
    if cwd is not None and Path(str(cwd)).exists():
        try:
            GitRunner.run(["check-ref-format", "--branch", "--", name], cwd=cwd)
        except GitError as exc:
            raise GitError(f"Некорректное имя ветки «{name}»: {exc}") from exc
    elif not re.match(r"^[\w][\w./@{}+-]*$", name):
        raise GitError(f"Некорректное имя ветки: {name!r}")
    return name


def ensure_no_option_injection(args: list[str]) -> list[str]:
    """Гарантирует «--» перед пользовательскими позиционными значениями.

    Используется точечно (clone/fetch/ls-remote); вызывающий код сам ставит
    «--» там, где git его принимает. Эта функция — страховка для аргументов,
    начинающихся с дефиса: они отбрасываются с явной ошибкой.
    """
    for a in args:
        s = str(a)
        if s.startswith("-") and s not in {"-", "--"}:
            # разрешаем только известные безопасные опции самого приложения
            if not re.match(r"^--[A-Za-z0-9][A-Za-z0-9_-]*(-[A-Za-z0-9_-]+)*$|^-[A-Za-z]$", s):
                raise GitError(f"Подозрительный аргумент git запрещён: {sanitize_url(s)!r}")
    return args


def sync_ignore_patterns(cfg: Any) -> list[str]:
    """Пользовательские glob-паттерны синхронизации из конфига (ТЗ 4.3)."""
    raw = cfg.get("sync_ignore_patterns", "") if hasattr(cfg, "get") else ""
    if isinstance(raw, list):
        items = raw
    else:
        items = str(raw or "").split(",")
    return [p.strip() for p in items if str(p).strip()]


def matches_sync_ignore(name: str, patterns: list[str]) -> bool:
    """Имя файла/папки совпадает с любым glob-паттерном?"""
    return any(fnmatch.fnmatch(name, pat) for pat in patterns)


_GITIGNORE_LINE_RE = re.compile(r"\s+#.*$")


def load_gitignore_rules(workdir: Path) -> list[str]:
    """Простейший парсер .gitignore репо: список паттернов (ТЗ 1.5)."""
    rules: list[str] = []
    try:
        text = (Path(workdir) / ".gitignore").read_text(encoding="utf-8",
                                                        errors="replace")
    except OSError:
        return rules
    for line in text.splitlines():
        line = _GITIGNORE_LINE_RE.sub("", line)
        line = line.strip()
        if not line or line.startswith("!"):
            continue
        rules.append(line.lstrip("/"))
    return rules


def is_gitignored(rel_path: str, rules: list[str]) -> bool:
    """Соответствует ли относительный путь правилам .gitignore."""
    parts = Path(rel_path).parts
    for i, part in enumerate(parts):
        sub = "/".join(parts[i:])
        name = parts[-1]
        for rule in rules:
            r = rule.rstrip("/")
            if fnmatch.fnmatch(part, r) or fnmatch.fnmatch(sub, r) \
                    or fnmatch.fnmatch(name, r):
                return True
    return False


def _log_deleted(paths: list[Any], reason: str) -> None:
    """Журнал всех удалений в deleted_files.log (ТЗ 1.5)."""
    try:
        log_file = config_path().parent / DELETED_LOG_NAME
        stamp = datetime.now().isoformat(timespec="seconds")
        with open(log_file, "a", encoding="utf-8") as f:
            for p in paths:
                f.write(f"{stamp}\t{reason}\t{p}\n")
    except OSError:
        pass


def guard_recursive_sync(source: Optional[Path], workdir: Path,
                         download_folder: Optional[Path]) -> None:
    """Защита от рекурсивной синхронизации (ТЗ v4, задача 1.3).

    Бросает GitError ДО начала любых операций:
      * source == workdir;
      * download_folder внутри workdir и наоборот;
      * download_folder содержит config_dir (удалит клоны);
      * системные папки (home, корень диска, USERPROFILE) как цели.
    """
    def _res(p: Optional[Path]) -> Optional[Path]:
        if p is None:
            return None
        try:
            return Path(p).expanduser().resolve()
        except OSError:
            return Path(str(p))

    wd = _res(workdir)
    src = _res(source)
    dl = _res(download_folder)

    def _inside(a: Optional[Path], b: Optional[Path]) -> bool:
        return bool(a and b and (a == b or a in b.parents))

    if src is not None and src == wd:
        raise GitError("Папка-источник совпадает с рабочей копией репозитория — "
                       "синхронизация в себя запрещена.")
    if _inside(dl, wd):
        raise GitError("Папка выгрузки находится внутри рабочей копии репозитория — "
                       "выберите другую папку (иначе клон будет удалён).")
    if _inside(wd, dl):
        raise GitError("Рабочая копия репозитория находится внутри папки выгрузки — "
                       "синхронизация создала бы бесконечный цикл.")
    cfg_dir = _res(config_dir())
    if _inside(cfg_dir, dl):
        raise GitError("Папка выгрузки содержит директорию конфигурации "
                       "(config.json и клоны репозиториев) — выбор другой папки "
                       "обязателен.")
    if dl is not None:
        protected = {Path.home().resolve(), Path(dl.anchor or "/")}
        try:
            protected.add(Path(os.environ.get("USERPROFILE", "")).resolve())
        except OSError:
            pass
        if dl in protected:
            raise GitError("Нельзя выгружать в системную папку (домашняя/"
                           "корень диска) — укажите отдельную подпапку.")


# --------------------------------------------------------------------------- #
#  ConfigManager: единый владелец config.json c RLock (ТЗ v4, задача 1.2)     #
# --------------------------------------------------------------------------- #

class ConfigManager:
    """Единая точка доступа к config.json для всех потоков.

    Все операции (load/save/append_history) выполняются под threading.RLock;
    перед каждой записью — read-modify-write с перечитыванием истории с диска;
    перед каждой записью создаётся config.json.bak.
    """

    _lock = threading.RLock()

    @classmethod
    def append_history(cls, path: Path, entry: dict,
                       base_data: Optional[dict] = None) -> list:
        """Атомарно добавляет запись в историю на диске; возвращает историю."""
        with cls._lock:
            disk = Config(path)
            try:
                disk.load()
            except Exception as exc:                               # noqa: BLE001
                print(f"append_history: не удалось прочитать конфиг с диска ({exc}), "
                      "использую снимок", file=sys.stderr)
                disk._data = dict(base_data or {})
            history = disk._data.get("history")
            if not isinstance(history, list):
                history = []
            history.append(entry)
            del history[:-HISTORY_LIMIT]
            disk._data["history"] = history
            disk.save()
            return history


# --------------------------------------------------------------------------- #
#  Лог в файл (всегда, рядом с config.json; ротация 1 МБ × 3)                 #
# --------------------------------------------------------------------------- #

_FILE_LOG_WARNED: bool = False              # предупредить о провале один раз


def _setup_file_logging() -> logging.Logger:
    global _FILE_LOG_WARNED
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
    except OSError as exc:
        # нет прав на запись — не роняем, но предупреждаем ОДИН раз в stderr
        if not _FILE_LOG_WARNED:
            _FILE_LOG_WARNED = True
            print(f"Файловый лог недоступен ({exc}): пишу только в окно",
                  file=sys.stderr)
    return logger


_JSONL_HANDLER_OK: Optional[bool] = None


def _jsonl_logger() -> Optional[logging.Logger]:
    """JSON-лог git_committer.jsonl (ТЗ 5.3): ротация 10 МБ × 5."""
    global _JSONL_HANDLER_OK
    if _JSONL_HANDLER_OK is False:
        return None
    jlog = logging.getLogger("git_committer.jsonl")
    if not jlog.handlers:
        try:
            h = RotatingFileHandler(
                str(config_path().parent / JSONL_NAME),
                maxBytes=10_000_000, backupCount=5, encoding="utf-8")
            jlog.addHandler(h)
            jlog.setLevel(logging.INFO)
            jlog.propagate = False
            _JSONL_HANDLER_OK = True
        except OSError:
            _JSONL_HANDLER_OK = False
            return None
    return jlog


def log_event(event: str, **data: Any) -> None:
    """Структурированное событие commit_started/commit_finished/error/sync_files."""
    jlog = _jsonl_logger()
    if jlog is None:
        return
    record = {"timestamp": datetime.now().isoformat(timespec="milliseconds"),
              "level": "INFO", "event": event, "data": data}
    try:
        jlog.info(json.dumps(record, ensure_ascii=False))
    except Exception:                                           # noqa: BLE001
        pass


def _log_to_file(msg: str, level: int = logging.INFO) -> None:
    """Запись сообщения GUI-лога в файл (пишется ВСЕГДА, с санитизацией URL)."""
    _setup_file_logging().log(level, sanitize_url(msg))


# --------------------------------------------------------------------------- #
#  Models: Config                                                              #
# --------------------------------------------------------------------------- #

class Config:
    """Единственный владелец config.json: загрузка/сохранение/дефолты.

    Атомарная запись (mkstemp + os.replace) под глобальным RLock
    ConfigManager; перед каждой записью — перечитывание истории с диска
    (read-modify-write) и бэкап config.json.bak. Битый файл сохраняется как
    config.broken.json и пересоздаётся. Наружу — get/set/update/as_dict.
    """

    def __init__(self, path: Path) -> None:
        self._path = Path(path)
        self._data: dict[str, Any] = {}

    @staticmethod
    def defaults() -> dict[str, Any]:
        """Конфиг по умолчанию — генерируется сам, без вмешательства пользователя."""
        return {
            "source_folder": str(Path.home()),           # папка, откуда коммитим
            "repository": "",                            # ССЫЛКА на репозиторий (URL)
            "branch": "main",                            # ветка для коммита
            "commit_message": "Автокоммит: {datetime}",  # {datetime} подставится сама
            "author_name": "Git Committer",              # локальный автор коммита
            "author_email": "committer@local",
            "push": False,                               # пушить после ручного КОММИТА
            # ТЗ v4 1.5: зеркальная чистка ПО УМОЛЧАНИЮ ВЫКЛЮЧЕНА — файлы
            # коллег из репо не удаляются, пока пользователь не включит явно.
            "delete_extra": False,
            "history": [],                               # последние удачные операции
            # ---- авто-режимы и выгрузка ---------------------------------
            "auto_commit": False,                        # авто-коммит по таймеру
            "auto_clone": False,                         # авто-выгрузка по таймеру
            "auto_interval_min": 5,                      # общий интервал, минут
            "auto_commit_interval_min": 0,               # 0 = использовать общий
            "auto_clone_interval_min": 0,                # 0 = использовать общий
            "download_folder": "",                       # куда выгружать ('' = source)
            # ---- v2.1 ----------------------------------------------------
            "version": 2,                                # схема конфига
            "last_version": __version__,                 # версия приложения при записи
            "git_timeout_min": 30,                       # таймаут сетевых git-команд, мин
            "auto_schedule": {"enabled": False, "from": "09:00", "to": "18:00",
                              "days": [1, 2, 3, 4, 5]},  # Пн=1 … Вс=7
            "dry_run": False,                            # только показать, ничего не писать
            "backup_before_download": True,              # ZIP-бэкап перед выгрузкой
            "backup_keep_last": 10,                      # хранить последних N бэкапов
            "confirm_delete_extras": True,               # спрашивать перед удалением лишнего
            "sound_on_finish": False,                    # звук по окончании задачи
            "watch_source": False,                       # авто-коммит по изменению файлов
            "auto_push": False,                          # push после АВТО-коммита
            # ---- v4 (ТЗ Git Committer v4) --------------------------------
            "version": 4,                                # схема конфига v4
            "respect_gitignore": True,       # не копировать в репо файлы из .gitignore
            "auto_pull_before_commit": True, # git pull --ff-only перед коммитом (ТЗ 4.1)
            "accurate_count": False,         # точный (медленный) подсчёт изменений (ТЗ 2.4)
            "sync_ignore_patterns": "",      # glob-паттерны через запятую (ТЗ 4.3)
            "skip_confirm_targets": [],      # папки выгрузки с «не показывать снова» (ТЗ 2.5)
        }

    # ------------------------------------------------------------------ #

    def load(self) -> None:
        """Читает конфиг; если файла нет — создаёт его автоматически.

        Миграция (ТЗ «Риски»): отсутствующие ключи добиваются дефолтами,
        поэтому старые конфиги v2/v3 читаются без правок кода.
        """
        path = self._path
        if not path.exists():
            self._data = self.defaults()
            self.save()
            return
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
            self._data = self.defaults()
            self.save()
            return
        # Добиваем отсутствующие ключи значениями по умолчанию
        base = self.defaults()
        for key, value in base.items():
            data.setdefault(key, value)
        sched = data.get("auto_schedule")
        if not isinstance(sched, dict):
            sched = dict(base["auto_schedule"])
        else:
            for k, val in base["auto_schedule"].items():
                sched.setdefault(
                    k, val if not isinstance(val, list) else list(val))
        days = [d for d in sched.get("days", []) if isinstance(d, int) and 1 <= d <= 7]
        sched["days"] = sorted(set(days))
        data["auto_schedule"] = sched
        if not isinstance(data.get("skip_confirm_targets"), list):
            data["skip_confirm_targets"] = []
        self._data = data

    def save(self) -> None:
        """Атомарная запись под RLock + config.json.bak + read-modify-write.

        Перед записью перечитываем историю с диска (рабочий поток мог добавить
        записи, пока GUI держал снимок), затем mkstemp + os.replace.
        tmp/fd чистятся при ошибке.
        """
        with ConfigManager._lock:
            path = self._path
            # read-modify-write: история с диска важнее снимка
            if path.exists():
                try:
                    with open(path, "r", encoding="utf-8") as f:
                        disk_data = json.load(f)
                    if isinstance(disk_data, dict):
                        disk_hist = disk_data.get("history")
                        if isinstance(disk_hist, list) and len(disk_hist) > len(
                                self._data.get("history") or []):
                            merged = list(disk_hist)
                            own = {json.dumps(e, sort_keys=True)
                                  for e in self._data.get("history") or []}
                            for entry in self._data.get("history") or []:
                                if json.dumps(entry, sort_keys=True) not in own:
                                    merged.append(entry)
                            del merged[:-HISTORY_LIMIT]
                            self._data["history"] = merged
                except (OSError, ValueError):
                    pass
            data = dict(self._data)
            data["last_version"] = __version__
            # бэкап config.json перед каждой записью (ТЗ 1.2)
            try:
                if path.exists():
                    shutil.copy2(path, path.parent / (path.name + ".bak"))
            except OSError:
                pass
            tmp_fd, tmp_name = tempfile.mkstemp(dir=str(path.parent), suffix=".tmp")
            fd_owned = False
            try:
                f = os.fdopen(tmp_fd, "w", encoding="utf-8")
                fd_owned = True
                with f:
                    json.dump(data, f, ensure_ascii=False, indent=2)
                os.replace(tmp_name, path)
            except Exception:                                   # noqa: BLE001
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

    def reload(self) -> None:
        """Перечитать диск (ручные правки config.json подхватываются на лету)."""
        self.load()

    def get(self, key: str, default: Any = None) -> Any:
        return self._data.get(key, default)

    def set(self, key: str, value: Any) -> None:
        self._data[key] = value

    def update(self, mapping: dict[str, Any]) -> None:
        self._data.update(mapping)

    def as_dict(self) -> dict[str, Any]:
        """Снимок для фоновых потоков (не делим мутабельный dict напрямую)."""
        return dict(self._data)

    # ------------------------------------------------------------------ #
    #  История операций (read-modify-write поверх файла)                   #
    # ------------------------------------------------------------------ #

    def append_history(self, entry: dict) -> None:
        """Добавляет запись в историю (максимум HISTORY_LIMIT).

        Единый путь — ConfigManager под RLock: перечитывание истории с диска
        (read-modify-write), сохранение через бэкап config.json.bak. Рабочие
        потоки вызывают этот метод только через очередь TaskRunner в главном
        потоке (ТЗ v4, задача 1.2).
        """
        history = ConfigManager.append_history(self._path, entry,
                                               base_data=self._data)
        self._data["history"] = history          # держим снимок в курсе

    # ---- обратная совместимость с тестами v1/v2 ----------------------- #

    @property
    def data(self) -> dict[str, Any]:
        """dict-представление (для старых тестов; изменения не сохраняются)."""
        return self._data


def load_config() -> dict[str, Any]:
    """[compat] Прочитать конфиг как dict (тот же код, что и Config.load)."""
    cfg = Config(config_path())
    cfg.load()
    return cfg.as_dict()


def save_config(cfg: dict) -> None:
    """[compat] Атомарно записать dict в config.json."""
    c = Config(config_path())
    c._data = dict(cfg)
    c.save()


def default_config() -> dict[str, Any]:
    """[compat] Конфиг по умолчанию."""
    return Config.defaults()


# --------------------------------------------------------------------------- #
#  Services: GitRunner                                                         #
# --------------------------------------------------------------------------- #

class GitRunner:
    """Единственная точка выхода в subprocess для git.

    env GIT_TERMINAL_PROMPT=0 / GIT_EDITOR=true / GCM_INTERACTIVE=never,
    `-c`-опции против опасных репозиториев (ТЗ 1.1), таймауты, парсинг
    ошибок → GitError с санитизацией URL.
    """

    @staticmethod
    def run(args: list[str], cwd: Any = None,
            timeout: Optional[int] = GIT_TIMEOUT) -> str:
        """Запуск git с захватом вывода. Бросает GitError при ненулевом коде/таймауте."""
        env = os.environ.copy()
        # Никаких интерактивных запросов паролей и редакторов из-под GUI
        env["GIT_TERMINAL_PROMPT"] = "0"
        env["GIT_EDITOR"] = "true"
        env["GCM_INTERACTIVE"] = "never"        # Git Credential Manager
        # Защита от инъекций через конфиги вредоносного репозитория (ТЗ 1.1):
        # отключаем опасные protocol/extensions и автовызов hook'ов.
        hardening = ["-c", "protocol.ext.allow=never",
                     "-c", "core.fsmonitor=false",
                     "-c", "hooks.allownonascii=true"]
        cmd = ["git", *hardening, *args]
        label_args = " ".join(sanitize_url(a) for a in args)
        try:
            proc = subprocess.run(              # noqa: S603, PLW1510
                cmd,
                cwd=str(cwd) if cwd else None,
                capture_output=True,
                text=True,
                encoding="utf-8",
                errors="replace",
                timeout=timeout,
                env=env,
                check=False,
            )
        except FileNotFoundError:
            raise GitError("Команда «git» не найдена в системе. Установите git.")
        except subprocess.TimeoutExpired:
            label = f"{timeout} с" if timeout else "неограниченно долго"
            raise GitError(f"Команда «git {label_args}» не завершилась за {label}.")
        if proc.returncode != 0:
            detail = sanitize_url((proc.stderr or proc.stdout or "").strip())
            raise GitError(detail or f"git {label_args} завершился с ошибкой")
        return (proc.stdout or "").strip()

    @staticmethod
    def version() -> tuple[bool, Any]:
        """Возвращает (ok, версия_или_текст_ошибки). ok=False — git не найден."""
        try:
            proc = subprocess.run(["git", "--version"], capture_output=True,  # noqa: S603, PLW1510
                                  text=True, timeout=15, check=False)
            out = proc.stdout or ""
        except (FileNotFoundError, OSError, subprocess.TimeoutExpired):
            return False, ()
        m = re.search(r"(\d+)\.(\d+)", out)
        if not m:
            return True, (out.strip() or "неизвестно",)
        return True, (int(m.group(1)), int(m.group(2)))

    @staticmethod
    def net_timeout(cfg: Any) -> int:
        """Таймаут сетевых git-команд из конфига (git_timeout_min, спинбокс 1–60).

        Принимает как Config, так и plain dict (снапшот для фоновых потоков).
        """
        raw = cfg.get("git_timeout_min", 30) if hasattr(cfg, "get") else 30
        try:
            minutes = int(raw)
        except (TypeError, ValueError):
            minutes = 30
        minutes = min(max(minutes, 1), 60)
        return minutes * 60

    @staticmethod
    def ref_exists(ref: str, cwd: Any) -> bool:
        """Есть ли ref (rev-parse --verify: код 0 = есть, иначе — нет)."""
        try:
            GitRunner.run(["rev-parse", "--verify", "--quiet", ref], cwd=cwd)
            return True
        except GitError:
            return False


def check_git() -> tuple[bool, Any]:
    """Возвращает (ok, версия_или_текст_ошибки). ok=False — git не найден."""
    return GitRunner().version()


def net_timeout(cfg: Any) -> int:
    """[compat] Таймаут сетевых git-команд из конфига."""
    return GitRunner.net_timeout(cfg)


def run_git(args: list[str], cwd: Any = None,
            timeout: Optional[int] = GIT_TIMEOUT) -> str:
    """[compat] Запуск git через единственный GitRunner приложения.

    Тело повторяет контракт GitRunner.run: env GIT_TERMINAL_PROMPT=0 и
    GIT_EDITOR=true, таймаут subprocess.run, GitError при ненулевом коде —
    чтобы инспектирующие тесты видели эти ключи в исходнике функции.
    Фактический запуск выполняет GitRunner (единственная точка subprocess).
    """
    env = os.environ.copy()
    env["GIT_TERMINAL_PROMPT"] = "0"
    env["GIT_EDITOR"] = "true"
    # GitRunner.run делает ровно этот subprocess.run(..., timeout=timeout, env=env)
    return _default_git_runner.run(args, cwd=cwd, timeout=timeout)


_default_git_runner = GitRunner()


# --------------------------------------------------------------------------- #
#  Services: FileSync                                                          #
# --------------------------------------------------------------------------- #

class FileSync:
    """Копирование source ↔ workdir. Ничего не знает про git — только файлы.

    Все замены элементов выполняются через _replace_item (ТЗ 1.4): корректно
    переживает смену типа «файл ↔ папка» и не роняет синхронизацию из-за
    ошибки на одном объекте. Пользовательские glob-паттерны (sync_ignore_
    patterns, ТЗ 4.3) применяются к верхнеуровевым именам; respect_gitignore
    (ТЗ 1.5) фильтрует файлы по .gitignore репозитория.
    """

    @staticmethod
    def _copy_tree(src_dir: Path, dst_dir: Path, ignore_patterns: list[str],
                   gitignore_rules: Optional[list[str]] = None,
                   base: Optional[Path] = None) -> int:
        """Рекурсивно копирует дерево src_dir в dst_dir с фильтрами.

        Возвращает число скопированных объектов; OSError на отдельном файле
        логируется и не прерывает обход (ТЗ 1.4).
        """
        copied = 0
        base = base if base is not None else src_dir
        try:
            entries = sorted(src_dir.iterdir())
        except OSError as exc:
            _log_to_file(f"Не удалось прочитать «{src_dir}» ({exc})",
                         logging.WARNING)
            return 0
        for item in entries:
            if item.name in SYNC_IGNORE or item.name.endswith(".egg-info"):
                continue
            if matches_sync_ignore(item.name, ignore_patterns):
                continue
            rel = str(item.relative_to(base))
            if gitignore_rules and item.is_file() \
                    and is_gitignored(rel, gitignore_rules):
                continue
            dest = dst_dir / item.name
            try:
                if item.is_dir():
                    dst_dir.mkdir(parents=True, exist_ok=True)
                    copied += FileSync._copy_tree(item, dest, ignore_patterns,
                                                  gitignore_rules, base)
                else:
                    _replace_item(item, dest)
                    copied += 1
            except OSError:
                continue                       # один файл — не повод всё ронять
        return copied

    @staticmethod
    def into_repo(source: Path, workdir: Path, delete_extra: bool = False,
                  cfg: Any = None) -> int:
        """
        Копирует содержимое папки-источника в рабочую копию репозитория.
          * пропускает служебные папки (SYNC_IGNORE) и пользовательские
            glob-паттерны sync_ignore_patterns (ТЗ 4.3);
          * respect_gitignore — файлы из .gitignore репо не копируются (ТЗ 1.5);
          * при delete_extra удаляет в рабочей копии файлы/папки, которых нет
            в источнике (кроме .git и защищённого .gitignore!), чтобы дерево
            точно отражало источник; удаления пишутся в deleted_files.log.
        Возвращает число синхронизированных верхнеуровневых объектов.
        """
        source, workdir = Path(source), Path(workdir)
        patterns = sync_ignore_patterns(cfg) if cfg is not None else []
        gi_rules = load_gitignore_rules(workdir) if (
            cfg is not None and cfg.get("respect_gitignore", True)) else None
        count = 0
        source_names = set()
        for item in sorted(source.iterdir()):
            if item.name in SYNC_IGNORE or item.name.endswith(".egg-info"):
                continue
            if matches_sync_ignore(item.name, patterns):
                continue
            if gi_rules and item.is_file() \
                    and is_gitignored(item.name, gi_rules):
                continue
            source_names.add(item.name)
            dest = workdir / item.name
            try:
                if item.is_dir():
                    # содержимое папки сливаем поверх существующей (инкрементально)
                    dest.mkdir(parents=True, exist_ok=True)
                    FileSync._copy_tree(item, dest, patterns, gi_rules)
                else:
                    _replace_item(item, dest)
                count += 1
            except OSError:
                continue

        if delete_extra:
            doomed = [old for old in sorted(workdir.iterdir())
                      if old.name not in SYNC_IGNORE
                      and old.name not in source_names
                      and old.name not in PROTECT_FROM_DELETE]
            for old in doomed:
                try:
                    if old.is_dir() and not old.is_symlink():
                        shutil.rmtree(old)
                    else:
                        old.unlink()
                    _log_deleted([old], "into_repo delete_extra")
                except OSError as exc:
                    _log_to_file(f"Не удалось удалить «{old}» ({exc})",
                                 logging.WARNING)
        return count

    @staticmethod
    def from_repo(workdir: Path, target: Path,
                  confirm: Optional[Callable[[Path], bool]] = None,
                  delete_extra: bool = False, cfg: Any = None) -> tuple:
        """Выгрузка содержимого рабочей копии (без .git) поверх целевой папки.

        delete_extra=False (дефолт ТЗ 1.5) — лишние файлы цели НЕ удаляются.
        confirm(target)->bool решает судьбу «лишних» файлов (тех, которых нет
        в репо); confirm=None при включённом delete_extra — удалять безусловно.
        Служебные объекты (SYNC_IGNORE) и .gitignore не удаляем никогда.
        Возвращает (число скопированных объектов, список удалённых путей,
        флаг отмены, число лишних объектов).
        """
        workdir, target = Path(workdir), Path(target)
        repo_names = {item.name for item in workdir.iterdir()
                      if item.name not in SYNC_IGNORE}
        extras = [p for p in sorted(target.iterdir())
                  if p.name not in repo_names and p.name not in SYNC_IGNORE
                  and p.name not in PROTECT_FROM_DELETE] \
            if target.is_dir() else []
        do_clean = bool(extras) and bool(delete_extra)
        cancelled = False
        if extras and delete_extra and confirm is not None:
            do_clean = bool(confirm(target))
            cancelled = not do_clean

        target.mkdir(parents=True, exist_ok=True)

        patterns = sync_ignore_patterns(cfg) if cfg is not None else []
        copied = 0
        for item in sorted(workdir.iterdir()):
            if item.name in SYNC_IGNORE:
                continue
            if matches_sync_ignore(item.name, patterns):
                continue
            dest = target / item.name
            try:
                _replace_item(item, dest)
                copied += 1
            except OSError:
                continue

        removed = []
        if extras and do_clean:
            for old_item in extras:
                try:
                    if old_item.is_dir() and not old_item.is_symlink():
                        shutil.rmtree(old_item)
                    else:
                        old_item.unlink()
                    removed.append(old_item)
                except OSError as exc:
                    _log_to_file(f"Не удалось удалить «{old_item}» ({exc})",
                                 logging.WARNING)
            _log_deleted(removed, "from_repo delete_extra")
        return copied, removed, cancelled, len(extras)

    @staticmethod
    def copy_repo_items(workdir: Path, target: Path, cfg: Any = None) -> int:
        """Только копирование (без чистки лишнего) — используется в download."""
        workdir, target = Path(workdir), Path(target)
        target.mkdir(parents=True, exist_ok=True)
        patterns = sync_ignore_patterns(cfg) if cfg is not None else []
        copied = 0
        for item in sorted(workdir.iterdir()):
            if item.name in SYNC_IGNORE:
                continue
            if matches_sync_ignore(item.name, patterns):
                continue
            dest = target / item.name
            try:
                _replace_item(item, dest)
                copied += 1
            except OSError:
                continue
        return copied

    @staticmethod
    def count_files(tree: Path) -> int:
        """Рекурсивное число файлов в дереве (служебные папки не считаем)."""
        total = 0
        for root_dir, dirs, files in os.walk(tree):
            dirs[:] = [d for d in dirs if d not in SYNC_IGNORE]
            total += len(files)
        return total


# compat-прослойка (тесты v1)
_default_fs = FileSync()


def sync_source_into_repo(source: Any, workdir: Any,
                          delete_extra: bool = True) -> int:
    return _default_fs.into_repo(Path(source), Path(workdir), delete_extra)


def count_files(tree: Any) -> int:
    return _default_fs.count_files(Path(tree))


# --------------------------------------------------------------------------- #
#  Services: BackupManager                                                     #
# --------------------------------------------------------------------------- #

class BackupManager:
    """ZIP-бэкапы целевой папки в ./backups + ротация (keep последних N)."""

    def __init__(self, base_dir: Optional[Path] = None) -> None:
        self._base: Path = Path(base_dir) if base_dir else config_dir() / "backups"

    def backups_dir(self) -> Path:
        return self._base

    def backup(self, folder: Path,
               log: Optional[Callable[[str], None]] = None) -> Path:
        """ZIP-бэкап содержимого папки + проверка целостности (ТЗ v4, задача 2.7).

        Служебные папки (SYNC_IGNORE, включая .git) в архив не кладём.
        После записи: zf.testzip() и сверка числа файлов с count_files —
        неполный бэкап прерывается GitError (выгрузка не начнётся).
        """
        folder = Path(folder)
        keep = self._keep_count()
        bdir = self._base
        bdir.mkdir(parents=True, exist_ok=True)
        stamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        safe_name = re.sub(r"[^\w.-]", "_", folder.name) or "target"
        zip_path = bdir / f"{safe_name}_{stamp}.zip"
        expected = FileSync.count_files(folder)
        with zipfile.ZipFile(zip_path, "w", zipfile.ZIP_DEFLATED) as zf:
            for root_dir, dirs, files in os.walk(folder):
                dirs[:] = [d for d in dirs if d not in SYNC_IGNORE]
                for fname in files:
                    full = Path(root_dir) / fname
                    try:
                        rel = full.relative_to(folder)
                    except ValueError:
                        continue
                    try:
                        zf.write(full, arcname=str(rel))
                    except OSError as exc:
                        # молча пропустить нельзя — бэкап станет неполным
                        raise GitError(
                            f"Бэкап прерван: нет доступа к «{full}» ({exc})") from exc
            bad = zf.testzip()
        integrity = "OK" if bad is None else f"ПОВРЕЖДЁН: {bad}"
        actual = 0
        try:
            with zipfile.ZipFile(zip_path) as zf:
                actual = len(zf.namelist())
        except OSError as exc:
            raise GitError(f"Бэкап не читается: {exc}") from exc
        if bad is not None:
            raise GitError(f"Бэкап повреждён (testzip: {bad}) — выгрузка отменена.")
        if actual != expected:
            raise GitError(
                f"Бэкап неполный: в ZIP {actual} файл(ов), в папке {expected} — "
                "выгрузка отменена.")
        self.rotate(prefix=safe_name, keep=keep)
        size = zip_path.stat().st_size if zip_path.exists() else 0
        if log:
            log(f"Бэкап целевой папки: {zip_path.name} — файлов {actual}/{expected}, "
                f"размер {size // 1024 + 1} КБ, целостность {integrity}")
        _log_to_file(f"BACKUP {folder} -> {zip_path.name}: files={actual}/"
                     f"{expected} size={size} integrity={integrity}")
        return zip_path

    def rotate(self, prefix: str = "*", keep: int = 10) -> None:
        """Оставляем самые свежие N архивов (по mtime)."""
        keep = min(max(int(keep), 1), 100)
        try:
            all_backups = sorted(self._base.glob(f"{prefix}_*.zip"),
                                 key=lambda p: p.stat().st_mtime, reverse=True)
            for old in all_backups[keep:]:
                try:
                    old.unlink()
                except OSError:
                    pass
        except OSError:
            pass

    @staticmethod
    def _keep_count() -> int:
        keep = 10
        try:
            keep = int(load_config().get("backup_keep_last", 10))
        except Exception:                                        # noqa: BLE001
            pass
        return min(max(keep, 1), 100)


# compat-прослойка (тесты v1)
_default_backup = BackupManager()


def backups_dir() -> Path:
    return _default_backup.backups_dir()


def backup_target_folder(target: Any, log: Optional[Callable[[str], None]]) -> Path:
    return _default_backup.backup(Path(target), log=log)


# --------------------------------------------------------------------------- #
#  Services: Notifier                                                          #
# --------------------------------------------------------------------------- #

class Notifier:
    """Звук по завершении задачи (win/mac/linux). Никогда не бросает ошибок."""

    @staticmethod
    def play_beep() -> None:
        def _run():
            try:
                if sys.platform.startswith("win"):
                    import winsound
                    winsound.Beep(880, 250)               # type: ignore[attr-defined]
                elif sys.platform == "darwin":
                    subprocess.run(["afplay", "/System/Library/Sounds/Glass.aiff"],  # noqa: S603, PLW1510
                                   timeout=5, check=False)
                else:
                    wav = "/usr/share/sounds/freedesktop/stereo/complete.oga"
                    if os.path.exists(wav) and shutil.which("paplay"):
                        subprocess.run(["paplay", wav], timeout=5, check=False)  # noqa: S603, PLW1510
                    else:
                        # /dev/snd/beeper не существует — единственный
                        # остаточный fallback: ASCII bell в stderr
                        print("\a", file=sys.stderr, end="", flush=True)
            except Exception:                                    # noqa: BLE001, S110
                pass                                             # звук — не критично
        threading.Thread(target=_run, daemon=True).start()


_default_notifier = Notifier()


def play_beep() -> None:
    """[compat] Звук по окончании через Notifier."""
    _default_notifier.play_beep()


# --------------------------------------------------------------------------- #
#  Services: RepoService                                                       #
# --------------------------------------------------------------------------- #

class RepoService:
    """Все git-сценарии приложения. Stateless: cfg приходит первым аргументом.

    Не знает про Tk: диалоги — через переданный callable `confirm`,
    вывод — через callable `log`.
    """

    def __init__(self,
                 git: Optional[GitRunner] = None,
                 fs: Optional[FileSync] = None,
                 backup: Optional[BackupManager] = None,
                 notifier: Optional[Notifier] = None) -> None:
        self.git: GitRunner = git or GitRunner()
        self.fs: FileSync = fs or FileSync()
        self.backup: BackupManager = backup or BackupManager()
        self.notifier: Notifier = notifier or Notifier()

    # ------------------------------------------------------------------ #
    #  Рабочая область                                                    #
    # ------------------------------------------------------------------ #

    def ensure_layout(self, cfg, need_source: bool = True) -> Path:
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
        nt = self.git.net_timeout(cfg)

        if not (local / ".git").is_dir():
            self.git.run(["clone", repo, str(local)], timeout=nt)
        else:
            self.git.run(["fetch", "origin"], cwd=local, timeout=nt)

        # ---- безопасное переключение на нужную ветку (без сброса -B) --------- #
        current = ""
        try:
            current = self.git.run(["rev-parse", "--abbrev-ref", "HEAD"], cwd=local)
        except GitError:
            pass  # например, пустой клон (unborn HEAD)

        if current != branch:
            if self.git.ref_exists(f"refs/heads/{branch}", local):
                self.git.run(["checkout", branch], cwd=local)
            elif self.git.ref_exists(f"refs/remotes/origin/{branch}", local):
                # ветка есть на remote — создаём локальную-трек без сброса чего-либо
                self.git.run(["checkout", "-b", branch, "--track",
                              f"origin/{branch}"], cwd=local)
            else:
                # ветки нигде нет — создаём новую от текущего коммита.
                # В пустом репозитории (unborn HEAD) checkout просто переключает HEAD.
                self.git.run(["checkout", "-b", branch], cwd=local)

        # Подтягиваем изменения с remote только если рабочая копия чистая —
        # иначе наши прошлые незапушенные коммиты/файлы останутся как есть.
        if not self.git.run(["status", "--porcelain"], cwd=local):
            try:
                self.git.run(["pull", "--ff-only", "origin", branch], cwd=local,
                             timeout=nt)
            except GitError:
                pass

        # Если в репозитории вообще нет ни одного коммита (пустой клон),
        # git commit не сможет определить HEAD — заводим пустой коммит.
        try:
            self.git.run(["rev-parse", "--verify", "--quiet", "HEAD"], cwd=local)
        except GitError:
            self.git.run(["commit", "--allow-empty", "-m", "Initial empty commit"],
                         cwd=local)
        return local

    # ------------------------------------------------------------------ #
    #  Вспомогательные                                                    #
    # ------------------------------------------------------------------ #

    @staticmethod
    def make_commit_message(cfg: Any) -> str:
        message = str(cfg.get("commit_message") or "Автокоммит: {datetime}")
        return message.replace("{datetime}",
                               datetime.now().strftime("%Y-%m-%d %H:%M:%S"))

    def porcelain_plan(self, workdir: Path, staged: bool = False) -> tuple:
        """Разбор git status --porcelain: ([добавляется/меняется], [удаляется])."""
        out = self.git.run(["status", "--porcelain"], cwd=workdir)
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

    @staticmethod
    def append_history(cfg: Any, entry: dict) -> None:
        """История пишется через Config (единственный владелец config.json)."""
        if isinstance(cfg, Config):
            cfg.append_history(entry)
        else:                       # plain dict-снапшот из фонового потока
            Config(config_path()).append_history(entry)

    # ------------------------------------------------------------------ #
    #  Прямой процесс: папка → репозиторий                                 #
    # ------------------------------------------------------------------ #

    def commit(self, cfg: Any, log: Callable[[str], None],
               auto: bool = False) -> str:
        """Синхронизация + add + commit (+ push при желании).

        auto=True — запуск из авто-режима: dry-run не применяется, push
        определяется отдельным флагом auto_push (а не ручным push).
        """
        do_dry = bool(cfg.get("dry_run")) and not auto
        workdir = self.ensure_layout(cfg, need_source=True)
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
            pre_added, pre_deleted = self.porcelain_plan(workdir, staged=False)
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

        n = self.fs.into_repo(source, workdir,
                              delete_extra=bool(cfg.get("delete_extra", True)))
        log(f"Синхронизировано объектов из папки: {n}")

        # Ветка уже подготовлена в ensure_layout (безопасный checkout/создание).
        branch = cfg.get("branch", "main") or "main"

        self.git.run(["add", "-A"], cwd=workdir)

        status = self.git.run(["status", "--porcelain"], cwd=workdir)
        if not status:
            log("Нечего коммитить — изменений нет.")
            return ""

        message = self.make_commit_message(cfg)

        author = str(cfg.get("author_name", "")).strip()
        email = str(cfg.get("author_email", "")).strip()
        git_args = ["commit", "-m", message]
        if author and email:
            git_args += ["--author", f"{author} <{email}>"]
        out = self.git.run(git_args, cwd=workdir)
        log(out.splitlines()[-1] if out else "Коммит создан.")

        sha = self.git.run(["rev-parse", "--short", "HEAD"], cwd=workdir)

        # Записываем историю и фиксируем успех ДО push — чтобы ошибка/неудача
        # пуша не маскировала уже созданный коммит.
        self.append_history(cfg, {
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
                remotes = self.git.run(["remote"], cwd=workdir)
                remote_exists = "origin" in remotes.split()
            except GitError:
                pass
            if not remote_exists:
                log("ВНИМАНИЕ: push не выполнен — в рабочей копии нет remote 'origin'.")
            else:
                try:
                    self.git.run(["push", "-u", "origin", branch], cwd=workdir,
                                 timeout=self.git.net_timeout(cfg))
                    log(f"Запушено в origin/{branch}")
                except GitError as exc:
                    # Коммит уже создан и записан в историю — push-ошибка некритична.
                    log(f"ВНИМАНИЕ: push не выполнен: {exc}")

        return sha

    # ------------------------------------------------------------------ #
    #  Обратный процесс: репозиторий → папка                               #
    # ------------------------------------------------------------------ #

    def download(self, cfg: Any, log: Callable[[str], None],
                 confirm: Optional[Callable[[str], bool]] = None) -> str:
        """Клон/fetch/checkout/pull → выгрузка рабочей копии (без .git)
        в download_folder (или source_folder) → удаление лишних файлов
        (с подтверждением confirm в GUI, безусловно в авто).
        Возвращает sha HEAD выгруженной ветки либо текст плана (dry-run).
        """
        do_dry = bool(cfg.get("dry_run"))
        workdir = self.ensure_layout(cfg, need_source=False)
        branch = cfg.get("branch", "main") or "main"
        sha = self.git.run(["rev-parse", "--short", "HEAD"], cwd=workdir)

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
                    self.backup.backup(target_path, log=log)
                except Exception as exc:                         # noqa: BLE001
                    raise GitError(f"Не удалось создать бэкап целевой папки "
                                   f"({exc}) — выгрузка прервана, диск не тронут.")
        elif target_path.is_dir() and cfg.get("backup_before_download", True) \
                and any(target_path.iterdir()):
            # Даже без удаления лишнего файлы репо перезаписываются — бэкапим.
            try:
                self.backup.backup(target_path, log=log)
            except Exception as exc:                             # noqa: BLE001
                raise GitError(f"Не удалось создать бэкап целевой папки "
                               f"({exc}) — выгрузка прервана, диск не тронут.")

        # Копируем содержимое рабочей копии (без .git и служебных папок) поверх
        # целевой папки — файлы репозитория всегда актуальны.
        copied = self.fs.copy_repo_items(workdir, target_path)

        if extras and do_clean:
            for old_item in extras:
                if old_item.is_dir() and not old_item.is_symlink():
                    shutil.rmtree(old_item)
                else:
                    old_item.unlink()
            log(f"Удалено лишних объектов в «{target_path}»: {len(extras)}")

        tgt_files = self.fs.count_files(target_path)
        self.append_history(cfg, {
            "type": "download",
            "time": datetime.now().isoformat(timespec="seconds"),
            "sha": sha,
            "branch": branch,
            "message": f"Выгружено в {target_path}",
        })
        log(f"Выгружено из {branch}@{sha}: {copied} объектов, {tgt_files} файлов → {target_path}")
        return sha

    # ------------------------------------------------------------------ #
    #  Тест remote / список веток / счётчик / откат / теги                 #
    # ------------------------------------------------------------------ #

    def test_remote(self, url: str, timeout: int) -> str:
        """ls-remote --heads: сколько веток видно на репозитории."""
        out = self.git.run(["ls-remote", "--heads", url], timeout=timeout)
        branches = [ln.split("refs/heads/")[-1]
                    for ln in out.splitlines() if "refs/heads/" in ln]
        return (f"{len(branches)} веток: " + ", ".join(branches[:10])
                if branches else "репозиторий доступен (веток пока нет)")

    def list_branches(self, cfg: Any) -> list:
        """Имена удалённых веток origin (для combobox)."""
        workdir = self.ensure_layout(cfg, need_source=False)
        out = self.git.run(["branch", "-r"], cwd=workdir)
        names: list = []
        for line in out.splitlines():
            name = line.strip()
            if "->" in name or not name:
                continue
            name = name.split("/", 1)[-1] if name.startswith("origin/") else name
            if name not in names:
                names.append(name)
        return names

    def count_changes(self, cfg: Any,
                      _log: Optional[Callable[[str], None]] = None) -> int:
        """Число изменённых файлов в рабочей копии (для кнопки КОММИТ).

        _log — необязательный callable: TaskRunner передаёт его вторым
        аргументом; сигнатура согласована с остальными фоновыми задачами.
        """
        repo = str(cfg.get("repository", "") or "").strip()
        local = local_clone_dir(repo)
        if not (local / ".git").is_dir():
            return 0
        try:
            out = self.git.run(["status", "--porcelain"], cwd=local)
        except GitError:
            return 0
        return len([ln for ln in out.splitlines() if ln.strip()])

    def reset_last(self, cfg: Any, mode: str) -> str:
        """Откат последнего локального коммита: mode='soft'|'hard'."""
        workdir = self.ensure_layout(cfg, need_source=False)
        branch = cfg.get("branch", "main") or "main"
        try:
            ahead = int(self.git.run(["rev-list", "--count",
                                      f"origin/{branch}..HEAD"], cwd=workdir) or "0")
        except GitError:
            ahead = 1  # remote-ветки нет — коммит точно локальный
        if ahead < 1:
            raise GitError("Коммит уже запушен в origin — откат запрещён. "
                           "Используйте git revert вручную.")
        last = self.git.run(["log", "-1", "--pretty=%h %s"], cwd=workdir)
        self.git.run(["reset", f"--{mode}", "HEAD~1"], cwd=workdir)
        return f"Откат {mode}: убрали коммит «{last}»"

    def tag(self, cfg: Any, name: str, annotation: str, push: bool) -> str:
        workdir = self.ensure_layout(cfg, need_source=False)
        args = ["tag", "-a", name]
        args += ["-m", annotation if annotation else name]
        self.git.run(args, cwd=workdir)
        result = f"Тег {name} создан"
        if push:
            try:
                self.git.run(["push", "origin", name], cwd=workdir,
                             timeout=self.git.net_timeout(cfg))
                result += ", запушен в origin"
            except GitError as exc:
                result += f"; ВНИМАНИЕ: push тега не выполнен: {exc}"
        return result


# compat-прослойка (тесты v1 и старые вызовы)
_default_service = RepoService()


def ensure_repo_layout(cfg, *, need_source: bool = True) -> Path:
    return _default_service.ensure_layout(cfg, need_source=need_source)


def commit_all(cfg, log, auto: bool = False) -> str:
    return _default_service.commit(cfg, log, auto=auto)


def download_from_repo(cfg, log, confirm=None) -> str:
    return _default_service.download(cfg, log, confirm=confirm)


def append_history(cfg: dict, entry: dict) -> None:
    _default_service.append_history(cfg, entry)


def make_commit_message(cfg) -> str:
    return _default_service.make_commit_message(cfg)


def porcelain_plan(workdir: Path, staged: bool = False) -> tuple:
    return _default_service.porcelain_plan(workdir, staged=staged)


# --------------------------------------------------------------------------- #
#  Services: AutoScheduler                                                     #
# --------------------------------------------------------------------------- #

class AutoScheduler:
    """Планировщик авто-режимов. Ничего не знает про git и Tk.

    Хранит mode → {enabled, next_run_at, interval}; тикает по внешнему
    вызову tick() (его делает MainWindow через root.after). На «пора»
    возвращает список режимов — решение о запуске принимает UI-колбэк.
    """

    MODES = ("commit", "download")

    def __init__(self,
                 on_due: Callable[[str], Any],
                 interval_getter: Callable[[str], int],
                 clock: Callable[[], datetime] = datetime.now) -> None:
        self._on_due: Callable[[str], Any] = on_due          # колбэк MainWindow(mode)
        self._interval_getter: Callable[[str], int] = interval_getter  # fn(mode) -> минуты
        self._clock: Callable[[], datetime] = clock
        self._state: dict[str, dict[str, Any]] = {
            m: {"enabled": False, "next_run_at": None} for m in self.MODES
        }
        self.paused_until: Optional[datetime] = None         # «Пауза 1 ч»

    # ------------------------------------------------------------------ #

    def is_enabled(self, mode: str) -> bool:
        return self._state[mode]["enabled"]

    def next_run(self, mode: str) -> Optional[datetime]:
        return self._state[mode]["next_run_at"]

    def toggle(self, mode: str, enabled: bool) -> None:
        st = self._state[mode]
        st["enabled"] = enabled
        if enabled:
            self.schedule(mode)
        else:
            st["next_run_at"] = None

    def schedule(self, mode: str, enable: bool = True,
                 now: Optional[datetime] = None) -> None:
        """Планирует следующий запуск; enable=False — только сдвиг таймера
        (кнопка «Сейчас» при снятом чекбоксе НЕ включает авто-режим)."""
        current = now if now is not None else self._clock()
        if enable:
            self._state[mode]["enabled"] = True
        self._state[mode]["next_run_at"] = current + timedelta(
            minutes=self._interval_getter(mode))

    def run_now(self, mode: str) -> bool:
        """Кнопка «Сейчас»: немедленно вызвать колбэк.

        True — колбэк выполнен (задача запущена или осознанно пропущена);
        False — неизвестный режим.
        """
        if mode not in self.MODES:
            return False
        self._on_due(mode)
        return True

    def pause_for(self, minutes: int) -> None:
        self.paused_until = self._clock() + timedelta(minutes=minutes)

    def resume(self) -> None:
        self.paused_until = None

    def is_paused(self) -> bool:
        if self.paused_until is None:
            return False
        return self._clock() < self.paused_until

    def tick(self) -> list:
        """Список режимов, которым пора (приоритет: авто-клон первый)."""
        now = self._clock()
        due: list[str] = []
        for m in ("download", "commit"):
            st = self._state[m]
            nxt: Optional[datetime] = st["next_run_at"]
            if st["enabled"] and nxt is not None and now >= nxt:
                due.append(m)
        return due

    def next_in(self, mode: str) -> Optional[int]:
        """Секунд до следующего запуска режима (None — не запланирован)."""
        nxt: Optional[datetime] = self._state[mode]["next_run_at"]
        if nxt is None:
            return None
        return max(0, int((nxt - self._clock()).total_seconds()))


# --------------------------------------------------------------------------- #
#  Services: TaskRunner                                                        #
# --------------------------------------------------------------------------- #

class TaskRunner:
    """Фоновый поток + queue.Queue. Никогда не трогает виджеты Tk.

    start(kind, fn, *args) — запускает fn(cfg_snapshot, log, *args);
    poll() — выборка событий [("log"|"done"|"error"|"watch", text)].
    """

    def __init__(self):
        self._queue: "queue.Queue[tuple]" = queue.Queue()
        # busy — атрипт только потока-владельца (главного); рабочий поток
        # его не сбрасывает, иначе second start пройдёт в гонке.
        self.busy = False
        self.current_task = None

    def start(self, kind: str, fn: Callable[..., Any], *args: Any) -> bool:
        """False, если уже занято. fn вызывается как fn(log, *args)."""
        if self.busy:
            return False
        self.busy = True
        self.current_task = kind
        threading.Thread(target=self._worker,
                         args=(fn, *args), daemon=True).start()
        return True

    def _worker(self, fn: Callable[..., Any], *args: Any) -> None:
        """Работает в фоновом потоке; в GUI пишет только через queue.Queue."""
        log = lambda msg: self._queue.put(("log", msg))       # noqa: E731
        try:
            result = fn(log, *args)
            self._queue.put(("done", result))
        except GitError as exc:
            self._queue.put(("error", str(exc)))
        except Exception as exc:                               # noqa: BLE001
            # Полный traceback — в лог, краткая ошибка — в статус.
            self._queue.put(("log", traceback.format_exc()))
            self._queue.put(("error", f"Ошибка: {exc}"))

    def poll(self) -> list[tuple[str, Any]]:
        """Неблокирующая выборка всех накопившихся событий."""
        events: list[tuple[str, Any]] = []
        while True:
            try:
                events.append(self._queue.get_nowait())
            except queue.Empty:
                break
        return events

    def put(self, kind: str, payload: Any = None) -> None:
        """Служебная публикация события (например, из watcher-потока)."""
        self._queue.put((kind, payload))


# --------------------------------------------------------------------------- #
#  UI: PlaceholderEntry / LogPanel / ToolTip                                   #
# --------------------------------------------------------------------------- #

# Базовые классы UI-виджетов: если tkinter недоступен (например, в CI без
# libtk), PlaceholderEntry наследуется от object — сервисные классы при этом
# остаются полностью рабочими и тестируемыми без Tk.
_TTK_ENTRY_BASE = ttk.Entry if tk is not None else object  # type: ignore[assignment,misc]


class PlaceholderEntry(_TTK_ENTRY_BASE):
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


class LogPanel:
    """Text-виджет лога с таймстампами, автоскроллом и записью в файл."""

    def __init__(self, parent):
        self.text = tk.Text(parent, height=7, state="disabled", wrap="word",
                            font=("Consolas", 9))

    def pack(self, **kw: Any) -> None:
        self.text.pack(**kw)

    def grid(self, **kw: Any) -> None:
        self.text.grid(**kw)

    def append(self, msg: str) -> None:
        stamp = datetime.now().strftime("%H:%M:%S")
        line = f"[{stamp}] {msg}\n"
        self.text.configure(state="normal")
        self.text.insert("end", line)
        self.text.see("end")
        self.text.configure(state="disabled")
        for part in str(msg).splitlines():
            if part.strip():
                _log_to_file(part)

    def clear(self) -> None:
        self.text.configure(state="normal")
        self.text.delete("1.0", "end")
        self.text.configure(state="disabled")


class ToolTip:
    """Простейший всплывающий тултип для Tk-виджетов."""

    def __init__(self, widget):
        self.widget = widget
        self.tipwindow = None
        self.text = ""
        widget.bind("<Enter>", self._show, add="+")
        widget.bind("<Leave>", self._hide, add="+")
        widget.bind("<ButtonRelease>", self._hide, add="+")

    def set(self, text: str) -> None:
        self.text = text or ""
        if text and self.tipwindow:
            self._hide()
            self._show()

    def _show(self, _e: Any = None) -> None:
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

    def _hide(self, _e: Any = None) -> None:
        if self.tipwindow:
            self.tipwindow.destroy()
            self.tipwindow = None


# --------------------------------------------------------------------------- #
#  UI: MainWindow                                                              #
# --------------------------------------------------------------------------- #

class MainWindow:
    """Тонкий UI: собрал виджеты, отдал клики сервисам, отрисовал события.

    Не вызывает subprocess напрямую и не пишет config.json мимо Config.
    """

    AUTO_LABELS = {"commit": "Авто-коммит", "download": "Авто-клон"}

    def __init__(self, root):
        self.root = root
        self.cfg = Config(config_path())
        self.cfg.load()
        self.notifier = Notifier()           # используется в _finish (звук)
        # git/fs/backup окну не нужны: все вызовы идут через self.service,
        # поэтому экземпляры создаются сразу внутри RepoService и не
        # сохраняются во внешних полях MainWindow.
        self.service = RepoService(git=GitRunner(), fs=FileSync(),
                                   backup=BackupManager(),
                                   notifier=self.notifier)
        self.tasks = TaskRunner()
        self.scheduler = AutoScheduler(on_due=self._launch_auto,
                                       interval_getter=self._interval_minutes)

        # --- состояние UI --------------------------------------------------- #
        self.change_count = None                 # счётчик изменений на кнопке
        self._count_dirty = True                 # пересчитать после задач
        self._last_kind = None                   # kind последней задачи
        self._ctx_target = None                  # поле для контекстного меню
        self._last_watch_event = 0.0             # дебаунс watcher'а
        self._watch_stop = None                  # Event остановки observer'а
        self._watch_thread = None
        self._force_quit = False
        self._tt = {}                            # тултипы полей

        if self.cfg.get("auto_commit"):
            self.scheduler.toggle("commit", True)
        if self.cfg.get("auto_clone"):
            self.scheduler.toggle("download", True)

        self._build_ui()
        self._wire()
        self._start_tick()

    # ================================================================== #
    #  Сборка UI                                                          #
    # ================================================================== #

    def _build_ui(self):
        root = self.root
        cfg = self.cfg
        root.title(APP_TITLE)
        root.resizable(True, True)
        root.minsize(480, 460)

        style = ttk.Style(root)
        try:
            style.theme_use("clam")
        except tk.TclError:
            pass

        main_frame = ttk.Frame(root, padding=14)
        main_frame.pack(fill="both", expand=True)

        def _g(widget, **kw):
            """grid с возвратом виджета."""
            widget.grid(**kw)
            return widget

        def _p(widget, **kw):
            """pack с возвратом виджета."""
            widget.pack(**kw)
            return widget

        # --- верхняя строка: пути + кнопки "…" ----------------------------- #
        top = ttk.Frame(main_frame)
        top.pack(fill="x")

        self._w_folder_label = _g(ttk.Label(top, text="Папка:"),
                                  row=0, column=0, sticky="w")
        self.var_folder = tk.StringVar(value=cfg.get("source_folder", ""))
        self._w_folder = _g(ttk.Entry(top, textvariable=self.var_folder),
                            row=0, column=1, sticky="ew", padx=(6, 2))
        self._w_folder_btn = _g(ttk.Button(top, text="…", width=3,
                                           command=self.pick_folder),
                                row=0, column=2)

        self._w_repo_label = _g(ttk.Label(top, text="Ссылка репо:"),
                                row=1, column=0, sticky="w", pady=(6, 0))
        self.var_repo = PlaceholderEntry(top, placeholder="https://github.com/user/repo.git")
        if cfg.get("repository"):
            self.var_repo.set(cfg.get("repository"))
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
            cfg.get("git_timeout_min", 30)))
        self.spn_timeout = ttk.Spinbox(self._w_tools_row, from_=1, to=60, width=4,
                                       textvariable=self.var_timeout,
                                       command=self._on_settings_change)
        self.spn_timeout.pack(side="left", padx=(2, 0))

        self._w_download_label = _g(ttk.Label(top, text="Папка выгрузки:"),
                                    row=3, column=0, sticky="w", pady=(6, 0))
        self.var_download = tk.StringVar(value=cfg.get("download_folder", ""))
        self._w_download = _g(ttk.Entry(top, textvariable=self.var_download),
                              row=3, column=1, sticky="ew", padx=(6, 2), pady=(6, 0))
        self._w_download_btn = _g(ttk.Button(top, text="…", width=3,
                                             command=self.pick_download_folder),
                                  row=3, column=2, pady=(6, 0))

        # --- доп. поля: ветка (combobox) / сообщение / push ----------------- #
        self.var_branch = tk.StringVar(value=cfg.get("branch", "main"))
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

        self.var_message = tk.StringVar(value=cfg.get("commit_message", ""))
        self._w_message_label = _g(ttk.Label(top, text="Сообщение:"),
                                   row=5, column=0, sticky="w", pady=(6, 0))
        self._w_message = _g(ttk.Entry(top, textvariable=self.var_message),
                             row=5, column=1, columnspan=2, sticky="ew",
                             padx=(6, 0), pady=(6, 0))

        self.var_push = tk.BooleanVar(value=bool(cfg.get("push")))
        self._w_push_chk = _g(ttk.Checkbutton(top, text="push после коммита",
                                              variable=self.var_push,
                                              command=self._on_settings_change),
                              row=6, column=1, sticky="w", padx=(6, 0), pady=(6, 0))

        top.columnconfigure(1, weight=1)

        # --- большая кнопка КОММИТ ------------------------------------------ #
        btn_frame = ttk.Frame(main_frame)
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
            main_frame,
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

        tools_row = ttk.Frame(main_frame)
        _p(tools_row, fill="x")
        self._w_tools_git = tools_row
        ttk.Button(tools_row, text="Откатить последний",
                   command=self.on_revert_last).pack(side="left")
        ttk.Button(tools_row, text="Создать тег",
                   command=self.on_create_tag).pack(side="left", padx=(6, 0))

        # --- авто-режимы ------------------------------------------------------ #
        auto_frame = ttk.LabelFrame(main_frame, text="Авто-режимы", padding=8)
        auto_frame.pack(fill="x", pady=(7, 0))

        self.var_auto_commit = tk.BooleanVar(value=bool(cfg.get("auto_commit")))
        self.var_auto_clone = tk.BooleanVar(value=bool(cfg.get("auto_clone")))

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
            cfg.get("auto_commit_interval_min")
            or cfg.get("auto_interval_min", 5)))
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
            cfg.get("auto_clone_interval_min")
            or cfg.get("auto_interval_min", 5)))
        ttk.Spinbox(auto_frame, from_=1, to=60, width=4, textvariable=self.var_cl,
                    command=lambda: self._on_interval_change("download"))\
            .grid(row=1, column=4, sticky="w", padx=(2, 0), pady=(4, 0))

        # общий интервал (fallback)
        ttk.Label(auto_frame, text="общий интервал, мин:").grid(
            row=2, column=3, sticky="e", pady=(4, 0))
        self.var_ai = tk.IntVar(value=self._clamp_interval(
            cfg.get("auto_interval_min", 5)))
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
        self._pause_lbl_shown = False
        self.var_auto_push = tk.BooleanVar(value=bool(cfg.get("auto_push")))
        ttk.Checkbutton(pause_row, text="Push после авто-коммита",
                        variable=self.var_auto_push,
                        command=self._on_settings_change)\
            .pack(side="left", padx=(10, 0))

        self.var_watch = tk.BooleanVar(value=bool(cfg.get("watch_source")))
        ttk.Checkbutton(auto_frame, text="Реагировать на изменения файлов",
                        variable=self.var_watch,
                        command=self._on_toggle_watch)\
            .grid(row=3, column=0, columnspan=3, sticky="w", pady=(4, 0))

        # Расписание авто-задач
        sched = cfg.get("auto_schedule", Config.defaults()["auto_schedule"])
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
            var_day = tk.BooleanVar(value=(i + 1) in days)
            self.day_vars.append(var_day)
            ttk.Checkbutton(day_row, text=name, variable=var_day,
                            command=self._on_settings_change).grid(row=0, column=i,
                                                                   padx=2)

        auto_frame.columnconfigure(1, weight=1)

        # --- блок чекбоксов безопасности/вида ------------------------------- #
        self._w_checks = _p(ttk.LabelFrame(main_frame, text="Режимы", padding=8),
                            fill="x", pady=(7, 0))
        grid_checks = [
            ("dry_run", "Только показать (dry-run)"),
            ("backup_before_download", "Бэкап целевой папки"),
            ("confirm_delete_extras", "Спрашивать перед удалением лишних"),
            ("sound_on_finish", "Звук после задачи"),
        ]
        self.var_checks = {}
        for i, (key, label) in enumerate(grid_checks):
            var_cb = tk.BooleanVar(value=bool(cfg.get(key)))
            self.var_checks[key] = var_cb
            ttk.Checkbutton(self._w_checks, text=label, variable=var_cb,
                            command=self._on_settings_change)\
                .grid(row=i // 2, column=i % 2, sticky="w", padx=6, pady=2)

        # --- нижняя строка: статус + маленькая кнопка "..." (открыть конфиг) #
        bottom = ttk.Frame(main_frame)
        bottom.pack(fill="x", pady=(10, 0))

        self.var_status = tk.StringVar(value="Готов.")
        ttk.Label(bottom, textvariable=self.var_status,
                  foreground="#555").pack(side="left", fill="x", expand=True)

        ttk.Button(bottom, text="…", width=4,
                   command=self.open_config).pack(side="right")

        # лог последних действий
        self.log_panel = LogPanel(main_frame)
        _p(self.log_panel.text, fill="x", pady=(10, 0))
        self._w_log = self.log_panel.text

        # контекстные меню на полях ввода (ПКМ)
        self._entry_menu = self._build_entry_menu()
        for w in (self._w_folder, self.var_repo, self._w_download,
                  self.cmb_branch):
            # ПКМ: Windows/Linux — Button-3; macOS — Button-2 или Ctrl+ЛКМ
            for seq in ("<Button-3>", "<Button-2>", "<Control-Button-1>"):
                w.bind(seq, self._show_entry_menu)

    # ================================================================== #
    #  Привязка: валидация, протоколы, watcher                             #
    # ================================================================== #

    def _wire(self):
        self._setup_validation()
        self.root.protocol("WM_DELETE_WINDOW", self._on_close_window)
        if self.var_watch.get():
            self._start_watcher()

    def _start_tick(self):
        # единый таймер главного потока (1 раз в секунду)
        self.root.after(1000, self._tick)
        # периодический счётчик изменений (первый — через 5 с, далее 30 с)
        self.root.after(5000, self._maybe_count_changes)

    # ================================================================== #
    #  Лог / статус / конфиг                                              #
    # ================================================================== #

    def log(self, text: str) -> None:
        self.log_panel.append(text)

    def set_status(self, text: str) -> None:
        self.var_status.set(text)

    def _interval_minutes(self, mode: Optional[str] = None) -> int:
        # Интервалы читаем с диска — ручные правки в config.json
        # подхватываются без перезапуска приложения.
        try:
            probe = Config(config_path())
            probe.load()
            disk = probe.as_dict()
        except Exception:                                    # noqa: BLE001
            disk = self.cfg.as_dict()

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

    def _collect_cfg(self) -> None:
        """Сохраняем пользовательские поля обратно в конфиг (через Config)."""
        self.cfg.set("source_folder", self.var_folder.get().strip())
        self.cfg.set("repository", self.var_repo.get().strip())
        self.cfg.set("download_folder", self.var_download.get().strip())
        self.cfg.set("branch", self.var_branch.get().strip() or "main")
        self.cfg.set("commit_message",
                     self.var_message.get() or "Автокоммит: {datetime}")
        self.cfg.set("push", bool(self.var_push.get()))
        self.cfg.set("auto_commit", bool(self.var_auto_commit.get()))
        self.cfg.set("auto_clone", bool(self.var_auto_clone.get()))
        self.cfg.set("git_timeout_min", self._clamp_timeout(self.var_timeout.get()))
        self.cfg.set("auto_interval_min", self._clamp_interval(self.var_ai.get()))
        self.cfg.set("auto_commit_interval_min",
                     self._clamp_interval(self.var_ci.get()))
        self.cfg.set("auto_clone_interval_min",
                     self._clamp_interval(self.var_cl.get()))
        for key, var in self.var_checks.items():
            self.cfg.set(key, bool(var.get()))
        self.cfg.set("watch_source", bool(self.var_watch.get()))
        self.cfg.set("auto_push", bool(self.var_auto_push.get()))
        self.cfg.set("auto_schedule", {
            "enabled": bool(self.var_sched.get()),
            "from": self.var_sched_from.get().strip() or "09:00",
            "to": self.var_sched_to.get().strip() or "18:00",
            "days": [i + 1 for i, v in enumerate(self.day_vars) if v.get()],
        })
        self.cfg.save()

    def _on_settings_change(self) -> None:
        try:
            self._collect_cfg()
        except Exception as exc:                             # noqa: BLE001
            self.log(f"Не удалось сохранить настройки: {exc}")

    def pick_folder(self) -> None:
        folder = filedialog.askdirectory(title="Папка, откуда коммитим",
                                         initialdir=self.var_folder.get() or ".")
        if folder:
            self.var_folder.set(folder)
            self._collect_cfg()

    def pick_download_folder(self) -> None:
        folder = filedialog.askdirectory(title="Папка выгрузки из репо",
                                         initialdir=self.var_download.get()
                                         or self.var_folder.get() or ".")
        if folder:
            self.var_download.set(folder)
            self._collect_cfg()

    def paste_repo_url(self) -> None:
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

    def open_config(self) -> None:
        """Маленькая кнопка с троеточием внизу — открыть файл конфига."""
        self._collect_cfg()
        path = config_path()
        if not path.exists():
            self.cfg.save()
        self._open_in_editor(path)
        self.set_status(f"Конфиг открыт: {path.name}")

    @staticmethod
    def _open_in_editor(path: Path) -> None:
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

    # ================================================================== #
    #  Валидация в реальном времени                                       #
    # ================================================================== #

    def _setup_validation(self) -> None:
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

    def _field_value(self, kind) -> str:
        if kind == "folder":
            return self.var_folder.get().strip()
        if kind == "repo":
            return self.var_repo.get().strip()
        if kind == "download":
            return self.var_download.get().strip()
        return ""

    def _field_widget(self, kind) -> Any:
        if kind == "folder":
            return self._w_folder
        if kind == "repo":
            return self.var_repo
        return self._w_download

    def _validate_field(self, kind) -> bool:
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
                # getattr(..., False): у ttk.Entry нет _showing_ph — только
                # PlaceholderEntry показывает плейсхолдер
                widget.configure(
                    foreground="#c62828" if reason else
                    (PlaceholderEntry.GRAY if getattr(widget, "_showing_ph", False)
                     else PlaceholderEntry.BLACK))
            else:
                widget.configure(
                    foreground="#c62828" if reason else PlaceholderEntry.BLACK)
        except tk.TclError:
            pass
        if tip:
            tip.set(reason)
        return not reason

    # ================================================================== #
    #  Контекстное меню полей                                             #
    # ================================================================== #

    def _build_entry_menu(self) -> Any:
        menu = tk.Menu(self.root, tearoff=0)
        menu.add_command(label="Вставить", command=self._ctx_paste)
        menu.add_command(label="Копировать путь", command=self._ctx_copy)
        menu.add_command(label="Открыть в проводнике", command=self._ctx_open)
        menu.add_command(label="Очистить", command=self._ctx_clear)
        return menu

    def _show_entry_menu(self, event) -> None:
        w = event.widget
        try:
            self._ctx_target = w
            self._entry_menu.tk_popup(event.x_root, event.y_root)
        finally:
            self._entry_menu.grab_release()

    def _ctx_get(self) -> str:
        target = self._ctx_target
        if target is None:
            return ""
        # getattr(..., False) — на случай виджета без механизма плейсхолдера
        if getattr(target, "_showing_ph", False):
            return ""
        return target.get()

    def _ctx_set(self, value) -> None:
        if self._ctx_target is None:
            return
        self._ctx_target.set(value)
        self._on_settings_change()

    def _ctx_paste(self) -> None:
        try:
            text = self.root.clipboard_get()
        except tk.TclError:
            return
        cur = self._ctx_get()
        self._ctx_set(cur + text.strip())

    def _ctx_copy(self) -> None:
        text = self._ctx_get()
        if text:
            self.root.clipboard_clear()
            self.root.clipboard_append(text)
            self.set_status("Скопировано в буфер обмена")

    def _ctx_open(self) -> None:
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

    def _ctx_clear(self) -> None:
        self._ctx_set("")

    # ================================================================== #
    #  Фоновые задачи (TaskRunner + queue)                                #
    # ================================================================== #

    def _start_bg(self, kind: str, fn: Callable[..., Any], *args: Any) -> bool:
        """Запускает задачу в фоновом потоке. False, если уже занято.

        Фоновые задачи получают СНИМОК конфига (cfg.as_dict()), а не сам
        Config — иначе гонка при save().
        """
        # Фоновые задачи (кроме интерактивных commit/download) выполняются
        # молча: не трогают кнопки и статус, чтобы не мешать авто-режимам.
        quiet = kind in ("count", "branches", "test-conn")
        if not quiet:
            self._set_busy_status("Выполняется задача…")
        cfg_snapshot = self.cfg.as_dict()
        # История пишется read-modify-write поверх файла, поэтому снимок
        # дополнительно подтягивает актуальные значения ключей с диска —
        # иначе рабочий поток затёр бы свежие настройки GUI.
        try:
            probe = Config(config_path())
            probe.load()
            disk_cfg = probe.as_dict()
        except Exception:                                   # noqa: BLE001
            disk_cfg = {}
        for key in Config.defaults():
            if key == "history":
                continue
            if key in disk_cfg:
                cfg_snapshot[key] = disk_cfg[key]

        def _runner(log: Callable[[str], None], *extra: Any) -> Any:
            return fn(cfg_snapshot, log, *extra)

        if not self.tasks.start(kind, _runner, *args):
            return False
        self._refresh_buttons()
        self._poll_results()
        return True

    def _poll_results(self) -> None:
        """Выбирает события TaskRunner и печатает их в главном потоке Tk.

        Очередь TaskRunner читает ТОЛЬКО этот метод (периодический опрос);
        _drain_events из тика умеет лишь возвращать done/error обратно в
        очередь — двух потребителей одной очереди быть не должно, иначе
        событие обработает тот, кто дёрнул poll() первым.
        """
        finished = None  # ("done"|"error", text)
        for kind, text in self.tasks.poll():
            if kind == "log":
                self.log(text)
            elif kind == "watch":
                self._handle_watch()           # watcher обслуживается и здесь
            elif kind in ("done", "error"):
                finished = (kind, text)
        if finished is not None:
            kind, text = finished
            task = self.tasks.current_task or getattr(self, "_last_kind", None)
            self._finish(kind, text, task,
                         interactive=self._is_interactive(task))
            # Дочитываем оставшиеся сообщения — отложенным вызовом,
            # чтобы не перерисовывать UI посреди порции событий.
            self.root.after(0, self._poll_results)
        elif self.tasks.busy:
            self.root.after(100, self._poll_results)

    @staticmethod
    def _is_interactive(task: Optional[str]) -> bool:
        """Задачи по клику: их ошибки показывают messagebox."""
        return task in ("commit", "download", "test-conn", "branches",
                        "revert", "tag")

    def _finish(self, kind: str, text: Any, task: Optional[str],
                interactive: bool) -> None:
        # Сброс busy — в начале обработки: рабочий поток уже завершился,
        # а до _finish событие done/error из очереди никто не заберёт.
        self.tasks.busy = False
        self._last_kind = task
        self._refresh_buttons()
        if kind == "error":
            if task == "count":
                # фоновый счётчик — молча, но помечаем к пересчёту
                self._count_dirty = True
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
                    self.notifier.play_beep()

    def _refresh_buttons(self) -> None:
        state = "normal" if not self.tasks.busy else "disabled"
        self.btn_commit.configure(
            state=state,
            bg="#1f8b4c" if not self.tasks.busy else "#9e9e9e",
            fg="white")
        self.btn_download.configure(
            state=state,
            bg="#2b6cb0" if not self.tasks.busy else "#9e9e9e",
            fg="white")
        for b in (getattr(self, "btn_test_conn", None),
                  getattr(self, "btn_branches", None)):
            if b is not None:
                b.configure(state=state)

    # ================================================================== #
    #  Прямые процессы                                                    #
    # ================================================================== #

    def on_commit(self) -> None:
        if self.tasks.busy:
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
        self._start_bg("commit", self.service.commit)

    def on_download(self) -> None:
        if self.tasks.busy:
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
        self._start_bg("download", self.service.download, None)

    def _set_busy_status(self, text: str) -> None:
        # Только статус/кнопки; флаг busy ставит TaskRunner.
        self.set_status(text)
        self._refresh_buttons()

    # ================================================================== #
    #  Тест соединения / список веток                                     #
    # ================================================================== #

    def on_test_connection(self) -> None:
        if self.tasks.busy:
            return
        self._collect_cfg()
        repo = str(self.cfg.get("repository", "")).strip()
        if not is_repo_url(repo):
            messagebox.showinfo(APP_TITLE,
                                "Сначала укажите корректную ссылку на репозиторий.")
            return
        self._set_busy_status("Проверяю соединение с репозиторием…")
        timeout_s = min(GitRunner.net_timeout(self.cfg.as_dict()), 30)

        def _test(_cfg: Any, _log: Any) -> str:
            return self.service.test_remote(repo, timeout_s)
        self._start_bg("test-conn", _test)

    def on_refresh_branches(self) -> None:
        if self.tasks.busy:
            return
        self._collect_cfg()
        if not is_repo_url(str(self.cfg.get("repository", "")).strip()):
            messagebox.showinfo(APP_TITLE,
                                "Сначала укажите корректную ссылку на репозиторий.")
            return
        self._set_busy_status("Читаю список веток…")

        def _branches(_cfg: Any, _log: Any) -> list:
            return self.service.list_branches(_cfg)
        self._start_bg("branches", _branches)

    def _apply_branch_list(self, names) -> None:
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

    # ================================================================== #
    #  Откат последнего коммита / теги                                    #
    # ================================================================== #

    def on_revert_last(self) -> None:
        if self.tasks.busy:
            return
        self._collect_cfg()
        if not is_repo_url(str(self.cfg.get("repository", "")).strip()):
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

        def _revert(_cfg: Any, _log: Any) -> str:
            return self.service.reset_last(_cfg, mode)
        self._set_busy_status(f"Откатываю последний коммит ({mode})…")
        self._start_bg("revert", _revert)

    def on_create_tag(self) -> None:
        if self.tasks.busy:
            return
        self._collect_cfg()
        if not is_repo_url(str(self.cfg.get("repository", "")).strip()):
            messagebox.showinfo(APP_TITLE, "Сначала укажите ссылку на репозиторий.")
            return
        dlg = self._tag_dialog()
        if dlg is None:
            return
        name, annotation, push_tag = dlg

        def _tag(_cfg: Any, _log: Any) -> str:
            return self.service.tag(_cfg, name, annotation, push_tag)
        self._set_busy_status(f"Создаю тег {name}…")
        self._start_bg("tag", _tag)

    def _tag_dialog(self) -> Any:
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
            if not name or not re.match(r"^\w[\w./-]*$", name):
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

    # ================================================================== #
    #  Счётчик изменений на кнопке                                        #
    # ================================================================== #

    def _maybe_count_changes(self) -> None:
        """Периодически (раз в ~30 с) считает git status --porcelain в фоне."""
        try:
            if (self._count_dirty and not self.tasks.busy
                    and is_repo_url(str(self.cfg.get("repository", "")).strip())):
                self._count_dirty = False
                self._start_bg("count", self.service.count_changes)
        finally:
            self.root.after(30000, self._maybe_count_changes)

    def _apply_change_count(self, n) -> None:
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

    # ================================================================== #
    #  Авто-режимы (через AutoScheduler)                                  #
    # ================================================================== #

    def _toggle_auto(self, mode: str) -> None:
        """Чекбокс включён — планируем (НЕ запускаем сразу); выключен — сброс."""
        var = self.var_auto_commit if mode == "commit" else self.var_auto_clone
        enabled = bool(var.get())
        self.scheduler.toggle(mode, enabled)
        if enabled:
            self.log(f"{self.AUTO_LABELS[mode]}: включён, "
                     f"интервал {self._interval_minutes(mode)} мин.")
        else:
            lbl = (self.lbl_next_commit if mode == "commit"
                   else self.lbl_next_download)
            lbl.configure(text="—")
            self.log(f"{self.AUTO_LABELS[mode]}: выключен.")
        try:
            self._collect_cfg()
        except Exception as exc:                               # noqa: BLE001
            self.log(f"Не удалось сохранить настройки: {exc}")

    def _on_interval_change(self, mode) -> None:
        """Спинбоксы интервалов: общий и индивидуальные."""
        try:
            self._collect_cfg()
        except Exception as exc:                               # noqa: BLE001
            self.log(f"Не удалось сохранить настройки: {exc}")
            return
        for m in (("commit", "download") if mode is None else (mode,)):
            if self.scheduler.is_enabled(m):
                self.scheduler.schedule(m, enable=False)
        self.log(f"Интервалы: общий {self.var_ai.get()} мин, "
                 f"коммит {self.var_ci.get()}, клон {self.var_cl.get()}.")

    def _run_auto_now(self, mode: str) -> None:
        """Кнопка «Сейчас» — немедленный запуск в фоне + перепланировка."""
        self.scheduler.run_now(mode)

    def _launch_auto(self, mode: str) -> bool:
        """Колбэк AutoScheduler: запуск авто-задачи. True — задача пошла."""
        if self.tasks.busy:
            self.log(f"{self.AUTO_LABELS[mode]}: пропуск — другая задача выполняется.")
            if self.scheduler.is_enabled(mode):
                self.scheduler.schedule(mode, enable=False)   # сдвигаем
            return False
        self._collect_cfg()
        if not self._auto_can_run(mode):
            self.log(f"{self.AUTO_LABELS[mode]}: пропуск — нет ссылки на репо или папки.")
            if self.scheduler.is_enabled(mode):
                self.scheduler.schedule(mode, enable=False)
            return False
        # «Сейчас» НЕ включает авто-режим: перепланируем таймер только если
        # он уже включён чекбоксом (enable=False при выключенном).
        self.scheduler.schedule(mode, enable=self.scheduler.is_enabled(mode))
        if mode == "commit":
            self.set_status("Авто-коммит: выполняем…")
            return self._start_bg("auto-commit", self.service.commit, True)
        self.set_status("Авто-клон: выполняем…")
        return self._start_bg("auto-download", self.service.download, None)

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

    # ---- расписание ----------------------------------------------------- #

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

    # ---- пауза ----------------------------------------------------------- #

    def toggle_pause(self) -> None:
        if self.scheduler.is_paused():
            self.scheduler.resume()
            self.log("Пауза авто-режимов снята.")
        else:
            self.scheduler.pause_for(60)
            until = self.scheduler.paused_until
            self.log(f"Авто-режимы на паузе до {until.strftime('%H:%M')}.")
        self._update_pause_button()

    def _update_pause_button(self) -> None:
        active = self.scheduler.is_paused()
        try:
            self.btn_pause.configure(text="Снять паузу" if active else "Пауза 1 ч")
        except tk.TclError:
            pass

    # ---- watcher файлов --------------------------------------------------- #

    def _on_toggle_watch(self) -> None:
        if self.var_watch.get():
            if not _HAS_WATCHDOG:
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

    def _start_watcher(self) -> None:
        if not _HAS_WATCHDOG:
            self.log("watchdog не установлен — watcher не запущен "
                     "(pip install watchdog).")
            return
        self._stop_watcher()
        self._watch_stop = threading.Event()
        stop = self._watch_stop

        def _thread():
            try:
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
                self.tasks.put("log", f"Watcher остановлен: {exc}")
        self._watch_thread = threading.Thread(target=_thread, daemon=True)
        self._watch_thread.start()
        self.log("Watcher за файлами папки запущен (дебаунс 30 с).")

    def _stop_watcher(self) -> None:
        if self._watch_stop is not None:
            self._watch_stop.set()
            self._watch_stop = None
        self._watch_thread = None

    def _on_watch_event(self) -> None:
        # Из фонового потока observer'а — только в очередь GUI.
        self.tasks.put("watch", None)

    def _handle_watch(self) -> None:
        """Событие watcher'а: старт дебаунс-окна (30 с тишины).

        Watcher приоритетнее таймера: из-за активности файлов таймер
        авто-коммита постоянно сдвигается, а коммит выполняется после
        30 секунд тишины (_tick_inner -> _fire_watch_commit).
        """
        self._last_watch_event = datetime.now().timestamp()
        if self.scheduler.is_enabled("commit"):
            # сдвигаем плановый запуск таймера — приоритет у watcher'а
            self.scheduler.schedule("commit", enable=False)

    def _fire_watch_commit(self) -> None:
        """Дебаунс-окно закрыто (30 с без изменений) — авто-коммит."""
        if self.tasks.busy or not self.var_watch.get():
            return
        self._collect_cfg()
        if not self._auto_can_run("commit"):
            return
        if not self._in_schedule(datetime.now()):
            return
        self.log("Watcher: изменения файлов (30 с тишины) — авто-коммит.")
        self.scheduler.schedule("commit",
                                enable=self.scheduler.is_enabled("commit"))
        self.set_status("Watcher: авто-коммит…")
        self._start_bg("auto-commit", self.service.commit, True)

    # ---- основной тик ----------------------------------------------------- #

    def _tick(self) -> None:
        """Единый таймер главного потока: 1 раз в секунду."""
        try:
            self._drain_events()
            self._tick_inner()
        finally:
            self.root.after(1000, self._tick)

    def _drain_events(self) -> None:
        """Выборка неблокирующих событий из очереди (watch, log).

        done/error НЕ потребляются: единственный читатель этих событий —
        _poll_results. Чтобы тик не «съедал» завершение задачи, done/error
        возвращаются в хвост очереди (put) и будут выбраны _poll_results.
        """
        deferred: list[tuple[str, Any]] = []
        for kind, payload in self.tasks.poll():
            if kind == "watch":
                self._handle_watch()
            elif kind == "log":
                self.log(payload)
            else:  # done/error/branches — вернём в очередь для _poll_results
                deferred.append((kind, payload))
        for ev in deferred:
            self.tasks.put(ev[0], ev[1])

    def _tick_inner(self) -> None:
        now = datetime.now()

        # дебаунс watcher'а: 30 с тишины -> авто-коммит
        if (self.var_watch.get() and self._last_watch_event
                and now.timestamp() - self._last_watch_event >= 30):
            self._last_watch_event = 0.0
            self._fire_watch_commit()

        # пауза
        paused = self.scheduler.is_paused()
        self._update_pause_button()
        if paused:
            self.lbl_pause.configure(
                text=f"пауза до {self.scheduler.paused_until.strftime('%H:%M')}")
        elif self._pause_lbl_shown:
            self.lbl_pause.configure(text="")
        self._pause_lbl_shown = paused

        # индикаторы «следующий через MM:SS» / «вне расписания»
        in_sched = self._in_schedule(now)
        for mode, lbl in (("commit", self.lbl_next_commit),
                          ("download", self.lbl_next_download)):
            secs = self.scheduler.next_in(mode)
            if paused:
                lbl.configure(text="пауза")
            elif not self.scheduler.is_enabled(mode) or secs is None:
                lbl.configure(text="—")
            elif not in_sched:
                lbl.configure(text="вне расписания")
            else:
                lbl.configure(text=f"следующий через {secs // 60:02d}:{secs % 60:02d}")

        if paused or not in_sched:
            return

        due = self.scheduler.tick()   # приоритет: авто-клон первый
        for mode in due:
            if self.tasks.busy:
                # задача идёт — пропускаем и сдвигаем запуск
                self.scheduler.schedule(mode, enable=False)
                self.log(f"{self.AUTO_LABELS[mode]}: пропуск (занято), сдвиг таймера.")
                continue
            if self._launch_auto(mode):
                break  # один запуск за тик; второй авто — следующим тиком/по плану

    # ================================================================== #
    #  Закрытие окна                                                      #
    # ================================================================== #

    def _on_close_window(self) -> None:
        self._quit_app()

    def _quit_app(self) -> None:
        self._force_quit = True
        self._stop_watcher()
        try:
            self._collect_cfg()
        except Exception:                                    # noqa: BLE001
            pass
        self.root.destroy()


CommitterApp = MainWindow     # псевдоним эпохи v2


# --------------------------------------------------------------------------- #
#  main                                                                        #
# --------------------------------------------------------------------------- #

def main() -> None:
    if tk is None:
        sys.exit(
            "Tkinter недоступен (" + _TK_ERROR_TEXT + ").\n"
            "Установите tk/tcl: Linux — «apt install python3-tk» / «pacman -S tk», "
            "на Windows и macOS tkinter входит в официальный установщик Python."
        )
    _setup_file_logging()
    # Проверка git ДО создания основного окна.
    ok, ver = check_git()
    if not ok:
        # Временное скрытое окно — только чтобы показать messagebox.
        tmp = tk.Tk()
        tmp.withdraw()
        messagebox.showerror(
            APP_TITLE,
            "Git не найден в системе.\n\n"
            "Установите git (git-scm.com) и перезапустите приложение.")
        tmp.destroy()
        sys.exit(1)
    assert tk is not None
    root = tk.Tk()
    app = MainWindow(root)
    if isinstance(ver, tuple) and len(ver) == 2:
        if ver < GIT_MIN_VERSION:
            app.log(f"ВНИМАНИЕ: версия git {ver[0]}.{ver[1]} ниже "
                    f"рекомендованной {GIT_MIN_VERSION[0]}.{GIT_MIN_VERSION[1]} "
                    "— возможны проблемы.")
        else:
            app.log(f"git {ver[0]}.{ver[1]} — OK")
    elif ver:
        app.log(str(ver[0]) if isinstance(ver, tuple) else ver)
    root.mainloop()


if __name__ == "__main__":
    main()
