#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Git Committer — маленькое GUI-приложение (Tkinter), которое коммитит изменения
из указанной папки в выбранный репозиторий.

Особенности:
  * Одна большая кнопка «КОММИТ».
  * Маленькая кнопка с троеточием «...» — открывает файл конфигурации config.json.
  * Конфигурация генерируется автоматически при первом запуске и хранит все
    изменения (путь к папке, путь/адрес репозитория, ветка, автор, сообщение).
  * От пользователя требуется только указать: папку откуда коммитить и репозиторий.

Запуск:  python git_committer.py
Зависимости: только стандартная библиотека Python + установленный git.
"""

import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile
import threading
from datetime import datetime
from pathlib import Path

try:
    import tkinter as tk
    from tkinter import filedialog, messagebox, ttk

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
                self._showing_ph = False
                self.configure(foreground=self.BLACK)
                self.var.set(value)
            else:
                self._show_placeholder()

        def _show_placeholder(self):
            self._showing_ph = True
            self.var.set(self.placeholder)
            self.configure(foreground=self.GRAY)

        def _hide_placeholder(self):
            if self._showing_ph:
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
    """Каталог, где живёт конфиг (рядом со скриптом)."""
    try:
        base = Path(__file__).resolve().parent
    except NameError:                      # интерактивный режим / frozen
        base = Path.cwd()
    return base


def config_path() -> Path:
    return config_dir() / CONFIG_NAME


def default_config() -> dict:
    """Конфиг по умолчанию — генерируется сам, без вмешательства пользователя."""
    return {
        "source_folder": str(Path.home()),          # папка, откуда коммитим
        "repository": "",                           # ССЫЛКА на репозиторий (URL)
        "branch": "main",                           # ветка для коммита
        "commit_message": "Автокоммит: {datetime}", # подстрока {datetime} подставится сама
        "author_name": "Git Committer",             # локальный автор коммита
        "author_email": "committer@local",
        "push": False,                              # пушить ли после коммита
        "history": [],                              # последние удачные коммиты
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
    except (json.JSONDecodeError, OSError):
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
    return data


def save_config(cfg: dict) -> None:
    path = config_path()
    tmp_fd, tmp_name = tempfile.mkstemp(dir=str(path.parent), suffix=".tmp")
    try:
        with os.fdopen(tmp_fd, "w", encoding="utf-8") as f:
            json.dump(cfg, f, ensure_ascii=False, indent=2)
        os.replace(tmp_name, path)
    finally:
        if os.path.exists(tmp_name):
            os.remove(tmp_name)


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


def run_git(args, cwd=None):
    """Запуск git с захватом вывода. Бросает GitError при ненулевом коде."""
    try:
        proc = subprocess.run(
            ["git", *args],
            cwd=str(cwd) if cwd else None,
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
        )
    except FileNotFoundError:
        raise GitError("Команда «git» не найдена в системе. Установите git.")
    if proc.returncode != 0:
        raise GitError((proc.stderr or proc.stdout or "").strip()
                       or f"git {' '.join(args)} завершился с ошибкой")
    return (proc.stdout or "").strip()


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
    digest = hashlib.sha1(repo_url.encode("utf-8")).hexdigest()[:8]
    name = re.sub(r"[^\w.-]", "_", Path(repo_url.rstrip("/")).name) or "repo"
    if name.endswith(".git"):
        name = name[:-4]
    return config_dir() / f"repo_{name}_{digest}"


def ensure_repo_layout(cfg: dict) -> Path:
    """
    Подготавливает рабочую область по ССЫЛКЕ на репозиторий:
      * repository — URL (https/git/ssh/file:// или путь .git);
      * клонируем в подпапку ./repo_<имя>_<hash>, если её ещё нет;
      * если есть — fetch/checkout/pull, чтобы быть в актуальном состоянии.
    Возвращает Path к рабочей копии репозитория.
    """
    repo = cfg.get("repository", "").strip()
    source = cfg.get("source_folder", "").strip()
    if not repo:
        raise GitError("Вставьте ссылку на репозиторий (ключ «repository» в конфиге), "
                       "например https://github.com/user/repo.git")
    if not source or not Path(source).is_dir():
        raise GitError(f"Папка-источник не существует: {source}")

    if not is_repo_url(repo):
        raise GitError(
            f"«{repo}» не похоже на ссылку на репозиторий.\n"
            "Поддерживаются: https://…, http://…, git://…, ssh://…, "
            "git@host:user/repo.git, file:///… или путь, оканчивающийся на .git")

    local = local_clone_dir(repo)
    branch = cfg.get("branch", "main")

    if not (local / ".git").is_dir():
        run_git(["clone", repo, str(local)])
    else:
        run_git(["fetch", "origin"], cwd=local)

    # Аккуратно переключаемся на нужную ветку, сохраняя незакоммиченное.
    current = ""
    try:
        current = run_git(["rev-parse", "--abbrev-ref", "HEAD"], cwd=local)
    except GitError:
        pass
    if current != branch:
        try:
            run_git(["checkout", branch], cwd=local)
        except GitError:
            try:
                run_git(["checkout", "-b", branch, f"origin/{branch}"], cwd=local)
            except GitError:
                run_git(["checkout", "-B", branch], cwd=local)  # новая локальная ветка
    # Подтягиваем изменения с remote только если рабочая копия чистая —
    # иначе наши прошлые незапушенные коммиты/файлы останутся как есть.
    if not run_git(["status", "--porcelain"], cwd=local):
        try:
            run_git(["pull", "--ff-only", "origin", branch], cwd=local)
        except GitError:
            pass
    return local


def sync_source_into_repo(source: Path, workdir: Path) -> int:
    """Копирует содержимое папки-источника в рабочую копию репозитория."""
    import shutil
    count = 0
    for item in source.iterdir():
        if item.name == ".git":
            continue
        dest = workdir / item.name
        if item.is_dir():
            if dest.exists():
                shutil.rmtree(dest)
            shutil.copytree(item, dest)
        else:
            shutil.copy2(item, dest)
        count += 1
    return count


def commit_all(cfg: dict, log) -> str:
    """Главная операция: синхронизация + add + commit (+ push при желании)."""
    workdir = ensure_repo_layout(cfg)
    source = Path(cfg["source_folder"]).expanduser()

    # Не копируем репозиторий сам в себя (защита от ручного конфига).
    try:
        same = source.resolve() == workdir.resolve()
    except OSError:
        same = False
    if same:
        raise GitError("Папка-источник и рабочая копия репозитория совпадают. "
                       "Укажите отдельную папку для файлов.")
    n = sync_source_into_repo(source, workdir)
    log(f"Синхронизировано объектов из папки: {n}")

    branch = cfg.get("branch", "main")
    try:
        run_git(["rev-parse", "--verify", branch], cwd=workdir)
        run_git(["checkout", branch], cwd=workdir)
    except GitError:
        # новой ветки ещё нет в истории — создаём её от текущего коммита;
        # незакоммиченные изменения (синхронизированные файлы) сохраняются
        run_git(["checkout", "-b", branch], cwd=workdir)

    run_git(["add", "-A"], cwd=workdir)

    status = run_git(["status", "--porcelain"], cwd=workdir)
    if not status:
        log("Нечего коммитить — изменений нет.")
        return ""

    message = cfg.get("commit_message", "Автокоммит")
    message = message.replace("{datetime}",
                              datetime.now().strftime("%Y-%m-%d %H:%M:%S"))

    author = cfg.get("author_name", "").strip()
    email = cfg.get("author_email", "").strip()
    git_args = ["commit", "-m", message]
    if author and email:
        git_args += ["--author", f"{author} <{email}>"]
    out = run_git(git_args, cwd=workdir)
    log(out.splitlines()[-1] if out else "Коммит создан.")

    sha = run_git(["rev-parse", "--short", "HEAD"], cwd=workdir)

    if cfg.get("push"):
        remote_exists = False
        try:
            remotes = run_git(["remote"], cwd=workdir)
            remote_exists = "origin" in remotes.split()
        except GitError:
            pass
        if remote_exists:
            run_git(["push", "-u", "origin", branch], cwd=workdir)
            log(f"Запушено в origin/{branch}")
        else:
            log("Внимание: remote 'origin' отсутствует — push пропущен.")

    # Записываем историю в конфиг (последние 50 коммитов)
    history = cfg.setdefault("history", [])
    history.append({
        "time": datetime.now().isoformat(timespec="seconds"),
        "sha": sha,
        "branch": branch,
        "message": message,
    })
    del history[:-50]
    save_config(cfg)
    return sha


# --------------------------------------------------------------------------- #
#  GUI                                                                        #
# --------------------------------------------------------------------------- #

class CommitterApp:
    def __init__(self, root):
        self.root = root
        self.cfg = load_config()
        self.busy = False

        root.title(APP_TITLE)
        root.resizable(True, True)
        root.minsize(460, 320)

        style = ttk.Style(root)
        try:
            style.theme_use("clam")
        except tk.TclError:
            pass

        main = ttk.Frame(root, padding=14)
        main.pack(fill="both", expand=True)

        # --- верхняя строка: пути (read-only ориентир) + кнопка "..." ----- #
        top = ttk.Frame(main)
        top.pack(fill="x")

        ttk.Label(top, text="Папка:").grid(row=0, column=0, sticky="w")
        self.var_folder = tk.StringVar(value=self.cfg.get("source_folder", ""))
        ent_folder = ttk.Entry(top, textvariable=self.var_folder)
        ent_folder.grid(row=0, column=1, sticky="ew", padx=(6, 2))
        ttk.Button(top, text="…", width=3,
                   command=self.pick_folder).grid(row=0, column=2)

        ttk.Label(top, text="Ссылка репо:").grid(row=1, column=0, sticky="w",
                                                 pady=(6, 0))
        self.var_repo = PlaceholderEntry(top, placeholder="https://github.com/user/repo.git")
        if self.cfg.get("repository"):
            self.var_repo.set(self.cfg["repository"])
        self.var_repo.grid(row=1, column=1, sticky="ew", padx=(6, 2), pady=(6, 0))
        ttk.Button(top, text="…", width=3,
                   command=self.paste_repo_url).grid(row=1, column=2, pady=(6, 0))
        top.columnconfigure(1, weight=1)

        # --- большая кнопка КОММИТ ----------------------------------------- #
        btn_frame = ttk.Frame(main)
        btn_frame.pack(fill="both", expand=True, pady=14)

        self.btn_commit = tk.Button(
            btn_frame,
            text="КОММИТ",
            font=("Segoe UI", 26, "bold"),
            bg="#1f8b4c",
            fg="white",
            activebackground="#17703d",
            activeforeground="white",
            relief="flat",
            cursor="hand2",
            command=self.on_commit,
        )
        self.btn_commit.pack(fill="both", expand=True)

        # --- нижняя строка: статус + маленькая кнопка "..." (открыть конфиг) #
        bottom = ttk.Frame(main)
        bottom.pack(fill="x")

        self.var_status = tk.StringVar(value="Готов.")
        ttk.Label(bottom, textvariable=self.var_status,
                  foreground="#555").pack(side="left", fill="x", expand=True)

        ttk.Button(bottom, text="...", width=4,
                   command=self.open_config).pack(side="right")

        # лог последних действий
        self.log_box = tk.Text(main, height=7, state="disabled", wrap="word",
                               font=("Consolas", 9))
        self.log_box.pack(fill="x", pady=(10, 0))

    # ------------------------------------------------------------------ #
    #  Обработчики                                                        #
    # ------------------------------------------------------------------ #

    def log(self, text: str):
        self.log_box.configure(state="normal")
        stamp = datetime.now().strftime("%H:%M:%S")
        self.log_box.insert("end", f"[{stamp}] {text}\n")
        self.log_box.see("end")
        self.log_box.configure(state="disabled")

    def set_status(self, text: str):
        self.var_status.set(text)

    def _collect_cfg(self):
        """Сохраняем пользовательские поля обратно в конфиг."""
        self.cfg["source_folder"] = self.var_folder.get().strip()
        self.cfg["repository"] = self.var_repo.get().strip()
        save_config(self.cfg)

    def pick_folder(self):
        folder = filedialog.askdirectory(title="Папка, откуда коммитим",
                                         initialdir=self.var_folder.get() or ".")
        if folder:
            self.var_folder.set(folder)
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
        """Маленькая кнопка с троеточием — открыть файл конфига."""
        self._collect_cfg()
        path = config_path()
        if not path.exists():
            save_config(self.cfg)
        open_config_in_editor(path)
        self.set_status(f"Конфиг открыт: {path.name}")

    def on_commit(self):
        if self.busy:
            return
        self._collect_cfg()
        if not self.cfg.get("repository"):
            messagebox.showinfo(
                APP_TITLE,
                "Вставьте ссылку на репозиторий (поле «Ссылка репо» или кнопка «…» — из буфера)\n"
                "и папку-источник, затем нажмите КОММИТ.\n\n"
                "Кнопка «...» справа внизу открывает файл config.json.")
            return

        self.busy = True
        self.btn_commit.configure(state="disabled", bg="#9e9e9e",
                                  fg="white")
        self.set_status("Выполняется коммит…")
        self._result_queue = []
        threading.Thread(target=self._commit_worker,
                         args=(self._result_queue,), daemon=True).start()
        self.root.after(100, self._poll_results)

    def _commit_worker(self, queue):
        """Работает в фоновом потоке; в GUI пишет только через очередь."""
        try:
            sha = commit_all(self.cfg, log=lambda m: queue.append(("log", m)))
            if sha:
                queue.append(("done", f"Готово: коммит {sha}"))
            else:
                queue.append(("done", "Изменений нет."))
        except GitError as exc:
            queue.append(("error", str(exc)))
        except Exception as exc:                                # noqa: BLE001
            queue.append(("error", f"Ошибка: {exc}"))

    def _poll_results(self):
        """Выбирает сообщения из очереди и печатает их в главном потоке Tk."""
        for kind, text in list(self._result_queue):
            self._result_queue.remove((kind, text))
            if kind == "log":
                self.log(text)
            elif kind == "done":
                self._finish(text, None)
            elif kind == "error":
                self._finish(None, text)
        if self.busy:
            self.root.after(100, self._poll_results)

    def _finish(self, ok_msg, err_msg):
        self.busy = False
        self.btn_commit.configure(state="normal", bg="#1f8b4c")
        if err_msg:
            self.set_status("Ошибка коммита")
            self.log(err_msg)
            messagebox.showerror(APP_TITLE, err_msg)
        else:
            self.set_status(ok_msg or "Готово.")
            self.log(ok_msg or "Готово.")


def main():
    if tk is None:
        sys.exit(
            "Tkinter недоступен (" + _TK_ERROR_TEXT + ").\n"
            "Установите tk/tcl: Linux — «apt install python3-tk» / «pacman -S tk», "
            "на Windows и macOS tkinter входит в официальный установщик Python."
        )
    root = tk.Tk()
    CommitterApp(root)
    root.mainloop()


if __name__ == "__main__":
    main()
