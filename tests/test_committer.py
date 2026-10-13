#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Интеграционный тест Git Committer по ТЗ."""
import json
import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

SCRIPT = "/workspace/git_committer_v4.py"
PASS, FAIL = 0, []

def check(name, cond, detail=""):
    global PASS
    if cond:
        PASS += 1
        print(f"  ok   {name}")
    else:
        FAIL.append(name)
        print(f"  FAIL {name}  {detail}")

def run(cmd, cwd=None):
    return subprocess.run(cmd, cwd=cwd, capture_output=True, text=True)

def git(args, cwd):
    p = run(["git", *args], cwd=str(cwd))
    assert p.returncode == 0, f"git {args}: {p.stderr}"
    return p.stdout.strip()

tmp = Path(tempfile.mkdtemp(prefix="gc_test_"))
appdir = tmp / "app"; appdir.mkdir()
source = tmp / "src"; source.mkdir()
remote = tmp / "remote.git"

shutil.copy2(SCRIPT, appdir / "git_committer.py")
run(["git", "init", "--bare", "-b", "main", str(remote)])
seed = tmp / "seed"; seed.mkdir()
(seed / "README.md").write_text("initial\n")
git(["init", "-b", "main"], seed)
git(["config", "user.email", "t@t"], seed)
git(["config", "user.name", "T"], seed)
git(["add", "-A"], seed); git(["commit", "-m", "seed"], seed)
git(["remote", "add", "origin", str(remote)], seed)
git(["push", "origin", "main"], seed)

(source / "hello.txt").write_text("hello world\n")
(source / "sub").mkdir(); (source / "sub" / "a.py").write_text("print(1)\n")
(source / "node_modules").mkdir(); (source / "node_modules" / "junk.js").write_text("x\n")
(source / "__pycache__").mkdir(); (source / "__pycache__" / "x.pyc").write_bytes(b"\x00")
(source / ".venv").mkdir(); (source / ".venv" / "pyvenv.cfg").write_text("v\n")

cfg = {
    "source_folder": str(source),
    "repository": "file://" + str(remote),
    "branch": "main",
    "commit_message": "test commit {datetime}",
    "author_name": "Tester",
    "author_email": "tester@example.com",
    "push": True,
    "delete_extra": True,
    "history": [],
}
(appdir / "config.json").write_text(json.dumps(cfg), encoding="utf-8")

sys.path.insert(0, str(appdir))
import importlib.util
spec = importlib.util.spec_from_file_location("gcmod", str(appdir / "git_committer.py"))
gc = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gc)

logs = []
sha = gc.commit_all(dict(cfg), log=logs.append)
check("1. commit_all вернул sha", bool(sha), logs)
workdir = gc.local_clone_dir(cfg["repository"])
log_remote = git(["log", "--oneline", "main"], remote)
check("2. пуш дошёл до remote", len(log_remote.splitlines()) >= 2, log_remote)

files_remote = git(["ls-tree", "--name-only", "-r", "main"], remote)
check("3. hello.txt в репо", "hello.txt" in files_remote, files_remote)
check("4. sub/a.py в репо", "sub/a.py" in files_remote, files_remote)
check("5. node_modules проигнорирован", "node_modules" not in files_remote, files_remote)
check("6. __pycache__ проигнорирован", "__pycache__" not in files_remote, files_remote)
check("7. .venv проигнорирован", ".venv" not in files_remote, files_remote)

author = git(["log", "-1", "--format=%an <%ae>", "main"], remote)
check("8. автор коммита", author == "Tester <tester@example.com>", author)
msg = git(["log", "-1", "--format=%s", "main"], remote)
check("9. {datetime} подставлен", msg.startswith("test commit ") and "{datetime}" not in msg, msg)

saved = json.loads((appdir / "config.json").read_text(encoding="utf-8"))
check("10. история записана в конфиг", bool(saved["history"]) and saved["history"][-1]["sha"] == sha, saved.get("history"))

(source / "hello.txt").unlink()
sha2 = gc.commit_all(dict(cfg), log=logs.append)
files2 = git(["ls-tree", "--name-only", "-r", "main"], remote)
check("11. удалённый файл исчез из репо (delete_extra)", "hello.txt" not in files2, files2)

sha3 = gc.commit_all(dict(cfg), log=logs.append)
check("12. пустого коммита нет", sha3 == "", repr(sha3))

# источник меняется -> появляется новый контент для feature-ветки
(source / "for_feature.txt").write_text("feature content\n")
cfg_new = dict(cfg); cfg_new["branch"] = "feature"
shaF = gc.commit_all(cfg_new, log=logs.append)
check("13a. коммит в новую ветку вернул sha", bool(shaF), logs[-3:])
branches = git(["branch", "--format=%(refname:short)"], remote)
check("13. новая ветка запущена в remote", "feature" in branches, branches)
f_files = git(["ls-tree", "--name-only", "-r", "feature"], remote)
check("13b. for_feature.txt в feature", "for_feature.txt" in f_files, f_files)
m_files = git(["ls-tree", "--name-only", "-r", "main"], remote)
check("13c. main не polluted содержимым feature", "for_feature.txt" not in m_files, m_files)
cfg_new["branch"] = "main"
gc.commit_all(cfg_new, log=logs.append)
check("14. main не сброшена (история цела)",
      len(git(["log", "--oneline", "main"], remote).splitlines()) >= 2)

bad = dict(cfg); bad["repository"] = str(tmp / "not_a_repo_path")
try:
    gc.commit_all(bad, log=logs.append)
    check("15. путь вместо ссылки -> ошибка", False)
except gc.GitError as e:
    check("15. путь вместо ссылки -> GitError", "не похоже на ссылку" in str(e), str(e))
except Exception as e:
    check("15. путь вместо ссылки -> GitError", False, repr(e))

broken_cfg = appdir / "config.json"
broken_cfg.write_text("{[not json", encoding="utf-8")
loaded_broken = gc.load_config()
check("16. битый конфиг -> .broken.json + дефолты",
      (appdir / "config.broken.json").exists() and loaded_broken["branch"] == "main")

partial = {"source_folder": "x"}
(broken_cfg).write_text(json.dumps(partial), encoding="utf-8")
loaded = gc.load_config()
missing_ok = all(k in loaded for k in gc.default_config())
check("17. недостающие ключи добиты дефолтами", missing_ok, list(loaded))

gc.save_config({"z": 1})
leftovers = list(appdir.glob("*.tmp"))
check("18. save_config не оставляет *.tmp", not leftovers, leftovers)

if shutil.which("xvfb-run"):
    gui_code = """
import sys, json
sys.path.insert(0, %r)
import importlib.util
spec = importlib.util.spec_from_file_location('gcgui', %r)
gc = importlib.util.module_from_spec(spec); spec.loader.exec_module(gc)
import tkinter as tk
opened = []
gc.open_config_in_editor = lambda p: opened.append(str(p))
root = tk.Tk()
app = gc.CommitterApp(root)
root.after(200, root.quit)
root.mainloop()
assert app.btn_commit.cget('text') == 'КОММИТ'
app.open_config()
assert opened, 'config not opened'
import queue as q
assert isinstance(app.msg_queue, q.Queue)
assert app.var_branch.get()
assert app.var_message.get() is not None
print('GUI_OK', opened[0])
""" % (str(appdir), str(appdir / "git_committer.py"))
    p = run(["xvfb-run", "-a", sys.executable, "-c", gui_code])
    check("19. GUI стартует, кнопка КОММИТ, «...» открывает конфиг",
          "GUI_OK" in p.stdout, (p.stdout + p.stderr)[-600:])
else:
    print("  skip 19 (нет xvfb-run)")

import inspect
src_run = inspect.getsource(gc.run_git)
check("20. GIT_TERMINAL_PROMPT=0", "GIT_TERMINAL_PROMPT" in src_run)
check("21. GIT_EDITOR=true", "GIT_EDITOR" in src_run)
check("22. timeout в subprocess.run", "timeout=" in src_run)

shutil.rmtree(tmp, ignore_errors=True)
print(f"\n=== PASS: {PASS}, FAIL: {len(FAIL)} ===")
if FAIL:
    print("Failed:", FAIL)
    sys.exit(1)
