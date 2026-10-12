"""List immutable Git tree changes without consulting candidate Git configuration.

The caller supplies the merge base from GitHub's comparison of the exact base/head
SHAs. Read only the checkout's object database; never enter its working tree or
load its config, attributes, replacement refs, hooks, or executable helpers.
Missing objects cause the caller to fall back to full lint.
"""

import argparse
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile


def changed_files(checkout, base, head, *, include_deleted=False):
    if not all(re.fullmatch(r"[0-9a-f]{40}", sha) for sha in (base, head)):
        raise ValueError("expected immutable commit SHAs")
    objects = (Path(checkout) / ".git" / "objects").resolve(strict=True)
    # Locate the runner's Git once (also supports Nix installations); subprocesses
    # get only the minimal PATH below and cannot search the candidate checkout.
    git = shutil.which("git")
    if git is None:
        raise OSError("Git is unavailable")
    with tempfile.TemporaryDirectory(prefix="lint-scope-git-") as directory:
        # No inherited token, Git configuration, shell startup, or candidate PATH.
        env = {"PATH": os.defpath, "HOME": directory, "LC_ALL": "C",
               "GIT_CONFIG_NOSYSTEM": "1", "GIT_CONFIG_GLOBAL": "/dev/null"}
        repository = str(Path(directory) / "repo.git")
        subprocess.run([git, "init", "--quiet", "--bare", "--template=", repository],
                       env=env, check=True, stdout=subprocess.DEVNULL)
        env["GIT_OBJECT_DIRECTORY"] = str(objects)
        command = [git, "--no-replace-objects", f"--git-dir={repository}",
                   "-c", "core.attributesFile=/dev/null"]
        for sha in (base, head):
            kind = subprocess.check_output(command + ["cat-file", "-t", sha], env=env)
            if kind != b"commit\n":
                raise ValueError("scope endpoint is not a commit")
        # Disable rename detection: a rename is a deletion plus an addition, so
        # the destination is included and the absent old module is excluded.
        # NUL separation preserves tabs, newlines and non-ASCII filenames.
        return subprocess.check_output(
            command + ["diff", "--no-ext-diff", "--no-textconv", "--no-renames",
                       "--name-only", "-z"] + ([] if include_deleted else ["--diff-filter=d"])
            + [base, head, "--"], env=env)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("checkout")
    parser.add_argument("base")
    parser.add_argument("head")
    parser.add_argument("--policy", action="store_true",
                        help="include deletions and emit lines for the merge-policy scope guard")
    args = parser.parse_args()
    try:
        files = changed_files(args.checkout, args.base, args.head, include_deleted=args.policy)
        if args.policy:
            paths = files.split(b"\0")[:-1]
            if any(b"\n" in path or b"\r" in path for path in paths):
                raise ValueError("filename cannot be represented by the scope guard's line format")
            files = b"".join(path + b"\n" for path in paths)
        sys.stdout.buffer.write(files)
    except (OSError, ValueError, subprocess.CalledProcessError) as error:
        print(f"lint-scope: cannot read the immutable local diff: {error}", file=sys.stderr)
        sys.exit(1)
