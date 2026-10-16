#!/usr/bin/env python3
"""Materialize only ordinary config blobs; never check out or run candidate code.

The workflow fetches an immutable upstream PR head. Reuse check-bump.sh with main as
the current policy anchor and the real merge base as the pin-delta anchor, before
Lake executes the inherited configuration in this otherwise empty project.
"""

import argparse
from pathlib import Path
import re
import subprocess

FILES = ("lakefile.toml", "lakefile.lean", "lean-toolchain", "lake-manifest.json")


def git(repo, *args):
    return subprocess.check_output(["git", "-C", str(repo), *args])


def materialize(repo, revision, destination):
    destination.mkdir()
    for name in FILES:
        entry = git(repo, "ls-tree", revision, "--", name).decode().strip()
        if not entry:
            if name in ("lean-toolchain", "lake-manifest.json"):
                raise ValueError("missing pin: " + name)
            continue
        if not entry.startswith("100644 blob ") and not entry.startswith("100755 blob "):
            raise ValueError("configuration must be an ordinary blob: " + name)
        (destination / name).write_bytes(git(repo, "show", revision + ":" + name))


def prepare(repo, head, destination, base=None):
    if not re.fullmatch(r"[0-9a-f]{40}", head):
        raise ValueError("head must be an immutable full SHA")
    base = base or git(repo, "rev-parse", "HEAD").decode().strip()
    if not re.fullmatch(r"[0-9a-f]{40}", base):
        raise ValueError("policy base must be an immutable full SHA")
    mergebase = git(repo, "merge-base", base, head).decode().strip()
    destination.mkdir()
    for name, revision in (("base", base), ("mergebase", mergebase), ("project", head)):
        materialize(repo, revision, destination / name)
    # A warmer never executes historical or edited lakefiles: use today's trusted config.
    # Old inherited pins are still allowed; actual bump deltas must pass check-bump.sh.
    for name in ("lakefile.toml", "lakefile.lean"):
        expected = destination / "base" / name
        actual = destination / "project" / name
        if expected.exists() != actual.exists() or (expected.exists() and
                                                   expected.read_bytes() != actual.read_bytes()):
            raise ValueError("candidate lakefile differs from main: " + name)
    subprocess.run(["bash", str(repo / "scripts/check-bump.sh"),
                    str(destination / "base"), str(destination / "mergebase"),
                    str(destination / "project")], check=True)
    return destination / "project"


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("repo", type=Path)
    parser.add_argument("head")
    parser.add_argument("destination", type=Path)
    parser.add_argument("--base", help="Immutable current main policy anchor")
    args = parser.parse_args()
    print(prepare(args.repo.resolve(), args.head, args.destination.resolve(), args.base))
