#!/usr/bin/env python3
"""Retain verified downloaded Lake archives for the final CI output mapping.

Snapshot immediately after a successful cache download, before candidate code runs.
Keep the snapshot outside the writable checkout (read-only in the build sandbox).
Reconnect after the audits, then let stock Lake validate the current inputs and
generate the complete map with --no-build --rehash -o, packing cache misses.
--rehash is essential: hash archive bytes rather than trusting potentially stale
or candidate-written .ltar.hash sidecars beside the new links.

Temporary workaround: remove this script and its snapshot/reconnect workflow calls
once the pinned Lean includes https://github.com/leanprover/lean4/pull/15231, which
supersedes https://github.com/leanprover/lean4/pull/15189 and lets Lake reuse restored
archives for later output mapping while preserving platform independence.
Unknown formats and failed hard links simply forgo the optimization; archive
payloads are never copied.
"""

from __future__ import annotations

import argparse
from contextlib import contextmanager
import hashlib
import json
import os
from pathlib import Path
import re
import stat


HASH = re.compile(r"[0-9a-f]{16}")
ARCHIVE = re.compile(r"[0-9a-f]{16}\.ltar")
SHA256 = re.compile(r"[0-9a-f]{64}")
OUTPUT_SCHEMA = "2026-02-25"
TRACE_SCHEMA = "2025-09-10"


@contextmanager
def directory(root: Path, relative: Path):
    """Open a directory beneath root without following any internal symlinks."""
    if relative.is_absolute() or ".." in relative.parts:
        raise ValueError("expected a relative path beneath the project")
    fd = os.open(root, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
    try:
        for part in relative.parts:
            child = os.open(part, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW, dir_fd=fd)
            os.close(fd)
            fd = child
        yield fd
    finally:
        os.close(fd)


@contextmanager
def regular_file(parent: int, name: str):
    fd = os.open(name, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK, dir_fd=parent)
    try:
        if not stat.S_ISREG(os.fstat(fd).st_mode):
            raise ValueError("expected a regular file")
        with os.fdopen(fd, "rb", closefd=False) as handle:
            yield handle
    finally:
        os.close(fd)


def read_json(root: Path, relative: Path):
    with directory(root, relative.parent) as parent, regular_file(parent, relative.name) as handle:
        return json.load(handle)


def digest(parent: int, name: str) -> str:
    with regular_file(parent, name) as handle:
        result = hashlib.sha256()
        while block := handle.read(1024 * 1024):
            result.update(block)
        return result.hexdigest()


def snapshot(root: Path, package: str = "TauCeti") -> dict:
    """Record input hashes and SHA-256 of the archives Lake has just verified."""
    if not re.fullmatch(r"[A-Za-z0-9_-]+", package):
        raise ValueError("invalid package name")
    entries = {}
    outputs = Path(".lake/cache/outputs") / package
    try:
        with directory(root, outputs) as parent, directory(root, Path(".lake/cache/artifacts")) as artifacts:
            for name in sorted(os.listdir(parent)):
                if not name.endswith(".json") or not HASH.fullmatch(name[:-5]):
                    continue
                try:
                    with regular_file(parent, name) as handle:
                        record = json.load(handle)
                    if not isinstance(record, dict) or record.get("schemaVersion") != OUTPUT_SCHEMA:
                        continue
                    archive = record.get("data")
                    if not isinstance(archive, str) or not ARCHIVE.fullmatch(archive):
                        continue
                    entries[name[:-5]] = [archive, digest(artifacts, archive)]
                except (OSError, ValueError):
                    continue
    except OSError:
        pass  # No downloaded cache is a normal cold build.
    return {"version": 1, "entries": entries}


def reconnect(root: Path, saved: dict) -> int:
    """Link matching, unchanged downloaded archives; leave every miss to Lake."""
    if not isinstance(saved, dict) or saved.get("version") != 1:
        return 0
    entries = saved.get("entries")
    if not isinstance(entries, dict):
        return 0
    linked = 0
    trace_root = Path(".lake/build/lib/lean")
    # os.walk does not follow directory symlinks; descriptor-based opens below also
    # reject symlinked parents/files, including replacements since the traversal.
    for base, _, names in os.walk(root / trace_root, followlinks=False):
        for name in names:
            if not name.endswith(".trace"):
                continue
            trace_path = (Path(base) / name).relative_to(root)
            try:
                trace = read_json(root, trace_path)
                if not isinstance(trace, dict) or trace.get("schemaVersion") != TRACE_SCHEMA:
                    continue
                input_hash = trace.get("depHash")
                if not isinstance(input_hash, str) or not HASH.fullmatch(input_hash):
                    continue
                entry = entries.get(input_hash)
                if (not isinstance(entry, list) or len(entry) != 2
                        or not isinstance(entry[0], str) or not ARCHIVE.fullmatch(entry[0])
                        or not isinstance(entry[1], str) or not SHA256.fullmatch(entry[1])):
                    continue
                archive, expected = entry
                target = Path(".lake/build/ir") / trace_path.relative_to(trace_root).with_suffix(".ltar")
                with directory(root, Path(".lake/cache/artifacts")) as artifacts, directory(root, target.parent) as dest:
                    # Never replace an archive already supplied by Lake (including
                    # versions with the upstream fix). No copy fallback on EXDEV.
                    if os.path.lexists(root / target):
                        continue
                    os.link(archive, target.name, src_dir_fd=artifacts, dst_dir_fd=dest,
                            follow_symlinks=False)
                    # Verify the inode actually linked, not a source path that
                    # could have been replaced before the link was created.
                    try:
                        if digest(dest, target.name) != expected:
                            raise ValueError("archive changed while linking")
                    except (OSError, ValueError):
                        os.unlink(target.name, dir_fd=dest)
                        continue
                    linked += 1
            except (OSError, ValueError):
                continue
    return linked


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=("snapshot", "reconnect"))
    parser.add_argument("project", type=Path)
    parser.add_argument("index", type=Path)
    args = parser.parse_args()
    root = args.project.resolve()
    if args.action == "snapshot":
        saved = snapshot(root)
        args.index.write_text(json.dumps(saved) + "\n")
        print(f"Lake archive reuse: saved {len(saved['entries'])} verified cache records")
    else:
        try:
            saved = json.loads(args.index.read_text())
        except (OSError, ValueError):
            saved = {}
        print(f"Lake archive reuse: linked {reconnect(root, saved)} unchanged archives (no copies)")


if __name__ == "__main__":
    main()
