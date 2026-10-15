#!/usr/bin/env python3
"""Verify exact-pin, official-release toolchain snapshots on ephemeral runners.

Only the isolated main-defined dependency warmer writes these snapshots. The manifest
detects corruption, not proof correctness: the producer's official-release provenance
and the workflow/cache write boundary supply trust. Never snapshot candidate builds.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import stat

MANIFEST = ".tauceti-toolchain.json"
PRODUCER = "TauCetiProject/TauCeti/.github/workflows/warm-dependencies.yml"


def toolchain_name(pin):
    match = re.fullmatch(r"leanprover/lean4:(v[0-9][A-Za-z0-9.\-]*)", pin)
    if not match:
        raise ValueError("expected an official Lean release pin")
    return "leanprover--lean4---" + match[1]


def inventory(root):
    if root.is_symlink() or not root.is_dir():
        raise ValueError("snapshot root must be an ordinary directory")
    result = {}
    for path in sorted(root.rglob("*")):
        relative = str(path.relative_to(root))
        if relative == MANIFEST:
            continue
        mode = path.lstat().st_mode
        if stat.S_ISLNK(mode):
            target = os.readlink(path)
            if Path(target).is_absolute() or not path.resolve().is_relative_to(root.resolve()):
                raise ValueError("toolchain symlink escapes snapshot: " + relative)
            result[relative] = ["link", target]
        elif stat.S_ISREG(mode):
            with path.open("rb") as stream:
                digest = hashlib.file_digest(stream, "sha256").hexdigest()
            result[relative] = ["file", stat.S_IMODE(mode), digest]
        elif stat.S_ISDIR(mode):
            result[relative] = ["dir", stat.S_IMODE(mode)]
        else:
            raise ValueError("special file in snapshot: " + relative)
    for executable in ("bin/lean", "bin/lake"):
        if executable not in result or not os.access(root / executable, os.X_OK):
            raise ValueError("missing executable: " + executable)
    return result


def seal(root, pin, revision, run_id):
    toolchain_name(pin)
    if not re.fullmatch(r"[0-9a-f]{40}", revision) or not run_id.isdecimal():
        raise ValueError("invalid producer revision/run")
    data = dict(schema=1, producer=PRODUCER, ref="refs/heads/main", pin=pin,
                revision=revision, run_id=run_id, files=inventory(root))
    (root / MANIFEST).write_text(json.dumps(data, sort_keys=True) + "\n")


def verify(root, pin):
    toolchain_name(pin)
    manifest = root / MANIFEST
    if manifest.is_symlink():
        raise ValueError("symlinked provenance manifest")
    data = json.loads(manifest.read_text())
    if (data.get("schema"), data.get("producer"), data.get("ref"), data.get("pin")) != (
            1, PRODUCER, "refs/heads/main", pin):
        raise ValueError("snapshot provenance or toolchain mismatch")
    if not re.fullmatch(r"[0-9a-f]{40}", data.get("revision", "")) or not str(
            data.get("run_id", "")).isdecimal():
        raise ValueError("invalid snapshot producer identity")
    if data.get("files") != inventory(root):
        raise ValueError("snapshot file inventory/digests changed")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=("path", "seal", "verify"))
    parser.add_argument("pin_file", type=Path)
    parser.add_argument("--root", type=Path)
    parser.add_argument("--revision")
    parser.add_argument("--run-id")
    args = parser.parse_args()
    pin = args.pin_file.read_text().strip()
    if args.command == "path":
        print(Path.home() / ".elan/toolchains" / toolchain_name(pin))
    elif args.command == "seal":
        seal(args.root, pin, args.revision, args.run_id)
    else:
        verify(args.root, pin)


if __name__ == "__main__":
    main()
