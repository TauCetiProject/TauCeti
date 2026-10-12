#!/usr/bin/env python3
"""Summarise one CI build's telemetry as a small JSON artifact for TauCetiCI.

    python3 scripts/ci_telemetry.py --dir pr/.lake/telemetry --out telemetry.json

Reads what `sandbox-build.sh` left in the telemetry directory:

  phases.tsv       `<phase>\t<epoch seconds>` as each phase starts, ending with `end`
  lake-build.log   the `lake build` output: one `✔ [i/N] <Verb> <Module> (<time>)` line per job

and writes `tauceti-ci.telemetry/v1`: the phases with their durations, and the build's jobs counted
by verb (Built, Unpacked from the artifact cache, Replayed, ...) with the slowest built modules.
Extra context (the runner picker's decision) comes from `--meta key=value` pairs.

Everything read here was written inside the sandbox, where candidate code runs, so it is recorded
as statistics only (`"trust": "sandbox"`) and never feeds a decision. It is also read defensively
(`read_untrusted`): no symlink is followed, only regular files are read, and reads are capped, so a
planted symlink, FIFO or huge file yields a smaller record, not a leak, a hang or an exhausted
runner. `--dir` must be relative to the working directory.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import stat
from pathlib import Path

LINE = re.compile(r"^[✔⚠✖]\s*\[(\d+)/(\d+)\]\s+(\w+)\s+(\S+)(?:\s+\(([\d.]+)(ms|s)\))?")
MAX_MODULES = 500
MAX_LINES = 200_000
MAX_BYTES = {"phases.tsv": 64 * 1024, "lake-build.log": 64 * 1024 * 1024}


def read_untrusted(directory: str, name: str) -> str:
    """Read a file the sandbox wrote, without following anything it could have planted: every path
    component is opened with O_NOFOLLOW relative to its parent, the file must be a regular file
    (not a FIFO, device or directory), and at most MAX_BYTES[name] bytes are read. Anything else
    reads as empty."""
    fds = []
    try:
        fd = os.open(".", os.O_RDONLY | os.O_DIRECTORY)
        fds.append(fd)
        for part in Path(directory).parts:
            fd = os.open(part, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW, dir_fd=fd)
            fds.append(fd)
        f = os.open(name, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK, dir_fd=fd)
        fds.append(f)
        if not stat.S_ISREG(os.fstat(f).st_mode):
            return ""
        return _read_all(f, MAX_BYTES[name])
    except OSError:
        return ""
    finally:
        for fd in reversed(fds):
            os.close(fd)


def _read_all(fd: int, limit: int) -> str:
    chunks, total = [], 0
    while total < limit:
        b = os.read(fd, min(1 << 20, limit - total))
        if not b:
            break
        chunks.append(b)
        total += len(b)
    return b"".join(chunks).decode("utf-8", errors="replace")


def phases(text: str) -> list[dict]:
    marks = []
    for line in text.splitlines()[:1000]:
        name, _, t = line.partition("\t")
        try:
            marks.append((name.strip()[:40], float(t)))
        except ValueError:
            continue
    out = []
    for (name, start), (_, end) in zip(marks, marks[1:]):
        out.append({"phase": name, "start": round(start, 3), "seconds": round(end - start, 3)})
    if marks and marks[-1][0] != "end":
        # The build stopped inside this phase (a failure): its end is unknown.
        out.append({"phase": marks[-1][0], "start": round(marks[-1][1], 3), "seconds": None})
    return out


def build_log(text: str) -> dict:
    verbs: dict[str, int] = {}
    built: list[tuple[str, float]] = []
    total = 0
    if not text:
        return {}
    for i, line in enumerate(text.splitlines()):
        if i >= MAX_LINES:
            break
        m = LINE.match(line.strip())
        if not m:
            continue
        total = max(total, int(m.group(2)))
        verb, module = m.group(3)[:20], m.group(4)
        verbs[verb] = verbs.get(verb, 0) + 1
        if verb == "Built" and m.group(5):
            secs = float(m.group(5)) / (1000 if m.group(6) == "ms" else 1)
            built.append((module[:200], secs))
    built.sort(key=lambda x: -x[1])
    return {
        "jobs_total": total,
        "jobs_by_verb": verbs,
        "built_seconds_total": round(sum(s for _, s in built), 1),
        "slowest_built": [{"module": m, "seconds": round(s, 2)} for m, s in built[:MAX_MODULES]],
    }


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--dir", required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("--meta", action="append", default=[], help="key=value context to include")
    args = ap.parse_args(argv)
    record = {
        "schema": "tauceti-ci.telemetry/v1",
        "trust": "sandbox",
        "meta": dict(kv.split("=", 1) for kv in args.meta if "=" in kv),
        "phases": phases(read_untrusted(args.dir, "phases.tsv")),
        "build": build_log(read_untrusted(args.dir, "lake-build.log")),
    }
    Path(args.out).write_text(json.dumps(record, indent=1) + "\n")


if __name__ == "__main__":
    main()
