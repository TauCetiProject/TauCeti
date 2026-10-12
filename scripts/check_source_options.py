#!/usr/bin/env python3
"""Reject set_option anywhere in library code, ignoring comments and strings."""

from __future__ import annotations

import argparse
from pathlib import Path
import re

from lean_source import strip_comments_and_strings


SET_OPTION = re.compile(r"\bset_option\b")


def option_lines(source: str) -> list[int]:
    # Most files contain no candidate token. Avoid lexing them at all.
    if "set_option" not in source:
        return []
    code = strip_comments_and_strings(source)
    return [number for number, line in enumerate(code.splitlines(), 1)
            if SET_OPTION.search(line)]


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("paths", nargs="+", type=Path)
    args = parser.parse_args()
    failed = False
    for root in args.paths:
        if not root.exists():
            parser.error(f"source path does not exist: {root}")
        paths = sorted(root.rglob("*.lean")) if root.is_dir() else [root]
        for path in paths:
            for line in option_lines(path.read_text(encoding="utf-8")):
                print(f"{path}:{line}: set_option is forbidden in library code; remove it")
                failed = True
    return int(failed)


if __name__ == "__main__":
    raise SystemExit(main())
