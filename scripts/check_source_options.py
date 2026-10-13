#!/usr/bin/env python3
"""Reject option overrides, conservatively including strings, names and quote-bearing comments."""

from __future__ import annotations

import argparse
from pathlib import Path
import re

from lean_source import strip_comments_and_strings


# Keep heartbeat instrumentation in tooling; some Mathlib command forms disable limits.
OPTION_OVERRIDES = ("set_option", "guard_min_heartbeats", "count_heartbeats")
# Also reject qualified/quoted syntax-kind names and Mathlib's bang heartbeat command.
OPTION_PATTERN = re.compile(
    r"(?<![\w'!?])(?:set_option|guard_min_heartbeats|count_heartbeats!?)(?![\w'!?])")


def option_lines(source: str) -> list[int]:
    """Return 1-based lines containing forbidden standalone option-override tokens.

    Ignore ordinary comments, character literals, and tokens within longer identifiers.
    Conservatively include strings, qualified/quoted names, and quote-bearing comments
    that this approximate lexer cannot reliably distinguish from interpolation text.
    """
    # Most files contain no candidate token. Avoid lexing them at all.
    if not any(token in source for token in OPTION_OVERRIDES):
        return []
    code = strip_comments_and_strings(source, mask_strings=False)
    return [number for number, line in enumerate(code.split("\n"), 1)
            if OPTION_PATTERN.search(line)]


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
                print(f"{path}:{line}: option overrides are forbidden in library code; remove them")
                failed = True
    return int(failed)


if __name__ == "__main__":
    raise SystemExit(main())
