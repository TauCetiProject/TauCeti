#!/usr/bin/env python3
"""Cheap source policy: reject option overrides and metaprogramming, allowing local macros.

This is a conservative token check, not a Lean parser or a sandbox. In particular, local
macro bodies still need review; dynamically assembled commands are outside this check.
"""

from __future__ import annotations

import argparse
from pathlib import Path
import re

from lean_source import strip_comments_and_strings


# Keep heartbeat instrumentation in tooling; some Mathlib command forms disable limits.
FORBIDDEN_TOKENS = (
    "set_option", "guard_min_heartbeats", "count_heartbeats",
    "meta", "unsafe", "elab", "elab_rules", "initialize", "builtin_initialize",
    "run_cmd", "run_elab", "run_tac", "run_meta", "by_elab", "#eval",
)
REGISTRATION_ATTRIBUTES = (
    "command_elab", "term_elab", "doElem_elab", "tactic", "grind_tactic", "try_tactic",
    "macro", "app_unexpander", "delab", "inductive_elab", "init",
)
REGISTRATION_TOKEN_PATTERN = re.compile(
    r"(?<![\w'!?])(?:builtin_)?(?:"
    + "|".join(REGISTRATION_ATTRIBUTES) + r")(?![\w'!?])")
# Keep the existing conservative treatment of qualified/quoted names and literal text.
# Match the local modifier with the macro keyword, including across masked comments/newlines.
TOKEN_PATTERN = re.compile(
    r"(?<![\w'!?])(?:(?:(?P<local>local)\s+)?(?P<macro>macro(?:_rules)?)|"
    + "|".join(re.escape(token) + ("!?" if token in ("count_heartbeats", "#eval") else "")
               for token in FORBIDDEN_TOKENS) + r")(?![\w'!?])")
# `tactic` is a normal syntax category in a local macro, so reject it only inside attributes.
# Cover both declaration attributes and later `attribute [...]` registrations. Nested attribute
# syntax is not parsed; this guard targets the ordinary registration forms, not arbitrary code.
REGISTRATION_PATTERN = re.compile(
    r"(?:@\s*\[|(?<![\w'!?])attribute\s*\[)[^\]]*?"
    + "(?P<attribute>" + REGISTRATION_TOKEN_PATTERN.pattern + ")")
CANDIDATE_WORDS = frozenset((*FORBIDDEN_TOKENS, "count_heartbeats!", "#eval!", "macro", "macro_rules",
                             *REGISTRATION_ATTRIBUTES,
                             *("builtin_" + name for name in REGISTRATION_ATTRIBUTES)))
# Search each shared substring only once: e.g. elab covers run_elab and command_elab too.
CANDIDATE_FRAGMENTS = tuple(word for word in sorted(CANDIDATE_WORDS)
                            if not any(other != word and other in word
                                       for other in CANDIDATE_WORDS))


def has_candidate(source: str) -> bool:
    """Use literal searches and inspect only nearby identifier characters before lexing.

    Widen left over identifier characters except apostrophes: a character literal immediately
    before a keyword will be masked later. Extra candidates are harmless. Actual policy
    decisions still happen after comment masking.
    """
    for token in CANDIDATE_FRAGMENTS:
        position = source.find(token)
        while position != -1:
            start, end = position, position + len(token)
            while start and (source[start - 1].isalnum() or source[start - 1] in "_!?"):
                start -= 1
            while end < len(source) and (source[end].isalnum() or source[end] in "_'!?"):
                end += 1
            if source[start:end] in CANDIDATE_WORDS:
                return True
            position = source.find(token, end)
    return False


def forbidden_tokens(source: str) -> dict[int, set[str]]:
    """Return forbidden token spellings keyed by their 1-based diagnostic lines.

    Ignore ordinary comments, character literals, and tokens within longer identifiers.
    Conservatively include strings, qualified/quoted names, and quote-bearing comments
    that this approximate lexer cannot reliably distinguish from interpolation text.
    """
    # Most files contain no forbidden token. Avoid full-file regex searches and Python lexing
    # even when a candidate substring occurs in longer identifiers such as elaboration.
    if not has_candidate(source):
        return {}
    code = strip_comments_and_strings(source, mask_strings=False)
    blank = None
    positions = []
    for match in TOKEN_PATTERN.finditer(code):
        if match.group("local") is not None:
            # Conservative literal/comment text can cause rejections, never grant an exception.
            # Only real source code may supply the local modifier. Mask this second view lazily:
            # files without apparent local macro definitions need no extra lexer pass.
            if blank is None:
                blank = strip_comments_and_strings(source)
            if blank[match.start("local"):match.end("local")] == "local":
                continue
        group = "macro" if match.group("macro") is not None else 0
        positions.append((match.start(group), match.group(group)))
    positions.extend((match.start("attribute"), match.group("attribute"))
                     for match in REGISTRATION_PATTERN.finditer(code))
    problems: dict[int, set[str]] = {}
    for position, token in sorted(positions):
        problems.setdefault(code.count("\n", 0, position) + 1, set()).add(token)
    return problems


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
            for line, tokens in forbidden_tokens(path.read_text(encoding="utf-8")).items():
                spellings = ", ".join(sorted(tokens))
                print(f"{path}:{line}: forbidden library source token(s): {spellings}; "
                      "move tooling to scripts/ (only local macros are allowed). Strings, quoted "
                      "names, and comments containing double quotes are checked conservatively.")
                failed = True
    return int(failed)


if __name__ == "__main__":
    raise SystemExit(main())
