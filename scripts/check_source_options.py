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


# Lean v4.36.0-rc1, Init/Meta/Defs.lean: isLetterLike, isSubScriptAlnum, isIdFirst/isIdRest.
# Python's Unicode word class differs in both directions (e.g. ℘ versus postfix ᶜ).
ID_FIRST = (r"A-Za-z_\u03b1-\u03ba\u03bc-\u03c9\u0391-\u039f\u03a1-\u03a2\u03a4-\u03a9"
            r"\u03ca-\u03fb\u1f00-\u1ffe\u2100-\u214f\U0001d49c-\U0001d59f"
            r"\u00c0-\u00d6\u00d8-\u00f6\u00f8-\u00ff\u0100-\u017f")
ID_NON_DIGIT_REST = ID_FIRST + r"'!?\u2080-\u2089\u2090-\u209c\u1d62-\u1d6a\u2c7c"
ID_REST = ID_NON_DIGIT_REST + "0-9"
ID_FIRST_PATTERN = re.compile(f"[{ID_FIRST}]")
ID_REST_PATTERN = re.compile(f"[{ID_REST}]")
# Left context is checked below: numerals and symbols can touch the next keyword (1run_cmd),
# whereas identifier suffixes such as foo1run_cmd must stay allowed.
AFTER_WORD = f"(?![{ID_REST}])"


# Keep heartbeat instrumentation in tooling; some Mathlib command forms disable limits.
FORBIDDEN_TOKENS = (
    "set_option", "guard_min_heartbeats", "count_heartbeats",
    "meta", "unsafe", "elab", "elab_rules", "initialize", "builtin_initialize",
    "run_cmd", "run_elab", "run_tac", "run_meta", "by_elab",
)
# Symbol commands do not obey identifier boundaries: #evalIO.println is valid Lean.
SYMBOL_COMMANDS = ("#eval", "#count_heartbeats")
SYMBOL_PATTERN = re.compile("(?:" + "|".join(map(re.escape, SYMBOL_COMMANDS)) + ")!?")
REGISTRATION_ATTRIBUTES = (
    "command_elab", "term_elab", "doElem_elab", "tactic", "grind_tactic", "try_tactic",
    "macro", "app_unexpander", "delab", "inductive_elab", "init",
)
REGISTRATION_TOKEN_PATTERN = re.compile(
    r"(?:builtin_)?(?:"
    + "|".join(REGISTRATION_ATTRIBUTES) + ")" + AFTER_WORD)
# Keep the existing conservative treatment of qualified/quoted names and literal text.
# Match the local modifier with the macro keyword, including across masked comments/newlines.
TOKEN_PATTERN = re.compile(
    r"(?:(?:(?P<local>local)\s+)?(?P<macro>macro(?:_rules)?)|"
    + "|".join(re.escape(token) + ("!?" if token == "count_heartbeats" else "")
               for token in FORBIDDEN_TOKENS) + ")" + AFTER_WORD)
# `tactic` is a normal syntax category in a local macro, so reject it only inside attributes.
# Cover both declaration attributes and later `attribute [...]` registrations. Nested attribute
# syntax is not parsed; this guard targets the ordinary registration forms, not arbitrary code.
ATTRIBUTE_OPENER_PATTERN = re.compile(r"@\s*\[|(?P<command>attribute)\s*\[")
CANDIDATE_WORDS = frozenset((*FORBIDDEN_TOKENS, "count_heartbeats!", "macro", "macro_rules",
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
    if any(token in source for token in SYMBOL_COMMANDS):
        return True
    for token in CANDIDATE_FRAGMENTS:
        position = source.find(token)
        while position != -1:
            start, end = position, position + len(token)
            while (start and source[start - 1] != "'"
                   and ID_REST_PATTERN.fullmatch(source[start - 1])):
                start -= 1
            while end < len(source) and ID_REST_PATTERN.fullmatch(source[end]):
                end += 1
            # Numerals (including hex/exponent forms) can touch an ensuing keyword. Let the
            # masked scan handle these rare candidates conservatively instead of skipping them.
            if (source[start:end] in CANDIDATE_WORDS
                    or ID_FIRST_PATTERN.fullmatch(source[start]) is None):
                return True
            position = source.find(token, end)
    return False


def inside_identifier(source: str, position: int) -> bool:
    """Whether an unambiguous identifier prefix runs into this position.

    Fragments starting with a numeral remain possible token boundaries. This deliberately
    rejects unusual number/identifier adjacency conservatively; it never grants an exception.
    """
    start = position
    while start and ID_REST_PATTERN.fullmatch(source[start - 1]):
        start -= 1
    # Rest-only characters may themselves be notation tokens before an identifier. For
    # example !foo_run_cmd still contains an identifier suffix, while !run_cmd does not.
    while (start < position and ID_FIRST_PATTERN.fullmatch(source[start]) is None
           and source[start] not in "0123456789"):
        start += 1
    return start < position and ID_FIRST_PATTERN.fullmatch(source[start]) is not None


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
            # A name literal `local or qualified name Foo.local is not a modifier either.
            before = match.start("local")
            while before and blank[before - 1] in " \t\r":
                before -= 1
            local_start = match.start("local")
            line_start = source.rfind("\n", 0, local_start) + 1
            if (blank[match.start("local"):match.end("local")] == "local"
                    # Grant exceptions only with an unambiguous delimiter, never with the
                    # conservative numeric-prefix handling used for rejecting other tokens.
                    # Use original characters: masking a literal inside an identifier can
                    # introduce whitespace that must not grant a local exception.
                    and (not local_start or source[local_start - 1].isspace()
                         or source[local_start - 1] == "]"
                         or source[max(0, local_start - 2):local_start] == "-/")
                    # Interpolation can confuse the approximate masker. Line comments have
                    # no closing delimiter to interrupt local + newline + macro, so deny
                    # their text an exception directly from the original physical line.
                    and "--" not in source[line_start:local_start]
                    and (not before or blank[before - 1] not in ".`")):
                continue
        group = "macro" if match.group("macro") is not None else 0
        if inside_identifier(code, match.start(group)):
            continue
        if (group == 0 and match.group().startswith("count_heartbeats")
                and match.start() and code[match.start() - 1] == "#"):
            continue  # Report symbolic heartbeat commands once, with their leading #.
        positions.append((match.start(group), match.group(group)))
    positions.extend((match.start(), match.group()) for match in SYMBOL_PATTERN.finditer(code))
    for opener in ATTRIBUTE_OPENER_PATTERN.finditer(code):
        # The symbolic @[ opener may touch an identifier; only the word attribute needs
        # a left-context check. Examine every entry: an identifier-suffix decoy must not
        # hide a later actual registration in the same brackets.
        if opener.group("command") and inside_identifier(code, opener.start()):
            continue
        end = code.find("]", opener.end())
        if end == -1:
            end = len(code)
        for match in REGISTRATION_TOKEN_PATTERN.finditer(code, opener.end(), end):
            if not inside_identifier(code, match.start()):
                positions.append((match.start(), match.group()))
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
