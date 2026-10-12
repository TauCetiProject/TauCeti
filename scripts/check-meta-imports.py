#!/usr/bin/env python3
"""Reject `meta import` in TauCeti sources.

`meta import` exists to make a module's contents available to compile-time code:
elaborators, macros, tactics, `deriving` handlers. TauCeti contains no
metaprogramming at all -- the only Lean meta code in the repository is the
human-owned governance machinery under `scripts/` -- so a `meta import` under
`TauCeti/` is either a copy-paste accident or the start of meta code that does not
belong in the AI-owned library. Either way it should fail before it lands.

The verdict comes from Lean's own header parser, never from a regex over the
source. `lean --deps-json` runs `Lean.parseImports'`, the hand-written fast
scanner in `Lean/Elab/ParseImportsFast.lean` that Lake itself uses to compute
dependencies, and prints one JSON record per input file. So this check sees the
`meta` modifier exactly as the frontend does -- through block comments, nested
`/- -/`, string literals and guillemet-quoted module names -- and it reports a
malformed header as a failure instead of quietly matching nothing.

It is cheap enough to run on every PR. The scanner stops at the end of the
header, a single `lean` process handles the whole file list, and nothing is
elaborated or imported: the whole library takes about three seconds at 13k files,
and an ordinary PR's changed-file list about a tenth of one.

A non-`prelude` module header implicitly carries `import Init` and `meta import
Init` -- `ParseImports.main` pushes both when `prelude` is absent -- so both
appear in every record without being source text. Imports of `Init` are
therefore skipped; no TauCeti file writes one.
"""

from __future__ import annotations

import argparse
import json
import pathlib
import shutil
import subprocess

# The AI-owned library: everything under this directory, plus the library root file.
SOURCE_DIR = "TauCeti"
ROOT_MODULE = "TauCeti.lean"

# Implicitly added to every non-`prelude` module header, so never a source `meta import`.
IMPLICIT_MODULE = "Init"


def library_files(root: pathlib.Path) -> list[str]:
    """Every TauCeti source in `root`, as repository-relative POSIX names."""
    names = []
    source_dir = root / SOURCE_DIR
    if source_dir.is_dir():
        names = [path.relative_to(root).as_posix()
                 for path in sorted(source_dir.rglob("*.lean"))]
    if (root / ROOT_MODULE).is_file():
        names.append(ROOT_MODULE)
    return names


def changed_library_files(root: pathlib.Path, listing: pathlib.Path) -> list[str]:
    """The TauCeti sources named by a NUL-separated changed-file list.

    The list is produced by `scripts/lint_scope_files.py` from immutable Git
    objects and excludes deletions, so every name it carries must exist at the
    head being checked. A missing one means the list and the checkout disagree,
    which is not something to interpret: fail closed and let a human look.
    """
    entries = [entry for entry in listing.read_bytes().split(b"\0") if entry]
    names = []
    for entry in entries:
        try:
            name = entry.decode("utf-8")
        except UnicodeDecodeError:
            raise ValueError(f"changed path is not valid UTF-8: {entry!r}") from None
        if not name.endswith(".lean"):
            continue
        parts = pathlib.PurePosixPath(name).parts
        if ".." in parts or pathlib.PurePosixPath(name).is_absolute():
            raise ValueError(f"changed path escapes the checkout: {name}")
        if name != ROOT_MODULE and parts[:1] != (SOURCE_DIR,):
            continue
        # `--deps-json --stdin` reads one file name per line, so a name containing a
        # newline cannot be handed to the parser. No module-shaped name does; refusing
        # is still better than checking one fewer file than the PR changed.
        if "\n" in name or "\r" in name:
            raise ValueError(f"changed path cannot be passed to the header parser: {name!r}")
        if not (root / name).is_file():
            raise ValueError(f"changed path is listed but absent from the checkout: {name}")
        names.append(name)
    return sorted(names)


def parse_headers(lean: str, root: pathlib.Path, names: list[str]) -> list[dict]:
    """Header records for `names`, straight from Lean's own header parser."""
    listing = "".join(f"{root / name}\n" for name in names)
    try:
        result = subprocess.run([lean, "--deps-json", "--stdin"], input=listing,
                                capture_output=True, text=True, check=False)
    except OSError as error:
        raise RuntimeError(f"cannot run `{lean} --deps-json`: {error}") from error
    if result.returncode != 0:
        detail = result.stderr.strip() or result.stdout.strip()
        raise RuntimeError(f"`{lean} --deps-json` exited {result.returncode}: {detail}")
    try:
        records = json.loads(result.stdout)["imports"]
    except (json.JSONDecodeError, KeyError, TypeError) as error:
        raise RuntimeError(f"cannot read the header parser's output: {error}") from error
    if not isinstance(records, list) or len(records) != len(names):
        raise RuntimeError(f"the header parser returned {len(records)} record(s) "
                           f"for {len(names)} file(s)")
    return records


def violations(names: list[str], records: list[dict]) -> list[tuple[str, str]]:
    """Each (file, message) pair that must fail the check."""
    found = []
    for name, record in zip(names, records):
        errors = record.get("errors") or []
        for error in errors:
            found.append((name, f"its header does not parse: {error}"))
        result = record.get("result")
        if result is None:
            if not errors:
                found.append((name, "the header parser returned neither a result nor an error"))
            continue
        for imported in result.get("imports") or []:
            module = imported.get("module")
            if imported.get("isMeta") and module != IMPLICIT_MODULE:
                found.append((name, f"`meta import {module}` is not allowed: TauCeti/ holds "
                                    "no metaprogramming, and meta code belongs in scripts/"))
    return found


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Reject `meta import` in TauCeti sources.",
        epilog=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--root", type=pathlib.Path, default=pathlib.Path("."),
                        help="checkout holding the sources to inspect (default: .)")
    parser.add_argument("--changed", type=pathlib.Path,
                        help="NUL-separated list of repository-relative changed paths; "
                             "omit to scan the whole library")
    parser.add_argument("--lean", default="lean",
                        help="the `lean` binary whose header parser decides (default: lean)")
    args = parser.parse_args(argv)

    if shutil.which(args.lean) is None and not pathlib.Path(args.lean).is_file():
        print(f"::error::check-meta-imports: no `lean` binary at {args.lean}")
        return 1
    try:
        names = (library_files(args.root) if args.changed is None
                 else changed_library_files(args.root, args.changed))
    except (OSError, ValueError) as error:
        print(f"::error::check-meta-imports: {error}")
        return 1
    if not names:
        print("check-meta-imports: no TauCeti sources in scope")
        return 0
    try:
        records = parse_headers(args.lean, args.root, names)
    except RuntimeError as error:
        print(f"::error::check-meta-imports: {error}")
        return 1

    found = violations(names, records)
    for name, message in found:
        print(f"::error file={name}::check-meta-imports: {name}: {message}")
    if found:
        print(f"check-meta-imports: {len(found)} problem(s) in "
              f"{len({name for name, _ in found})} of {len(names)} file(s)")
        return 1
    scope = "the whole library" if args.changed is None else "the changed files"
    print(f"check-meta-imports: no `meta import` in {len(names)} TauCeti source(s) "
          f"({scope})")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
