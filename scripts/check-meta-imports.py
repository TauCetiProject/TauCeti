#!/usr/bin/env python3
"""Reject `meta import` in TauCeti sources.

Chooses which sources to audit and reports the verdict; `scripts/MetaImports.lean`,
run once under `lean --run`, is what actually reads the headers. That driver uses
Lean's own `Lean.Parser.parseHeader` and takes the written imports straight out of
the resulting syntax, so the `meta` modifier is seen exactly as the compiler sees
it and never matched as text. See its module doc for why the syntax, rather than
the computed import list, is the right thing to ask.

By default every TauCeti source is audited. `--changed` narrows that to the `.lean`
library sources named by a NUL-separated changed-file list, which is what CI passes
on a pull request. Nothing is elaborated, built or imported either way: the whole
library costs a few seconds and a pull request's files a fraction of one.
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

DRIVER = "MetaImports.lean"


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
    head being audited. A missing one means the list and the checkout disagree,
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
        # The driver reads one path per line from stdin, so a name containing a newline
        # cannot be handed to it. No module-shaped name does; refusing is still better
        # than auditing one fewer file than the change touched.
        if "\n" in name or "\r" in name:
            raise ValueError(f"changed path cannot be passed to the header parser: {name!r}")
        if not (root / name).is_file():
            raise ValueError(f"changed path is listed but absent from the checkout: {name}")
        names.append(name)
    return sorted(names)


def audit(lean: str, driver: pathlib.Path, root: pathlib.Path,
          names: list[str]) -> list[tuple[str, str]]:
    """Each (file, message) pair the Lean driver reports for `names`."""
    paths = {str(root / name): name for name in names}
    listing = "".join(f"{path}\n" for path in paths)
    try:
        result = subprocess.run([lean, "--run", str(driver)], input=listing,
                                capture_output=True, text=True, check=False)
    except OSError as error:
        raise RuntimeError(f"cannot run `{lean} --run {driver}`: {error}") from error
    if result.returncode != 0:
        detail = (result.stderr.strip() or result.stdout.strip()).replace("\n", " ")
        raise RuntimeError(f"`{lean} --run {driver}` exited {result.returncode}: {detail}")
    try:
        reported = json.loads(result.stdout)
    except json.JSONDecodeError as error:
        raise RuntimeError(f"cannot read the audit driver's output: {error}") from error
    if not isinstance(reported, list):
        raise RuntimeError("the audit driver did not report a list of problems")
    found = []
    for problem in reported:
        try:
            path, message = problem["file"], problem["message"]
        except (KeyError, TypeError) as error:
            raise RuntimeError(f"malformed problem from the audit driver: {error}") from error
        # Only ever report a file that was asked about, so a driver that lost track of its
        # input cannot be mistaken for a clean run of a different file list.
        if path not in paths:
            raise RuntimeError(f"the audit driver reported an unrequested file: {path}")
        found.append((paths[path], message))
    return found


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Reject `meta import` in TauCeti sources.",
        epilog=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--root", type=pathlib.Path, default=pathlib.Path("."),
                        help="checkout holding the sources to audit (default: .)")
    parser.add_argument("--changed", type=pathlib.Path,
                        help="NUL-separated list of repository-relative changed paths; "
                             "omit to audit the whole library")
    parser.add_argument("--lean", default="lean",
                        help="the `lean` binary to run the driver with (default: lean)")
    parser.add_argument("--driver", type=pathlib.Path,
                        default=pathlib.Path(__file__).resolve().with_name(DRIVER),
                        help=f"the Lean driver that reads the headers (default: {DRIVER} "
                             "beside this script)")
    args = parser.parse_args(argv)

    if shutil.which(args.lean) is None and not pathlib.Path(args.lean).is_file():
        print(f"::error::check-meta-imports: no `lean` binary at {args.lean}")
        return 1
    if not args.driver.is_file():
        print(f"::error::check-meta-imports: no audit driver at {args.driver}")
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
        found = audit(args.lean, args.driver, args.root, names)
    except RuntimeError as error:
        print(f"::error::check-meta-imports: {error}")
        return 1

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
