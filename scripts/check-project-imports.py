#!/usr/bin/env python3
"""Preflight project-local imports against the complete exact candidate source tree.

No Lake environment or compiled artifacts are used. ProjectImports.lean uses the
pinned Lean header parser and reads candidate sources only as data. External
imports, elaboration, and all existing build/audit gates remain Lake's responsibility.
"""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import subprocess


def inventory(root: Path) -> list[dict]:
    """Fail closed on unreadable, absent, or symlinked source inventory."""
    if not (root / "TauCeti").is_dir() or (root / "TauCeti").is_symlink():
        raise ValueError("missing or symlinked TauCeti source directory")
    names = ["TauCeti.lean"]
    for directory, dirs, files in os.walk(root / "TauCeti", onerror=_raise):
        for name in dirs + files:
            path = Path(directory) / name
            if path.is_symlink():
                raise ValueError(f"symlinked source path: {path}")
        names.extend((Path(directory) / name).relative_to(root).as_posix()
                     for name in files if name.endswith(".lean"))
    sources = []
    for name in sorted(names):
        path = root / name
        if not path.is_file() or path.is_symlink():
            raise ValueError(f"missing or symlinked source: {name}")
        # JSON preserves whitespace/escapes in paths; components preserve quoted Lean names.
        sources.append({"file": str(path), "components": list(Path(name[:-5]).parts)})
    return sources


def _raise(error: OSError) -> None:
    raise error


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path("."))
    parser.add_argument("--lean", default="lean")
    parser.add_argument("--driver", type=Path,
                        default=Path(__file__).resolve().with_name("ProjectImports.lean"))
    args = parser.parse_args(argv)
    try:
        root = args.root.resolve()
        sources = inventory(root)
        result = subprocess.run([args.lean, "--run", str(args.driver.resolve())],
                                input=json.dumps(sources), capture_output=True,
                                text=True, check=False)
        if result.returncode:
            raise ValueError(f"Lean header driver exited {result.returncode}: "
                             f"{result.stderr.strip() or result.stdout.strip()}")
        report = json.loads(result.stdout)
        if not isinstance(report, dict) or report.get("checked") != len(sources):
            raise ValueError("header driver did not check the complete source inventory")
        problems = report.get("problems")
        if not isinstance(problems, list):
            raise ValueError("header driver did not report a list of problems")
        paths = {source["file"]: str(Path(source["file"]).relative_to(root))
                 for source in sources}
        for problem in problems:
            if (not isinstance(problem, dict) or problem.get("file") not in paths
                    or not isinstance(problem.get("message"), str)):
                raise ValueError("malformed problem from header driver")
        for problem in problems:
            name = paths[problem["file"]].replace("\r", "\\r").replace("\n", "\\n")
            message = problem["message"].replace("\r", "\\r").replace("\n", "\\n")
            # Plain text keeps candidate-controlled names out of workflow command syntax.
            print(f"{name}: {message}")
        if problems:
            print(f"check-project-imports: {len(problems)} problem(s); compilation refused")
            return 1
        print(f"check-project-imports: all local imports exist in {len(sources)} "
              "exact-candidate source(s)")
        return 0
    except (OSError, ValueError, TypeError) as error:
        print(f"check-project-imports: {error}")
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
