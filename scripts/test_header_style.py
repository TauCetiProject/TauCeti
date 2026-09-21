#!/usr/bin/env python3
"""Compare header-prefix diagnostics with Mathlib's full-input checker.

Run with `lake env python3 scripts/test_header_style.py`. Compiles only the
trusted header driver; no TauCeti modules are built or imported.
"""

import json
import os
from pathlib import Path
import random
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent.parent
HEADER = (
    "/-\nCopyright (c) 2026 Jane Doe. All rights reserved.\n"
    "Released under Apache 2.0 license as described in the file LICENSE.\n"
    "Authors: Jane Doe\n-/\n"
)


def cases():
    headers = [
        HEADER, HEADER[:-1],
        HEADER.replace("Jane Doe\n-/", "Jane Doe,\n-/"),
        HEADER.replace("Authors:", "Author:"),
        HEADER.replace("Jane Doe\n-/", "Jane Doe,\n  Another Person\n-/"),
        HEADER.replace("\n-/\n", "\n-/ garbage\n"),
        HEADER.replace("\n-/\n", "\n  -/\n"),
        HEADER.replace("\n", "\r\n"),
        HEADER.replace("Doe. All", "Doe.\nAll"),
        HEADER.replace("Authors: Jane Doe", "Authors: "),
        HEADER.replace("/-\n", "/-!\n"),
        "", "/-\n", "-/\n", "unclosed header\nAuthors: Test,\n-/\nextra\n-/\n",
    ]
    tails = ["", "module\n", "\n/-!\nBody,\n  Unicode α😃\n-/\n", "\n-/\n", "\n" * 20]
    for header in headers:
        for tail in tails:
            yield header + tail
    # Exercise delimiter/continuation interactions, including malformed headers.
    rng = random.Random(7003)
    fragments = ["\n", ",\n", ",\n  ", "\n-/", "-/\n", ".\nAll rights reserved.",
                 "/-", "α😃", "\r\n", " ", "Authors: A", "\x00"]
    for _ in range(500):
        yield (HEADER if rng.randrange(2) else "") + "".join(
            rng.choice(fragments) for _ in range(rng.randrange(1, 15)))
    yield HEADER + ("-- irrelevant body α😃\n" * 10000)


def main():
    with tempfile.TemporaryDirectory(prefix="tauceti-header-test-") as tmp:
        tmp = Path(tmp)
        (tmp / "scripts").mkdir()
        subprocess.run(["lean", f"--root={ROOT}", "-o", str(tmp / "scripts/HeaderStyle.olean"),
                        str(ROOT / "scripts/HeaderStyle.lean")], check=True)
        paths = []
        for i, source in enumerate(cases()):
            path = tmp / f"case-{i}.lean"
            path.write_text(source)
            paths.append(str(path))
        driver = tmp / "Compare.lean"
        driver.write_text('''import scripts.HeaderStyle
open Mathlib.Linter
unsafe def compareHeaders : IO Unit := do
  let paths : List String := ''' + json.dumps(paths, ensure_ascii=False) + '''
  for path in paths do
    let full := copyrightHeaderChecks (← IO.FS.readFile path) expectedLicense
    let limited := copyrightHeaderChecks (← readCopyrightHeader path) expectedLicense
    unless full == limited do
      throw <| IO.userError s!"changed diagnostics for {path}"
  IO.println s!"header-style: {paths.length} full/prefix comparisons passed"
#eval compareHeaders
''')
        env = dict(os.environ, LEAN_PATH=str(tmp) + os.pathsep + os.environ.get("LEAN_PATH", ""))
        subprocess.run(["lean", str(driver)], env=env, check=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
