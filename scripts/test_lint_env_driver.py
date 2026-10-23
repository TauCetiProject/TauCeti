#!/usr/bin/env python3
"""Real Lean origin smoke test: test_lint_env_driver.py PROJECT_ROOT DRIVER_EXE.

Uses the pinned Mathlib by path and a temporary fixture library. No repository
sources, baselines or shared caches are changed. Build the driver separately.
"""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

from lint_env_locations import LOCATIONS, ORIGINS, locations


def main():
    project, driver = map(lambda p: Path(p).resolve(), sys.argv[1:])
    with tempfile.TemporaryDirectory() as temp:
        root = Path(temp)
        (root / "lean-toolchain").write_text((project / "lean-toolchain").read_text())
        (root / "lakefile.toml").write_text(
            'name = "origin-fixture"\n[[require]]\nname = "mathlib"\n'
            f'path = "{project / ".lake/packages/mathlib"}"\n'
            '[[lean_lib]]\nname = "TauCeti"\n')
        (root / "TauCeti").mkdir()
        (root / "TauCeti/Probe.lean").write_text('''module
public import Mathlib.Algebra.Module.Torsion.Basic
public section
namespace TauCeti
@[simp] theorem «λ.雪» (n : Nat) : n + 0 = n := Nat.add_zero n
@[simp] theorem «quote"slash\\» (n : Nat) : n + 0 = n := Nat.add_zero n
@[simp] private theorem privateProbe (n : Nat) : n + 0 = n := Nat.add_zero n
end TauCeti
''')
        env = {**os.environ, "LAKE_CACHE_DIR": "", "LAKE_ARTIFACT_CACHE": "false",
               "LAKE_RESTORE_ARTIFACTS": "false", "LAKE_NO_CACHE": "true", "LEAN_NUM_THREADS": "4"}
        subprocess.run(["lake", "build", "TauCeti.Probe"], cwd=root, env=env, check=True)
        (root / "modules").write_text("TauCeti.Probe\n")
        (root / "marker").write_text("ORIGIN-TEST-COMPLETE\n")
        result = subprocess.run(["lake", "env", str(driver), "/tmp/origin-test",
                                 str(root / "marker"), str(root / "modules"), "simpNF"],
                                cwd=root, env=env, text=True, capture_output=True)
        assert result.returncode == 1, result.stdout + result.stderr
        origin = json.loads(next(l[len(ORIGINS):] for l in result.stdout.splitlines()
                                 if l.startswith(ORIGINS)))
        assert origin["total"] == 3 and origin["truncated"] is False, origin
        records = origin["records"]
        assert sum(r.get("unknown") == "private_or_generated" for r in records) == 1, records
        new = "".join("simpNF " + r["report_name"] + "\n" for r in records)
        emitted = locations(result.stdout, new, "TauCeti.Probe\n", root, 3)
        known = [f for f in emitted["findings"] if "path" in f]
        assert len(known) == 2, emitted
        assert {f["path"] for f in known} == {"TauCeti/Probe.lean"}, emitted
        assert {f["line"] for f in known} == {5, 6}, emitted
        assert all(f["column"] == 17 for f in known), emitted
        assert {f["declaration"] for f in known} == {'TauCeti.«λ.雪»', 'TauCeti.«quote"slash\\»'}
        print(LOCATIONS + json.dumps(emitted, ensure_ascii=True))
        print("Real Lean escaped/Unicode/private origin smoke test passed")


if __name__ == "__main__":
    main()
