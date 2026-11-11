#!/usr/bin/env python3
"""Fixture check for scripts/DeclarationNames.lean: test_declaration_names.py [PROJECT_ROOT].

Builds a tiny Lean library twice with the repository's pinned toolchain in a temporary
directory (no Mathlib, no shared caches, no repository sources changed) and checks the
DECLARATION-NAMES record: added names, private and auxiliary names excluded, a new module
fully added, and the incomplete cases.
"""
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

RECORD = "DECLARATION-NAMES "

V1 = '''namespace TauCeti.Probe
theorem base_thm : 1 = 1 := rfl
private theorem privateBase : 2 = 2 := rfl
end TauCeti.Probe
'''

V2 = '''namespace TauCeti.Probe
theorem base_thm : 1 = 1 := rfl
private theorem privateBase : 2 = 2 := rfl
theorem added_thm : 3 = 3 := rfl
private theorem privateAdded : 4 = 4 := rfl
inductive Color where
  | red
  | green
def twice : Nat → Nat
  | 0 => 0
  | k + 1 => twice k + 2
theorem «λ.雪» : 5 = 5 := rfl
end TauCeti.Probe
'''

FRESH = '''theorem TauCeti.Fresh.fresh_thm : 6 = 6 := rfl
'''


def run(script, root, env, modules, head="h" * 40, base="b" * 40, tested="t" * 40,
        base_dir="base-oleans"):
    result = subprocess.run(
        ["lake", "env", "lean", "--run", str(script), head, base, tested, str(modules),
         ".lake/build/lib/lean", base_dir],
        cwd=root, env=env, text=True, capture_output=True)
    assert result.returncode == 0, result.stdout + result.stderr
    lines = [l for l in result.stdout.splitlines() if l.startswith(RECORD)]
    assert len(lines) == 1, result.stdout + result.stderr
    assert lines[0].isascii(), lines[0]
    return json.loads(lines[0][len(RECORD):])


def main():
    project = Path(sys.argv[1] if len(sys.argv) > 1 else Path(__file__).resolve().parents[1])
    script = (project / "scripts/DeclarationNames.lean").resolve()
    with tempfile.TemporaryDirectory() as temp:
        root = Path(temp)
        (root / "lean-toolchain").write_text((project / "lean-toolchain").read_text())
        (root / "lakefile.toml").write_text('name = "names-fixture"\n[[lean_lib]]\nname = "TauCeti"\n')
        (root / "TauCeti").mkdir()
        env = {**os.environ, "LAKE_CACHE_DIR": "", "LAKE_ARTIFACT_CACHE": "false",
               "LAKE_RESTORE_ARTIFACTS": "false", "LAKE_NO_CACHE": "true", "LEAN_NUM_THREADS": "2"}
        (root / "TauCeti/Probe.lean").write_text(V1)
        subprocess.run(["lake", "build", "TauCeti.Probe"], cwd=root, env=env, check=True)
        base_dir = root / "base-oleans/TauCeti"
        base_dir.mkdir(parents=True)
        shutil.copy(root / ".lake/build/lib/lean/TauCeti/Probe.olean", base_dir / "Probe.olean")

        (root / "TauCeti/Probe.lean").write_text(V2)
        (root / "TauCeti/Fresh.lean").write_text(FRESH)
        subprocess.run(["lake", "build", "TauCeti.Probe", "TauCeti.Fresh"], cwd=root, env=env, check=True)
        modules = root / "modules"
        modules.write_text("TauCeti.Probe\nTauCeti.Fresh\n")

        record = run(script, root, env, modules)
        assert record["version"] == 1 and record["complete"] is True, record
        assert record["head"] == "h" * 40 and record["base"] == "b" * 40 and record["tested"] == "t" * 40
        probe = record["added"]["TauCeti.Probe"]
        assert probe == sorted(probe), probe
        for expected in ("TauCeti.Probe.added_thm", "TauCeti.Probe.Color", "TauCeti.Probe.Color.red",
                         "TauCeti.Probe.Color.green", "TauCeti.Probe.twice", "TauCeti.Probe.λ.雪"):
            assert expected in probe, (expected, probe)
        assert "TauCeti.Probe.base_thm" not in probe, probe
        assert not any("private" in n.lower() or n.startswith("_private") for n in probe), probe
        for name in probe:
            last = name.rsplit(".", 1)[-1]
            assert not last.startswith("_") and "match_" not in name and not last.isdigit(), name
            assert last not in ("rec", "recOn", "casesOn", "noConfusion", "noConfusionType",
                                "toCtorIdx", "ofNat"), name
        assert record["added"]["TauCeti.Fresh"] == ["TauCeti.Fresh.fresh_thm"], record["added"]

        # A listed module without a tested header is incomplete.
        modules.write_text("TauCeti.Probe\nTauCeti.Missing\n")
        incomplete = run(script, root, env, modules)
        assert incomplete["complete"] is False and incomplete["added"] == {}, incomplete

        # An existing but unreadable base header is incomplete.
        modules.write_text("TauCeti.Probe\n")
        (base_dir / "Probe.olean").write_bytes(b"not an olean")
        incomplete = run(script, root, env, modules)
        assert incomplete["complete"] is False and incomplete["added"] == {}, incomplete

        # Too many modules is incomplete before any header is read.
        modules.write_text("".join(f"TauCeti.M{i}\n" for i in range(4097)))
        incomplete = run(script, root, env, modules)
        assert incomplete["complete"] is False and incomplete["added"] == {}, incomplete

        # Bad arguments exit 2 with no record.
        result = subprocess.run(["lake", "env", "lean", "--run", str(script)], cwd=root, env=env,
                                text=True, capture_output=True)
        assert result.returncode == 2 and RECORD not in result.stdout, result.stdout + result.stderr
    print("declaration names fixture: ok")


if __name__ == "__main__":
    main()
