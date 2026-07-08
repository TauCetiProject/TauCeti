#!/usr/bin/env python3
"""Tests for the roadmap-label classifier.

Run the fast, hermetic checks:

    python3 scripts/test_roadmap_label.py

Optionally replay the whole PR history against a live GitHub (needs `gh` auth and
a TauCetiRoadmap checkout); this is how the classifier was validated and is not
run in CI:

    python3 scripts/test_roadmap_label.py --replay-live \
        --repo TauCetiProject/TauCeti --roadmap-dir /path/to/TauCetiRoadmap
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys

import roadmap_label as rl

# The canonical roadmap set as of writing; the real code reads this from a
# checkout, but the unit tests pin it so they need no network.
AREAS = {
    "CombinatorialHeegaardFloer", "ConformalMapping", "ContourIntegration",
    "Exchangeability", "GeometricTopology", "HeegaardFloer", "JacobianChallenge",
    "Multiquadratic", "OneParameterSemigroups", "OrthogonalL2Bases", "PDE",
    "ReductiveGroups", "UniversalCovers",
}

TC = ["TauCeti/Analysis/Foo.lean"]        # an allowed (AI-ownable) math diff
INFRA = ["TauCeti/Foo.lean", ".github/workflows/x.yml"]  # trips the scope guard

# (name, title, body, files, expected_label)
CASES = [
    # 1. citation resolves the area (real bodies, abbreviated) -----------------
    ("full path", "feat: add semigroup exponential shifts",
     "It advances TauCetiRoadmap/OneParameterSemigroups/README.md, Part A.", TC,
     "roadmap/OneParameterSemigroups"),
    ("bare README path", "feat(Analysis/Contour): piecewise C1",
     "toward the roadmap (roadmap `ContourIntegration/README.md`: ...).", TC,
     "roadmap/ContourIntegration"),
    ("suggested.lean path", "feat: add quotient comodules",
     "See TauCetiRoadmap/ReductiveGroups/Suggested.lean for the target.", TC,
     "roadmap/ReductiveGroups"),

    # 2. infra override wins even over a citation ------------------------------
    ("infra beats citation", "feat: add roadmap CI",
     "advances TauCetiRoadmap/ContourIntegration/README.md", INFRA, "roadmap/none"),
    ("infra feat (website)", "feat: add site favicon", "", [".github/x", "web/y"],
     "roadmap/none"),
    ("empty diff", "feat: something", "advances TauCetiRoadmap/PDE/README.md", [],
     "roadmap/none"),

    # 3. non-roadmap titles, no citation --------------------------------------
    ("refactor", "refactor: move split into Cylinder.lean", "", TC, "roadmap/none"),
    ("fix", "fix: drop the vacuous coe lemma", "", TC, "roadmap/none"),
    ("mathlib bump", "chore: bump mathlib to 40b45a0, fix breaking changes", "",
     ["TauCeti/A.lean", "lake-manifest.json", "lean-toolchain"], "roadmap/none"),

    # 4. new mathematics, no parseable citation -> Unknown --------------------
    ("feat cites decl not file", "feat(Analysis/Contour): continuous argument lift",
     "Prerequisite for homologyCauchyTheorem (Dixon) and the residue theorem.", TC,
     "roadmap/Unknown"),
    ("feat no roadmap section", "feat: general conditional-expectation helper", "",
     TC, "roadmap/Unknown"),

    # edge: non-canonical area token is ignored (no bogus label) ---------------
    ("unknown area token", "feat: add thing",
     "advances TauCetiRoadmap/NotARoadmap/README.md", TC, "roadmap/Unknown"),
    # edge: two areas cited -> no single roadmap to name, so Unknown -----------
    ("multi-area citation", "feat: add thing",
     "spans TauCetiRoadmap/PDE/README.md and TauCetiRoadmap/Multiquadratic/README.md",
     TC, "roadmap/Unknown"),
    # a refactor bump touching only the pins is allowed-set + non-roadmap title
    ("pin-only bump", "chore: forward bump", "",
     ["lake-manifest.json", "lean-toolchain"], "roadmap/none"),
]


def run_unit() -> int:
    fails = 0
    for name, title, body, files, expected in CASES:
        got = rl.classify(title, body, files, AREAS)
        ok = got == expected
        fails += not ok
        print(f"  [{'ok' if ok else 'FAIL'}] {name}: {got}"
              + ("" if ok else f"  (expected {expected})"))
    # parse helper spot checks
    assert rl.parse_cited_areas("TauCetiRoadmap/PDE/README.md", AREAS) == {"PDE"}
    assert rl.parse_cited_areas("nothing here", AREAS) == set()
    assert rl.is_infra(["TauCeti/A.lean"]) is False
    assert rl.is_infra(["scripts/x.sh"]) is True
    print(f"\n{len(CASES) - fails}/{len(CASES)} classifier cases passed")
    return 1 if fails else 0


def run_replay(repo: str, roadmap_dir: str) -> int:
    """Replay the whole PR history; report the bucket distribution.

    This is a characterization check (no hard oracle for 700+ PRs): it prints the
    split and asserts only invariants that must always hold -- every label is in
    the known namespace, and any PR reaching outside the allowed path set is
    roadmap/none.
    """
    import pathlib
    areas = rl.canonical_areas(pathlib.Path(roadmap_dir))
    prs = json.loads(subprocess.run(
        ["gh", "pr", "list", "--repo", repo, "--state", "all", "--limit", "5000",
         "--json", "number,title,body,files"],
        check=True, text=True, stdout=subprocess.PIPE).stdout)
    from collections import Counter
    tally: Counter[str] = Counter()
    valid = {rl.NONE_LABEL, rl.UNKNOWN_LABEL} | {rl.area_label(a) for a in areas}
    for p in prs:
        files = [f["path"] for f in p.get("files") or []]
        label = rl.classify(p.get("title") or "", p.get("body") or "", files, areas)
        tally[label] += 1
        assert label in valid, f"#{p['number']}: label {label} outside namespace"
        if rl.is_infra(files):
            assert label == rl.NONE_LABEL, f"#{p['number']}: infra but {label}"
    print(f"replayed {sum(tally.values())} PRs across {len(areas)} roadmaps:")
    for name, n in sorted(tally.items(), key=lambda kv: -kv[1]):
        print(f"  {name:32} {n}")
    return 0


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--replay-live", action="store_true")
    ap.add_argument("--repo", default="TauCetiProject/TauCeti")
    ap.add_argument("--roadmap-dir")
    a = ap.parse_args()
    if a.replay_live:
        if not a.roadmap_dir:
            ap.error("--replay-live needs --roadmap-dir")
        return run_replay(a.repo, a.roadmap_dir)
    return run_unit()


if __name__ == "__main__":
    raise SystemExit(main())
