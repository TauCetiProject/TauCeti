#!/usr/bin/env python3
"""Hermetic tests for the advisory structure nudge.

    python3 scripts/test_structure_nudge.py

Covers the tokenizer spec (acronyms, digits, single letters, lowercase-first
names) and the pair-rule detector: two files sharing a CamelCase prefix should
be a directory, in either order (extension added beside an anchor, anchor
added beside extensions, or a second extension). The whole-tree surface lives
in `structure_nudge_snapshot.txt` (regenerate with `--tree-dry-run`), reviewed
by humans rather than asserted here, since the tree moves daily.
"""

from __future__ import annotations

import unittest

import structure_nudge as sn


class TestTokenize(unittest.TestCase):
    def test_spec_fixtures(self):
        cases = {
            "JHolomorphic": ["J", "Holomorphic"],
            "JHolomorphicProdMap": ["J", "Holomorphic", "Prod", "Map"],
            "NNReal": ["NN", "Real"],
            "L2Norm": ["L2", "Norm"],
            "pAdic": ["p", "Adic"],
            "CStarAlgebra": ["C", "Star", "Algebra"],
            "RootsOfUnity": ["Roots", "Of", "Unity"],
            "SemigroupGroupTimeSlice": ["Semigroup", "Group", "Time", "Slice"],
            "W2k": ["W2k"],
            "Basic": ["Basic"],
        }
        for base, want in cases.items():
            self.assertEqual(sn.tokenize(base), want, base)


def T(*paths: str) -> set[str]:
    return set(paths)


D = "TauCeti/Analysis/Demo"


class TestCandidates(unittest.TestCase):
    def test_existing_subdirectory(self):
        cands = sn.candidates_for(f"{D}/FooBaz.lean", T(f"{D}/Foo/Bar.lean"))
        self.assertEqual([c["prefix"] for c in cands], ["Foo"])
        self.assertTrue(cands[0]["subdir"])

    def test_extension_beside_anchor_triggers(self):
        # Foo.lean exists; adding FooBar.lean makes the pair -> directory time.
        cands = sn.candidates_for(f"{D}/FooBar.lean", T(f"{D}/Foo.lean"))
        self.assertEqual(len(cands), 1)
        self.assertTrue(cands[0]["anchor"])
        self.assertFalse(cands[0]["is_prefix_of_family"])

    def test_second_extension_triggers(self):
        cands = sn.candidates_for(f"{D}/FooBaz.lean", T(f"{D}/FooBar.lean"))
        self.assertEqual(len(cands), 1)
        self.assertEqual(cands[0]["family_size"], 1)
        self.assertFalse(cands[0]["anchor"])

    def test_anchor_beside_extensions_triggers(self):
        # Adding Foo.lean where FooBar/FooBaz exist: this file becomes
        # Foo/Basic.lean (or Defs.lean) in the relocation.
        cands = sn.candidates_for(
            f"{D}/Foo.lean", T(f"{D}/FooBar.lean", f"{D}/FooBaz.lean"))
        self.assertEqual(len(cands), 1)
        self.assertTrue(cands[0]["is_prefix_of_family"])
        self.assertEqual(cands[0]["examples"], ["FooBar", "FooBaz"])

    def test_lone_file_is_silent(self):
        self.assertEqual(
            sn.candidates_for(f"{D}/FooBar.lean", T(f"{D}/Unrelated.lean")), [])
        self.assertEqual(sn.candidates_for(f"{D}/Foo.lean", T()), [])

    def test_token_boundary_not_string_prefix(self):
        # Football is NOT a Foo extension: token boundary must match.
        self.assertEqual(
            sn.candidates_for(f"{D}/FooBar.lean", T(f"{D}/Football.lean")), [])
        self.assertEqual(
            sn.candidates_for(f"{D}/Football.lean", T(f"{D}/Foo.lean")), [])

    def test_competing_prefixes_all_reported(self):
        tree = T(f"{D}/PrimeDiscriminantA.lean", f"{D}/PrimeX.lean")
        cands = sn.candidates_for(f"{D}/PrimeDiscriminantF.lean", tree)
        self.assertEqual([c["prefix"] for c in cands],
                         ["Prime", "PrimeDiscriminant"])
        self.assertEqual(cands[0]["family_size"], 2)
        self.assertEqual(cands[1]["family_size"], 1)

    def test_simultaneous_adds_count(self):
        # A sibling added by the same PR counts toward the pair.
        cands = sn.candidates_for(f"{D}/FooBar.lean", T(f"{D}/FooBaz.lean"))
        self.assertEqual(len(cands), 1)

    def test_non_taucet_or_non_lean_ignored(self):
        self.assertEqual(sn.candidates_for("scripts/FooBar.py", T()), [])
        self.assertEqual(
            sn.candidates_for("Other/FooBar.lean", T("Other/Foo.lean")), [])

    def test_render(self):
        findings = {
            f"{D}/FooBar.lean":
                sn.candidates_for(f"{D}/FooBar.lean", T(f"{D}/Foo.lean")),
            f"{D}/Quux.lean":
                sn.candidates_for(f"{D}/Quux.lean", T(f"{D}/QuuxA.lean")),
        }
        body = sn.render_comment("abc123", findings)
        self.assertIn(sn.MARKER, body)
        self.assertIn("never blocks", body)
        self.assertIn("move as you add", body)
        self.assertIn("`Foo/Basic.lean` or `Foo/Defs.lean`", body)
        self.assertIn("as `Quux/Basic.lean` or `Quux/Defs.lean`", body)


if __name__ == "__main__":
    unittest.main()
