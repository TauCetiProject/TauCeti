#!/usr/bin/env python3
"""Hermetic tests for the advisory structure nudge.

    python3 scripts/test_structure_nudge.py

Covers the tokenizer spec (acronyms, digits, single letters, lowercase-first
names) and the candidate detector (existing subdirectory, anchor module, flat
family threshold, bare-prefix self-guard, competing prefixes, simultaneous
adds, below-threshold silence). The whole-tree false-positive surface lives in
`structure_nudge_snapshot.txt` (regenerate with `--tree-dry-run`), reviewed by
humans rather than asserted here, since the tree moves daily.
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
    def test_existing_subdirectory_wins_mention(self):
        tree = T(f"{D}/Foo/Bar.lean", f"{D}/Other.lean")
        cands = sn.candidates_for(f"{D}/FooBaz.lean", tree)
        self.assertEqual([c["prefix"] for c in cands], ["Foo"])
        self.assertTrue(cands[0]["subdir"])
        self.assertFalse(cands[0]["anchor"])

    def test_anchor_alone_is_not_a_trigger(self):
        # A topic file beside one extension is a normal pattern, not a family.
        self.assertEqual(
            sn.candidates_for(f"{D}/FooBar.lean", T(f"{D}/Foo.lean")), [])

    def test_anchor_is_supplementary_evidence_with_a_family(self):
        tree = T(f"{D}/Foo.lean", *[f"{D}/Foo{s}.lean" for s in ("A", "B", "C", "E")])
        cands = sn.candidates_for(f"{D}/FooD.lean", tree)
        self.assertEqual(len(cands), 1)
        self.assertTrue(cands[0]["anchor"])
        self.assertEqual(cands[0]["family_size"], 4)

    def test_flat_family_threshold(self):
        sibs = [f"{D}/Foo{s}.lean" for s in ("A", "B", "C")]
        self.assertEqual(sn.candidates_for(f"{D}/FooD.lean", T(*sibs)), [])
        sibs.append(f"{D}/FooE.lean")
        cands = sn.candidates_for(f"{D}/FooD.lean", T(*sibs))
        self.assertEqual(len(cands), 1)
        self.assertEqual(cands[0]["family_size"], 4)

    def test_bare_prefix_no_self_suggestion(self):
        # Adding Foo.lean itself must not suggest a Foo family/subdirectory.
        sibs = [f"{D}/Foo{s}.lean" for s in ("A", "B", "C", "E")]
        self.assertEqual(sn.candidates_for(f"{D}/Foo.lean", T(*sibs)), [])

    def test_token_boundary_not_string_prefix(self):
        # Football* files are NOT a Foo family: token boundary must match.
        sibs = [f"{D}/Football{s}.lean" for s in ("A", "B", "C", "E")]
        self.assertEqual(sn.candidates_for(f"{D}/FooBar.lean", T(*sibs)), [])

    def test_competing_prefixes_all_reported(self):
        # Both PrimeDiscriminant* (2-token) and Prime* (1-token) families exist;
        # neither is auto-chosen, both are reported.
        sibs = ([f"{D}/PrimeDiscriminant{s}.lean" for s in ("A", "B", "C", "E")]
                + [f"{D}/Prime{s}.lean" for s in ("W", "X", "Y", "Z")])
        cands = sn.candidates_for(f"{D}/PrimeDiscriminantF.lean", T(*sibs))
        self.assertEqual([c["prefix"] for c in cands],
                         ["Prime", "PrimeDiscriminant"])
        # The 1-token family counts every PrimeDiscriminant* file too.
        self.assertEqual(cands[0]["family_size"], 8)
        self.assertEqual(cands[1]["family_size"], 4)

    def test_simultaneous_adds_count_toward_family(self):
        sibs = [f"{D}/Foo{s}.lean" for s in ("A", "B")]
        added_sibling = f"{D}/FooC.lean"  # another file added by the same PR
        tree = T(*sibs, added_sibling, f"{D}/FooD.lean")
        cands = sn.candidates_for(f"{D}/FooE.lean", tree)
        self.assertEqual(len(cands), 1)
        self.assertEqual(cands[0]["family_size"], 4)

    def test_non_taucet_or_non_lean_ignored(self):
        self.assertEqual(sn.candidates_for("scripts/FooBar.py", T()), [])
        self.assertEqual(
            sn.candidates_for("Other/FooBar.lean", T("Other/Foo.lean")), [])

    def test_single_letter_prefix_reported_only_with_evidence(self):
        # J* families exist in the wild (JHolomorphic*); a 1-letter prefix is
        # reported like any other when the evidence is there...
        sibs = [f"{D}/J{s}.lean" for s in ("Alpha", "Beta", "Gamma", "Delta")]
        cands = sn.candidates_for(f"{D}/JEpsilon.lean", T(*sibs))
        self.assertEqual([c["prefix"] for c in cands], ["J"])
        # ...and stays silent without it.
        self.assertEqual(
            sn.candidates_for(f"{D}/JEpsilon.lean", T(f"{D}/JAlpha.lean")), [])

    def test_render_mentions_no_prescribed_path(self):
        tree = T(*[f"{D}/Foo{s}.lean" for s in ("A", "B", "C", "E")])
        findings = {f"{D}/FooD.lean": sn.candidates_for(f"{D}/FooD.lean", tree)}
        body = sn.render_comment("abc123", findings)
        self.assertIn(sn.MARKER, body)
        self.assertIn("never blocks", body)
        self.assertIn("preliminary PR", body)
        # The comment names the family directory but never a path for the
        # added file itself (that choice stays with the author).
        self.assertNotIn("Foo/D", body)


if __name__ == "__main__":
    unittest.main()
