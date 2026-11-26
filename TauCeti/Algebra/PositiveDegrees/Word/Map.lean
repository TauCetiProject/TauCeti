/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.PositiveDegrees.Map
public import TauCeti.Algebra.PositiveDegrees.Word.Basic
import Mathlib.Algebra.Group.Submonoid.BigOperators

/-!
# Word cutoffs under positive degree maps

A target cutoff on the mapped sum bounds the source word by the map's cutoff modulus.

Adapted from `Mei/Algebra/PositiveDegrees/Word.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`bf3986029ff4d3eb4025d4067489511b0724374e`, released under Apache 2.0.
-/

public section

namespace TauCeti.PositiveDegreeMap

variable {N M : Type*} [AddCommMonoid N] [AddCommMonoid M]
  {d : PositiveDegrees N} {e : PositiveDegrees M} (T : PositiveDegreeMap d e)

/-- Words of nonzero allowed source increments whose mapped sum has target degree at most
`k` belong to the source word cutoff at `T.modulus k`. -/
theorem setOf_degree_map_sum_le_subset_wordCutoff (k : ℕ) :
    {l : List N | (∀ n ∈ l, n ∈ d.monoid ∧ n ≠ 0) ∧
      e.degree (T l.sum) ≤ k} ⊆ d.wordCutoff (T.modulus k) := by
  intro l hl
  exact d.mem_wordCutoff.mpr
    ⟨hl.1, T.degree_le k (d.monoid.list_sum_mem (fun n hn => (hl.1 n hn).1)) hl.2⟩

/-- There are finitely many words of nonzero allowed source increments whose mapped sum has
target degree at most `k`. -/
theorem finite_setOf_degree_map_sum_le (k : ℕ) :
    Set.Finite {l : List N | (∀ n ∈ l, n ∈ d.monoid ∧ n ≠ 0) ∧
      e.degree (T l.sum) ≤ k} :=
  (d.finite_wordCutoff (T.modulus k)).subset (T.setOf_degree_map_sum_le_subset_wordCutoff k)

end TauCeti.PositiveDegreeMap
