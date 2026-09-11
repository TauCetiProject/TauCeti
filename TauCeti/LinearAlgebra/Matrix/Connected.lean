/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Defs
public import TauCeti.Logic.Relation

/-!
# Connectedness of the graph of a matrix

A square matrix `A` with entries in a partially ordered type determines a graph on its index set,
joining distinct indices `i`, `j` with `0 < A i j`. When the off-diagonal entries are
nonnegative, connectedness of this graph is the same as the absence of a disconnecting cut: no
nonempty proper set of indices has all its cross-entries zero. This is the form in which
[Stacks, Tag 0C6Z](https://stacks.math.columbia.edu/tag/0C6Z) states the connectedness condition
on the intersection matrix of a numerical type.

## Main results

* `Matrix.forall_reflTransGen_ne_and_pos_iff`: for a matrix with nonnegative off-diagonal
  entries, connectedness of its graph is the absence of a disconnecting cut.
-/

public section

namespace Matrix

/-- For a matrix `A` whose off-diagonal entries are nonnegative, connectedness of the graph
joining distinct indices `i`, `j` with `0 < A i j` is equivalent to the absence of a disconnecting
cut: no nonempty proper set of indices `s` has all its cross-entries zero. The right-hand side is
the form in which [Stacks, Tag 0C6Z](https://stacks.math.columbia.edu/tag/0C6Z) states the
connectedness condition on a numerical type, so this is what supplies the `connected` field of
`TauCeti.NumericalType` when one is constructed.

The nonnegativity hypothesis is what turns a nonzero cross-entry into a positive one, and so
cannot be dropped. -/
lemma forall_reflTransGen_ne_and_pos_iff {C R : Type*} [PartialOrder R] [Zero R]
    (A : Matrix C C R) (hA : ∀ i j, i ≠ j → 0 ≤ A i j) :
    (∀ i j, Relation.ReflTransGen (fun i j ↦ i ≠ j ∧ 0 < A i j) i j) ↔
      ∀ s : Set C, s.Nonempty → s ≠ Set.univ → ¬ ∀ i ∈ s, ∀ j ∉ s, A i j = 0 := by
  rw [TauCeti.forall_reflTransGen_iff]
  refine forall_congr' fun s ↦ imp_congr_right fun _ ↦ imp_congr_right fun _ ↦ ?_
  constructor
  · rintro ⟨i, hi, j, hj, -, hpos⟩ hcut
    exact hpos.ne' (hcut i hi j hj)
  · intro hcut
    by_contra hcon
    refine hcut fun i hi j hj ↦ ?_
    have hij : i ≠ j := fun h ↦ hj (h ▸ hi)
    by_contra hne
    exact hcon ⟨i, hi, j, hj, hij, lt_of_le_of_ne (hA i j hij) (Ne.symm hne)⟩

end Matrix
