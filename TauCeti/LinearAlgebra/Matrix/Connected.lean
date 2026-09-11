/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Defs
public import TauCeti.Logic.Relation

/-!
# Strong connectivity of the directed graph of a matrix

A square matrix `A` with entries in a partially ordered type determines a directed graph on its
index set, with an edge from `i` to a distinct `j` when `0 < A i j`. When the off-diagonal
entries are nonnegative, strong connectivity of this directed graph is the same as the absence of
a disconnecting cut: no nonempty proper set of indices has all of its outgoing entries zero.

For a symmetric `A` the directed graph is an ordinary graph and strong connectivity is ordinary
connectedness; the cut condition is then the form in which
[Stacks, Tag 0C6Z](https://stacks.math.columbia.edu/tag/0C6Z) states the connectedness condition
on the intersection matrix of a numerical type.

## Main results

* `Matrix.forall_reflTransGen_ne_and_pos_iff`: for a matrix with nonnegative off-diagonal
  entries, strong connectivity of its directed graph is the absence of a disconnecting cut.
-/

public section

namespace Matrix

/-- For a matrix `A` whose off-diagonal entries are nonnegative, strong connectivity of the
directed graph with an edge from `i` to a distinct `j` when `0 < A i j` is equivalent to the
absence of a disconnecting cut: no nonempty proper set of indices `s` has all of its outgoing
entries `A i j`, for `i ∈ s` and `j ∉ s`, zero. No symmetry of `A` is assumed, so the left-hand
side is connectedness of an ordinary graph only when `A` is symmetric, as the intersection matrix
of a numerical type is. The right-hand side is then the form in which
[Stacks, Tag 0C6Z](https://stacks.math.columbia.edu/tag/0C6Z) states the connectedness condition
on a numerical type, so this is what supplies the `connected` field of `TauCeti.NumericalType`
when one is constructed.

The nonnegativity hypothesis is what turns a nonzero cross-entry into a positive one, and so
cannot be dropped. -/
lemma forall_reflTransGen_ne_and_pos_iff {C R : Type*} [PartialOrder R] [Zero R]
    (A : Matrix C C R) (hA : ∀ i j, i ≠ j → 0 ≤ A i j) :
    (∀ i j, Relation.ReflTransGen (fun i j ↦ i ≠ j ∧ 0 < A i j) i j) ↔
      ∀ s : Set C, s.Nonempty → s ≠ Set.univ → ¬ ∀ i ∈ s, ∀ j ∉ s, A i j = 0 := by
  rw [Relation.forall_reflTransGen_iff]
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
