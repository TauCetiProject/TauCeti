/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Stallings.Basis
public import TauCeti.Combinatorics.Graph.Stallings.Coset.Basic
public import Mathlib.GroupTheory.Schreier
public import Mathlib.Tactic.LinearCombination

/-!
# The Schreier index formula for subgroups of free groups

Let `H` be a subgroup of finite index `i` of a free group `G` of finite rank. Then `H` is finitely
generated (Mathlib's `Subgroup.fg_of_index_ne_zero`) and its rank satisfies the exact Schreier
formula `rank H - 1 = i * (rank G - 1)` as integers. For the trivial free group both sides are
`-1`. For arbitrary finitely generated groups Mathlib's `Subgroup.rank_le_index_mul_rank` and
Tau Ceti's `Subgroup.rank_le_one_add_index_mul_rank_sub_one` are only inequalities; for a free
group of positive finite rank the latter is attained.

The formula is first read off the coset graph of a subgroup `H` of the free group on a finite
alphabet `α`. Its vertices are the `i` cosets of `H`, and its darts labelled by a basis letter,
rather than by the inverse of one, form an orientation with exactly `i * |α|` darts. The coset
graph is folded and connected and accepts `H`, so the Euler form of the rank of an accepted
subgroup gives `rank H + i = i * |α| + 1`. A free group of finite rank is isomorphic to the free
group on a finite basis, whose cardinality is the rank.

## Main results

* `Subgroup.rank_add_index_eq_index_mul_natCard_add_one`: the formula in natural numbers for the
  free group on `α`, `rank H + i = i * |α| + 1`.
* `Subgroup.rank_sub_one_eq_index_mul_natCard_sub_one`: the same formula as integers,
  `rank H - 1 = i * (|α| - 1)`.
* `Subgroup.rank_add_index_eq_index_mul_rank_add_one` and
  `Subgroup.rank_sub_one_eq_index_mul_rank_sub_one`: the two forms for a finitely generated free
  group `G`, with `rank G` in place of `|α|`.

## References

* I. Kapovich and A. Myasnikov, *Stallings foldings and subgroups of free groups*,
  Section 8, Lemma 8.2, Proposition 8.3 and Corollary 8.4.
-/

public section

namespace Subgroup

open TauCeti TauCeti.StallingsGraph

section FreeGroup

variable {α : Type*} (H : Subgroup (FreeGroup α)) [Finite α] [H.FiniteIndex]

/-- **Schreier's index formula** for a subgroup `H` of finite index `i` of the free group on a
finite alphabet `α`, in natural numbers: `rank H + i = i * |α| + 1`. -/
theorem rank_add_index_eq_index_mul_natCard_add_one :
    Group.rank H + H.index = H.index * Nat.card α + 1 := by
  have h := (cosetGraph H).rank_subgroup_add_card (cosetGraph H).base (cosetGraph_isFolded H)
    (cosetGraph H).isOrientation_setOf_label_snd (cosetGraph_connected H)
  rwa [rank_congr (cosetGraph_subgroup H),
    (cosetGraph_isComplete H).natCard_setOf_label_snd (cosetGraph_isFolded H), ← index_eq_card] at h

/-- **Schreier's index formula**: a subgroup `H` of finite index `i` of the free group on a
finite alphabet `α` satisfies `rank H - 1 = i * (|α| - 1)` as integers. -/
theorem rank_sub_one_eq_index_mul_natCard_sub_one :
    (Group.rank H : ℤ) - 1 = H.index * (Nat.card α - 1) := by
  have h := H.rank_add_index_eq_index_mul_natCard_add_one
  zify at h
  linear_combination h

end FreeGroup

section IsFreeGroup

variable {G : Type*} [Group G] [IsFreeGroup G] [Group.FG G] (H : Subgroup G) [H.FiniteIndex]

/-- **Schreier's index formula** for a subgroup `H` of finite index `i` of a finitely generated
free group `G`, in natural numbers: `rank H + i = i * rank G + 1`. -/
theorem rank_add_index_eq_index_mul_rank_add_one :
    Group.rank H + H.index = H.index * Group.rank G + 1 := by
  let b := IsFreeGroup.basis G
  let f : G →* FreeGroup (IsFreeGroup.Generators G) := b.repr
  have := b.finite_of_fg
  have := FiniteIndex.map_of_surjective H (f := f) b.repr.surjective
  have h := (H.map f).rank_add_index_eq_index_mul_natCard_add_one
  rwa [index_map_equiv, ← b.rank_eq_nat_card,
    ← Group.rank_congr (H.equivMapOfInjective f b.repr.injective)] at h

/-- **Schreier's index formula**: a subgroup `H` of finite index `i` of a finitely generated free
group `G` satisfies `rank H - 1 = i * (rank G - 1)` as integers. -/
theorem rank_sub_one_eq_index_mul_rank_sub_one :
    (Group.rank H : ℤ) - 1 = H.index * (Group.rank G - 1) := by
  have h := H.rank_add_index_eq_index_mul_rank_add_one
  zify at h
  linear_combination h

end IsFreeGroup

end Subgroup
