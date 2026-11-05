/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Data.Set.Card.Arithmetic
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Topology.MetricSpace.Pseudo.Real

/-!
# Counting points of a discrete additive subgroup

This file gives a uniform bound on the number of points of a discrete additive subgroup in a set
of bounded diameter.  Translating one point of the intersection to the origin embeds the
intersection into a closed ball of the same radius.

Since a nonzero discrete subgroup meets the closed ball through any of its nonzero vectors in a
finite set, it has a shortest nonzero vector; for a lattice this is a vector realizing its first
minimum.

## Main results

* `AddSubgroup.finite_inter`: a discrete additive subgroup meets a bounded set in a finite set.
* `AddSubgroup.ncard_inter_le_ncard_closedBall_inter`: a set of diameter at most `r`
  carries at most as many points of a discrete additive subgroup as the closed ball of radius `r`
  centred at the origin.
* `Submodule.exists_norm_le_of_ne_bot`: a nonzero discrete additive subgroup, viewed as a
  `ℤ`-submodule, has a shortest nonzero vector.
-/

public section

open Bornology Metric Set

namespace AddSubgroup

variable {E : Type*} [NormedAddCommGroup E] [ProperSpace E]

/-- A discrete additive subgroup meets a bounded set in a finite set: it is closed and discrete,
and the bounded set is contained in its compact closure. -/
theorem finite_inter (L : AddSubgroup E) [DiscreteTopology L] {s : Set E} (hs : IsBounded s) :
    (s ∩ (L : Set E)).Finite :=
  Metric.finite_isBounded_inter_isClosed
    (SetLike.isDiscrete_iff_discreteTopology.2 ‹DiscreteTopology L›) hs
    AddSubgroup.isClosed_of_discreteTopology

/-- A set whose points are pairwise at distance at most `r` carries at most as many points of a
discrete subgroup as the closed ball of radius `r` centred at the origin does.  Translating a
point of the intersection to the origin is what makes the bound uniform over all such sets. -/
theorem ncard_inter_le_ncard_closedBall_inter (L : AddSubgroup E) [DiscreteTopology L]
    {s : Set E} {r : ℝ} (hs : ∀ x ∈ s, ∀ y ∈ s, dist x y ≤ r) :
    (s ∩ (L : Set E)).ncard ≤ (closedBall (0 : E) r ∩ (L : Set E)).ncard := by
  rcases (s ∩ (L : Set E)).eq_empty_or_nonempty with h | ⟨z, hzs, hzL⟩
  · simp [h]
  refine Set.ncard_le_ncard_of_injOn (fun x ↦ x - z) ?_ (fun x _ y _ h ↦ by simpa using h)
    (L.finite_inter isBounded_closedBall)
  rintro x ⟨hxs, hxL⟩
  exact ⟨mem_closedBall_zero_iff.2 ((dist_eq_norm x z) ▸ hs x hxs z hzs),
    L.sub_mem hxL hzL⟩

end AddSubgroup

namespace Submodule

variable {E : Type*} [NormedAddCommGroup E] [ProperSpace E]

/-- A nonzero discrete additive subgroup of a proper normed additive group has a shortest nonzero
vector. -/
theorem exists_norm_le_of_ne_bot (L : Submodule ℤ E) [DiscreteTopology L] (hL : L ≠ ⊥) :
    ∃ l₀ ∈ L, l₀ ≠ 0 ∧ ∀ l ∈ L, l ≠ 0 → ‖l₀‖ ≤ ‖l‖ := by
  obtain ⟨l₁, hl₁, hl₁0⟩ := L.ne_bot_iff.mp hL
  have hfin : (closedBall (0 : E) ‖l₁‖ ∩ ((L : Set E) \ {0})).Finite :=
    (L.toAddSubgroup.finite_inter isBounded_closedBall).subset
      (inter_subset_inter_right _ sdiff_subset)
  obtain ⟨l₀, ⟨-, hl₀, hl₀0⟩, hmin⟩ := exists_min_image _ (‖·‖) hfin ⟨l₁, by simp, hl₁, hl₁0⟩
  refine ⟨l₀, hl₀, hl₀0, fun l hl hl0 ↦ ?_⟩
  by_cases hl' : ‖l‖ ≤ ‖l₁‖
  · exact hmin l ⟨by simpa using hl', hl, hl0⟩
  · exact (hmin l₁ ⟨by simp, hl₁, hl₁0⟩).trans (le_of_not_ge hl')

end Submodule
