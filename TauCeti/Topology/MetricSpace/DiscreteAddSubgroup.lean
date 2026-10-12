/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

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

## Main results

* `AddSubgroup.finite_inter`: a discrete additive subgroup meets a bounded set in a finite set.
* `AddSubgroup.ncard_inter_le_ncard_closedBall_inter`: a set of diameter at most `r`
  carries at most as many points of a discrete additive subgroup as the closed ball of radius `r`
  centred at the origin.
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
