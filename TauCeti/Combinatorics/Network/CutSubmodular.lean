/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Network.Flow
public import TauCeti.Order.Lattice.Submodular

/-!
# Submodularity of directed cut bounds

This file proves that the capacity of the arrows leaving a vertex set is submodular. It then
expresses the signed upper cut bound for lower and upper arrow bounds as an outgoing capacity plus
a modular vertex-weight function, proving that this more general cut bound is also submodular.
These facts let the minimum-cut lattice apply both to ordinary directed networks and to bounded
assignments with signed lower bounds.

## Main results

* `TauCeti.isSubmodular_outgoingArrowSum`: nonnegative outgoing arrow capacity is submodular.
* `TauCeti.cutBound_eq_arrowSum_sub_sum_excessAt`: the upper cut bound is an outgoing arrow sum
  shifted by the excess of the lower bound.
* `TauCeti.isSubmodular_cutBound`: a pair of ordered signed bounds has a submodular upper cut bound.
-/

public section

namespace TauCeti

open Finset

universe u v w

variable {V : Type u} {Q : V → V → Type v} {K : Type w}
variable [Fintype V] [DecidableEq V] [∀ x y, Fintype (Q x y)]

/-- The capacity of arrows leaving a vertex set is submodular when every arrow capacity is
nonnegative. Loops, parallel arrows, and arrows in both directions are allowed. -/
theorem isSubmodular_outgoingArrowSum [AddCommMonoid K] [PartialOrder K]
    [IsOrderedAddMonoid K] (cap : Assignment Q K) (hcap : 0 ≤ cap) :
    IsSubmodular (fun S : Finset V ↦ arrowSum cap S Sᶜ) := by
  rw [isSubmodular_def]
  intro S T
  simp only [sup_eq_union, inf_eq_inter, arrowSum_eq_sum_ite]
  simp only [← sum_add_distrib]
  apply sum_le_sum
  intro v _
  apply sum_le_sum
  intro w _
  apply sum_le_sum
  intro e _
  have he := hcap v w e
  by_cases hvS : v ∈ S <;> by_cases hvT : v ∈ T <;>
    by_cases hwS : w ∈ S <;> by_cases hwT : w ∈ T <;>
    simp_all

/-- The signed upper cut bound is the outgoing arrow sum for the difference between upper and lower
bounds, minus the total excess of the lower bound on the source side. -/
theorem cutBound_eq_arrowSum_sub_sum_excessAt [AddCommGroup K]
    (lo hi : Assignment Q K) (S : Finset V) :
    cutBound lo hi S = arrowSum (hi - lo) S Sᶜ - ∑ v ∈ S, excessAt lo v := by
  rw [cutBound_def, arrowSum_sub, sum_excessAt_eq_arrowSum_sub]
  abel

/-- The signed upper cut bound is submodular whenever the lower bound is at most the upper bound.
No feasibility assumption on the bounds is needed. -/
theorem isSubmodular_cutBound [AddCommGroup K] [PartialOrder K] [IsOrderedAddMonoid K]
    (lo hi : Assignment Q K) (h : lo ≤ hi) : IsSubmodular (cutBound lo hi) := by
  have hcap : 0 ≤ hi - lo := by
    intro v w e
    exact sub_nonneg.mpr (h v w e)
  have hdir := isSubmodular_outgoingArrowSum (Q := Q) (cap := hi - lo) hcap
  have hmod := isSubmodular_finsetSum (f := fun v ↦ -excessAt lo v)
  have hadd := hdir.add hmod
  rw [isSubmodular_def]
  intro S T
  simpa [cutBound_eq_arrowSum_sub_sum_excessAt, sub_eq_add_neg] using hadd.apply S T

end TauCeti
