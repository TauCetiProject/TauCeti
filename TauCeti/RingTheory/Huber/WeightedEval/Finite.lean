/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.WeightedEval.Basic

/-!
# Evaluation bounds for finite weights

For a finite weight family, the boundedness condition for evaluating weighted restricted series
can be checked on individual weighted variables. The powers of each finite set of weighted
variables lie in its bounded submonoid closure. This is useful when factoring finite weighted
presentations through a larger coefficient ring.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Proposition 5.30(2)
  and Proposition 5.50.
-/

public section

open Pointwise

namespace TauCeti.Huber

variable {k : ℕ} {A B : Type*} [CommRing A] [CommRing B] [TopologicalSpace B]

/-- For finite weights, power-boundedness of each weighted variable is equivalent to
power-boundedness of the corresponding set. This lets finite weighted presentations be evaluated
from bounds on their generators. -/
theorem isWeightedVarPowerBounded_iff_of_finite {φ : A →+* B} {T : Fin k → Set A}
    {b : Fin k → B} (hT : ∀ i, (T i).Finite) :
    IsWeightedVarPowerBounded φ T b ↔ ∀ i, ∀ t ∈ T i, IsPowerBounded (φ t * b i) := by
  rw [isWeightedVarPowerBounded_iff]
  refine ⟨fun h i t ht ↦ isPowerBounded_iff.mpr ((h i).subset ?_), fun h i ↦ ?_⟩
  · rintro _ ⟨n, rfl⟩
    have hvar : φ t * b i ∈ weightedVar φ T b i := by
      rw [weightedVar_def]
      exact Set.mul_mem_mul ⟨t, ht, rfl⟩ rfl
    exact Set.mem_iUnion.mpr ⟨n, Set.pow_mem_pow hvar⟩
  · have hfin : (weightedVar φ T b i).Finite := by
      rw [weightedVar_def, Set.mul_singleton]
      exact ((hT i).image φ).image _
    refine (isBounded_submonoidClosure hfin ?_).subset
      (Set.iUnion_subset fun n ↦ Submonoid.pow_subset Submonoid.subset_closure)
    intro x hx
    rw [weightedVar_def] at hx
    obtain ⟨_, ⟨t, ht, rfl⟩, _, rfl, rfl⟩ := hx
    exact h i t ht

end TauCeti.Huber
