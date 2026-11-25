/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
public import Mathlib.Topology.Algebra.Valued.WithVal
public import Mathlib.RingTheory.AdicCompletion.Basic

import TauCeti.RingTheory.Huber.CompleteRankOneBase.FractionRing

/-!
# The valued fraction field of a complete discrete valuation ring

Adic completeness for the maximal ideal makes the fraction field complete for the
normalized discrete valuation. The two valuations used to transfer completeness both
have the original discrete valuation ring as their valuation ring.
-/

public section

namespace TauCeti.IsDiscreteValuationRing

open _root_.IsDiscreteValuationRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

/-- The fraction field of an adically complete DVR is complete for the normalized
discrete valuation. -/
theorem completeSpace_withVal_of_isAdicComplete [IsAdicComplete (IsLocalRing.maximalIdeal R) R] :
    CompleteSpace (WithVal ((maximalIdeal R).valuation K)) := by
  obtain ⟨π, hπ⟩ := exists_irreducible R
  let : TopologicalSpace R := (Ideal.span {π}).adicTopology
  have : Huber.IsCompleteRankOneBase R π :=
    { ringKrullDim_eq_one := ringKrullDim_eq_one R
      ne_zero := hπ.ne_zero
      not_isUnit := hπ.not_isUnit
      isAdic := rfl
      isAdicComplete := hπ.maximalIdeal_eq ▸ inferInstanceAs
        (IsAdicComplete (IsLocalRing.maximalIdeal R) R) }
  have heq : ((maximalIdeal R).valuation K).IsEquiv (ValuationRing.valuation R K) := by
    rw [Valuation.isEquiv_iff_val_le_one]
    intro x
    exact ⟨fun hx ↦ by
      obtain ⟨a, rfl⟩ := exists_lift_of_le_one hx
      exact (ValuationRing.integers R K).map_le_one a,
      fun hx ↦ by
        obtain ⟨a, rfl⟩ := (ValuationRing.integers R K).exists_of_le_one hx
        exact IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ a⟩
  exact heq.uniformEquiv.completeSpace_iff.mpr
    (Huber.IsCompleteRankOneBase.completeSpace_withVal π K)

end TauCeti.IsDiscreteValuationRing
