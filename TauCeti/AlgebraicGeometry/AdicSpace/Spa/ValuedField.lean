/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Basic
public import TauCeti.RingTheory.Valuation.Continuous.Valued
public import Mathlib.RingTheory.Valuation.ValuationSubring

/-!
# The closed point of the adic spectrum of a valued field

The defining valuation of a valued field `K` determines a point of the adic spectrum with
plus ring its valuation ring. Every point of this spectrum specializes to this point, and
its singleton is closed. This supplies the distinguished point needed when using valued
fields as sources of morphisms to adic spectra.
-/

public section

namespace TauCeti.ValuationSpectrum

variable (K : Type*) [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  [Valued K Γ₀]

/-- The point of the adic spectrum represented by the defining valuation of a valued field. -/
def valuedSpaPoint : spa (Valued.v (R := K)).valuationSubring.toSubring :=
  ⟨ofValuation Valued.v, (mem_spa_iff _ _).mpr
    ⟨(isContinuous_ofValuation_iff _).mpr Valued.isContinuous_v, fun a ha ↦ by
      rw [vle_ofValuation, map_one]
      exact (Valuation.mem_valuationSubring_iff _ a).mp ha⟩⟩

/-- The underlying valuation-spectrum point is the class of the defining valuation. -/
@[simp]
theorem coe_valuedSpaPoint :
    (valuedSpaPoint K : Spv K) = ofValuation (Valued.v : Valuation K Γ₀) := (rfl)

/-- Every point of the adic spectrum of a valued field with its valuation ring specializes to
the point represented by the defining valuation. -/
theorem specializes_valuedSpaPoint
    (x : spa (Valued.v (R := K)).valuationSubring.toSubring) : x ⤳ valuedSpaPoint K := by
  rw [subtype_specializes_iff, coe_valuedSpaPoint]
  refine specializes_of_forall_mem_basicOpen fun a b hab ↦ ?_
  rw [mem_basicOpen_iff, vle_ofValuation, vle_ofValuation, map_zero,
    nonpos_iff_eq_zero] at hab
  have hb : b ≠ 0 := fun h ↦ hab.2 (h ▸ map_zero _)
  have hdiv : a / b ∈ (Valued.v (R := K)).valuationSubring := by
    rw [Valuation.mem_valuationSubring_iff, map_div₀]
    exact div_le_one_of_le₀ hab.1 zero_le
  have hle := valuation_le_one_of_mem_spa x.property hdiv
  have hxb : x.val.valuation b ≠ 0 := (Valuation.ne_zero_iff _).mpr hb
  rw [map_div₀, div_le_one₀ (pos_iff_ne_zero.mpr hxb)] at hle
  exact (mem_basicOpen_iff_valuation a b x.val).mpr ⟨hle, hxb⟩

/-- The defining valuation is a closed point of the adic spectrum of its valued field. -/
theorem isClosed_singleton_valuedSpaPoint :
    IsClosed ({valuedSpaPoint K} : Set (spa (Valued.v (R := K)).valuationSubring.toSubring)) := by
  rw [← closure_subset_iff_isClosed]
  intro x hx
  exact Set.mem_singleton_iff.mpr
    (((specializes_iff_mem_closure.mpr hx).antisymm (specializes_valuedSpaPoint K x)).eq.symm)

end TauCeti.ValuationSpectrum
