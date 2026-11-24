/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Restricted.GaussNorm
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.GaussValuation
public import TauCeti.RingTheory.Valuation.Continuous.Valued

/-!
# The unit Gauss valuation on restricted series over an ultrametric normed field

For an ultrametric normed field `K`, specializing `TauCeti.Huber.weightedGaussValuation` to
`NormedField.valuation` gives the unit-radius Gauss valuation `TauCeti.Huber.unitGaussValuation` on
`K⟨T₁, …, Tₙ⟩`, sending `f = ∑_ν a_ν T^ν` to `max_ν ‖a_ν‖₊`. Its unfolding equation
`TauCeti.Huber.unitGaussValuation_def` connects it directly to the generic `weightedGaussValuation`
API (coefficient bounds, attainment, continuity, and values on constants, variables, and
monomials).

## Main definitions

* `TauCeti.Huber.unitGaussValuation`: the unit-radius Gauss valuation `K⟨T₁, …, Tₙ⟩ → ℝ≥0`.

## Main results

* `TauCeti.Huber.unitGaussValuation_def`: unfolding to `weightedGaussValuation`.
* `TauCeti.Huber.unitGaussValuation_eq_zero_iff`: `unitGaussValuation n K f = 0 ↔ f = 0`.
* `TauCeti.Huber.coe_unitGaussValuation`: coercion to Mathlib's `MvPowerSeries.gaussNorm`.
* `TauCeti.Huber.unitGaussValuation_le_one_iff_mem_weightedSubring` and
  `TauCeti.Huber.unitGaussValuation_le_one_of_mem_powerBoundedSubring`: unit Gauss valuation at
  most `1` characterizes `K°⟨T₁, …, Tₙ⟩` and holds on `(K⟨T₁, …, Tₙ⟩)°`.
-/

public section

namespace TauCeti.Huber

open scoped NNReal

variable (n : ℕ) (K : Type*) [NormedField K] [IsUltrametricDist K]

/-- **The unit Gauss valuation on `K⟨T₁, …, Tₙ⟩`**, sending `f = ∑_ν a_ν T^ν` to `max_ν ‖a_ν‖₊`. -/
noncomputable def unitGaussValuation :
    Valuation
      (weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight)
      ℝ≥0 :=
  weightedGaussValuation n (NormedField.isContinuous_valuation (K := K))

/-- Unfolding equation bridging `unitGaussValuation` to `weightedGaussValuation`. -/
theorem unitGaussValuation_def :
    unitGaussValuation n K =
      weightedGaussValuation n (NormedField.isContinuous_valuation (K := K)) :=
  (rfl)

/-- The unit Gauss valuation vanishes only on the zero series. -/
@[simp]
theorem unitGaussValuation_eq_zero_iff
    {f : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight} :
    unitGaussValuation n K f = 0 ↔ f = 0 := by
  rw [unitGaussValuation_def, weightedGaussValuation_eq_zero_iff]
  simp only [NormedField.valuation_apply, nnNorm_eq_zero]
  exact ⟨fun h ↦ Subtype.ext (MvPowerSeries.ext fun ν ↦ by simp [h ν]), fun h ν ↦ by simp [h]⟩

/-- The unit Gauss valuation coerces to Mathlib's unit-radius `MvPowerSeries.gaussNorm`. -/
theorem coe_unitGaussValuation
    (f : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight) :
    (unitGaussValuation n K f : ℝ) =
      MvPowerSeries.gaussNorm norm (fun _ : Fin n ↦ (1 : ℝ)) (f : MvPowerSeries (Fin n) K) := by
  rw [← coe_restrictedMvPowerSeriesGaussEquiv f, ← MvPowerSeries.norm_eq_gaussNorm]
  refine le_antisymm ?_ (MvPowerSeries.norm_le_iff.mpr fun ν ↦ ?_)
  · obtain ⟨ν, hν⟩ :=
      exists_coeff_eq_weightedGaussValuation (NormedField.isContinuous_valuation (K := K)) (f := f)
    have h := MvPowerSeries.norm_coeff_mul_prod_le (restrictedMvPowerSeriesGaussEquiv f) ν
    rw [unitGaussValuation_def, ← hν, NormedField.valuation_apply, coe_nnNorm]
    simpa only [coe_restrictedMvPowerSeriesGaussEquiv, one_pow, Finsupp.prod,
      Finset.prod_const_one, mul_one] using h
  · rw [unitGaussValuation_def]
    simpa only [coe_restrictedMvPowerSeriesGaussEquiv, one_pow, Finsupp.prod,
      Finset.prod_const_one, mul_one, ← coe_nnNorm, NormedField.valuation_apply] using
      NNReal.coe_le_coe.mpr
        (coeff_le_weightedGaussValuation (NormedField.isContinuous_valuation (K := K)) f ν)

/-- A series has unit Gauss valuation at most `1` if and only if it lies in `K°⟨T₁, …, Tₙ⟩`. -/
theorem unitGaussValuation_le_one_iff_mem_weightedSubring
    {f : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight} :
    unitGaussValuation n K f ≤ 1 ↔
      f ∈ weightedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight
        (powerBoundedSubring K) := by
  rw [unitGaussValuation_def, weightedGaussValuation_le_iff, mem_weightedSubring, mem_weightedNhd]
  refine forall_congr' fun ν ↦ ?_
  rw [weightMul_one_weight, Subring.mem_toAddSubgroup, mem_powerBoundedSubring,
    isPowerBounded_iff_norm_le_one, NormedField.valuation_apply, ← NNReal.coe_le_coe, coe_nnNorm,
    NNReal.coe_one]

variable {n K} in
/-- **The unit Gauss valuation is at most `1` on power-bounded series.** When `K` is nontrivially
normed, `K⟨T⟩° = K°⟨T⟩`; when `K` is trivially normed, every element of `K` already has norm at
most `1`. -/
theorem unitGaussValuation_le_one_of_mem_powerBoundedSubring
    {f : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight}
    (hf : f ∈ powerBoundedSubring
      (weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight)) :
    unitGaussValuation n K f ≤ 1 := by
  by_cases hnt : ∃ c : K, 1 < ‖c‖
  · let : NontriviallyNormedField K := { ‹NormedField K› with non_trivial := hnt }
    rw [unitGaussValuation_le_one_iff_mem_weightedSubring,
      weightedSubring_powerBoundedSubring_eq n]
    exact hf
  · push Not at hnt
    rw [unitGaussValuation_def, weightedGaussValuation_le_iff]
    intro ν
    rw [NormedField.valuation_apply, ← NNReal.coe_le_coe, coe_nnNorm, NNReal.coe_one]
    exact hnt _

end TauCeti.Huber
