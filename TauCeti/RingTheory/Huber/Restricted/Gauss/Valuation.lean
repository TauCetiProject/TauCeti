/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Restricted.Gauss.Norm
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.GaussValuation
public import TauCeti.RingTheory.Valuation.Continuous.Valued

/-!
# Comparison of the unit-radius Gauss valuation with the Gauss norm

Over an ultrametric normed field `K` (equipped with the valuation `NormedField.toValued`), the
trivial-weight restricted power-series ring `K⟨T₁, …, Tₙ⟩` carries two constructions of the
unit-radius Gauss functional:

* the continuous valuation `TauCeti.Huber.weightedGaussValuation` extending `NormedField.valuation`,
  taking values in `ℝ≥0`; and
* the Gauss norm `MvPowerSeries.gaussNorm` at unit polyradius, transported across the comparison
  equivalence `TauCeti.Huber.restrictedMvPowerSeriesGaussEquiv`.

This file shows that the real value of `weightedGaussValuation` agrees with the Gauss norm on every
restricted power series, and that every power-bounded element of `K⟨T₁, …, Tₙ⟩` has unit-radius
Gauss valuation at most `1` (both when `K` is nontrivially normed, using
`TauCeti.Huber.weightedSubring_powerBoundedSubring_eq`, and when `K` is trivially normed).

## Main results

* `TauCeti.Huber.unitGaussValuation`: the unit-radius Gauss valuation `K⟨T₁, …, Tₙ⟩ → ℝ≥0`,
  together with `TauCeti.Huber.unitGaussValuation_def`,
  `TauCeti.Huber.coe_unitGaussValuation_eq_norm`, `TauCeti.Huber.coe_unitGaussValuation`,
  `TauCeti.Huber.unitGaussValuation_eq_zero_iff`, `TauCeti.Huber.unitGaussValuation_weightedC`,
  `TauCeti.Huber.unitGaussValuation_weightedX`,
  `TauCeti.Huber.unitGaussValuation_le_one_iff_mem_weightedSubring`, and
  `TauCeti.Huber.unitGaussValuation_le_one_of_mem_powerBoundedSubring`.

## References

* S. Bosch, U. Güntzer, and R. Remmert, *Non-Archimedean Analysis*, §5.1.1.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Remark and Definition 5.48 and
  Example 7.57.
-/

public section

namespace TauCeti.Huber

open scoped NNReal NormedField

section UnitGaussValuation

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

/-- The unit Gauss valuation is continuous. -/
theorem isContinuous_unitGaussValuation :
    (unitGaussValuation n K).IsContinuous :=
  isContinuous_weightedGaussValuation _

variable {K} in
/-- The unit Gauss valuation has real value equal to the Gauss norm of
`restrictedMvPowerSeriesGaussEquiv f`. -/
theorem coe_unitGaussValuation_eq_norm
    (f : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight) :
    (unitGaussValuation n K f : ℝ) =
      ‖restrictedMvPowerSeriesGaussEquiv f‖ := by
  rw [unitGaussValuation_def]
  refine le_antisymm ?_ ?_
  · obtain ⟨ν, hν⟩ := exists_coeff_eq_weightedGaussValuation
      (NormedField.isContinuous_valuation (K := K)) (f := f)
    rw [← hν, ← coe_restrictedMvPowerSeriesGaussEquiv]
    exact MvPowerSeries.norm_coeff_le_norm (restrictedMvPowerSeriesGaussEquiv f) ν
  · obtain ⟨ν, hν⟩ := MvPowerSeries.exists_norm_coeff_eq_norm
      (restrictedMvPowerSeriesGaussEquiv f)
    rw [← hν, coe_restrictedMvPowerSeriesGaussEquiv]
    exact NNReal.coe_le_coe.mpr
      (coeff_le_weightedGaussValuation (NormedField.isContinuous_valuation (K := K)) f ν)

/-- **The unit Gauss valuation coerces to Mathlib's unit-radius `MvPowerSeries.gaussNorm`.** -/
theorem coe_unitGaussValuation
    (f : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight) :
    (unitGaussValuation n K f : ℝ) =
      MvPowerSeries.gaussNorm norm (fun _ : Fin n ↦ (1 : ℝ)) (f : MvPowerSeries (Fin n) K) := by
  rw [coe_unitGaussValuation_eq_norm, MvPowerSeries.norm_eq_gaussNorm,
    coe_restrictedMvPowerSeriesGaussEquiv]

/-- The unit Gauss valuation vanishes only on the zero series. -/
@[simp]
theorem unitGaussValuation_eq_zero_iff
    {f : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight} :
    unitGaussValuation n K f = 0 ↔ f = 0 := by
  rw [unitGaussValuation_def, weightedGaussValuation_eq_zero_iff]
  simp only [NormedField.valuation_apply, nnNorm_eq_zero]
  exact ⟨fun h ↦ Subtype.ext (MvPowerSeries.ext fun ν ↦ by simp [h ν]), fun h ν ↦ by simp [h]⟩

/-- On constants, `unitGaussValuation` restricts to `‖·‖₊`. -/
@[simp]
theorem unitGaussValuation_weightedC (c : K) :
    unitGaussValuation n K
        (weightedC (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight c) = ‖c‖₊ := by
  rw [unitGaussValuation_def, weightedGaussValuation_weightedC, NormedField.valuation_apply]

/-- Every coordinate variable `Tᵢ` has unit Gauss valuation `1`. -/
@[simp]
theorem unitGaussValuation_weightedX (i : Fin n) :
    unitGaussValuation n K
        (weightedX (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight i) = 1 := by
  rw [unitGaussValuation_def, weightedGaussValuation_weightedX]

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
/-- **The unit Gauss valuation is at most `1` on power-bounded series.** -/
theorem unitGaussValuation_le_one_of_mem_powerBoundedSubring
    {f : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight}
    (hf : f ∈ powerBoundedSubring
      (weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight)) :
    unitGaussValuation n K f ≤ 1 := by
  rw [unitGaussValuation_def]
  refine (weightedGaussValuation_le_iff _).mpr fun ν ↦ ?_
  by_cases hnt : ∃ c : K, 1 < ‖c‖
  · let : NontriviallyNormedField K := ⟨hnt⟩
    rw [← weightedSubring_powerBoundedSubring_eq n, mem_weightedSubring, mem_weightedNhd] at hf
    have hcoeff : MvPowerSeries.coeff ν (f : MvPowerSeries (Fin n) K) ∈ powerBoundedSubring K := by
      simpa only [weightMul_one_weight, Subring.mem_toAddSubgroup] using hf ν
    exact NNReal.coe_le_coe.mp (isPowerBounded_iff_norm_le_one.mp
      (mem_powerBoundedSubring.mp hcoeff))
  · push Not at hnt
    exact NNReal.coe_le_coe.mp (hnt _)

end UnitGaussValuation

end TauCeti.Huber
