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

* `TauCeti.Huber.coe_weightedGaussValuation_normedField_eq_norm`: the real value of
  `weightedGaussValuation` equals `‖restrictedMvPowerSeriesGaussEquiv f‖`.
* `TauCeti.Huber.coe_weightedGaussValuation_normedField`: the real value of
  `weightedGaussValuation` equals `MvPowerSeries.gaussNorm` at unit polyradius.
* `TauCeti.Huber.weightedGaussValuation_le_one_of_mem_powerBoundedSubring`: every power-bounded
  restricted power series over an ultrametric normed field has unit-radius Gauss valuation at most
  `1`.

## References

* S. Bosch, U. Güntzer, and R. Remmert, *Non-Archimedean Analysis*, §5.1.1.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Remark and Definition 5.48 and
  Example 7.57.
-/

public section

namespace TauCeti.Huber

open scoped NNReal NormedField

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

/-- The unit-radius Gauss valuation extending `NormedField.valuation` has real value equal to the
Gauss norm of `restrictedMvPowerSeriesGaussEquiv f`. -/
theorem coe_weightedGaussValuation_normedField_eq_norm (n : ℕ)
    (f : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight) :
    (weightedGaussValuation n (Valued.isContinuous_v (R := K)) f : ℝ) =
      ‖restrictedMvPowerSeriesGaussEquiv f‖ := by
  refine le_antisymm ?_ ?_
  · obtain ⟨ν, hν⟩ := exists_coeff_eq_weightedGaussValuation
      (Valued.isContinuous_v (R := K)) (f := f)
    rw [← hν, ← coe_restrictedMvPowerSeriesGaussEquiv]
    exact MvPowerSeries.norm_coeff_le_norm (restrictedMvPowerSeriesGaussEquiv f) ν
  · obtain ⟨ν, hν⟩ := MvPowerSeries.exists_norm_coeff_eq_norm
      (restrictedMvPowerSeriesGaussEquiv f)
    rw [← hν, coe_restrictedMvPowerSeriesGaussEquiv]
    exact NNReal.coe_le_coe.mpr
      (coeff_le_weightedGaussValuation (Valued.isContinuous_v (R := K)) f ν)

/-- **The unit-radius Gauss valuation agrees with `MvPowerSeries.gaussNorm` at unit polyradius.** -/
theorem coe_weightedGaussValuation_normedField (n : ℕ)
    (f : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight) :
    (weightedGaussValuation n (Valued.isContinuous_v (R := K)) f : ℝ) =
      MvPowerSeries.gaussNorm norm (fun _ : Fin n ↦ (1 : ℝ)) (f : MvPowerSeries (Fin n) K) := by
  rw [coe_weightedGaussValuation_normedField_eq_norm, MvPowerSeries.norm_eq_gaussNorm,
    coe_restrictedMvPowerSeriesGaussEquiv]

/-- Every power-bounded restricted series over an ultrametric normed field has unit-radius Gauss
valuation at most `1`. -/
theorem weightedGaussValuation_le_one_of_mem_powerBoundedSubring (n : ℕ)
    {f : weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight}
    (hf : f ∈ powerBoundedSubring _) :
    weightedGaussValuation n (Valued.isContinuous_v (R := K)) f ≤ 1 := by
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

end TauCeti.Huber
