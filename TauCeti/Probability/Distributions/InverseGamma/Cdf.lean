/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.InverseGamma.Basic
public import TauCeti.Probability.Distributions.Gamma.Cdf

/-!
# Cumulative distribution function of the inverse-gamma distribution

This file computes the inverse-gamma cdf as an upper regularized Gamma value.

It also gives the corresponding event probability for a random variable with an inverse-gamma
law.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal

namespace TauCeti

namespace Probability

variable {a r : ℝ}

/-! ### Cumulative distribution function -/

/-- **The cdf of a valid inverse-gamma law** is the upper regularized Gamma value
`1 - P(a, r / x)` on the positive half-line and zero elsewhere. -/
@[simp]
theorem cdf_inverseGammaMeasure_eq (ha : 0 < a) (hr : 0 < r) (x : ℝ) :
    cdf (inverseGammaMeasure a r) x =
      if x ≤ 0 then 0 else 1 - regularizedGamma a (r / x) := by
  let _ := isProbabilityMeasure_inverseGammaMeasure ha hr
  split_ifs with hx
  · rw [cdf_eq_real, measureReal_def,
      measure_mono_null (Iic_subset_Iic.mpr hx) (inverseGammaMeasure_Iic_zero a r),
      ENNReal.toReal_zero]
  · have hxpos : 0 < x := not_le.mp hx
    rw [cdf_eq_real, inverseGammaMeasure_of_pos ha hr, measureReal_def,
      Measure.map_apply measurable_inv measurableSet_Iic]
    have hpre : Inv.inv ⁻¹' Iic x = Iic 0 ∪ Ici x⁻¹ := by
      ext y
      simp only [mem_preimage, mem_Iic, mem_union, mem_Ici]
      constructor
      · intro hy
        rcases le_or_gt y 0 with hy0 | hy0
        · exact Or.inl hy0
        · exact Or.inr ((inv_le_comm₀ hy0 hxpos).mp hy)
      · rintro (hy | hy)
        · exact (inv_nonpos.mpr hy).trans hxpos.le
        · have hypos : 0 < y := (inv_pos.mpr hxpos).trans_le hy
          exact (inv_le_comm₀ hypos hxpos).mpr hy
    have hdisj : Disjoint (Iic (0 : ℝ)) (Ici x⁻¹) := Set.disjoint_left.2 fun y hy0 hy ↦
      (not_lt_of_ge hy0) ((inv_pos.mpr hxpos).trans_le hy)
    have hzero : gammaMeasure a r (Iic 0) = 0 := by
      let _ := isProbabilityMeasure_gammaMeasure ha hr
      rw [← measureReal_eq_zero_iff, measureReal_Iic_gammaMeasure ha hr,
        mul_zero, regularizedGamma_eq_zero_of_nonpos_right a le_rfl]
    rw [hpre, measure_union hdisj measurableSet_Ici,
      hzero, zero_add]
    have hsets : Ici x⁻¹ =ᵐ[gammaMeasure a r] Ioi x⁻¹ :=
      (Ioi_ae_eq_Ici' (μ := gammaMeasure a r) (by
        rw [gammaMeasure]
        exact measure_singleton _)).symm
    rw [measure_congr hsets, ← measureReal_def, measureReal_Ioi_gammaMeasure ha hr x⁻¹,
      div_eq_mul_inv]

/-- For positive shape and rate, an inverse-gamma random variable satisfies `P(X ≤ x) = 0` when
`x ≤ 0`, and `P(X ≤ x) = 1 - regularizedGamma a (r / x)` when `x > 0`. -/
theorem measureReal_le_of_hasLaw_inverseGammaMeasure {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℝ} (ha : 0 < a) (hr : 0 < r)
    (hX : HasLaw X (inverseGammaMeasure a r) P) (x : ℝ) :
    P.real {ω | X ω ≤ x} =
      if x ≤ 0 then 0 else 1 - regularizedGamma a (r / x) := by
  let _ := isProbabilityMeasure_inverseGammaMeasure ha hr
  rw [hX.measureReal_eq (p := fun y : ℝ => y ≤ x) measurableSet_Iic, Set.Iic_def,
    ← cdf_eq_real, cdf_inverseGammaMeasure_eq ha hr]


end Probability

end TauCeti
