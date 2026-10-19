/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.GeneralizedPareto.Basic

/-!
# Cumulative distribution function of the generalized Pareto law

For positive scale `s`, the generalized Pareto cdf is zero below zero. On its support it is
`1 - (1 + ξ * x / s) ^ (-1 / ξ)` for nonzero shape `ξ`, with the exponential limit
`1 - exp (-x / s)` at shape zero. When `ξ < 0`, the cdf is one at and above the finite upper
endpoint `-s / ξ`.

## Main results

* `TauCeti.Probability.cdf_generalizedParetoMeasure_of_shape_ne_zero` gives the nonzero-shape
  formula in the interior of the support.
* `TauCeti.Probability.cdf_generalizedParetoMeasure_eq` gives all shape and support branches.

## References

* S. Coles, *An Introduction to Statistical Modeling of Extreme Values*, Springer (2001),
  Chapter 4.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set

namespace TauCeti.Probability

variable {s ξ x : ℝ}

private lemma cdf_generalizedParetoMeasure_eq_preimage (hs : 0 < s) (ξ x : ℝ) :
    cdf (generalizedParetoMeasure s ξ) x =
      (expMeasure 1).real (generalizedParetoMap s ξ ⁻¹' Iic x) := by
  let _ := isProbabilityMeasure_generalizedParetoMeasure hs ξ
  rw [cdf_eq_real, generalizedParetoMeasure_of_pos hs,
    map_measureReal_apply (measurable_generalizedParetoMap_right s ξ) measurableSet_Iic]

private lemma nonneg_log_div_shape (hs : 0 < s) (hξ : ξ ≠ 0) (hx : 0 ≤ x)
    (hbase : 0 < 1 + ξ * x / s) :
    0 ≤ log (1 + ξ * x / s) / ξ := by
  rcases lt_or_gt_of_ne hξ with hξ | hξ
  · exact div_nonneg_of_nonpos
      (log_nonpos (by positivity) (by
        have : ξ * x / s ≤ 0 := div_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonpos_of_nonneg hξ.le hx) hs.le
        linarith)) hξ.le
  · exact div_nonneg (log_nonneg (by
      have : 0 ≤ ξ * x / s := div_nonneg (mul_nonneg hξ.le hx) hs.le
      linarith)) hξ.le

/-- On the interior of its support, the cdf of a positive-scale, nonzero-shape generalized
Pareto law is `1 - (1 + ξ * x / s) ^ (-1 / ξ)`. -/
theorem cdf_generalizedParetoMeasure_of_shape_ne_zero (hs : 0 < s) (hξ : ξ ≠ 0)
    (hx : 0 ≤ x) (hbase : 0 < 1 + ξ * x / s) :
    cdf (generalizedParetoMeasure s ξ) x =
      1 - (1 + ξ * x / s) ^ (-1 / ξ) := by
  let z := log (1 + ξ * x / s) / ξ
  have hz : 0 ≤ z := nonneg_log_div_shape hs hξ hx hbase
  have hpre : generalizedParetoMap s ξ ⁻¹' Iic x = Iic z := by
    ext e
    simp only [mem_preimage, mem_Iic]
    exact generalizedParetoMap_le_iff hs hξ hbase e
  let _ := isProbabilityMeasure_expMeasure one_pos
  rw [cdf_generalizedParetoMeasure_eq_preimage hs ξ x, hpre, ← cdf_eq_real,
    cdf_expMeasure_eq one_pos, ite_eq_left hz, one_mul]
  rw [Real.rpow_def_of_pos hbase]
  congr 2
  dsimp only [z]
  ring

/-- The cdf of a positive-scale generalized Pareto law vanishes below zero. -/
theorem cdf_generalizedParetoMeasure_eq_zero_of_neg (hs : 0 < s) (ξ : ℝ) (hx : x < 0) :
    cdf (generalizedParetoMeasure s ξ) x = 0 := by
  rw [cdf_generalizedParetoMeasure_eq_preimage hs ξ x]
  have hpre : generalizedParetoMap s ξ ⁻¹' Iic x =ᵐ[expMeasure 1] ∅ := by
    filter_upwards [ae_pos_expMeasure 1] with e he
    have hg : 0 < generalizedParetoMap s ξ e := by
      simpa using strictMono_generalizedParetoMap hs ξ he
    simp [not_le_of_gt (hx.trans hg)]
  rw [measureReal_congr hpre, measureReal_empty]

/-- For negative shape, the generalized Pareto cdf is one at and above its finite upper
endpoint. -/
theorem cdf_generalizedParetoMeasure_eq_one (hs : 0 < s) (hξ : ξ < 0)
    (hbase : 1 + ξ * x / s ≤ 0) :
    cdf (generalizedParetoMeasure s ξ) x = 1 := by
  have hnum : s + ξ * x ≤ 0 := by
    have hdiv : (s + ξ * x) / s ≤ 0 := by
      calc
        (s + ξ * x) / s = 1 + ξ * x / s := by field_simp
        _ ≤ 0 := hbase
    rcases div_nonpos_iff.mp hdiv with ⟨_, hs0⟩ | ⟨h, _⟩
    · linarith
    · exact h
  have hendpoint : -s / ξ ≤ x := by
    rw [div_le_iff_of_neg hξ]
    nlinarith
  have hx : 0 < x := by
    exact (div_pos_of_neg_of_neg (neg_neg_of_pos hs) hξ).trans_le hendpoint
  have hpre : generalizedParetoMap s ξ ⁻¹' Iic x =ᵐ[expMeasure 1] Set.univ := by
    filter_upwards [ae_pos_expMeasure 1] with e he
    simp only [mem_preimage, mem_Iic, mem_univ]
    rw [generalizedParetoMap_of_shape_ne_zero hξ.ne]
    have hexp : 0 < exp (ξ * e) := exp_pos _
    have hbound : s * (exp (ξ * e) - 1) / ξ < -s / ξ := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_lt_mul_of_neg_right (by nlinarith [mul_pos hs hexp]) (inv_lt_zero.mpr hξ)
    simp [hbound.le.trans hendpoint]
  let _ := isProbabilityMeasure_expMeasure one_pos
  rw [cdf_generalizedParetoMeasure_eq_preimage hs ξ x, measureReal_congr hpre,
    probReal_univ]

/-- The cdf of a positive-scale generalized Pareto law, including the exponential branch and
the finite upper endpoint for negative shape. -/
theorem cdf_generalizedParetoMeasure_eq (hs : 0 < s) (ξ x : ℝ) :
    cdf (generalizedParetoMeasure s ξ) x =
      if x < 0 then 0
      else if ξ = 0 then 1 - exp (-x / s)
      else if 0 < 1 + ξ * x / s then 1 - (1 + ξ * x / s) ^ (-1 / ξ)
      else 1 := by
  by_cases hx : x < 0
  · rw [ite_eq_left hx, cdf_generalizedParetoMeasure_eq_zero_of_neg hs ξ hx]
  rw [ite_eq_right hx]
  have hx0 : 0 ≤ x := not_lt.mp hx
  by_cases hξ : ξ = 0
  · subst ξ
    rw [ite_eq_left rfl, generalizedParetoMeasure_zero hs,
      cdf_expMeasure_eq (inv_pos.mpr hs), ite_eq_left hx0]
    congr 2
    field_simp
  rw [ite_eq_right hξ]
  by_cases hbase : 0 < 1 + ξ * x / s
  · rw [ite_eq_left hbase,
      cdf_generalizedParetoMeasure_of_shape_ne_zero hs hξ hx0 hbase]
  rw [ite_eq_right hbase]
  have hξ0 : ξ < 0 := by
    rcases lt_or_gt_of_ne hξ with hξ | hξ
    · exact hξ
    · have : 0 ≤ ξ * x / s := div_nonneg (mul_nonneg hξ.le hx0) hs.le
      linarith
  exact cdf_generalizedParetoMeasure_eq_one hs hξ0 (not_lt.mp hbase)

end TauCeti.Probability
