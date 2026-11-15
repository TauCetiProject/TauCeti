/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.GeneralizedExtremeValue.Basic

/-!
# Cumulative distribution function of the generalized extreme-value law

For positive scale, the generalized extreme-value cdf is

`exp (-((1 + ξ * ((x - m) / s)) ^ (-1 / ξ)))`

where the parenthesized term is positive. At the finite endpoint it extends by zero for positive
shape and by one for negative shape. At shape zero the law is Gumbel and uses the corresponding
Gumbel cdf.

The comparison theorem for `generalizedExtremeValueMap` records the inverse relation used both by
the cdf here and by quantiles of the law.

## References

* S. Coles, *An Introduction to Statistical Modeling of Extreme Values*, Springer (2001),
  Chapter 3.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set

namespace TauCeti.Probability

variable {m s ξ x e : ℝ}

private lemma generalizedExtremeValue_support_sub_eq (hs : s ≠ 0) (hξ : ξ ≠ 0) (t : ℝ) :
    1 + ξ * ((x - m) / s) - t =
      (ξ / s) * (x - (m + s * (t - 1) / ξ)) := by
  field_simp [hs, hξ]
  ring

/-- For positive shape, comparison with the generalized extreme-value transformation reduces to
comparison with a negative real power of the positive exponential input. -/
theorem generalizedExtremeValueMap_le_iff_of_shape_pos (hs : 0 < s) (hξ : 0 < ξ)
    (he : 0 < e) :
    generalizedExtremeValueMap m s ξ e ≤ x ↔
      e ^ (-ξ) ≤ 1 + ξ * ((x - m) / s) := by
  rw [generalizedExtremeValueMap_eq_rpow he, ite_eq_right hξ.ne']
  constructor
  · intro h
    rw [← sub_nonneg, generalizedExtremeValue_support_sub_eq hs.ne' hξ.ne']
    exact mul_nonneg (div_pos hξ hs).le (sub_nonneg.mpr h)
  · intro h
    rw [← sub_nonneg, generalizedExtremeValue_support_sub_eq hs.ne' hξ.ne'] at h
    exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left (div_pos hξ hs)).mp h)

/-- For negative shape, comparison with the generalized extreme-value transformation reverses the
algebraic comparison before reducing to a positive real power of the exponential input. -/
theorem generalizedExtremeValueMap_le_iff_of_shape_neg (hs : 0 < s) (hξ : ξ < 0)
    (he : 0 < e) :
    generalizedExtremeValueMap m s ξ e ≤ x ↔
      1 + ξ * ((x - m) / s) ≤ e ^ (-ξ) := by
  rw [generalizedExtremeValueMap_eq_rpow he, ite_eq_right hξ.ne]
  constructor
  · intro h
    rw [← sub_nonpos, generalizedExtremeValue_support_sub_eq hs.ne' hξ.ne]
    exact mul_nonpos_of_nonpos_of_nonneg (div_nonpos_of_nonpos_of_nonneg hξ.le hs.le)
      (sub_nonneg.mpr h)
  · intro h
    rw [← sub_nonpos, generalizedExtremeValue_support_sub_eq hs.ne' hξ.ne] at h
    exact sub_nonneg.mp (nonneg_of_mul_nonpos_right h (div_neg_of_neg_of_pos hξ hs))

/-- At or above the finite upper endpoint for negative shape, every source input maps below the
comparison point. -/
theorem generalizedExtremeValueMap_le_of_shape_neg_of_nonpos (hs : 0 < s) (hξ : ξ < 0)
    (hx : ¬0 < 1 + ξ * ((x - m) / s)) :
    generalizedExtremeValueMap m s ξ e ≤ x := by
  rw [generalizedExtremeValueMap_of_shape_ne_zero hξ.ne]
  have h := generalizedExtremeValue_support_sub_eq (x := x) (m := m) hs.ne' hξ.ne
    (Real.exp (-ξ * Real.log e))
  by_contra hlt
  have hD : x - (m + s * (Real.exp (-ξ * Real.log e) - 1) / ξ) ≤ 0 := by linarith [not_le.mp hlt]
  have hmul := mul_nonneg_of_nonpos_of_nonpos (div_neg_of_neg_of_pos hξ hs).le hD
  linarith [Real.exp_pos (-ξ * Real.log e), not_lt.mp hx]

/-- Below the finite lower endpoint for positive shape, no source input maps below the
comparison point. -/
theorem not_generalizedExtremeValueMap_le_of_shape_pos_of_nonpos (hs : 0 < s) (hξ : 0 < ξ)
    (hx : ¬0 < 1 + ξ * ((x - m) / s)) :
    ¬generalizedExtremeValueMap m s ξ e ≤ x := fun hle ↦ by
  rw [generalizedExtremeValueMap_of_shape_ne_zero hξ.ne'] at hle
  have h := generalizedExtremeValue_support_sub_eq (x := x) (m := m) hs.ne' hξ.ne'
    (Real.exp (-ξ * Real.log e))
  have hD : 0 ≤ x - (m + s * (Real.exp (-ξ * Real.log e) - 1) / ξ) := by linarith
  have hmul := mul_nonneg (div_pos hξ hs).le hD
  linarith [Real.exp_pos (-ξ * Real.log e), not_lt.mp hx]

/-- On the interior of its support, the generalized extreme-value transformation is at most `x`
exactly when the source exponential variable exceeds the inverse threshold. -/
theorem generalizedExtremeValueMap_le_iff (hs : 0 < s) (hξ : ξ ≠ 0) (he : 0 < e)
    (hx : 0 < 1 + ξ * ((x - m) / s)) :
    generalizedExtremeValueMap m s ξ e ≤ x ↔
      (1 + ξ * ((x - m) / s)) ^ (-1 / ξ) ≤ e := by
  rcases lt_or_gt_of_ne hξ with hξ | hξ
  · rw [generalizedExtremeValueMap_le_iff_of_shape_neg hs hξ he]
    convert (Real.rpow_inv_le_iff_of_pos hx.le he.le (neg_pos.mpr hξ)).symm using 1
    field_simp
  · rw [generalizedExtremeValueMap_le_iff_of_shape_pos hs hξ he]
    convert (Real.rpow_inv_le_iff_of_neg hx he (neg_neg_of_pos hξ)).symm using 1
    field_simp

/-- The cdf of a positive-scale, nonzero-shape generalized extreme-value law. The formula includes
the zero or one extension beyond its finite support endpoint. -/
theorem cdf_generalizedExtremeValueMeasure_eq (hs : 0 < s) (hξ : ξ ≠ 0) (m x : ℝ) :
    cdf (generalizedExtremeValueMeasure m s ξ) x =
      if 0 < 1 + ξ * ((x - m) / s) then
        exp (-((1 + ξ * ((x - m) / s)) ^ (-1 / ξ)))
      else if 0 < ξ then 0 else 1 := by
  let _ := isProbabilityMeasure_generalizedExtremeValueMeasure hs m ξ
  let _ : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure one_pos
  rw [cdf_eq_real, generalizedExtremeValueMeasure_of_pos hs, Measure.real, Measure.map_apply
    (measurable_generalizedExtremeValueMap_right m s ξ) measurableSet_Iic]
  by_cases hx : 0 < 1 + ξ * ((x - m) / s)
  · rw [ite_eq_left hx]
    have hpre :
        generalizedExtremeValueMap m s ξ ⁻¹' Iic x =ᵐ[expMeasure 1]
          Ici ((1 + ξ * ((x - m) / s)) ^ (-1 / ξ)) := by
      filter_upwards [ae_pos_expMeasure 1] with e he
      exact generalizedExtremeValueMap_le_iff hs hξ he hx
    have ht : 0 < (1 + ξ * ((x - m) / s)) ^ (-1 / ξ) :=
      rpow_pos_of_pos hx _
    have hsingleton :
        expMeasure 1 {(1 + ξ * ((x - m) / s)) ^ (-1 / ξ)} = 0 := by
      rw [expMeasure_eq_withDensity]
      exact withDensity_absolutelyContinuous volume _ (measure_singleton _)
    rw [measure_congr hpre, ← measure_congr (Ioi_ae_eq_Ici' hsingleton),
      measure_Ioi_expMeasure one_pos, ite_eq_left ht.le,
      one_mul, ENNReal.toReal_ofReal (exp_nonneg _)]
  · rw [ite_eq_right hx]
    rcases lt_or_gt_of_ne hξ with hξ | hξ
    · rw [ite_eq_right (not_lt.mpr hξ.le)]
      have hpre : generalizedExtremeValueMap m s ξ ⁻¹' Iic x = univ :=
        eq_univ_of_forall fun _ ↦ generalizedExtremeValueMap_le_of_shape_neg_of_nonpos hs hξ hx
      rw [hpre, measure_univ, ENNReal.toReal_one]
    · rw [ite_eq_left hξ]
      have hpre : generalizedExtremeValueMap m s ξ ⁻¹' Iic x = ∅ :=
        eq_empty_of_forall_notMem fun _ ↦
          not_generalizedExtremeValueMap_le_of_shape_pos_of_nonpos hs hξ hx
      rw [hpre, measure_empty, ENNReal.toReal_zero]

/-- At shape zero, the generalized extreme-value cdf is the Gumbel cdf. -/
theorem cdf_generalizedExtremeValueMeasure_zero (hs : 0 < s) (m x : ℝ) :
    cdf (generalizedExtremeValueMeasure m s 0) x =
      exp (-exp (-((x - m) / s))) := by
  rw [generalizedExtremeValueMeasure_zero, cdf_gumbelMeasure_eq hs]

/-- The cdf of a generalized extreme-value law is strictly increasing on its closed support. At
shape zero the support is the whole line. -/
theorem strictMonoOn_cdf_generalizedExtremeValueMeasure (hs : 0 < s) (m ξ : ℝ) :
    StrictMonoOn (cdf (generalizedExtremeValueMeasure m s ξ))
      {x | 0 ≤ 1 + ξ * ((x - m) / s)} := by
  rcases eq_or_ne ξ 0 with rfl | hξ
  · rw [generalizedExtremeValueMeasure_zero]
    exact (strictMono_cdf_gumbelMeasure hs m).strictMonoOn _
  intro x hx y hy hxy
  have hx0 : 0 ≤ 1 + ξ * ((x - m) / s) := hx
  have hy0 : 0 ≤ 1 + ξ * ((y - m) / s) := hy
  have hq : (x - m) / s < (y - m) / s :=
    div_lt_div_of_pos_right (sub_lt_sub_right hxy m) hs
  rw [cdf_generalizedExtremeValueMeasure_eq hs hξ m x,
    cdf_generalizedExtremeValueMeasure_eq hs hξ m y]
  rcases lt_or_gt_of_ne hξ with hξ | hξ
  · have hx' : 0 < 1 + ξ * ((x - m) / s) := by linarith [mul_lt_mul_of_neg_left hq hξ]
    rw [ite_eq_left hx']
    by_cases hy' : 0 < 1 + ξ * ((y - m) / s)
    · rw [ite_eq_left hy', exp_lt_exp]
      apply neg_lt_neg
      exact Real.rpow_lt_rpow hy'.le (by linarith [mul_lt_mul_of_neg_left hq hξ])
        (div_pos_of_neg_of_neg (by norm_num) hξ)
    · rw [ite_eq_right hy', ite_eq_right (not_lt.mpr hξ.le)]
      exact exp_lt_one_iff.2 (neg_neg_of_pos (rpow_pos_of_pos hx' _))
  · have hy' : 0 < 1 + ξ * ((y - m) / s) := by linarith [mul_lt_mul_of_pos_left hq hξ]
    rw [ite_eq_left hy']
    by_cases hx' : 0 < 1 + ξ * ((x - m) / s)
    · rw [ite_eq_left hx', exp_lt_exp]
      apply neg_lt_neg
      exact Real.rpow_lt_rpow_of_neg hx'
        (by linarith [mul_lt_mul_of_pos_left hq hξ])
        (div_neg_of_neg_of_pos (by norm_num) hξ)
    · rw [ite_eq_right hx', ite_eq_left hξ]
      exact exp_pos _

end TauCeti.Probability
