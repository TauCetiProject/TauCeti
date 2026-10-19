/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex, The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.GeneralizedExtremeValue.Basic

/-!
# Cumulative distribution function of the generalized extreme-value law

This file computes the cumulative distribution function of the generalized extreme-value law
in the maximum convention. For nonzero shape `ξ`, on the interior of its support the formula is

`exp (-(1 + ξ * (x - m) / s) ^ (-1 / ξ))`.

For positive shape the cdf is zero below the finite lower endpoint, while for negative shape it
is one above the finite upper endpoint. At shape zero the formula reduces to the Gumbel cdf.
The strict increase of the cdf on its support interior is also recorded for quantile calculations.

## Main results

* `cdf_generalizedExtremeValueMeasure_eq_of_shape_ne_zero_of_pos_support` gives the interior
  nonzero-shape formula.
* `cdf_generalizedExtremeValueMeasure_eq` gives all shape and support-boundary branches.
* `strictMonoOn_cdf_generalizedExtremeValueMeasure` proves strict increase on the support interior.

## References

* S. Coles, *An Introduction to Statistical Modeling of Extreme Values*, Springer (2001),
  Chapter 3.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

open scoped ENNReal

namespace TauCeti.Probability

variable {m s ξ x : ℝ}

private lemma generalizedExtremeValueSupport_eq (hs : s ≠ 0) :
    1 + ξ * (x - m) / s = (s + ξ * (x - m)) / s := by
  field_simp [hs]

private lemma generalizedExtremeValueSupportNumerator_nonpos (hs : 0 < s)
    (hx : 1 + ξ * (x - m) / s ≤ 0) : s + ξ * (x - m) ≤ 0 := by
  rw [generalizedExtremeValueSupport_eq hs.ne'] at hx
  simpa only [div_nonpos_iff, hs.le, not_le_of_gt hs, and_false, false_or, and_true] using hx

private lemma generalizedExtremeValueMap_algebra_of_shape_neg {t : ℝ} (hs : 0 < s)
    (hξ : ξ < 0) :
    m + s * (t - 1) / ξ ≤ x ↔ 1 + ξ * (x - m) / s ≤ t := by
  rw [generalizedExtremeValueSupport_eq hs.ne']
  constructor
  · intro h
    have hd : s * (t - 1) / ξ ≤ x - m := by linarith
    have h' := (div_le_iff_of_neg hξ).1 hd
    apply (div_le_iff₀ hs).2
    nlinarith
  · intro h
    have h' := (div_le_iff₀ hs).1 h
    have hd : s * (t - 1) / ξ ≤ x - m :=
      (div_le_iff_of_neg hξ).2 (by nlinarith)
    linarith

private lemma generalizedExtremeValueMap_algebra_of_shape_pos {t : ℝ} (hs : 0 < s)
    (hξ : 0 < ξ) :
    m + s * (t - 1) / ξ ≤ x ↔ t ≤ 1 + ξ * (x - m) / s := by
  rw [generalizedExtremeValueSupport_eq hs.ne']
  constructor
  · intro h
    have hd : s * (t - 1) / ξ ≤ x - m := by linarith
    have h' := (div_le_iff₀ hξ).1 hd
    apply (le_div_iff₀ hs).2
    nlinarith
  · intro h
    have h' := (le_div_iff₀ hs).1 h
    have hd : s * (t - 1) / ξ ≤ x - m :=
      (div_le_iff₀ hξ).2 (by nlinarith)
    linarith

private lemma generalizedExtremeValueMap_le_iff {e : ℝ} (hs : 0 < s) (hξ : ξ ≠ 0)
    (he : 0 < e) (hx : 0 < 1 + ξ * (x - m) / s) :
    generalizedExtremeValueMap m s ξ e ≤ x ↔
      (1 + ξ * (x - m) / s) ^ (-1 / ξ) ≤ e := by
  rw [generalizedExtremeValueMap_eq_rpow he, ite_eq_right hξ]
  have hinv : (-ξ)⁻¹ = -1 / ξ := by
    simp [div_eq_mul_inv]
  rcases lt_or_gt_of_ne hξ with hξ | hξ
  · rw [generalizedExtremeValueMap_algebra_of_shape_neg hs hξ]
    rw [← hinv]
    exact (Real.rpow_inv_le_iff_of_pos hx.le he.le (neg_pos.mpr hξ)).symm
  · rw [generalizedExtremeValueMap_algebra_of_shape_pos hs hξ]
    rw [← hinv]
    exact (Real.rpow_inv_le_iff_of_neg hx he (neg_neg_of_pos hξ)).symm

/-- On the interior of its support, the cdf of a nonzero-shape generalized extreme-value law is
`exp (-(1 + ξ * (x - m) / s) ^ (-1 / ξ))`. -/
theorem cdf_generalizedExtremeValueMeasure_eq_of_shape_ne_zero_of_pos_support
    (hs : 0 < s) (hξ : ξ ≠ 0)
    (hx : 0 < 1 + ξ * (x - m) / s) :
    cdf (generalizedExtremeValueMeasure m s ξ) x =
      Real.exp (-(1 + ξ * (x - m) / s) ^ (-1 / ξ)) := by
  let z := (1 + ξ * (x - m) / s) ^ (-1 / ξ)
  have hz : 0 < z := Real.rpow_pos_of_pos hx _
  have hpre : generalizedExtremeValueMap m s ξ ⁻¹' Iic x =ᵐ[expMeasure 1] Ici z := by
    filter_upwards [ae_pos_expMeasure 1] with e he
    simp only [mem_preimage, mem_Iic, mem_Ici]
    exact propext (generalizedExtremeValueMap_le_iff hs hξ he hx)
  have hsingleton : expMeasure 1 {z} = 0 := by
    rw [expMeasure_eq_withDensity]
    exact withDensity_absolutelyContinuous volume _ (measure_singleton _)
  have hmeas := measurable_generalizedExtremeValueMap_right m s ξ
  let _ := isProbabilityMeasure_generalizedExtremeValueMeasure hs m ξ
  rw [cdf_eq_real, measureReal_def, generalizedExtremeValueMeasure_of_pos hs,
    Measure.map_apply hmeas measurableSet_Iic, measure_congr hpre,
    ← measure_congr (Ioi_ae_eq_Ici' hsingleton), measure_Ioi_expMeasure one_pos,
    ite_eq_left hz.le, one_mul, ENNReal.toReal_ofReal (Real.exp_nonneg _)]

private lemma generalizedExtremeValueMap_gt_of_shape_pos_of_nonpos {e : ℝ} (hs : 0 < s)
    (hξ : 0 < ξ) (he : 0 < e) (hx : 1 + ξ * (x - m) / s ≤ 0) :
    x < generalizedExtremeValueMap m s ξ e := by
  rw [generalizedExtremeValueMap_eq_rpow he, ite_eq_right hξ.ne']
  have hpow : 0 < e ^ (-ξ) := Real.rpow_pos_of_pos he _
  have hx := generalizedExtremeValueSupportNumerator_nonpos hs hx
  have hd : x - m < s * (e ^ (-ξ) - 1) / ξ :=
    (lt_div_iff₀ hξ).2 (by nlinarith [mul_pos hs hpow])
  linarith

/-- For positive shape, the generalized extreme-value cdf vanishes at and below its finite
lower support endpoint. -/
theorem cdf_generalizedExtremeValueMeasure_eq_zero (hs : 0 < s) (hξ : 0 < ξ)
    (hx : 1 + ξ * (x - m) / s ≤ 0) :
    cdf (generalizedExtremeValueMeasure m s ξ) x = 0 := by
  let _ := isProbabilityMeasure_generalizedExtremeValueMeasure hs m ξ
  rw [cdf_eq_real, measureReal_def, generalizedExtremeValueMeasure_of_pos hs,
    Measure.map_apply (measurable_generalizedExtremeValueMap_right m s ξ) measurableSet_Iic]
  have hpre : generalizedExtremeValueMap m s ξ ⁻¹' Iic x =ᵐ[expMeasure 1] ∅ := by
    filter_upwards [ae_pos_expMeasure 1] with e he
    simp only [mem_preimage, mem_Iic, mem_empty_iff_false]
    exact propext ⟨fun h ↦ not_le_of_gt
      (generalizedExtremeValueMap_gt_of_shape_pos_of_nonpos hs hξ he hx) h, False.elim⟩
  rw [measure_congr hpre, measure_empty, ENNReal.toReal_zero]

private lemma generalizedExtremeValueMap_le_of_shape_neg_of_nonpos {e : ℝ} (hs : 0 < s)
    (hξ : ξ < 0) (he : 0 < e) (hx : 1 + ξ * (x - m) / s ≤ 0) :
    generalizedExtremeValueMap m s ξ e ≤ x := by
  rw [generalizedExtremeValueMap_eq_rpow he, ite_eq_right hξ.ne]
  have hpow : 0 < e ^ (-ξ) := Real.rpow_pos_of_pos he _
  have hx := generalizedExtremeValueSupportNumerator_nonpos hs hx
  have hd : s * (e ^ (-ξ) - 1) / ξ ≤ x - m :=
    (div_le_iff_of_neg hξ).2 (by nlinarith [mul_pos hs hpow])
  linarith

/-- For negative shape, the generalized extreme-value cdf is one at and above its finite upper
support endpoint. -/
theorem cdf_generalizedExtremeValueMeasure_eq_one (hs : 0 < s) (hξ : ξ < 0)
    (hx : 1 + ξ * (x - m) / s ≤ 0) :
    cdf (generalizedExtremeValueMeasure m s ξ) x = 1 := by
  let _ := isProbabilityMeasure_generalizedExtremeValueMeasure hs m ξ
  rw [cdf_eq_real, measureReal_def, generalizedExtremeValueMeasure_of_pos hs,
    Measure.map_apply (measurable_generalizedExtremeValueMap_right m s ξ) measurableSet_Iic]
  have hpre : generalizedExtremeValueMap m s ξ ⁻¹' Iic x =ᵐ[expMeasure 1] Set.univ := by
    filter_upwards [ae_pos_expMeasure 1] with e he
    simp only [mem_preimage, mem_Iic, mem_univ]
    exact propext ⟨fun _ ↦ True.intro,
      fun _ ↦ generalizedExtremeValueMap_le_of_shape_neg_of_nonpos hs hξ he hx⟩
  let _ := isProbabilityMeasure_expMeasure one_pos
  rw [measure_congr hpre, measure_univ, ENNReal.toReal_one]

/-- The cdf of a positive-scale generalized extreme-value law, including the Gumbel branch and
both finite-support boundary branches. -/
theorem cdf_generalizedExtremeValueMeasure_eq (hs : 0 < s) (m ξ x : ℝ) :
    cdf (generalizedExtremeValueMeasure m s ξ) x =
      if ξ = 0 then Real.exp (-Real.exp (-((x - m) / s)))
      else if 0 < 1 + ξ * (x - m) / s then
        Real.exp (-(1 + ξ * (x - m) / s) ^ (-1 / ξ))
      else if 0 < ξ then 0 else 1 := by
  by_cases hξ : ξ = 0
  · simp [hξ, cdf_gumbelMeasure_eq hs]
  · rw [ite_eq_right hξ]
    by_cases hx : 0 < 1 + ξ * (x - m) / s
    · rw [ite_eq_left hx,
        cdf_generalizedExtremeValueMeasure_eq_of_shape_ne_zero_of_pos_support hs hξ hx]
    · rw [ite_eq_right hx]
      rcases lt_or_gt_of_ne hξ with hξ | hξ
      · rw [ite_eq_right (not_lt.mpr hξ.le), cdf_generalizedExtremeValueMeasure_eq_one hs hξ
          (not_lt.mp hx)]
      · rw [ite_eq_left hξ, cdf_generalizedExtremeValueMeasure_eq_zero hs hξ (not_lt.mp hx)]

/-- The cdf of a nonzero-shape generalized extreme-value law is strictly increasing on the
interior of its support. -/
theorem strictMonoOn_cdf_generalizedExtremeValueMeasure (hs : 0 < s) (hξ : ξ ≠ 0) (m : ℝ) :
    StrictMonoOn (cdf (generalizedExtremeValueMeasure m s ξ))
      {x | 0 < 1 + ξ * (x - m) / s} := by
  intro x hx y hy hxy
  rw [cdf_generalizedExtremeValueMeasure_eq_of_shape_ne_zero_of_pos_support hs hξ hx,
    cdf_generalizedExtremeValueMeasure_eq_of_shape_ne_zero_of_pos_support hs hξ hy,
    Real.exp_lt_exp]
  apply neg_lt_neg
  rcases lt_or_gt_of_ne hξ with hξ | hξ
  · apply Real.rpow_lt_rpow hy.le
      (by
        have hmul := mul_lt_mul_of_neg_left (sub_lt_sub_right hxy m) hξ
        have hdiv := div_lt_div_of_pos_right hmul hs
        linarith) (div_pos_of_neg_of_neg (by norm_num) hξ)
  · exact Real.rpow_lt_rpow_of_neg hx
      (by
        have hmul := mul_lt_mul_of_pos_left (sub_lt_sub_right hxy m) hξ
        have hdiv := div_lt_div_of_pos_right hmul hs
        linarith)
      (div_neg_of_neg_of_pos (by norm_num) hξ)

end TauCeti.Probability
