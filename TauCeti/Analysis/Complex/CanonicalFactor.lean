/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.Complex.CanonicalDecomposition

/-!
# Numerator bounds for canonical factors

Mathlib's `Complex.canonicalFactor R a` has numerator `R² - conj a * z`.
After division by `R`, this entire function has the same boundary norm as `z - a`,
is nonzero on the outer closed disc for interior parameters, and has a controlled logarithmic
derivative on smaller discs. These estimates allow finite canonical products to remove zeros
in Landau's local logarithmic-derivative estimate at arbitrary nested radii.
-/

public section

namespace Complex

open scoped ComplexConjugate
open Metric

/-- On the outer circle, the normalized numerator of a canonical factor has the same norm
as the ordinary zero factor. -/
lemma norm_canonicalFactor_numerator_eval_circle {R : ℝ} {a w : ℂ}
    (ha : ‖a‖ < R) (hw : ‖w‖ = R) :
    ‖((R : ℂ) ^ 2 - conj a * w) / (R : ℂ)‖ = ‖w - a‖ := by
  have hR : 0 < R := (norm_nonneg a).trans_lt ha
  have hwa : w - a ≠ 0 := by
    intro h
    have : w = a := sub_eq_zero.mp h
    rw [this] at hw
    linarith
  have he : ((R : ℂ) ^ 2 - conj a * w) / (R : ℂ) =
      canonicalFactor R a w * (w - a) := by
    rw [canonicalFactor_apply]
    field_simp
  rw [he, norm_mul, norm_canonicalFactor_eval_circle_eq_one
    (by simpa only [mem_ball_zero_iff] using ha)
    (by simpa only [mem_sphere_zero_iff_norm] using hw), one_mul]

/-- The numerator of a canonical factor is nonzero throughout the outer closed disc when
its parameter lies in a strictly smaller disc. -/
lemma norm_canonicalFactor_numerator_pos {R r : ℝ} {a t : ℂ} (hr : 0 < r) (hrR : r < R)
    (ha : ‖a‖ ≤ r) (ht : ‖t‖ ≤ R) :
    0 < ‖(R : ℂ) ^ 2 - conj a * t‖ := by
  have hR : 0 < R := hr.trans hrR
  have hprod : ‖conj a * t‖ ≤ r * R := by
    rw [norm_mul, norm_conj]
    exact mul_le_mul ha ht (norm_nonneg _) hr.le
  have hsub := norm_sub_norm_le ((R : ℂ) ^ 2) (conj a * t)
  simp only [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR] at hsub
  nlinarith

/-- The logarithmic derivative of a translated canonical-factor numerator is bounded
uniformly for parameters in an inner disc. -/
lemma norm_logDeriv_canonicalFactor_numerator_le {R r : ℝ} {a z₀ z : ℂ} (hr : 0 < r) (hrR : r < R)
    (ha : ‖a‖ ≤ r) (hz : ‖z - z₀‖ < r) :
    ‖logDeriv (fun w : ℂ ↦ ((R : ℂ) ^ 2 - conj a * (w - z₀)) / (R : ℂ)) z‖ ≤
      r / (R ^ 2 - r * ‖z - z₀‖) := by
  have hR : 0 < R := hr.trans hrR
  have hder : HasDerivAt
      (fun w : ℂ ↦ ((R : ℂ) ^ 2 - conj a * (w - z₀)) / (R : ℂ))
      (-conj a / (R : ℂ)) z := by
    convert ((hasDerivAt_const z ((R : ℂ) ^ 2)).sub
      (((hasDerivAt_id z).sub_const z₀).const_mul (conj a))).div_const (R : ℂ) using 1 <;> simp
  have hden : 0 < R ^ 2 - r * ‖z - z₀‖ := by
    have : r * ‖z - z₀‖ < r * r := mul_lt_mul_of_pos_left hz hr
    nlinarith
  have hbound : R ^ 2 - r * ‖z - z₀‖ ≤ ‖(R : ℂ) ^ 2 - conj a * (z - z₀)‖ := by
    have hprod := mul_le_mul_of_nonneg_right ha (norm_nonneg (z - z₀))
    have hsub := norm_sub_norm_le ((R : ℂ) ^ 2) (conj a * (z - z₀))
    simp only [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR,
      norm_mul, norm_conj] at hsub
    linarith
  rw [logDeriv_apply, hder.deriv, div_div_div_cancel_right₀ (Complex.ofReal_ne_zero.mpr hR.ne'),
    norm_div, norm_neg, norm_conj]
  exact (div_le_div_of_nonneg_right ha (norm_nonneg _)).trans
    (div_le_div_of_nonneg_left hr.le hden hbound)

end Complex
