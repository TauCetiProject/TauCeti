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

/-- The normalized numerator of `canonicalFactor R a`. Unlike the canonical factor,
this affine function has no pole at `a`. -/
noncomputable def canonicalFactorNumerator (R : ℝ) (a : ℂ) : ℂ → ℂ :=
  fun w ↦ ((R : ℂ) ^ 2 - conj a * w) / (R : ℂ)

/-- Evaluation of the normalized numerator of a canonical factor. -/
@[simp] lemma canonicalFactorNumerator_apply (R : ℝ) (a w : ℂ) :
    canonicalFactorNumerator R a w = ((R : ℂ) ^ 2 - conj a * w) / (R : ℂ) := by
  rfl

/-- A normalized canonical-factor numerator is entire, even when `R = 0`. -/
lemma differentiable_canonicalFactorNumerator (R : ℝ) (a : ℂ) :
    Differentiable ℂ (canonicalFactorNumerator R a) := by
  unfold canonicalFactorNumerator
  fun_prop

/-- The uniform lower bound for a canonical-factor numerator is positive on the outer disc,
including negative inner bounds `r`. -/
lemma sq_sub_mul_norm_pos {R r : ℝ} {t : ℂ} (hR : 0 < R) (hrR : r < R)
    (ht : ‖t‖ ≤ R) : 0 < R ^ 2 - r * ‖t‖ := by
  by_cases hr : 0 ≤ r
  · have hprod := mul_le_mul_of_nonneg_left ht hr
    nlinarith
  · have hprod := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hr) (norm_nonneg t)
    nlinarith [sq_pos_of_pos hR]

/-- On a nonzero-radius circle, the normalized numerator of a canonical factor has the same
norm as the ordinary zero factor, for every complex parameter. -/
lemma norm_canonicalFactorNumerator_eval_circle {R : ℝ} {a w : ℂ}
    (hR : R ≠ 0) (hw : ‖w‖ = R) :
    ‖canonicalFactorNumerator R a w‖ = ‖w - a‖ := by
  rw [canonicalFactorNumerator_apply]
  have he : (R : ℂ) ^ 2 - conj a * w = w * conj (w - a) := by
    rw [map_sub, mul_sub, mul_conj', hw]
    ring
  rw [he, norm_div, norm_mul, norm_conj, Complex.norm_real, Real.norm_eq_abs, ← hw,
    abs_of_nonneg (norm_nonneg w)]
  exact mul_div_cancel_left₀ _ (by rwa [hw])

/-- A lower bound for the norm of `R² - conj a * t`, uniform over parameters
in the closed disc of radius `r`. No division by `R` is involved. -/
lemma sq_sub_mul_norm_le_norm_sq_sub_conj_mul {R r : ℝ} {a t : ℂ}
    (ha : ‖a‖ ≤ r) :
    R ^ 2 - r * ‖t‖ ≤ ‖(R : ℂ) ^ 2 - conj a * t‖ := by
  have hprod := mul_le_mul_of_nonneg_right ha (norm_nonneg t)
  have hsub := norm_sub_norm_le ((R : ℂ) ^ 2) (conj a * t)
  simp only [norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    norm_mul, norm_conj] at hsub
  linarith

/-- The expression `R² - conj a * t` has positive norm throughout the outer closed disc when
its parameter lies in the open outer disc. -/
lemma norm_sq_sub_conj_mul_pos {R : ℝ} {a t : ℂ}
    (ha : ‖a‖ < R) (ht : ‖t‖ ≤ R) :
    0 < ‖(R : ℂ) ^ 2 - conj a * t‖ := by
  exact (sq_sub_mul_norm_pos ((norm_nonneg a).trans_lt ha) ha ht).trans_le
    (sq_sub_mul_norm_le_norm_sq_sub_conj_mul le_rfl)

/-- Interior parameters give a nonzero normalized numerator throughout the outer closed disc. -/
lemma canonicalFactorNumerator_ne_zero {R : ℝ} {a t : ℂ}
    (ha : ‖a‖ < R) (ht : ‖t‖ ≤ R) : canonicalFactorNumerator R a t ≠ 0 := by
  have hR : 0 < R := (norm_nonneg a).trans_lt ha
  exact div_ne_zero (norm_pos_iff.mp (norm_sq_sub_conj_mul_pos ha ht))
    (Complex.ofReal_ne_zero.mpr hR.ne')

/-- The logarithmic derivative of a translated normalized canonical-factor numerator is bounded
uniformly for parameters and evaluation points in a closed inner disc. -/
lemma norm_logDeriv_canonicalFactorNumerator_comp_sub_le {R r : ℝ} {a z₀ z : ℂ} (hrR : r < R)
    (ha : ‖a‖ ≤ r) (hz : ‖z - z₀‖ ≤ r) :
    ‖logDeriv (fun w : ℂ ↦ canonicalFactorNumerator R a (w - z₀)) z‖ ≤
      r / (R ^ 2 - r * ‖z - z₀‖) := by
  simp only [canonicalFactorNumerator_apply]
  have hr : 0 ≤ r := (norm_nonneg _).trans hz
  have hR : 0 < R := hr.trans_lt hrR
  have hder : HasDerivAt
      (fun w : ℂ ↦ ((R : ℂ) ^ 2 - conj a * (w - z₀)) / (R : ℂ))
      (-conj a / (R : ℂ)) z := by
    convert ((hasDerivAt_const z ((R : ℂ) ^ 2)).sub
      (((hasDerivAt_id z).sub_const z₀).const_mul (conj a))).div_const (R : ℂ) using 1 <;> simp
  have hden := sq_sub_mul_norm_pos hR hrR (hz.trans hrR.le)
  have hbound := sq_sub_mul_norm_le_norm_sq_sub_conj_mul (R := R) ha (t := z - z₀)
  rw [logDeriv_apply, hder.deriv, div_div_div_cancel_right₀ (Complex.ofReal_ne_zero.mpr hR.ne'),
    norm_div, norm_neg, norm_conj]
  exact (div_le_div_of_nonneg_right ha (norm_nonneg _)).trans
    (div_le_div_of_nonneg_left hr hden hbound)

end Complex
