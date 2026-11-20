/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# Norm bounds for nonnegative translations in complex sectors

For a complex number `s` separated in argument from the negative real axis and a nonnegative
real `t`, the norm of the translate `s + t` is bounded below by a fixed multiple of `‖s‖ + t`:
`√c * (‖s‖ + t) ≤ ‖s + t‖` whenever `(2c - 1) ‖s‖ ≤ re s` and `0 ≤ c ≤ 1`
(`Complex.sqrt_mul_norm_add_le_norm_add_ofReal`), which sharpens `c * (‖s‖ + t) ≤ ‖s + t‖`
(`Complex.mul_norm_add_le_norm_add_ofReal`). On the sector `|arg s| ≤ π - δ` (`0 ≤ δ`), the sharp
constant is `sin (δ / 2)` (`Complex.sin_half_mul_norm_add_le_norm_add_ofReal_of_abs_arg_le`),
strengthening the squared constant `(1 - cos δ) / 2 = sin (δ / 2) ^ 2`
(`Complex.mul_norm_add_le_norm_add_ofReal_of_abs_arg_le`). For `z` in the sector
`Re z ≤ c ‖z‖`, `c < 1`, around the negative real axis,
`(1 - max c (-1)) / 2 * (t + ‖z‖) ≤ ‖t - z‖`. These inequalities control reciprocal kernels in
sectorial integrals and resolvent symbols. A nonzero point of such a sector, with `0 < δ`, lies in
the slit plane.
-/

public section

open Complex Real

namespace Complex

/-- If `(2c - 1) ‖s‖ ≤ re s` with `0 ≤ c ≤ 1`, then `√c * (‖s‖ + t) ≤ ‖s + t‖` for every
nonnegative real `t`. This sharpens `Complex.mul_norm_add_le_norm_add_ofReal`. -/
theorem sqrt_mul_norm_add_le_norm_add_ofReal {s : ℂ} {c t : ℝ}
    (hc : 0 ≤ c) (hc1 : c ≤ 1) (ht : 0 ≤ t)
    (hs : (2 * c - 1) * ‖s‖ ≤ s.re) :
    Real.sqrt c * (‖s‖ + t) ≤ ‖s + t‖ := by
  have hsq : ‖s + t‖ ^ 2 = ‖s‖ ^ 2 + 2 * t * s.re + t ^ 2 := by
    simp only [Complex.sq_norm, normSq_apply, add_re, ofReal_re, add_im, ofReal_im, add_zero]
    ring
  have h : c * (‖s‖ + t) ^ 2 ≤ ‖s + t‖ ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hc1) (sq_nonneg (‖s‖ - t)),
      mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 2 * t)]
  have h2 : (Real.sqrt c * (‖s‖ + t)) ^ 2 ≤ ‖s + t‖ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hc]
    exact h
  nlinarith [norm_nonneg (s + t), Real.sqrt_nonneg c, norm_nonneg s]

/-- If `(2c - 1) ‖s‖ ≤ re s` with `0 ≤ c ≤ 1`, then `c * (‖s‖ + t) ≤ ‖s + t‖` for every
nonnegative real `t`. -/
theorem mul_norm_add_le_norm_add_ofReal {s : ℂ} {c t : ℝ}
    (hc : 0 ≤ c) (hc1 : c ≤ 1) (ht : 0 ≤ t)
    (hs : (2 * c - 1) * ‖s‖ ≤ s.re) :
    c * (‖s‖ + t) ≤ ‖s + t‖ := by
  refine le_trans ?_ (sqrt_mul_norm_add_le_norm_add_ofReal hc hc1 ht hs)
  have hle : c ≤ Real.sqrt c := by
    rw [Real.le_sqrt hc hc]
    nlinarith
  exact mul_le_mul_of_nonneg_right hle (by positivity)

/-- On the closed sector `|arg s| ≤ π - δ` (`0 ≤ δ`), translation by a nonnegative real `t`
satisfies `sin (δ / 2) * (‖s‖ + t) ≤ ‖s + t‖`. This sharpens
`Complex.mul_norm_add_le_norm_add_ofReal_of_abs_arg_le`. -/
theorem sin_half_mul_norm_add_le_norm_add_ofReal_of_abs_arg_le {s : ℂ} {δ t : ℝ}
    (hδ : 0 ≤ δ) (hs : |s.arg| ≤ Real.pi - δ) (ht : 0 ≤ t) :
    Real.sin (δ / 2) * (‖s‖ + t) ≤ ‖s + t‖ := by
  have hδπ : δ ≤ Real.pi := by linarith [abs_nonneg s.arg]
  have hsin : 0 ≤ Real.sin (δ / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  rw [← Real.sqrt_sq hsin]
  apply sqrt_mul_norm_add_le_norm_add_ofReal (sq_nonneg _)
  · nlinarith [Real.sin_sq_add_cos_sq (δ / 2)]
  · exact ht
  · have hcos := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg s.arg)
      (by linarith : Real.pi - δ ≤ Real.pi) hs
    rw [Real.cos_abs, Real.cos_pi_sub] at hcos
    have h2 : Real.cos δ = 1 - 2 * Real.sin (δ / 2) ^ 2 := by
      have hdouble := Real.cos_two_mul (δ / 2)
      rw [mul_div_cancel₀ δ two_ne_zero] at hdouble
      linarith [Real.sin_sq_add_cos_sq (δ / 2)]
    have h := mul_le_mul_of_nonneg_left hcos (norm_nonneg s)
    rw [norm_mul_cos_arg, h2] at h
    linarith

/-- On the closed sector `|arg s| ≤ π - δ`, translation by a nonnegative real `t` satisfies
`((1 - cos δ) / 2) * (‖s‖ + t) ≤ ‖s + t‖`. -/
theorem mul_norm_add_le_norm_add_ofReal_of_abs_arg_le {s : ℂ} {δ t : ℝ}
    (hδ : 0 < δ) (hs : |s.arg| ≤ Real.pi - δ) (ht : 0 ≤ t) :
    ((1 - Real.cos δ) / 2) * (‖s‖ + t) ≤ ‖s + t‖ := by
  apply mul_norm_add_le_norm_add_ofReal
  · linarith [Real.cos_le_one δ]
  · linarith [Real.neg_one_le_cos δ]
  · exact ht
  · have hcos := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg s.arg)
      (by linarith : Real.pi - δ ≤ Real.pi) hs
    rw [Real.cos_abs, Real.cos_pi_sub] at hcos
    have h := mul_le_mul_of_nonneg_left hcos (norm_nonneg s)
    rw [norm_mul_cos_arg] at h
    nlinarith

/-- On the sector `Re z ≤ c ‖z‖`, the difference `t - z` with a nonnegative real `t` satisfies
`(1 - max c (-1)) / 2 * (t + ‖z‖) ≤ ‖t - z‖`. For `c < 1` this keeps `t - z` away from `0`; for
`c ≥ 1` the left side is nonpositive. -/
theorem mul_add_norm_le_norm_ofReal_sub {z : ℂ} {c t : ℝ} (ht : 0 ≤ t) (hz : z.re ≤ c * ‖z‖) :
    (1 - max c (-1)) / 2 * (t + ‖z‖) ≤ ‖(t : ℂ) - z‖ := by
  rcases le_or_gt 1 c with hc | hc
  · have : (1 - max c (-1)) / 2 ≤ 0 := by linarith [le_max_left c (-1)]
    nlinarith [norm_nonneg ((t : ℂ) - z), norm_nonneg z]
  have h := mul_norm_add_le_norm_add_ofReal (s := -z) (c := (1 - max c (-1)) / 2)
    (by linarith [max_lt hc (show (-1 : ℝ) < 1 by norm_num)]) (by linarith [le_max_right c (-1)])
    ht (by
      rw [norm_neg, neg_re]
      nlinarith [mul_le_mul_of_nonneg_right (le_max_left c (-1)) (norm_nonneg z)])
  rwa [norm_neg, neg_add_eq_sub, add_comm ‖z‖ t] at h

/-- A nonzero complex number with `|arg s| < π` lies in the slit plane. -/
theorem mem_slitPlane_of_abs_arg_lt {s : ℂ} (hs : |s.arg| < Real.pi) (hs0 : s ≠ 0) :
    s ∈ slitPlane :=
  mem_slitPlane_iff_arg.mpr ⟨fun h ↦ by rw [h, abs_of_pos Real.pi_pos] at hs; exact hs.false, hs0⟩

/-- A nonzero complex number in the closed sector `|arg s| ≤ π - δ`, with `0 < δ`, lies in the
slit plane. -/
theorem mem_slitPlane_of_abs_arg_le {s : ℂ} {δ : ℝ} (hδ : 0 < δ) (hs : |s.arg| ≤ Real.pi - δ)
    (hs0 : s ≠ 0) : s ∈ slitPlane :=
  mem_slitPlane_of_abs_arg_lt (by linarith) hs0

end Complex
