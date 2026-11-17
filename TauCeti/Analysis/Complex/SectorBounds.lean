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
`c * (‖s‖ + t) ≤ ‖s + t‖`, where `0 ≤ c ≤ 1` depends only on the angular separation. The sharp
angular factor is `c = cos (arg s / 2)`, coming from the exact identity
`‖s + t‖² = cos²(arg s / 2) (‖s‖ + t)² + sin²(arg s / 2) (‖s‖ - t)²`. On the closed sector
`|arg s| ≤ π - δ`, one obtains both `c = sin (δ / 2)` and the weaker `c = (1 - cos δ) / 2`.
These inequalities control reciprocal kernels in sectorial integrals. A nonzero point of such a
sector, with `0 < δ`, lies in the slit plane.
-/

public section

open Complex Real

namespace Complex

/-- For every complex number `s`, `cos (arg s / 2) ≥ 0`, since `arg s ∈ (-π, π]`. -/
theorem cos_arg_div_two_nonneg (s : ℂ) : 0 ≤ Real.cos (s.arg / 2) :=
  Real.cos_nonneg_of_mem_Icc ⟨by linarith [neg_pi_lt_arg s], by linarith [arg_le_pi s]⟩

/-- For `s` in the slit plane, `cos (arg s / 2) > 0`, since `arg s ∈ (-π, π)`. -/
theorem cos_arg_div_two_pos_of_mem_slitPlane {s : ℂ} (hs : s ∈ slitPlane) :
    0 < Real.cos (s.arg / 2) := by
  have hlt : s.arg < Real.pi := lt_of_le_of_ne (arg_le_pi s) (mem_slitPlane_iff_arg.mp hs).1
  exact Real.cos_pos_of_mem_Ioo ⟨by linarith [neg_pi_lt_arg s], by linarith⟩

/-- Sharp half-angle norm bound for real translations: for every `s : ℂ` and `t : ℝ`,
`cos (arg s / 2) * (‖s‖ + t) ≤ ‖s + t‖`. -/
theorem cos_arg_div_two_mul_norm_add_le_norm_add_ofReal (s : ℂ) (t : ℝ) :
    Real.cos (s.arg / 2) * (‖s‖ + t) ≤ ‖s + t‖ := by
  have hsq : ‖s + t‖ ^ 2 = ‖s‖ ^ 2 + 2 * t * s.re + t ^ 2 := by
    simp only [Complex.sq_norm, normSq_apply, add_re, ofReal_re, add_im, ofReal_im, add_zero]
    ring
  have hcos : s.re = ‖s‖ * (2 * Real.cos (s.arg / 2) ^ 2 - 1) := by
    rw [← norm_mul_cos_arg s, ← Real.cos_two_mul, mul_div_cancel₀ _ two_ne_zero]
  have hid : ‖s + t‖ ^ 2 = (Real.cos (s.arg / 2) * (‖s‖ + t)) ^ 2 +
      (Real.sin (s.arg / 2) * (‖s‖ - t)) ^ 2 := by
    rw [hsq, hcos]
    linear_combination -((‖s‖ - t) ^ 2) * Real.sin_sq_add_cos_sq (s.arg / 2)
  have : (Real.cos (s.arg / 2) * (‖s‖ + t)) ^ 2 ≤ ‖s + t‖ ^ 2 := by
    linarith [sq_nonneg (Real.sin (s.arg / 2) * (‖s‖ - t))]
  nlinarith [norm_nonneg (s + t)]

/-- On the closed sector `|arg s| ≤ π - δ` with `0 ≤ δ`, `sin (δ / 2) ≤ cos (arg s / 2)`. -/
theorem sin_div_two_le_cos_arg_div_two_of_abs_arg_le {s : ℂ} {δ : ℝ}
    (hδ : 0 ≤ δ) (hs : |s.arg| ≤ Real.pi - δ) :
    Real.sin (δ / 2) ≤ Real.cos (s.arg / 2) := by
  rw [← Real.cos_pi_div_two_sub, ← Real.cos_abs (s.arg / 2), abs_div,
    abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) (by linarith [Real.pi_pos])
    (by linarith)

/-- On the closed sector `|arg s| ≤ π - δ` with `0 ≤ δ`, translation by a nonnegative real `t`
satisfies the sharp half-angle bound `sin (δ / 2) * (‖s‖ + t) ≤ ‖s + t‖`. -/
theorem sin_div_two_mul_norm_add_le_norm_add_ofReal_of_abs_arg_le {s : ℂ} {δ t : ℝ}
    (hδ : 0 ≤ δ) (hs : |s.arg| ≤ Real.pi - δ) (ht : 0 ≤ t) :
    Real.sin (δ / 2) * (‖s‖ + t) ≤ ‖s + t‖ :=
  (mul_le_mul_of_nonneg_right (sin_div_two_le_cos_arg_div_two_of_abs_arg_le hδ hs)
    (add_nonneg (norm_nonneg s) ht)).trans
    (cos_arg_div_two_mul_norm_add_le_norm_add_ofReal s t)

/-- If `(2c - 1) ‖s‖ ≤ re s` with `0 ≤ c ≤ 1`, then `c * (‖s‖ + t) ≤ ‖s + t‖` for every
nonnegative real `t`. -/
theorem mul_norm_add_le_norm_add_ofReal {s : ℂ} {c t : ℝ}
    (hc : 0 ≤ c) (hc1 : c ≤ 1) (ht : 0 ≤ t)
    (hs : (2 * c - 1) * ‖s‖ ≤ s.re) :
    c * (‖s‖ + t) ≤ ‖s + t‖ := by
  have hsq : ‖s + t‖ ^ 2 = ‖s‖ ^ 2 + 2 * t * s.re + t ^ 2 := by
    simp only [Complex.sq_norm, normSq_apply, add_re, ofReal_re, add_im, ofReal_im, add_zero]
    ring
  have h : c * (‖s‖ + t) ^ 2 ≤ ‖s + t‖ ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hc1) (sq_nonneg (‖s‖ - t)),
      mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 2 * t)]
  have hc2 : c ^ 2 ≤ c := by nlinarith
  have h2 : (c * (‖s‖ + t)) ^ 2 ≤ ‖s + t‖ ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hc2 (sq_nonneg (‖s‖ + t))]
  nlinarith [norm_nonneg (s + t)]

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
