/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# The argument of a quotient, and rotations onto the nonpositive real axis

Mathlib computes the argument of a quotient only modulo `2π` (`Complex.arg_div_coe_angle`), and
of a product exactly when the sum of the arguments lies in `(-π, π]`
(`Complex.arg_mul_eq_add_arg_iff`). This file records the analogue for quotients, and its most
common instance: for two points of the open upper half-plane the arguments lie in `(0, π)`, so
the argument of their quotient is the difference of their arguments. It also records that every
complex number is rotated onto the nonpositive real axis by the square of a unit complex number.
Finally, a sector `{|arg ((z - v) / b)| < α}` of half-opening `α ≤ π`, cut off by a punctured ball
about its vertex, is the image of an open rectangle in polar coordinates.

## Main results

* `Complex.arg_div_eq_sub_arg_iff`: `arg (x / y) = arg x - arg y` exactly when
  `arg x - arg y ∈ (-π, π]`.
* `Complex.arg_div_of_im_pos`: if `0 < x.im` and `0 < y.im`, then `arg (x / y) = arg x - arg y`.
* `Complex.exists_norm_eq_one_mul_sq_eq_neg_norm`: every `c` has a unit `ω` with `c ω² = -‖c‖`.
* `TauCeti.image_polar_rectangle_eq`: in polar coordinates about `v`, rotated and scaled by `b`,
  the punctured truncated sector `{|arg ((z - v) / b)| < α}`, `α ≤ π`, is the image of an open
  rectangle.
-/

public section

open Real

namespace Complex

/-- The argument of a quotient is the difference of the arguments exactly when that difference
lies in `(-π, π]`. -/
theorem arg_div_eq_sub_arg_iff {x y : ℂ} (hx₀ : x ≠ 0) (hy₀ : y ≠ 0) :
    arg (x / y) = arg x - arg y ↔ arg x - arg y ∈ Set.Ioc (-π) π := by
  rw [← arg_coe_angle_toReal_eq_arg, arg_div_coe_angle hx₀ hy₀, ← Real.Angle.coe_sub,
    Real.Angle.toReal_coe_eq_self_iff_mem_Ioc]

/-- The argument of the quotient of two points of the open upper half-plane is the difference of
their arguments. -/
theorem arg_div_of_im_pos {x y : ℂ} (hx : 0 < x.im) (hy : 0 < y.im) :
    arg (x / y) = arg x - arg y :=
  (arg_div_eq_sub_arg_iff (fun h ↦ hx.ne' (by rw [h, zero_im]))
    (fun h ↦ hy.ne' (by rw [h, zero_im]))).2
    ⟨by linarith [arg_nonneg_iff.2 hx.le, arg_lt_pi_iff.2 (Or.inr hy.ne')],
      by linarith [arg_nonneg_iff.2 hy.le, arg_le_pi x]⟩

/-- Every complex number `c` is rotated onto the nonpositive real axis by the square of a unit:
`c ω² = -‖c‖`. -/
theorem exists_norm_eq_one_mul_sq_eq_neg_norm (c : ℂ) :
    ∃ ω : ℂ, ‖ω‖ = 1 ∧ c * ω ^ 2 = -‖c‖ := by
  refine ⟨exp (((π - arg c) / 2 : ℝ) * I), norm_exp_ofReal_mul_I _, ?_⟩
  have h : (arg c : ℂ) * I + 2 * (((π - arg c) / 2 : ℝ) * I) = π * I := by
    push_cast
    ring
  calc c * exp (((π - arg c) / 2 : ℝ) * I) ^ 2
      = ‖c‖ * exp ((arg c : ℂ) * I + 2 * (((π - arg c) / 2 : ℝ) * I)) := by
        rw [exp_add, ← mul_assoc, norm_mul_exp_arg_mul_I, ← exp_nat_mul]
        norm_num
    _ = -‖c‖ := by
        rw [h, exp_pi_mul_I]
        ring

end Complex

namespace TauCeti

open Complex Metric Set

/-- In polar coordinates about `v`, rotated and scaled by `b`, the open sector
`{|arg ((z - v) / b)| < α}` of half-opening `α ≤ π`, cut off by the punctured ball of radius `δ`, is
the image of an open rectangle. -/
theorem image_polar_rectangle_eq {v b : ℂ} (hb : b ≠ 0) {δ α : ℝ} (hα : α ≤ Real.pi) :
    (fun p : ℝ × ℝ => v + b * ((p.1 : ℂ) * (Complex.cos (p.2 : ℂ) + Complex.sin (p.2 : ℂ) * I))) ''
        (Ioo 0 (δ / ‖b‖) ×ˢ Ioo (-α) α) =
      {z | z ∈ ball v δ ∧ z ≠ v ∧ |((z - v) / b).arg| < α} := by
  have hb' : 0 < ‖b‖ := norm_pos_iff.mpr hb
  ext z
  constructor
  · rintro ⟨⟨r, θ⟩, ⟨⟨hr, hrδ⟩, hθ⟩, rfl⟩
    have hdiv : (v + b * ((r : ℂ) * (Complex.cos (θ : ℂ) + Complex.sin (θ : ℂ) * I)) - v) / b =
        (r : ℂ) * (Complex.cos (θ : ℂ) + Complex.sin (θ : ℂ) * I) := by
      field_simp
      ring
    have hnorm : ‖v + b * ((r : ℂ) * (Complex.cos (θ : ℂ) + Complex.sin (θ : ℂ) * I)) - v‖ =
        ‖b‖ * r := by
      rw [add_sub_cancel_left, norm_mul, norm_mul, norm_real, norm_cos_add_sin_mul_I,
        Real.norm_of_nonneg hr.le, mul_one]
    refine ⟨?_, fun h => ?_, ?_⟩
    · rw [mem_ball, dist_eq_norm, hnorm]
      rwa [lt_div_iff₀' hb'] at hrδ
    · beta_reduce at h
      rw [h, sub_self, norm_zero] at hnorm
      exact (mul_pos hb' hr).ne' hnorm.symm
    · rw [hdiv, arg_mul_cos_add_sin_mul_I hr ⟨by linarith [hθ.1, hθ.2], by linarith [hθ.2]⟩]
      exact abs_lt.mpr hθ
  · rintro ⟨hzb, hzv, harg⟩
    have hw : (z - v) / b ≠ 0 := div_ne_zero (sub_ne_zero.mpr hzv) hb
    refine ⟨(‖(z - v) / b‖, ((z - v) / b).arg), ⟨⟨norm_pos_iff.mpr hw, ?_⟩, abs_lt.mp harg⟩, ?_⟩
    · rw [norm_div, div_lt_div_iff_of_pos_right hb', ← dist_eq_norm]
      exact mem_ball.mp hzb
    · simp only [norm_mul_cos_add_sin_mul_I]
      field_simp
      ring

end TauCeti
