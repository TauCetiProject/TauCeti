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

## Main results

* `Complex.arg_div_eq_sub_arg_iff`: `arg (x / y) = arg x - arg y` exactly when
  `arg x - arg y ∈ (-π, π]`.
* `Complex.arg_div_of_im_pos`: if `0 < x.im` and `0 < y.im`, then `arg (x / y) = arg x - arg y`.
* `Complex.exists_norm_eq_one_mul_sq_eq_neg_norm`: every `c` has a unit `ω` with `c ω² = -‖c‖`.
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
