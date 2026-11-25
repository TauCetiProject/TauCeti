/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.IncompleteBeta.Neighbours

/-!
# Examples: the incomplete beta kernel at the slope `(1/3, 1/3)`

At `s = t = 1/3` the complex slope is `ξ = e^{πi/3}`, of modulus `1`. The kernel between the
vertical neighbours `(0, 0)` and `(0, 1)` is `-1/3` going up and `1/3 - √3/(2π)` going down, and
along a row the kernel is the discrete sine kernel `sin(πm/3) / (πm)`.
-/

public section

open Complex
open scoped Real

namespace TauCeti.IncompleteBetaNeighboursExample

private theorem pos : (0 : ℝ) < 1 / 3 := by norm_num

private theorem sum_lt : (1 / 3 : ℝ) + 1 / 3 < 1 := by norm_num

private theorem sin_ratio : Real.sin (π * (1 / 3)) / Real.sin (π * (1 - 1 / 3 - 1 / 3)) = 1 := by
  rw [show (1 : ℝ) - 1 / 3 - 1 / 3 = 1 / 3 by norm_num,
    div_self (Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])).ne']

-- At `s = t = 1/3` the complex slope is `e^{πi/3}`.
example : complexSlope (1 / 3) (1 / 3) = exp (↑(π / 3) * I) := by
  rw [complexSlope_def, sin_ratio]
  simp [div_eq_mul_inv, mul_comm]

/-- At `s = t = 1/3` the complex slope has modulus `1`. -/
theorem norm_complexSlope_third : ‖complexSlope (1 / 3) (1 / 3)‖ = 1 := by
  rw [norm_complexSlope pos pos sum_lt, sin_ratio]

/-- At `s = t = 1/3` the complex slope has imaginary part `√3 / 2`. -/
theorem im_complexSlope_third : (complexSlope (1 / 3) (1 / 3)).im = √3 / 2 := by
  rw [← norm_mul_sin_arg, norm_complexSlope_third, arg_complexSlope pos pos sum_lt, one_mul,
    show π * (1 / 3) = π / 3 by ring, Real.sin_pi_div_three]

-- Going up, `K_ξ((0, 0); (0, 1)) = -1/3`.
example : incompleteBetaKernel (complexSlope (1 / 3) (1 / 3)) (0, 0) (0, 1) = -1 / 3 := by
  have h := incompleteBetaKernel_complexSlope_add_snd_one pos pos sum_lt (0, 0)
  simp only [Prod.mk_add_mk, add_zero, zero_add] at h
  rw [h]
  push_cast
  ring

-- Going down, `K_ξ((0, 1); (0, 0)) = 1/3 - √3 / (2π)`.
example : incompleteBetaKernel (complexSlope (1 / 3) (1 / 3)) (0, 1) (0, 0) =
    ((1 / 3 - √3 / (2 * π) : ℝ) : ℂ) := by
  have h := incompleteBetaKernel_complexSlope_add_snd_one_left pos pos sum_lt (0, 0)
  simp only [Prod.mk_add_mk, add_zero, zero_add] at h
  rw [h, im_complexSlope_third]
  congr 1
  field_simp

-- Along a row the kernel is the discrete sine kernel `sin(πm/3) / (πm)`.
example (v : ℤ × ℤ) {m : ℤ} (hm : m ≠ 0) :
    incompleteBetaKernel (complexSlope (1 / 3) (1 / 3)) v (v + (m, 0)) =
      ((Real.sin (π * m / 3) / (π * m) : ℝ) : ℂ) := by
  rw [incompleteBetaKernel_add_row _ v hm, norm_complexSlope_third, one_zpow, one_mul,
    arg_complexSlope pos pos sum_lt]
  congr 2
  ring_nf

end TauCeti.IncompleteBetaNeighboursExample
