/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Tiling.Lozenge.KernelAngles
import TauCeti.Analysis.SpecialFunctions.Trigonometric.Arccos
import TauCeti.Examples.Combinatorics.Tiling.Lozenge.CharacteristicFunction

/-!
# Checks: the angles of the lozenge kernel for uniform weights

For `w = (1, 1, 1)` the triangle with sides `w₁, w₂, w₃` is equilateral, so every angle `θ_k` is
`π/3`:

* `G(0) = 1/3`, so each lozenge type has density `1/3`;
* `G(−e₂) = G(e₁) = 1/3`;
* along the row `d₂ = −1`, `G((1, −1)) = −√3 / (2π)`;
* `G((0, −2)) = √3 / (2π) − 1/3`, from the three-term identity at `d = (0, −1)`.
-/

public section

noncomputable section

open Complex
open scoped Real

namespace TauCeti.Examples.LozengeKernelAngles

/-- For uniform weights every angle of the triangle is `π/3`. -/
theorem lozengeTriangleAngle_one_one_one : lozengeTriangleAngle 1 1 1 = π / 3 := by
  have hmem := lozengeTriangleAngle_mem_Icc 1 1 1
  have hcos := cos_lozengeTriangleAngle (a := 1) one_pos one_pos (by norm_num) (by norm_num)
    (by norm_num)
  rw [← Real.arccos_one_half, ← Real.arccos_cos hmem.1 hmem.2, hcos]
  norm_num

/-- `1 / P_w` is integrable on the torus for uniform weights, which are liquid. -/
private theorem integrableOn_one_one_one :
    MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (lozengeCharFun 1 1 1 p.1 p.2)⁻¹)
      (Set.Ioc 0 (2 * π) ×ˢ Set.Ioc 0 (2 * π)) :=
  LozengeCharFun.isLiquidWeights_one_one_one.integrableOn_inv_lozengeCharFun

/-- For uniform weights `G(0) = 1/3`: each lozenge type has density `1/3`. -/
theorem lozengeKernel_one_one_one_zero : lozengeKernel 1 1 1 0 = 1 / 3 := by
  have h := mul_lozengeKernel_zero one_pos one_pos one_pos integrableOn_one_one_one
  rw [lozengeTriangleAngle_one_one_one, ofReal_one, one_mul] at h
  rw [h]
  push_cast
  field_simp

/-- For uniform weights `G(−e₂) = 1/3`. -/
theorem lozengeKernel_one_one_one_zero_neg_one : lozengeKernel 1 1 1 (0, -1) = 1 / 3 := by
  have h := mul_lozengeKernel_zero_neg_one one_pos one_pos one_pos integrableOn_one_one_one
  rw [lozengeTriangleAngle_one_one_one, ofReal_one, one_mul] at h
  rw [h]
  push_cast
  field_simp

/-- For uniform weights `G(e₁) = 1/3`. -/
theorem lozengeKernel_one_one_one_one_zero : lozengeKernel 1 1 1 (1, 0) = 1 / 3 := by
  have h := mul_lozengeKernel_one_zero one_pos one_pos one_pos integrableOn_one_one_one
  rw [lozengeTriangleAngle_one_one_one, ofReal_one, one_mul] at h
  rw [h]
  push_cast
  field_simp

/-- For uniform weights `G((1, −1)) = −√3 / (2π)`. -/
theorem lozengeKernel_one_one_one_one_neg_one :
    lozengeKernel 1 1 1 (1, -1) = -((√3 / (2 * π) : ℝ) : ℂ) := by
  have h := mul_lozengeKernel_row_of_ne_zero one_pos one_pos one_pos integrableOn_one_one_one
    (m := 1) one_ne_zero
  rw [lozengeTriangleAngle_one_one_one, ofReal_one, one_mul, Int.cast_one] at h
  rw [h, one_mul, Real.sin_pi_div_three, zpow_one]
  push_cast
  ring

/-- For uniform weights `G((0, −2)) = √3 / (2π) − 1/3`, by the three-term identity at
`d = (0, −1)`: `G((0, −1)) + G((1, −1)) + G((0, −2)) = 0`. -/
theorem lozengeKernel_one_one_one_zero_neg_two :
    lozengeKernel 1 1 1 (0, -2) = ((√3 / (2 * π) : ℝ) : ℂ) - 1 / 3 := by
  have h := LozengeCharFun.isLiquidWeights_one_one_one.lozengeKernel_three_term (0, -1)
  rw [ite_eq_right (by decide)] at h
  rw [Prod.mk_add_mk, Prod.mk_sub_mk, zero_add, add_zero, sub_self,
    show (-1 : ℤ) - 1 = -2 by norm_num, lozengeKernel_one_one_one_zero_neg_one,
    lozengeKernel_one_one_one_one_neg_one] at h
  push_cast at h ⊢
  linear_combination h

end TauCeti.Examples.LozengeKernelAngles
