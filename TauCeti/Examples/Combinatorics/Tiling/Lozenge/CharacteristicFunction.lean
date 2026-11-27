/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Tiling.Lozenge.CharacteristicFunction
import TauCeti.Analysis.Fourier.InvAddMulExp
import TauCeti.Analysis.SpecialFunctions.Trigonometric.Arccos
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Checks: zeros of the characteristic function of lozenge type weights

* `w = (1, 1, 1)` is liquid, with zero angles `θ₀ = φ₀ = 2π/3`: the zeros of
  `P_w(θ, φ) = 1 + e^{iθ} + e^{−iφ}` are `±(2π/3, 2π/3)` modulo `2π`.
* `w = (1, 1, 2)` is not liquid (`w₃ = w₁ + w₂`): `P_w` vanishes only at `(π, π)` modulo `2π`,
  and there `sin(θ + φ) = 0`, so the real Jacobian `w₁ w₂ sin(θ + φ)` is singular; such
  degenerate weights are excluded from "liquid".
* `w = (1, 1, 3)` is not liquid: `‖P_w‖ ≥ 1` everywhere, and `w₃ G_w(0) = 1`, the frozen value
  in which every lozenge has type `3`. The value comes from integrating `φ` and then `θ` with the
  Fourier coefficients of `1 / (b + c e^{iθ})` and `1 / (b + c e^{−iθ})`
  (`TauCeti.integral_exp_div_add_of_norm_lt_of_nonpos`, `TauCeti.integral_inv_add_mul_exp_neg`).
-/

public section

noncomputable section

open Complex Set MeasureTheory Filter

namespace TauCeti.Examples.LozengeCharFun

/-! ### `w = (1, 1, 1)` -/

/-- Uniform weights are liquid. -/
theorem isLiquidWeights_one_one_one : IsLiquidWeights 1 1 1 := by
  rw [isLiquidWeights_iff]; norm_num

/-- For uniform weights `θ₀ = 2π/3`. -/
theorem lozengeZeroAngleFst_one_one_one : lozengeZeroAngleFst 1 1 1 = 2 * Real.pi / 3 := by
  rw [lozengeZeroAngleFst_def, ← Real.arccos_neg_one_half]; norm_num

/-- For uniform weights `φ₀ = 2π/3`. -/
theorem lozengeZeroAngleSnd_one_one_one : lozengeZeroAngleSnd 1 1 1 = 2 * Real.pi / 3 := by
  rw [lozengeZeroAngleSnd_def, ← Real.arccos_neg_one_half]; norm_num

/-- For uniform weights the zeros of `P_w` are `±(2π/3, 2π/3)` modulo `2π`. -/
theorem lozengeCharFun_one_one_one_eq_zero_iff {θ φ : ℝ} :
    lozengeCharFun 1 1 1 θ φ = 0 ↔ ∃ m n : ℤ,
      (θ = 2 * m * Real.pi + 2 * Real.pi / 3 ∧ φ = 2 * n * Real.pi + 2 * Real.pi / 3) ∨
      (θ = 2 * m * Real.pi - 2 * Real.pi / 3 ∧ φ = 2 * n * Real.pi - 2 * Real.pi / 3) := by
  rw [lozengeCharFun_eq_zero_iff isLiquidWeights_one_one_one, lozengeZeroAngleFst_one_one_one,
    lozengeZeroAngleSnd_one_one_one]

/-! ### `w = (1, 1, 2)` -/

/-- `(1, 1, 2)` is not liquid: `w₃ = w₁ + w₂`. -/
theorem not_isLiquidWeights_one_one_two : ¬IsLiquidWeights 1 1 2 := by
  rw [isLiquidWeights_iff]; norm_num

/-- For `w = (1, 1, 2)` the only zero of `P_w` is `(π, π)` modulo `2π`. -/
theorem lozengeCharFun_one_one_two_eq_zero_iff {θ φ : ℝ} :
    lozengeCharFun 1 1 2 θ φ = 0 ↔ ∃ m n : ℤ,
      θ = Real.pi + m * (2 * Real.pi) ∧ φ = Real.pi + n * (2 * Real.pi) := by
  rw [lozengeCharFun_eq_zero_iff_re_im]
  constructor
  · rintro ⟨hre, -⟩
    have hθ : Real.cos θ = -1 := by
      nlinarith [Real.neg_one_le_cos θ, Real.neg_one_le_cos φ]
    have hφ : Real.cos φ = -1 := by
      nlinarith [Real.neg_one_le_cos θ, Real.neg_one_le_cos φ]
    obtain ⟨m, hm⟩ := Real.cos_eq_neg_one_iff.1 hθ
    obtain ⟨n, hn⟩ := Real.cos_eq_neg_one_iff.1 hφ
    exact ⟨m, n, hm.symm, hn.symm⟩
  · rintro ⟨m, n, rfl, rfl⟩
    simp only [Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi, Real.cos_pi,
      Real.sin_pi]
    norm_num

/-- At the zero `(π, π)` of `P_w` for `w = (1, 1, 2)`, `sin(θ + φ) = 0`: the real Jacobian
`w₁ w₂ sin(θ + φ)` is singular. -/
theorem sin_add_eq_zero_of_lozengeCharFun_one_one_two_eq_zero {θ φ : ℝ}
    (h : lozengeCharFun 1 1 2 θ φ = 0) : Real.sin (θ + φ) = 0 := by
  obtain ⟨m, n, rfl, rfl⟩ := lozengeCharFun_one_one_two_eq_zero_iff.1 h
  rw [show Real.pi + m * (2 * Real.pi) + (Real.pi + n * (2 * Real.pi)) =
    ((2 * (m + n + 1) : ℤ) : ℝ) * Real.pi by push_cast; ring, Real.sin_int_mul_pi]

/-! ### `w = (1, 1, 3)` -/

/-- `(1, 1, 3)` is not liquid: `w₃ > w₁ + w₂`. -/
theorem not_isLiquidWeights_one_one_three : ¬IsLiquidWeights 1 1 3 := by
  rw [isLiquidWeights_iff]; norm_num

private theorem two_le_norm_three_add_exp (θ : ℝ) : 2 ≤ ‖(3 : ℂ) + exp (θ * I)‖ := by
  have h := norm_sub_norm_le (3 : ℂ) (-exp (θ * I))
  rw [sub_neg_eq_add, norm_neg, norm_exp_ofReal_mul_I] at h
  norm_num at h
  linarith

/-- For `w = (1, 1, 3)`, `‖P_w‖ ≥ 1` everywhere. -/
theorem one_le_norm_lozengeCharFun_one_one_three (θ φ : ℝ) :
    1 ≤ ‖lozengeCharFun 1 1 3 θ φ‖ := by
  have h := norm_sub_norm_le ((3 : ℂ) + exp (θ * I)) (-exp (-(φ * I)))
  rw [sub_neg_eq_add, norm_neg, norm_exp_neg_ofReal_mul_I] at h
  rw [lozengeCharFun_def]
  push_cast
  simp only [one_mul]
  linarith [two_le_norm_three_add_exp θ]

/-- For `w = (1, 1, 3)`, `w₃ G_w(0) = 1`: the frozen value in which every lozenge has type `3`. -/
theorem three_mul_lozengeKernel_one_one_three_zero : 3 * lozengeKernel 1 1 3 0 = 1 := by
  have hcont : Continuous fun p : ℝ × ℝ => (lozengeCharFun 1 1 3 p.1 p.2)⁻¹ := by
    refine Continuous.inv₀ ?_ fun p h => ?_
    · simp only [lozengeCharFun_def]
      fun_prop
    · have := one_le_norm_lozengeCharFun_one_one_three p.1 p.2
      rw [h, norm_zero] at this
      norm_num at this
  have hint : IntegrableOn (fun p : ℝ × ℝ => (lozengeCharFun 1 1 3 p.1 p.2)⁻¹)
      (Ioc 0 (2 * Real.pi) ×ˢ Ioc 0 (2 * Real.pi)) (volume.prod volume) := by
    refine Measure.integrableOn_of_bounded (M := 1) ?_ hcont.aestronglyMeasurable
      (Eventually.of_forall fun p => ?_)
    · rw [Measure.prod_prod]; simp [ENNReal.mul_eq_top]
    · rw [norm_inv]
      exact inv_le_one_of_one_le₀ (one_le_norm_lozengeCharFun_one_one_three p.1 p.2)
  rw [lozengeKernel_def]
  simp only [Prod.fst_zero, Prod.snd_zero, Int.cast_zero, zero_mul, add_zero, ofReal_zero,
    Complex.exp_zero, one_div]
  rw [Measure.volume_eq_prod, setIntegral_prod _ hint]
  have hpi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have inner (x : ℝ) : ∫ y in Ioc 0 (2 * Real.pi), (lozengeCharFun 1 1 3 x y)⁻¹ =
      2 * Real.pi / (3 + exp (x * I)) := by
    rw [← intervalIntegral.integral_of_le hpi, ← integral_inv_add_mul_exp_neg (c := 1)
      (by rw [norm_one]; linarith [two_le_norm_three_add_exp x])]
    refine intervalIntegral.integral_congr fun y _ => ?_
    simp [lozengeCharFun_def]
  have outer := integral_exp_div_add_of_norm_lt_of_nonpos (b := 3) (c := 1) (by norm_num)
    (n := 0) le_rfl
  simp only [Int.cast_zero, zero_mul, Complex.exp_zero, one_mul, neg_zero, one_div] at outer
  simp_rw [inner, div_eq_mul_inv]
  rw [integral_const_mul, ← intervalIntegral.integral_of_le hpi, outer]
  have : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  simp only [real_smul, ofReal_inv, ofReal_mul, ofReal_pow]
  push_cast
  field_simp
  ring

end TauCeti.Examples.LozengeCharFun
