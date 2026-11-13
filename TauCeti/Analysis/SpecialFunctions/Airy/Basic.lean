/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.RegularizedHypergeometric
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
# Airy functions: definitions and series

The Airy functions `airyAi` and `airyBi` are defined through the regularized hypergeometric
function `₀F₁`. They are entire. Their everywhere convergent series and their values and first
derivatives at the origin fix the standard normalization of the two solutions of Airy's equation.

The series here use Gamma denominators, grouping the powers congruent to zero and one modulo
three.

## References

* NIST Digital Library of Mathematical Functions, §§9.2(ii), 9.4,
  <https://dlmf.nist.gov/9.2>, <https://dlmf.nist.gov/9.4>.
-/

public section

noncomputable section

open Complex
open scoped Nat

namespace TauCeti

/-- The Airy function `Ai`, with the standard normalization of DLMF 9.2.3–9.2.4. -/
def airyAi (z : ℂ) : ℂ :=
  (3 : ℂ) ^ (-2 / 3 : ℂ) * regularizedHGFun 0 {(2 / 3 : ℂ)} (z ^ 3 / 9) -
    (3 : ℂ) ^ (-4 / 3 : ℂ) * z * regularizedHGFun 0 {(4 / 3 : ℂ)} (z ^ 3 / 9)

/-- The Airy function `Bi`, with the standard normalization of DLMF 9.2.5–9.2.6. -/
def airyBi (z : ℂ) : ℂ :=
  (3 : ℂ) ^ (-1 / 6 : ℂ) * regularizedHGFun 0 {(2 / 3 : ℂ)} (z ^ 3 / 9) +
    (3 : ℂ) ^ (-5 / 6 : ℂ) * z * regularizedHGFun 0 {(4 / 3 : ℂ)} (z ^ 3 / 9)

/-- The defining hypergeometric expression for `Ai`. -/
theorem airyAi_def (z : ℂ) :
    airyAi z =
      (3 : ℂ) ^ (-2 / 3 : ℂ) * regularizedHGFun 0 {(2 / 3 : ℂ)} (z ^ 3 / 9) -
        (3 : ℂ) ^ (-4 / 3 : ℂ) * z * regularizedHGFun 0 {(4 / 3 : ℂ)} (z ^ 3 / 9) := (rfl)

/-- The defining hypergeometric expression for `Bi`. -/
theorem airyBi_def (z : ℂ) :
    airyBi z =
      (3 : ℂ) ^ (-1 / 6 : ℂ) * regularizedHGFun 0 {(2 / 3 : ℂ)} (z ^ 3 / 9) +
        (3 : ℂ) ^ (-5 / 6 : ℂ) * z * regularizedHGFun 0 {(4 / 3 : ℂ)} (z ^ 3 / 9) := (rfl)

@[fun_prop]
private theorem differentiable_airy_hypergeometric (b : ℂ) :
    Differentiable ℂ (fun z : ℂ => regularizedHGFun 0 {b} (z ^ 3 / 9)) := by
  intro z
  exact (analyticAt_regularizedHGFun_zero _).differentiableAt.comp z (by fun_prop)

/-- `Ai` is entire. -/
@[fun_prop]
theorem differentiable_airyAi : Differentiable ℂ airyAi := by
  rw [funext airyAi_def]
  fun_prop

/-- `Bi` is entire. -/
@[fun_prop]
theorem differentiable_airyBi : Differentiable ℂ airyBi := by
  rw [funext airyBi_def]
  fun_prop

/-- The everywhere convergent Gamma-denominator Maclaurin series of `Ai`. -/
theorem hasSum_airyAi_gamma (z : ℂ) :
    HasSum (fun n : ℕ =>
      (3 : ℂ) ^ (-2 / 3 : ℂ) * ((z ^ 3 / 9) ^ n / (n ! * Gamma (2 / 3 + n))) -
      (3 : ℂ) ^ (-4 / 3 : ℂ) * z *
        ((z ^ 3 / 9) ^ n / (n ! * Gamma (4 / 3 + n)))) (airyAi z) := by
  convert
    ((hasSum_regularizedHGFun (a := 0) (b := {(2 / 3 : ℂ)}) (by simp) (z ^ 3 / 9)).mul_left
      ((3 : ℂ) ^ (-2 / 3 : ℂ))).sub
    ((hasSum_regularizedHGFun (a := 0) (b := {(4 / 3 : ℂ)}) (by simp) (z ^ 3 / 9)).mul_left
      ((3 : ℂ) ^ (-4 / 3 : ℂ) * z)) using 1
  · ext n
    simp only [regularizedHGFunCoeff_zero_singleton]
    ring
  · rfl

/-- The everywhere convergent Gamma-denominator Maclaurin series of `Bi`. -/
theorem hasSum_airyBi_gamma (z : ℂ) :
    HasSum (fun n : ℕ =>
      (3 : ℂ) ^ (-1 / 6 : ℂ) * ((z ^ 3 / 9) ^ n / (n ! * Gamma (2 / 3 + n))) +
      (3 : ℂ) ^ (-5 / 6 : ℂ) * z *
        ((z ^ 3 / 9) ^ n / (n ! * Gamma (4 / 3 + n)))) (airyBi z) := by
  convert
    ((hasSum_regularizedHGFun (a := 0) (b := {(2 / 3 : ℂ)}) (by simp) (z ^ 3 / 9)).mul_left
      ((3 : ℂ) ^ (-1 / 6 : ℂ))).add
    ((hasSum_regularizedHGFun (a := 0) (b := {(4 / 3 : ℂ)}) (by simp) (z ^ 3 / 9)).mul_left
      ((3 : ℂ) ^ (-5 / 6 : ℂ) * z)) using 1
  · ext n
    simp only [regularizedHGFunCoeff_zero_singleton]
    ring
  · rfl

/-- DLMF 9.2.3: the value of `Ai` at the origin. -/
@[simp]
theorem airyAi_zero : airyAi 0 = (3 : ℂ) ^ (-2 / 3 : ℂ) / Gamma (2 / 3) := by
  simp [airyAi, div_eq_mul_inv]

/-- DLMF 9.2.5: the value of `Bi` at the origin. -/
@[simp]
theorem airyBi_zero : airyBi 0 = (3 : ℂ) ^ (-1 / 6 : ℂ) / Gamma (2 / 3) := by
  simp [airyBi, div_eq_mul_inv]

private theorem hasDerivAt_airy_hypergeometric_zero (b : ℂ) :
    HasDerivAt (fun z : ℂ => regularizedHGFun 0 {b} (z ^ 3 / 9)) 0 0 := by
  have h := (analyticAt_regularizedHGFun_zero (b := {b})
    ((0 : ℂ) ^ 3 / 9)).differentiableAt.hasDerivAt
  simpa [Function.comp_def] using
    h.comp 0 (((hasDerivAt_id' (0 : ℂ)).pow 3).div_const 9)

private theorem airy_derivative_coefficient (a : ℂ) :
    (3 : ℂ) ^ a / Gamma (4 / 3) = (3 : ℂ) ^ (a + 1) / Gamma (1 / 3) := by
  have hshift : (4 / 3 : ℂ) = 1 / 3 + 1 := by norm_num
  have hG : Gamma (4 / 3 : ℂ) = Gamma (1 / 3 : ℂ) / 3 := by
    rw [hshift, Gamma_add_one _ (by norm_num)]
    ring
  rw [hG, cpow_add _ _ (by norm_num), cpow_one]
  ring

/-- DLMF 9.2.4: the first derivative of `Ai` at the origin. -/
@[simp]
theorem deriv_airyAi_zero : deriv airyAi 0 = -(3 : ℂ) ^ (-1 / 3 : ℂ) / Gamma (1 / 3) := by
  have h := ((hasDerivAt_airy_hypergeometric_zero (2 / 3)).const_mul
    ((3 : ℂ) ^ (-2 / 3 : ℂ))).sub
    (((hasDerivAt_id' (0 : ℂ)).const_mul ((3 : ℂ) ^ (-4 / 3 : ℂ))).mul
      (hasDerivAt_airy_hypergeometric_zero (4 / 3)))
  rw [Pi.sub_def, Pi.mul_def] at h
  rw [funext airyAi_def, h.deriv]
  convert congrArg Neg.neg (airy_derivative_coefficient (-4 / 3)) using 1 <;>
    norm_num [div_eq_mul_inv]

/-- DLMF 9.2.6: the first derivative of `Bi` at the origin. -/
@[simp]
theorem deriv_airyBi_zero : deriv airyBi 0 = (3 : ℂ) ^ (1 / 6 : ℂ) / Gamma (1 / 3) := by
  have h := ((hasDerivAt_airy_hypergeometric_zero (2 / 3)).const_mul
    ((3 : ℂ) ^ (-1 / 6 : ℂ))).add
    (((hasDerivAt_id' (0 : ℂ)).const_mul ((3 : ℂ) ^ (-5 / 6 : ℂ))).mul
      (hasDerivAt_airy_hypergeometric_zero (4 / 3)))
  rw [Pi.add_def, Pi.mul_def] at h
  rw [funext airyBi_def, h.deriv]
  convert airy_derivative_coefficient (-5 / 6) using 1 <;> norm_num [div_eq_mul_inv]

end TauCeti
