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
The derivatives `Ai′` and `Bi′` are again combinations of regularized `₀F₁` series, since
differentiating `₀F₁(; b; ·)` raises the parameter `b` by one.

The series here use Gamma denominators, grouping the powers congruent to zero and one modulo
three.

## References

* NIST Digital Library of Mathematical Functions, §§9.2(ii), 9.4,
  <https://dlmf.nist.gov/9.2>, <https://dlmf.nist.gov/9.4>.

The derivative formulas are adapted from the lean-DLMF project
(<https://github.com/bjbraams/lean-DLMF>), file `DLMF/Airy/Basic/Properties.lean`.
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

/-- At the origin, `Bi(0)² = 3 Ai(0)²`. -/
theorem airyBi_zero_sq : airyBi 0 ^ 2 = 3 * airyAi 0 ^ 2 := by
  have h3 : (3 : ℂ) ≠ 0 := by norm_num
  have hpow : ((3 : ℂ) ^ (-1 / 6 : ℂ)) ^ 2 = 3 * ((3 : ℂ) ^ (-2 / 3 : ℂ)) ^ 2 := by
    nth_rw 2 [← cpow_one (3 : ℂ)]
    rw [sq, sq, ← cpow_add _ _ h3, ← cpow_add _ _ h3, ← cpow_add _ _ h3]
    norm_num
  rw [airyAi_zero, airyBi_zero, div_pow, div_pow, hpow, mul_div_assoc]

/-- At the origin, `Ai(0)² + Bi(0)² = 4 Ai(0)²`. -/
theorem airyAi_zero_sq_add_airyBi_zero_sq : airyAi 0 ^ 2 + airyBi 0 ^ 2 = 4 * airyAi 0 ^ 2 := by
  rw [airyBi_zero_sq]; ring

/-- The chain rule for `z ↦ ₀F₁(; b; z³/9)`: its derivative is `(z²/3) ₀F₁(; b + 1; z³/9)`. -/
theorem _root_.Complex.hasDerivAt_regularizedHGFun_zero_singleton_pow_three_div_nine (b z : ℂ) :
    HasDerivAt (fun z : ℂ => regularizedHGFun 0 {b} (z ^ 3 / 9))
      (z ^ 2 / 3 * regularizedHGFun 0 {b + 1} (z ^ 3 / 9)) z := by
  have h := (hasDerivAt_regularizedHGFun_zero_singleton b (z ^ 3 / 9)).comp z
    ((hasDerivAt_pow 3 z).div_const 9)
  refine h.congr_deriv ?_
  push_cast
  ring

/-- `3 ^ s = 3 ^ t * 3` when `s = t + 1`. This relates the constants `3^{-1/3}` and `3^{1/6}` of
`Ai′` and `Bi′` to the constants `3^{-4/3}` and `3^{-5/6}` of `Ai` and `Bi`. -/
private theorem three_cpow_of_eq_add_one {s t : ℂ} (h : s = t + 1) :
    (3 : ℂ) ^ s = 3 ^ t * 3 := by
  rw [h, cpow_add _ _ (by norm_num : (3 : ℂ) ≠ 0), cpow_one]

/-- The derivative of `Ai` as a combination of regularized `₀F₁` series. -/
theorem hasDerivAt_airyAi (z : ℂ) :
    HasDerivAt airyAi (-(3 : ℂ) ^ (-1 / 3 : ℂ) * regularizedHGFun 0 {(1 / 3 : ℂ)} (z ^ 3 / 9) +
      (3 : ℂ) ^ (-2 / 3 : ℂ) * (z ^ 2 / 3) * regularizedHGFun 0 {(5 / 3 : ℂ)} (z ^ 3 / 9)) z := by
  have h := ((hasDerivAt_regularizedHGFun_zero_singleton_pow_three_div_nine (2 / 3) z).const_mul
    ((3 : ℂ) ^ (-2 / 3 : ℂ))).sub (((hasDerivAt_id z).mul
      (hasDerivAt_regularizedHGFun_zero_singleton_pow_three_div_nine (4 / 3) z)).const_mul
      ((3 : ℂ) ^ (-4 / 3 : ℂ)))
  simp only [Pi.sub_def, Pi.mul_def, id] at h
  rw [funext airyAi_def]
  convert h using 1
  · ext w
    ring
  · rw [regularizedHGFun_zero_singleton_eq_mul_add_mul (1 / 3 : ℂ),
      three_cpow_of_eq_add_one (by norm_num : (-1 / 3 : ℂ) = -4 / 3 + 1)]
    norm_num
    ring

/-- The derivative of `Bi` as a combination of regularized `₀F₁` series. -/
theorem hasDerivAt_airyBi (z : ℂ) :
    HasDerivAt airyBi ((3 : ℂ) ^ (1 / 6 : ℂ) * regularizedHGFun 0 {(1 / 3 : ℂ)} (z ^ 3 / 9) +
      (3 : ℂ) ^ (-1 / 6 : ℂ) * (z ^ 2 / 3) * regularizedHGFun 0 {(5 / 3 : ℂ)} (z ^ 3 / 9)) z := by
  have h := ((hasDerivAt_regularizedHGFun_zero_singleton_pow_three_div_nine (2 / 3) z).const_mul
    ((3 : ℂ) ^ (-1 / 6 : ℂ))).add (((hasDerivAt_id z).mul
      (hasDerivAt_regularizedHGFun_zero_singleton_pow_three_div_nine (4 / 3) z)).const_mul
      ((3 : ℂ) ^ (-5 / 6 : ℂ)))
  simp only [Pi.add_def, Pi.mul_def, id] at h
  rw [funext airyBi_def]
  convert h using 1
  · ext w
    ring
  · rw [regularizedHGFun_zero_singleton_eq_mul_add_mul (1 / 3 : ℂ),
      three_cpow_of_eq_add_one (by norm_num : (1 / 6 : ℂ) = -5 / 6 + 1)]
    norm_num
    ring

/-- The derivative of `Ai`: `Ai′(z) = −3^{−1/3} 𝐅(⅓, z³/9) + 3^{−2/3} (z²/3) 𝐅(5/3, z³/9)`. -/
theorem deriv_airyAi (z : ℂ) :
    deriv airyAi z = -(3 : ℂ) ^ (-1 / 3 : ℂ) * regularizedHGFun 0 {(1 / 3 : ℂ)} (z ^ 3 / 9) +
      (3 : ℂ) ^ (-2 / 3 : ℂ) * (z ^ 2 / 3) * regularizedHGFun 0 {(5 / 3 : ℂ)} (z ^ 3 / 9) :=
  (hasDerivAt_airyAi z).deriv

/-- The derivative of `Bi`: `Bi′(z) = 3^{1/6} 𝐅(⅓, z³/9) + 3^{−1/6} (z²/3) 𝐅(5/3, z³/9)`. -/
theorem deriv_airyBi (z : ℂ) :
    deriv airyBi z = (3 : ℂ) ^ (1 / 6 : ℂ) * regularizedHGFun 0 {(1 / 3 : ℂ)} (z ^ 3 / 9) +
      (3 : ℂ) ^ (-1 / 6 : ℂ) * (z ^ 2 / 3) * regularizedHGFun 0 {(5 / 3 : ℂ)} (z ^ 3 / 9) :=
  (hasDerivAt_airyBi z).deriv

/-- DLMF 9.2.4: the first derivative of `Ai` at the origin. -/
@[simp]
theorem deriv_airyAi_zero : deriv airyAi 0 = -(3 : ℂ) ^ (-1 / 3 : ℂ) / Gamma (1 / 3) := by
  simp [deriv_airyAi, div_eq_mul_inv]

/-- DLMF 9.2.6: the first derivative of `Bi` at the origin. -/
@[simp]
theorem deriv_airyBi_zero : deriv airyBi 0 = (3 : ℂ) ^ (1 / 6 : ℂ) / Gamma (1 / 3) := by
  simp [deriv_airyBi, div_eq_mul_inv]

end TauCeti
