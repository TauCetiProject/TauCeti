/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.RegularizedHypergeometric.Basic

/-!
# Contiguous relations and derivative of the regularized Kummer function

Mathlib represents Olver's regularized confluent hypergeometric function
`𝐌(a, b, z) = ∑_{n ≥ 0} (a)ₙ zⁿ / (n! Γ(b + n))` as `Complex.regularizedHGFun {a} {b} z`.
Because `1 / Γ` is entire on `ℂ` (with Mathlib's convention `Γ(-n) = 0`), `𝐌(a, b, z)` is entire
in `z` for every pair of complex parameters `a` and `b`, including nonpositive integer values of
`b`.

This file establishes the derivative `∂𝐌(a, b, z)/∂z = a 𝐌(a + 1, b + 1, z)` and the contiguous
relations of `𝐌(a, b, z)` in `a` and `b` unconditionally for all `a, b, z : ℂ`. In particular,
`regularizedHGFun_one_singleton_eq_inv_Gamma_add_mul`, `regularizedHGFun_singleton_sub_mul`, and
`regularizedHGFun_singleton_sub_mul_add_one_left` drive the three-term recurrence for the explicit
Kummer solution of the incomplete Gamma continued fraction (DLMF 8.9.1).

## Main results

* `Complex.hasDerivAt_regularizedHGFun_singleton`, `Complex.deriv_regularizedHGFun_singleton` —
  `∂𝐌(a, b, z)/∂z = a 𝐌(a + 1, b + 1, z)` (DLMF 13.3.15).
* `Complex.regularizedHGFun_one_singleton_eq_inv_Gamma_add_mul` —
  `𝐌(1, b, z) = (Γ b)⁻¹ + z 𝐌(1, b + 1, z)`.
* `Complex.regularizedHGFun_add_one_singleton_sub` —
  `𝐌(a + 1, b, z) - 𝐌(a, b, z) = z 𝐌(a + 1, b + 1, z)` (DLMF 13.3.4).
* `Complex.regularizedHGFun_singleton_sub_mul` —
  `𝐌(a, b, z) - b 𝐌(a, b + 1, z) = a z 𝐌(a + 1, b + 2, z)`.
* `Complex.regularizedHGFun_singleton_sub_mul_add_one_left` —
  `𝐌(a, b, z) - b 𝐌(a + 1, b + 1, z) = (a - b) z 𝐌(a + 1, b + 2, z)`.
* `Complex.regularizedHGFun_singleton_eq_sub_mul_add_mul` —
  `𝐌(a, b, z) = (b - a) 𝐌(a, b + 1, z) + a 𝐌(a + 1, b + 1, z)` (DLMF 13.3.3).

## References

* *NIST Digital Library of Mathematical Functions*, [§13.2](https://dlmf.nist.gov/13.2) and
  [§13.3](https://dlmf.nist.gov/13.3).
-/

public section

noncomputable section

open Polynomial
open scoped Nat

namespace Complex

/-- The coefficients of the regularized Kummer series `𝐌(a, b, z) = regularizedHGFun {a} {b} z`
are `(a)ₙ / (n! Γ(b + n))`. -/
theorem regularizedHGFunCoeff_singleton (a b : ℂ) (n : ℕ) :
    regularizedHGFunCoeff {a} {b} n = (ascPochhammer ℂ n).eval a / (n ! * Gamma (b + n)) := by
  simp [regularizedHGFunCoeff]

/-- The constant term of the regularized Kummer series `𝐌(a, b, z)` is `(Γ b)⁻¹`. -/
@[simp]
theorem regularizedHGFunCoeff_singleton_zero (a b : ℂ) :
    regularizedHGFunCoeff {a} {b} 0 = (Gamma b)⁻¹ := by
  simp [regularizedHGFunCoeff]

/-- The derivative of the regularized Kummer function in its argument (DLMF 13.3.15):
`∂𝐌(a, b, z)/∂z = a 𝐌(a + 1, b + 1, z)`, valid for all complex `a`, `b`, and `z`. -/
theorem hasDerivAt_regularizedHGFun_singleton (a b z : ℂ) :
    HasDerivAt (regularizedHGFun {a} {b}) (a * regularizedHGFun {a + 1} {b + 1} z) z := by
  simpa using hasDerivAt_regularizedHGFun (a := {a}) (b := {b}) (z := z)
    (by simp [radius_regularizedHGFunSeries_eq_top])

/-- The derivative of `𝐌(a, b, ·)` as a function: `deriv (𝐌(a, b, ·)) = a 𝐌(a + 1, b + 1, ·)`. -/
@[simp]
theorem deriv_regularizedHGFun_singleton (a b : ℂ) :
    deriv (regularizedHGFun {a} {b}) = fun z => a * regularizedHGFun {a + 1} {b + 1} z :=
  funext fun z => (hasDerivAt_regularizedHGFun_singleton a b z).deriv

/-- Contiguous relation incrementing the upper parameter of `𝐌` (DLMF 13.3.4):
`𝐌(a + 1, b, z) - 𝐌(a, b, z) = z 𝐌(a + 1, b + 1, z)`, for all `a, b, z : ℂ`. -/
theorem regularizedHGFun_add_one_singleton_sub (a b z : ℂ) :
    regularizedHGFun {a + 1} {b} z - regularizedHGFun {a} {b} z =
      z * regularizedHGFun {a + 1} {b + 1} z := by
  have hsub := (hasSum_regularizedHGFun (a := {a + 1}) (b := {b}) (by simp) z).sub
    (hasSum_regularizedHGFun (a := {a}) (b := {b}) (by simp) z)
  have hshift := (hasSum_nat_add_iff' 1).mpr hsub
  simp only [Finset.range_one, Finset.sum_singleton, regularizedHGFunCoeff_singleton_zero, pow_zero,
    mul_one, sub_self, sub_zero] at hshift
  refine hshift.unique (((hasSum_regularizedHGFun (a := {a + 1}) (b := {b + 1})
    (by simp) z).mul_left z).congr_fun fun n => ?_)
  rw [regularizedHGFunCoeff_singleton, regularizedHGFunCoeff_singleton,
    regularizedHGFunCoeff_singleton]
  have hp : (ascPochhammer ℂ (n + 1)).eval (a + 1) - (ascPochhammer ℂ (n + 1)).eval a =
      (n + 1) * (ascPochhammer ℂ n).eval (a + 1) := by
    have h := congr_arg (eval a) (ascPochhammer_succ_comp_X_add_one ℂ n)
    simp only [nsmul_eq_mul, eval_add, eval_mul, eval_natCast, eval_one, eval_comp, eval_X,
      Nat.cast_add, Nat.cast_one] at h
    linear_combination h
  have hn : (n : ℂ) + 1 ≠ 0 := mod_cast n.succ_ne_zero
  have hb : b + ((n + 1 : ℕ) : ℂ) = b + 1 + n := by push_cast; ring
  rw [hb, Nat.factorial_succ, pow_succ']
  push_cast
  simp only [div_eq_mul_inv, mul_inv]
  linear_combination (((n : ℂ) + 1)⁻¹ * (n ! : ℂ)⁻¹ * (Gamma (b + 1 + n))⁻¹ * z * z ^ n) * hp +
    (ascPochhammer ℂ n).eval (a + 1) * (n ! : ℂ)⁻¹ * (Gamma (b + 1 + n))⁻¹ * z * z ^ n *
      mul_inv_cancel₀ hn

/-- Shifting the lower parameter in `𝐌(1, b, z) = ∑ zⁿ / Γ(b + n)` splits off the constant term:
`𝐌(1, b, z) = (Γ b)⁻¹ + z 𝐌(1, b + 1, z)`, for all `b, z : ℂ`. -/
theorem regularizedHGFun_one_singleton_eq_inv_Gamma_add_mul (b z : ℂ) :
    regularizedHGFun {1} {b} z = (Gamma b)⁻¹ + z * regularizedHGFun {1} {b + 1} z := by
  have h := regularizedHGFun_add_one_singleton_sub 0 b z
  rw [zero_add, regularizedHGFun_of_zero_mem (Multiset.mem_singleton_self 0)] at h
  simp only [Multiset.map_singleton, Multiset.prod_singleton] at h
  linear_combination h

/-- Contiguous relation combining `𝐌(a, b, z)` and `𝐌(a, b + 1, z)`:
`𝐌(a, b, z) - b 𝐌(a, b + 1, z) = a z 𝐌(a + 1, b + 2, z)`, for all `a, b, z : ℂ`. -/
theorem regularizedHGFun_singleton_sub_mul (a b z : ℂ) :
    regularizedHGFun {a} {b} z - b * regularizedHGFun {a} {b + 1} z =
      a * z * regularizedHGFun {a + 1} {b + 2} z := by
  have hsub := (hasSum_regularizedHGFun (a := {a}) (b := {b}) (by simp) z).sub
    ((hasSum_regularizedHGFun (a := {a}) (b := {b + 1}) (by simp) z).mul_left b)
  have hshift := (hasSum_nat_add_iff' 1).mpr hsub
  have h0 : regularizedHGFunCoeff {a} {b} 0 * z ^ 0 -
      b * (regularizedHGFunCoeff {a} {b + 1} 0 * z ^ 0) = 0 := by
    have hΓ := one_div_Gamma_eq_self_mul_one_div_Gamma_add_one b
    simp only [regularizedHGFunCoeff_singleton_zero, pow_zero, mul_one]
    linear_combination hΓ
  rw [Finset.range_one, Finset.sum_singleton, h0, sub_zero] at hshift
  refine hshift.unique (((hasSum_regularizedHGFun (a := {a + 1}) (b := {b + 2})
    (by simp) z).mul_left (a * z)).congr_fun fun n => ?_)
  rw [regularizedHGFunCoeff_singleton, regularizedHGFunCoeff_singleton,
    regularizedHGFunCoeff_singleton, ascPochhammer_succ_left, eval_mul, eval_X, eval_comp,
    eval_add, eval_X, eval_one, Nat.factorial_succ, pow_succ']
  have hΓ := one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (b + ((n + 1 : ℕ) : ℂ))
  have hb1 : b + 1 + (n + 1 : ℕ) = b + ((n + 1 : ℕ) : ℂ) + 1 := by push_cast; ring
  have hb2 : b + 2 + (n : ℂ) = b + ((n + 1 : ℕ) : ℂ) + 1 := by push_cast; ring
  have hn : (n : ℂ) + 1 ≠ 0 := mod_cast n.succ_ne_zero
  rw [hb1, hb2]
  push_cast
  simp only [div_eq_mul_inv, mul_inv]
  push_cast at hΓ
  linear_combination (a * (ascPochhammer ℂ n).eval (a + 1) * ((n : ℂ) + 1)⁻¹ * (n ! : ℂ)⁻¹ *
      z * z ^ n) * hΓ +
    a * (ascPochhammer ℂ n).eval (a + 1) * (n ! : ℂ)⁻¹ * (Gamma (b + (n + 1) + 1))⁻¹ *
      z * z ^ n * mul_inv_cancel₀ hn

/-- Contiguous relation combining `𝐌(a, b, z)` and `𝐌(a + 1, b + 1, z)`:
`𝐌(a, b, z) - b 𝐌(a + 1, b + 1, z) = (a - b) z 𝐌(a + 1, b + 2, z)`, for all `a, b, z : ℂ`. -/
theorem regularizedHGFun_singleton_sub_mul_add_one_left (a b z : ℂ) :
    regularizedHGFun {a} {b} z - b * regularizedHGFun {a + 1} {b + 1} z =
      (a - b) * z * regularizedHGFun {a + 1} {b + 2} z := by
  have h1 := regularizedHGFun_add_one_singleton_sub a (b + 1) z
  have h2 := regularizedHGFun_singleton_sub_mul a b z
  have hb : b + 1 + 1 = b + 2 := by ring
  rw [hb] at h1
  linear_combination h2 - b * h1

/-- Three-term parameter relation of `𝐌` with no `z` factor (DLMF 13.3.3):
`𝐌(a, b, z) = (b - a) 𝐌(a, b + 1, z) + a 𝐌(a + 1, b + 1, z)`, for all `a, b, z : ℂ`. -/
theorem regularizedHGFun_singleton_eq_sub_mul_add_mul (a b z : ℂ) :
    regularizedHGFun {a} {b} z =
      (b - a) * regularizedHGFun {a} {b + 1} z + a * regularizedHGFun {a + 1} {b + 1} z := by
  have h1 := regularizedHGFun_add_one_singleton_sub a (b + 1) z
  have h2 := regularizedHGFun_singleton_sub_mul a b z
  have hb : b + 1 + 1 = b + 2 := by ring
  rw [hb] at h1
  linear_combination h2 - a * h1

end Complex
