/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.RegularizedHypergeometric.Basic
import TauCeti.Data.Nat.Factorial.Triplication

/-!
# `₀F₁` at thirds with argument `z³/9`

For `b = ⅓, ⅔, 4/3, 5/3`, the series `₀F₁(; b; z³/9) = ∑ (z³/9)^k/(k! Γ(b + k))`, multiplied by
`1`, `1`, `z/3` and `z²/3` respectively, is a power series in `z` whose coefficients are Pochhammer
symbols at thirds over factorials of `3k`, `3k`, `3k + 1` and `3k + 2`:

`₀F₁(; ⅓; z³/9) = Γ(⅓)⁻¹ ∑ₖ 3^k (⅔)_k z^{3k}/(3k)!`,

`₀F₁(; ⅔; z³/9) = Γ(⅔)⁻¹ ∑ₖ 3^k (⅓)_k z^{3k}/(3k)!`,

`(z/3) ₀F₁(; 4/3; z³/9) = Γ(⅓)⁻¹ ∑ₖ 3^k (⅔)_k z^{3k+1}/(3k + 1)!`,

`(z²/3) ₀F₁(; 5/3; z³/9) = Γ(⅔)⁻¹ ∑ₖ 3^k (4/3)_k z^{3k+2}/(3k + 2)!`.

All four come from one coefficient conversion: given a factorization
`n! = C 27^k k! (b)_k (c)_k`, the `k`-th term of `₀F₁(; b; z³/9)` is
`C Γ(b)⁻¹ 3^k (c)_k z^{3k}/n!`, by `Γ(b)⁻¹ = (b)_k Γ(b + k)⁻¹`. The factorizations are the
triplications of factorials `(3k)! = 27^k k! (⅓)_k (⅔)_k`, `(3k + 1)! = 27^k k! (⅔)_k (4/3)_k`,
`(3k + 2)! = 2 · 27^k k! (4/3)_k (5/3)_k` of `TauCeti.Data.Nat.Factorial.Triplication`. These
are the series of the Airy functions and their derivatives (DLMF 9.4.1–9.4.4).

## Main results

* `Complex.regularizedHGFunCoeff_zero_singleton_mul_cube_div_nine`: the coefficient conversion.
* `Complex.hasSum_regularizedHGFun_one_third_cube_div_nine`: the series of `₀F₁(; ⅓; z³/9)`.
* `Complex.hasSum_regularizedHGFun_two_thirds_cube_div_nine`: the series of `₀F₁(; ⅔; z³/9)`.
* `Complex.hasSum_div_three_mul_regularizedHGFun_four_thirds_cube_div_nine`: the series of
  `(z/3) ₀F₁(; 4/3; z³/9)`.
* `Complex.hasSum_sq_div_three_mul_regularizedHGFun_five_thirds_cube_div_nine`: the series of
  `(z²/3) ₀F₁(; 5/3; z³/9)`.

## References

* NIST Digital Library of Mathematical Functions, §9.4, <https://dlmf.nist.gov/9.4>.

The computation is adapted from the lean-DLMF project (<https://github.com/bjbraams/lean-DLMF>),
file `DLMF/Airy/Basic/Maclaurin.lean`.
-/

public section

noncomputable section

open scoped Nat

namespace Complex

/-- If `n! = C 27^k k! (b)_k (c)_k`, then the `k`-th term of `₀F₁(; b; z³/9)` is
`C Γ(b)⁻¹ 3^k (c)_k z^{3k}/n!`. This holds for every `b`, including the poles of `Γ`, where both
sides are read with `Γ⁻¹`. -/
theorem regularizedHGFunCoeff_zero_singleton_mul_cube_div_nine {b c C : ℂ} {k n : ℕ}
    (hn : (n ! : ℂ) = C * 27 ^ k * k ! * (ascPochhammer ℂ k).eval b * (ascPochhammer ℂ k).eval c)
    (z : ℂ) :
    regularizedHGFunCoeff 0 {b} k * (z ^ 3 / 9) ^ k =
      C * (Gamma b)⁻¹ * (3 ^ k * (ascPochhammer ℂ k).eval c * z ^ (3 * k) / n !) := by
  have h0 : (n ! : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  rw [hn] at h0
  simp only [ne_eq, mul_eq_zero, not_or] at h0
  obtain ⟨⟨⟨⟨hC, -⟩, hk⟩, hb⟩, hc⟩ := h0
  rw [regularizedHGFunCoeff_zero_singleton,
    inv_Gamma_eq_ascPochhammer_eval_mul_inv_Gamma_add_natCast b k, hn, mul_inv]
  generalize (Gamma (b + k))⁻¹ = g
  -- The factorization carries `27 ^ k` and the series `9 ^ k`; split `27 = 3 * 9` so that
  -- `field_simp` can match the powers.
  have h27 : (27 : ℂ) = 3 * 9 := by norm_num
  rw [pow_mul z 3 k, div_pow, h27, mul_pow]
  field_simp

/-- `₀F₁(; ⅓; z³/9) = Γ(⅓)⁻¹ ∑ₖ 3^k (⅔)_k z^{3k}/(3k)!`. -/
theorem hasSum_regularizedHGFun_one_third_cube_div_nine (z : ℂ) :
    HasSum (fun k : ℕ =>
      (Gamma (1 / 3))⁻¹ * (3 ^ k * (ascPochhammer ℂ k).eval (2 / 3) * z ^ (3 * k) / (3 * k)!))
      (regularizedHGFun 0 {(1 / 3 : ℂ)} (z ^ 3 / 9)) := by
  refine (hasSum_regularizedHGFun (a := 0) (b := {(1 / 3 : ℂ)}) (by simp)
    (z ^ 3 / 9)).congr_fun fun k => ?_
  rw [regularizedHGFunCoeff_zero_singleton_mul_cube_div_nine (C := 1)
    (by rw [Nat.factorial_three_mul, one_mul]), one_mul]

/-- `₀F₁(; ⅔; z³/9) = Γ(⅔)⁻¹ ∑ₖ 3^k (⅓)_k z^{3k}/(3k)!`. -/
theorem hasSum_regularizedHGFun_two_thirds_cube_div_nine (z : ℂ) :
    HasSum (fun k : ℕ =>
      (Gamma (2 / 3))⁻¹ * (3 ^ k * (ascPochhammer ℂ k).eval (1 / 3) * z ^ (3 * k) / (3 * k)!))
      (regularizedHGFun 0 {(2 / 3 : ℂ)} (z ^ 3 / 9)) := by
  refine (hasSum_regularizedHGFun (a := 0) (b := {(2 / 3 : ℂ)}) (by simp)
    (z ^ 3 / 9)).congr_fun fun k => ?_
  rw [regularizedHGFunCoeff_zero_singleton_mul_cube_div_nine (C := 1)
    (by rw [Nat.factorial_three_mul]; ring), one_mul]

/-- `(z/3) ₀F₁(; 4/3; z³/9) = Γ(⅓)⁻¹ ∑ₖ 3^k (⅔)_k z^{3k+1}/(3k + 1)!`. -/
theorem hasSum_div_three_mul_regularizedHGFun_four_thirds_cube_div_nine (z : ℂ) :
    HasSum (fun k : ℕ =>
      (Gamma (1 / 3))⁻¹ *
        (3 ^ k * (ascPochhammer ℂ k).eval (2 / 3) * z ^ (3 * k + 1) / (3 * k + 1)!))
      (z / 3 * regularizedHGFun 0 {(4 / 3 : ℂ)} (z ^ 3 / 9)) := by
  refine ((hasSum_regularizedHGFun (a := 0) (b := {(4 / 3 : ℂ)}) (by simp)
    (z ^ 3 / 9)).mul_left (z / 3)).congr_fun fun k => ?_
  have h43 : Gamma (4 / 3 : ℂ) = Gamma (1 / 3) / 3 := by
    -- Write `4/3` as `1/3 + 1`, to apply the recurrence `Γ(s + 1) = s Γ(s)`.
    have h : (4 / 3 : ℂ) = 1 / 3 + 1 := by norm_num
    rw [h, Gamma_add_one _ (by norm_num)]
    ring
  rw [regularizedHGFunCoeff_zero_singleton_mul_cube_div_nine (C := 1)
    (by rw [Nat.factorial_three_mul_add_one]; ring), h43, pow_succ]
  ring

/-- `(z²/3) ₀F₁(; 5/3; z³/9) = Γ(⅔)⁻¹ ∑ₖ 3^k (4/3)_k z^{3k+2}/(3k + 2)!`. -/
theorem hasSum_sq_div_three_mul_regularizedHGFun_five_thirds_cube_div_nine (z : ℂ) :
    HasSum (fun k : ℕ =>
      (Gamma (2 / 3))⁻¹ *
        (3 ^ k * (ascPochhammer ℂ k).eval (4 / 3) * z ^ (3 * k + 2) / (3 * k + 2)!))
      (z ^ 2 / 3 * regularizedHGFun 0 {(5 / 3 : ℂ)} (z ^ 3 / 9)) := by
  refine ((hasSum_regularizedHGFun (a := 0) (b := {(5 / 3 : ℂ)}) (by simp)
    (z ^ 3 / 9)).mul_left (z ^ 2 / 3)).congr_fun fun k => ?_
  have h53 : Gamma (5 / 3 : ℂ) = 2 / 3 * Gamma (2 / 3) := by
    -- Write `5/3` as `2/3 + 1`, to apply the recurrence `Γ(s + 1) = s Γ(s)`.
    have h : (5 / 3 : ℂ) = 2 / 3 + 1 := by norm_num
    rw [h, Gamma_add_one _ (by norm_num)]
  rw [regularizedHGFunCoeff_zero_singleton_mul_cube_div_nine (C := 2)
    (by rw [Nat.factorial_three_mul_add_two]; ring), h53, mul_inv, pow_add]
  ring

end Complex
