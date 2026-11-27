/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.RegularizedHypergeometric.Basic
import TauCeti.Data.Nat.Factorial.Triplication
import TauCeti.RingTheory.Polynomial.Pochhammer

/-!
# `₀F₁` at thirds with argument `z³/9`

For the parameters `b = ⅓` and `b = 5/3`, the series `₀F₁(; b; z³/9) = ∑ (z³/9)^k/(k! Γ(b + k))`
is a power series in `z` whose coefficients are Pochhammer symbols at thirds over factorials of
`3k` and `3k + 2`:

`₀F₁(; ⅓; z³/9) = Γ(⅓)⁻¹ ∑ₖ 3^k (⅔)_k z^{3k}/(3k)!`,

`(z²/3) ₀F₁(; 5/3; z³/9) = Γ(⅔)⁻¹ ∑ₖ 3^k (4/3)_k z^{3k+2}/(3k + 2)!`.

They follow from `Γ(b + k) = (b)_k Γ(b)` and the triplication of factorials
`(3k)! = 27^k k! (⅓)_k (⅔)_k`, `(3k + 2)! = 2 · 27^k k! (4/3)_k (5/3)_k` of
`TauCeti.Data.Nat.Factorial.Triplication`. These are the two series in the derivatives of the
Airy functions (DLMF 9.4.2, 9.4.4).

## Main results

* `Complex.hasSum_regularizedHGFun_one_third_cube_div_nine`: the series of `₀F₁(; ⅓; z³/9)`.
* `Complex.hasSum_sq_div_three_mul_regularizedHGFun_five_thirds_cube_div_nine`: the series of
  `(z²/3) ₀F₁(; 5/3; z³/9)`.

## References

* NIST Digital Library of Mathematical Functions, §9.4, <https://dlmf.nist.gov/9.4>.

The computation is adapted from the lean-DLMF project (<https://github.com/bjbraams/lean-DLMF>),
file `DLMF/Airy/Basic/Maclaurin.lean`.
-/

public section

noncomputable section

open TauCeti (ascPochhammer_eval_ne_zero)
open scoped Nat

namespace Complex

/-- `₀F₁(; ⅓; z³/9) = Γ(⅓)⁻¹ ∑ₖ 3^k (⅔)_k z^{3k}/(3k)!`. -/
theorem hasSum_regularizedHGFun_one_third_cube_div_nine (z : ℂ) :
    HasSum (fun k : ℕ =>
      (Gamma (1 / 3))⁻¹ * (3 ^ k * (ascPochhammer ℂ k).eval (2 / 3) * z ^ (3 * k) / (3 * k)!))
      (regularizedHGFun 0 {(1 / 3 : ℂ)} (z ^ 3 / 9)) := by
  refine (hasSum_regularizedHGFun (a := 0) (b := {(1 / 3 : ℂ)}) (by simp)
    (z ^ 3 / 9)).congr_fun fun k => ?_
  simp only [regularizedHGFunCoeff_zero_singleton]
  rw [Gamma_add_natCast_eq_ascPochhammer_eval_mul (ne_neg_natCast_of_re_pos (by norm_num)) k,
    Nat.factorial_three_mul (K := ℂ)]
  have p1 := ascPochhammer_eval_ne_zero (ne_neg_natCast_of_re_pos (b := 1 / 3) (by norm_num)) k
  have p2 := ascPochhammer_eval_ne_zero (ne_neg_natCast_of_re_pos (b := 2 / 3) (by norm_num)) k
  have g1 : Gamma (1 / 3 : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by norm_num)
  have hk : (k ! : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  -- The triplication formula carries `27 ^ k` and the series `9 ^ k`; split `27 = 3 * 9` so
  -- that `field_simp` can match the powers.
  have h27 : (27 : ℂ) = 3 * 9 := by norm_num
  rw [pow_mul z 3 k, div_pow, h27, mul_pow]
  field_simp

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
  simp only [regularizedHGFunCoeff_zero_singleton]
  rw [Gamma_add_natCast_eq_ascPochhammer_eval_mul (ne_neg_natCast_of_re_pos (by norm_num)) k, h53,
    Nat.factorial_three_mul_add_two (K := ℂ)]
  have p4 := ascPochhammer_eval_ne_zero (ne_neg_natCast_of_re_pos (b := 4 / 3) (by norm_num)) k
  have p5 := ascPochhammer_eval_ne_zero (ne_neg_natCast_of_re_pos (b := 5 / 3) (by norm_num)) k
  have g2 : Gamma (2 / 3 : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by norm_num)
  have hk : (k ! : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  -- As above, split `27 = 3 * 9` so that `field_simp` can match the powers.
  have h27 : (27 : ℂ) = 3 * 9 := by norm_num
  rw [pow_add z (3 * k), pow_mul z 3 k, div_pow, h27, mul_pow]
  field_simp

end Complex
