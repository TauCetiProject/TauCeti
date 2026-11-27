/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Airy.Equation
public import TauCeti.Data.Nat.Factorial.Triplication
import TauCeti.Analysis.SpecialFunctions.RegularizedHypergeometric.CubeArgument
import TauCeti.RingTheory.Polynomial.Pochhammer

/-!
# Maclaurin series of the Airy functions

The Maclaurin series of `Ai`, `Bi` and their derivatives in the Pochhammer form of
DLMF 9.4.1–9.4.4:

`Ai(z) = Ai(0) ∑ₖ 3^k (⅓)_k z^{3k}/(3k)! + Ai′(0) ∑ₖ 3^k (⅔)_k z^{3k+1}/(3k + 1)!`,

`Ai′(z) = Ai′(0) ∑ₖ 3^k (⅔)_k z^{3k}/(3k)! + Ai(0) ∑ₖ 3^k (4/3)_k z^{3k+2}/(3k + 2)!`,

and the same for `Bi` and `Bi′` with `Bi(0)`, `Bi′(0)` in place of `Ai(0)`, `Ai′(0)`. They follow
from the Gamma-denominator series of `TauCeti.Analysis.SpecialFunctions.Airy.Basic`, the
derivative formulas of `TauCeti.Analysis.SpecialFunctions.Airy.Equation`, the triplication
of factorials `(3k)! = 27^k k! (⅓)_k (⅔)_k`, `(3k + 1)! = 27^k k! (⅔)_k (4/3)_k` of
`TauCeti.Data.Nat.Factorial.Triplication`, and, for the derivatives, the Pochhammer-form series
of `₀F₁(; ⅓; z³/9)` and `(z²/3) ₀F₁(; 5/3; z³/9)` of
`TauCeti.Analysis.SpecialFunctions.RegularizedHypergeometric.CubeArgument`.

## Main results

* `TauCeti.hasSum_airyAi`, `TauCeti.hasSum_airyBi`: DLMF 9.4.1 and 9.4.3.
* `TauCeti.hasSum_deriv_airyAi`, `TauCeti.hasSum_deriv_airyBi`: DLMF 9.4.2 and 9.4.4.

## References

* NIST Digital Library of Mathematical Functions, §9.4, <https://dlmf.nist.gov/9.4>.

The proofs are adapted from the lean-DLMF project (<https://github.com/bjbraams/lean-DLMF>), file
`DLMF/Airy/Basic/Maclaurin.lean` (`hasSum_airyAi_maclaurin`, `hasSum_airyAiDeriv_maclaurin`,
`hasSum_airyBi_maclaurin`, `hasSum_airyBiDeriv_maclaurin`).
-/

public section

noncomputable section

open Complex
open scoped Nat

namespace TauCeti

/-- The two Gamma-denominator terms in Pochhammer form, for any coefficients `A`, `B`. -/
private theorem airy_term_eq (A B z : ℂ) (k : ℕ) :
    A * ((z ^ 3 / 9) ^ k / (k ! * Gamma (2 / 3 + k))) + B * z *
      ((z ^ 3 / 9) ^ k / (k ! * Gamma (4 / 3 + k))) =
      A / Gamma (2 / 3) * (3 ^ k * (ascPochhammer ℂ k).eval (1 / 3) * z ^ (3 * k) / (3 * k)!) +
        3 * B / Gamma (1 / 3) *
          (3 ^ k * (ascPochhammer ℂ k).eval (2 / 3) * z ^ (3 * k + 1) / (3 * k + 1)!) := by
  have h43 : Gamma (4 / 3 : ℂ) = Gamma (1 / 3) / 3 := by
    -- Write `4/3` as `1/3 + 1`, to apply the recurrence `Γ(s + 1) = s Γ(s)`.
    have h : (4 / 3 : ℂ) = 1 / 3 + 1 := by norm_num
    rw [h, Gamma_add_one _ (by norm_num)]
    ring
  rw [Gamma_add_natCast_eq_ascPochhammer_eval_mul (ne_neg_natCast_of_re_pos (by norm_num)) k,
    Gamma_add_natCast_eq_ascPochhammer_eval_mul (ne_neg_natCast_of_re_pos (by norm_num)) k, h43,
    Nat.factorial_three_mul (K := ℂ), Nat.factorial_three_mul_add_one (K := ℂ)]
  have p1 := ascPochhammer_eval_ne_zero (ne_neg_natCast_of_re_pos (b := 1 / 3) (by norm_num)) k
  have p2 := ascPochhammer_eval_ne_zero (ne_neg_natCast_of_re_pos (b := 2 / 3) (by norm_num)) k
  have p4 := ascPochhammer_eval_ne_zero (ne_neg_natCast_of_re_pos (b := 4 / 3) (by norm_num)) k
  have g1 : Gamma (1 / 3 : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by norm_num)
  have g2 : Gamma (2 / 3 : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by norm_num)
  have hk : (k ! : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  -- The triplication formulas carry `27 ^ k` and the series `9 ^ k`; split `27 = 3 * 9` so
  -- that `field_simp` can match the powers.
  have h27 : (27 : ℂ) = 3 * 9 := by norm_num
  rw [pow_succ z (3 * k), pow_mul z 3 k, div_pow, h27, mul_pow]
  field_simp

/-- **The Maclaurin series of `Ai`** (DLMF 9.4.1). -/
theorem hasSum_airyAi (z : ℂ) :
    HasSum (fun k : ℕ =>
      airyAi 0 * (3 ^ k * (ascPochhammer ℂ k).eval (1 / 3) * z ^ (3 * k) / (3 * k)!) +
        deriv airyAi 0 *
          (3 ^ k * (ascPochhammer ℂ k).eval (2 / 3) * z ^ (3 * k + 1) / (3 * k + 1)!))
      (airyAi z) := by
  refine (hasSum_airyAi_gamma z).congr_fun fun k => ?_
  -- Write the exponent `−1/3` of `Ai′(0)` as `−4/3 + 1`, so that `cpow_add` relates it to the
  -- exponent `−4/3` of the series.
  have h : (-1 / 3 : ℂ) = -4 / 3 + 1 := by norm_num
  rw [airyAi_zero, deriv_airyAi_zero, sub_eq_add_neg, ← neg_mul, ← neg_mul,
    airy_term_eq, h, cpow_add _ _ (by norm_num : (3 : ℂ) ≠ 0), cpow_one]
  ring

/-- **The Maclaurin series of `Bi`** (DLMF 9.4.3). -/
theorem hasSum_airyBi (z : ℂ) :
    HasSum (fun k : ℕ =>
      airyBi 0 * (3 ^ k * (ascPochhammer ℂ k).eval (1 / 3) * z ^ (3 * k) / (3 * k)!) +
        deriv airyBi 0 *
          (3 ^ k * (ascPochhammer ℂ k).eval (2 / 3) * z ^ (3 * k + 1) / (3 * k + 1)!))
      (airyBi z) := by
  refine (hasSum_airyBi_gamma z).congr_fun fun k => ?_
  -- Write the exponent `1/6` of `Bi′(0)` as `−5/6 + 1`, so that `cpow_add` relates it to the
  -- exponent `−5/6` of the series.
  have h : (1 / 6 : ℂ) = -5 / 6 + 1 := by norm_num
  rw [airyBi_zero, deriv_airyBi_zero, airy_term_eq, h,
    cpow_add _ _ (by norm_num : (3 : ℂ) ≠ 0), cpow_one]
  ring

/-- **The Maclaurin series of `Ai′`** (DLMF 9.4.2). -/
theorem hasSum_deriv_airyAi (z : ℂ) :
    HasSum (fun k : ℕ =>
      deriv airyAi 0 * (3 ^ k * (ascPochhammer ℂ k).eval (2 / 3) * z ^ (3 * k) / (3 * k)!) +
        airyAi 0 *
          (3 ^ k * (ascPochhammer ℂ k).eval (4 / 3) * z ^ (3 * k + 2) / (3 * k + 2)!))
      (deriv airyAi z) := by
  rw [deriv_airyAi_zero, airyAi_zero, deriv_airyAi z, mul_assoc _ (z ^ 2 / 3)]
  refine (((hasSum_regularizedHGFun_one_third_cube_div_nine z).mul_left _).add
    ((hasSum_sq_div_three_mul_regularizedHGFun_five_thirds_cube_div_nine z).mul_left
      _)).congr_fun fun k => ?_
  ring

/-- **The Maclaurin series of `Bi′`** (DLMF 9.4.4). -/
theorem hasSum_deriv_airyBi (z : ℂ) :
    HasSum (fun k : ℕ =>
      deriv airyBi 0 * (3 ^ k * (ascPochhammer ℂ k).eval (2 / 3) * z ^ (3 * k) / (3 * k)!) +
        airyBi 0 *
          (3 ^ k * (ascPochhammer ℂ k).eval (4 / 3) * z ^ (3 * k + 2) / (3 * k + 2)!))
      (deriv airyBi z) := by
  rw [deriv_airyBi_zero, airyBi_zero, deriv_airyBi z, mul_assoc _ (z ^ 2 / 3)]
  refine (((hasSum_regularizedHGFun_one_third_cube_div_nine z).mul_left _).add
    ((hasSum_sq_div_three_mul_regularizedHGFun_five_thirds_cube_div_nine z).mul_left
      _)).congr_fun fun k => ?_
  ring

end TauCeti
