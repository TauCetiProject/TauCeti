/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Airy.Basic
public import TauCeti.Data.Nat.Factorial.Triplication

/-!
# Maclaurin series of the Airy functions

The Maclaurin series of `Ai` and `Bi` in the Pochhammer form of DLMF 9.4.1 and 9.4.3:

`Ai(z) = Ai(0) ∑ₖ 3^k (⅓)_k z^{3k}/(3k)! + Ai′(0) ∑ₖ 3^k (⅔)_k z^{3k+1}/(3k + 1)!`,

and the same for `Bi` with `Bi(0)`, `Bi′(0)` in place of `Ai(0)`, `Ai′(0)`. They follow from the
Gamma-denominator series of `TauCeti.Analysis.SpecialFunctions.Airy.Basic` and the triplication
of factorials `(3k)! = 27^k k! (⅓)_k (⅔)_k`, `(3k + 1)! = 27^k k! (⅔)_k (4/3)_k` of
`TauCeti.Data.Nat.Factorial.Triplication`.

## Main results

* `TauCeti.hasSum_airyAi`, `TauCeti.hasSum_airyBi`: DLMF 9.4.1 and 9.4.3.

## References

* NIST Digital Library of Mathematical Functions, §9.4, <https://dlmf.nist.gov/9.4>.

The proofs are adapted from the lean-DLMF project (<https://github.com/bjbraams/lean-DLMF>), file
`DLMF/Airy/Basic/Maclaurin.lean`.
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
    rw [show (4 / 3 : ℂ) = 1 / 3 + 1 by norm_num, Gamma_add_one _ (by norm_num)]
    ring
  have hoff : ∀ c : ℂ, 0 < c.re → ∀ m : ℕ, c ≠ -m := fun c hc m h => by
    have := congrArg re h
    simp only [neg_re, natCast_re] at this
    linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  rw [Gamma_add_natCast_eq_ascPochhammer_eval_mul (hoff _ (by norm_num)) k,
    Gamma_add_natCast_eq_ascPochhammer_eval_mul (hoff _ (by norm_num)) k, h43,
    factorial_three_mul (K := ℂ), factorial_three_mul_add_one (K := ℂ)]
  have p1 := ascPochhammer_eval_ne_zero (hoff (1 / 3) (by norm_num)) k
  have p2 := ascPochhammer_eval_ne_zero (hoff (2 / 3) (by norm_num)) k
  have p4 := ascPochhammer_eval_ne_zero (hoff (4 / 3) (by norm_num)) k
  have g1 : Gamma (1 / 3 : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by norm_num)
  have g2 : Gamma (2 / 3 : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by norm_num)
  have hk : (k ! : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  rw [pow_succ z (3 * k), pow_mul z 3 k, div_pow, show (27 : ℂ) = 3 * 9 by norm_num, mul_pow]
  field_simp

/-- **The Maclaurin series of `Ai`** (DLMF 9.4.1). -/
theorem hasSum_airyAi (z : ℂ) :
    HasSum (fun k : ℕ =>
      airyAi 0 * (3 ^ k * (ascPochhammer ℂ k).eval (1 / 3) * z ^ (3 * k) / (3 * k)!) +
        deriv airyAi 0 *
          (3 ^ k * (ascPochhammer ℂ k).eval (2 / 3) * z ^ (3 * k + 1) / (3 * k + 1)!))
      (airyAi z) := by
  refine (hasSum_airyAi_gamma z).congr_fun fun k => ?_
  rw [airyAi_zero, deriv_airyAi_zero, sub_eq_add_neg, ← neg_mul, ← neg_mul,
    airy_term_eq, show (-1 / 3 : ℂ) = -4 / 3 + 1 by norm_num,
    cpow_add _ _ (by norm_num : (3 : ℂ) ≠ 0), cpow_one]
  ring

/-- **The Maclaurin series of `Bi`** (DLMF 9.4.3). -/
theorem hasSum_airyBi (z : ℂ) :
    HasSum (fun k : ℕ =>
      airyBi 0 * (3 ^ k * (ascPochhammer ℂ k).eval (1 / 3) * z ^ (3 * k) / (3 * k)!) +
        deriv airyBi 0 *
          (3 ^ k * (ascPochhammer ℂ k).eval (2 / 3) * z ^ (3 * k + 1) / (3 * k + 1)!))
      (airyBi z) := by
  refine (hasSum_airyBi_gamma z).congr_fun fun k => ?_
  rw [airyBi_zero, deriv_airyBi_zero, airy_term_eq,
    show (1 / 6 : ℂ) = -5 / 6 + 1 by norm_num, cpow_add _ _ (by norm_num : (3 : ℂ) ≠ 0),
    cpow_one]
  ring

end TauCeti
