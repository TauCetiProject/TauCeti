/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.NumberTheory.DirichletCharacter.LFunction.LogDeriv.Principal
import Mathlib.Tactic.NormNum

/-!
# Principal-character geometric remainder checks

At level one and argument two the higher-prime-power remainder is strictly positive.
At level six the removed primes give a strictly negative, exactly evaluated correction.
-/

open Complex DirichletCharacter ArithmeticFunction

namespace TauCeti

/-- The endpoint majorant has an exact geometric prime expansion. -/
example : HasSum (fun p : Nat.Primes ↦ Real.log p / ((p : ℝ) * ((p : ℝ) - 1)))
    (∑' n : ℕ, (if n.Prime then 0 else vonMangoldt n) / n) := by
  simpa only [Real.rpow_one] using
    vonMangoldt.hasSum_prime_log_div_rpow_mul_sub_one (σ := 1) le_rfl

/-- The principal level-one remainder at two is the positive geometric higher-power tail. -/
example :
    (-(logDeriv (LFunctionTrivChar 1) 2).re - ∑' p : Nat.Primes, Real.log p / (p : ℝ) ^ 2) =
      ∑' p : Nat.Primes, Real.log p / ((p : ℝ) ^ 2 * ((p : ℝ) ^ 2 - 1)) ∧
      0 < ∑' p : Nat.Primes, Real.log p / ((p : ℝ) ^ 2 * ((p : ℝ) ^ 2 - 1)) := by
  have hL : LFunctionTrivChar 1 = riemannZeta := by
    exact LFunction_modOne_eq
  constructor
  · rw [hL]
    simpa only [Real.rpow_two, Complex.ofReal_ofNat] using
      neg_re_logDeriv_riemannZeta_sub_tsum_prime_eq (σ := 2) (by norm_num)
  · have hs := vonMangoldt.hasSum_prime_log_div_rpow_mul_sub_one (σ := 2) (by norm_num)
    simp only [Real.rpow_two] at hs
    refine hs.summable.tsum_pos (fun p ↦ ?_) ⟨2, Nat.prime_two⟩ ?_
    · have hp : (1 : ℝ) < p := by exact_mod_cast p.prop.one_lt
      exact div_nonneg (Real.log_nonneg hp.le)
        (mul_nonneg (sq_nonneg _) (sub_nonneg.mpr (one_le_pow₀ hp.le)))
    · norm_num [Real.log_pos (by norm_num : (1 : ℝ) < 2)]

/-- The two ramified primes give a negative exact correction at level six. -/
example :
    (-(logDeriv (LFunctionTrivChar 6) 2).re -
        ∑' p : Nat.Primes, ((1 : DirichletCharacter ℂ 6) p).re * Real.log p / (p : ℝ) ^ 2) -
      (-(logDeriv riemannZeta 2).re - ∑' p : Nat.Primes, Real.log p / (p : ℝ) ^ 2) =
      -Real.log 2 / 12 - Real.log 3 / 72 ∧ -Real.log 2 / 12 - Real.log 3 / 72 < 0 := by
  have h := neg_re_logDeriv_principal_remainder_sub_eq 6 (σ := 2) (by norm_num)
  have hp : Nat.primeFactors 6 = {2, 3} := by
    have h6 : 6 = 2 * 3 := by norm_num
    rw [h6, Nat.primeFactors_mul (by norm_num) (by norm_num)]
    rw [Nat.prime_two.primeFactors, Nat.prime_three.primeFactors]
    rfl
  norm_num [hp, Real.rpow_two] at h
  constructor
  · linarith
  · have h2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    have h3 := Real.log_pos (by norm_num : (1 : ℝ) < 3)
    linarith

/-- The majorant is chosen before both the level and the real argument. -/
example : ∃ C : ℝ, C ≤ 2 * Real.log 4 ∧ ∀ (N : ℕ) [NeZero N] (σ : ℝ), 1 < σ →
    |(-(logDeriv (LFunctionTrivChar N) (σ : ℂ)).re -
        ∑' p : Nat.Primes, ((1 : DirichletCharacter ℂ N) p).re * Real.log p / (p : ℝ) ^ σ) -
      (-(logDeriv riemannZeta (σ : ℂ)).re -
        ∑' p : Nat.Primes, Real.log p / (p : ℝ) ^ σ)| ≤ C := by
  refine ⟨∑' p : Nat.Primes, Real.log p / ((p : ℝ) * ((p : ℝ) - 1)), ?_,
    fun N _ σ hσ ↦ abs_neg_re_logDeriv_principal_remainder_sub_le N hσ⟩
  have hg := vonMangoldt.hasSum_prime_log_div_rpow_mul_sub_one (σ := 1) le_rfl
  simp only [Real.rpow_one] at hg
  rw [hg.tsum_eq]
  exact vonMangoldt.tsum_nonprime_div_le

end TauCeti
