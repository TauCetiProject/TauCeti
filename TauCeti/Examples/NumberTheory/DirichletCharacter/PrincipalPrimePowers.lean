/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.NumberTheory.DirichletCharacter.LFunction.LogDeriv.Principal
import TauCeti.NumberTheory.LSeries.RiemannZeta.LogDeriv.Basic
import TauCeti.NumberTheory.LSeries.RiemannZeta.LogDeriv.NearOne
import TauCeti.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Tactic.NormNum

/-!
# Principal-character geometric remainder checks

At level one and argument two the higher-prime-power remainder is strictly positive.
At level six the removed primes give a strictly negative, exactly evaluated correction.
The pole regularization also rejects adding the pole with the wrong sign.
-/

open Complex DirichletCharacter ArithmeticFunction Filter Topology

namespace TauCeti

/-- The endpoint majorant has an exact geometric prime expansion. -/
example : HasSum (fun p : Nat.Primes ↦ Real.log p / ((p : ℝ) * ((p : ℝ) - 1)))
    (∑' n : ℕ, (if n.Prime then 0 else vonMangoldt n) / n) := by
  simpa only [Real.rpow_one] using
    vonMangoldt.hasSum_prime_log_div_rpow_mul_sub_one (σ := 1) (by norm_num)

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
  have h := Nat.neg_re_logDeriv_LFunctionTrivChar_remainder_sub_eq 6 (σ := 2) (by norm_num)
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
    fun N _ σ hσ ↦ Nat.abs_neg_re_logDeriv_LFunctionTrivChar_remainder_sub_le N hσ⟩
  have hg := vonMangoldt.hasSum_prime_log_div_rpow_mul_sub_one (σ := 1) (by norm_num)
  simp only [Real.rpow_one] at hg
  rw [hg.tsum_eq]
  exact vonMangoldt.tsum_nonprime_div_le

/-- Deleting a negative prime weight reverses the sign of the finite correction. -/
example :
    (∑' p : Nat.Primes, ((1 : DirichletCharacter ℂ 2) p).re *
      (if (p : ℕ) = 2 then (-1 : ℝ) else 0)) -
      (∑' p : Nat.Primes, if (p : ℕ) = 2 then (-1 : ℝ) else 0) = 1 := by
  have hw : Summable fun n : ℕ ↦ if n = 2 then (-1 : ℝ) else 0 := by
    apply summable_of_ne_finset_zero (s := {2})
    exact fun n hn ↦ ite_eq_right (by simpa only [Finset.mem_singleton] using hn)
  have h := Nat.tsum_prime_re_one_mul_sub_tsum_prime_eq_neg_sum_primeFactors 2
    (fun n ↦ if n = 2 then (-1 : ℝ) else 0) (hw.subtype Nat.Prime)
  simpa [Nat.prime_two.primeFactors] using h

/-- Adding the pole with the wrong sign diverges to positive infinity at one. -/
example : Tendsto (fun η : ℝ ↦ -(logDeriv riemannZeta (1 + (η : ℂ))).re + η⁻¹)
    (𝓝[>] 0) atTop := by
  obtain ⟨C, hC⟩ := exists_norm_neg_logDeriv_riemannZeta_one_add_sub_inv_le
  have hi : Tendsto (fun η : ℝ ↦ 2 * η⁻¹ - C) (𝓝[>] 0) atTop := by
    simpa only [sub_eq_add_neg] using tendsto_atTop_add_const_right _ (-C)
      (tendsto_inv_nhdsGT_zero.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
  refine tendsto_atTop_mono' _ ?_ hi
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds]
    with η hη hη1
  have hb := hC η hη hη1.le
  have hr : |-(logDeriv riemannZeta (1 + (η : ℂ))).re - η⁻¹| ≤ C := by
    simpa only [Complex.sub_re, Complex.neg_re, ← Complex.ofReal_inv, Complex.ofReal_re] using
      (abs_re_le_norm _).trans hb
  linarith [(abs_le.mp hr).1]

end TauCeti
