/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arend Mellendijk, OpenAI Codex
-/
module

public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Algebra.Order.Antidiag.Nat

/-!
# Coefficient and support bounds for squared sieve weights

The lcm convolution of locally bounded real weights has coefficient at most `3^ω(n)`
at a squarefree index, with the zero index included by the canonical empty-divisor default.
Weights supported on `d² ≤ y` give squared weights supported on `d ≤ y`, for every real y.
The corresponding remainder estimate uses the existing `BoundingSieve` operations.

The finite-weight arguments are adapted from Arend Mellendijk's PNT+ files
`Mathlib/NumberTheory/Sieve/LambdaSquared.lean` and `Mathlib/NumberTheory/Sieve/Selberg.lean`,
revision 05076dfe4e396e6dbdea50fde395a5154341f59e of
https://github.com/TauCetiProject/PrimeNumberTheoremAnd.
-/

public noncomputable section

open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.omega

namespace BoundingSieve

/-- At a radical index, locally bounded weights have squared coefficient at most `3^ω(n)`.
Only the weights on the index's positive divisors matter; the zero index has coefficient zero. -/
theorem abs_lambdaSquared_le_three_pow_cardDistinctFactors (w : ℕ → ℝ) (n : ℕ)
    (hn : IsRadical n) (hw : ∀ d ∈ n.divisors, |w d| ≤ 1) :
    |lambdaSquared w n| ≤ (3 : ℝ) ^ ω n := by
  classical
  by_cases h0 : n = 0
  · simp [h0, lambdaSquared]
  have hs : Squarefree n := hn.squarefree h0
  calc
    |lambdaSquared w n| ≤
        ∑ a ∈ n.divisors, ∑ b ∈ n.divisors, if n = a.lcm b then (1 : ℝ) else 0 := by
      unfold lambdaSquared
      apply (abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro a ha
      apply (abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro b hb
      split_ifs with hab
      · rw [abs_mul]
        calc
          _ ≤ 1 * 1 := mul_le_mul (hw a ha) (hw b hb) (abs_nonneg _) zero_le_one
          _ = 1 := one_mul _
      · simp
    _ = (3 : ℝ) ^ ω n := by
      rw [← Finset.sum_product', ← Finset.sum_filter, Finset.sum_const, smul_one_eq_cast]
      norm_cast
      simpa only [eq_comm] using Nat.card_pair_lcm_eq hs

/-- Squared weights vanish above the squared-input cutoff, for every real cutoff.
The support condition is local to the positive divisors used by the coefficient. -/
theorem lambdaSquared_eq_zero_of_support (w : ℕ → ℝ) (y : ℝ) (n : ℕ)
    (hw : ∀ d ∈ n.divisors, ¬(d : ℝ) ^ 2 ≤ y → w d = 0) (hn : ¬(n : ℝ) ≤ y) :
    lambdaSquared w n = 0 := by
  classical
  unfold lambdaSquared
  refine Finset.sum_eq_zero fun a ha ↦ Finset.sum_eq_zero fun b hb ↦ ?_
  split_ifs with hab
  · have hNat : n ≤ (max a b) ^ 2 := calc
      n = a.lcm b := hab
      _ ≤ a * b := Nat.lcm_le_mul (Nat.pos_of_mem_divisors ha) (Nat.pos_of_mem_divisors hb)
      _ ≤ max a b * max a b := Nat.mul_le_mul (le_max_left _ _) (le_max_right _ _)
      _ = (max a b) ^ 2 := (pow_two _).symm
    have hl : (n : ℝ) ≤ ((max a b : ℕ) : ℝ) ^ 2 := by exact_mod_cast hNat
    have hmax : ¬(((max a b : ℕ) : ℝ) ^ 2 ≤ y) := fun h ↦ hn (hl.trans h)
    rcases le_total a b with h | h
    · rw [max_eq_right h] at hmax
      rw [hw b hb hmax, mul_zero]
    · rw [max_eq_left h] at hmax
      rw [hw a ha hmax, zero_mul]
  · rfl

/-- A strict input cutoff gives a strict squared-coefficient cutoff, including nonpositive
cutoffs through the empty-divisor and zero-weight defaults. -/
theorem lambdaSquared_eq_zero_of_support_lt (w : ℕ → ℝ) (z : ℝ) (n : ℕ)
    (hw : ∀ d ∈ n.divisors, z ≤ (d : ℝ) → w d = 0) (hn : z ^ 2 ≤ (n : ℝ)) :
    lambdaSquared w n = 0 := by
  classical
  unfold lambdaSquared
  refine Finset.sum_eq_zero fun a ha ↦ Finset.sum_eq_zero fun b hb ↦ ?_
  split_ifs with hab
  · have hNat : n ≤ (max a b) ^ 2 := calc
      n = a.lcm b := hab
      _ ≤ a * b := Nat.lcm_le_mul (Nat.pos_of_mem_divisors ha) (Nat.pos_of_mem_divisors hb)
      _ ≤ max a b * max a b := Nat.mul_le_mul (le_max_left _ _) (le_max_right _ _)
      _ = (max a b) ^ 2 := (pow_two _).symm
    have hl : (n : ℝ) ≤ ((max a b : ℕ) : ℝ) ^ 2 := by exact_mod_cast hNat
    have hmax : z ≤ (max a b : ℕ) := by
      by_contra h
      have hlt : ((max a b : ℕ) : ℝ) < z := lt_of_not_ge h
      have hz : 0 ≤ z := (Nat.cast_nonneg (max a b)).trans hlt.le
      exact (not_lt_of_ge (hn.trans hl)) ((sq_lt_sq₀ (Nat.cast_nonneg _) hz).mpr hlt)
    rcases le_total a b with h | h
    · rw [max_eq_right h] at hmax
      rw [hw b hb hmax, mul_zero]
    · rw [max_eq_left h] at hmax
      rw [hw a ha hmax, zero_mul]
  · rfl

/-- The coefficientwise squared-weight remainder bound with its exact cutoff and `3^ω` factor.
No weight normalization, remainder-size bound or sign assumption on the total mass is needed. -/
theorem errSum_lambdaSquared_le_sum_three_pow_cardDistinctFactors
    (s : BoundingSieve) (w : ℕ → ℝ) (y : ℝ)
    (hw : ∀ d ∈ s.prodPrimes.divisors, |w d| ≤ 1)
    (hsupp : ∀ d ∈ s.prodPrimes.divisors, ¬(d : ℝ) ^ 2 ≤ y → w d = 0) :
    s.errSum (lambdaSquared w) ≤
      ∑ d ∈ s.prodPrimes.divisors,
        if (d : ℝ) ≤ y then (3 : ℝ) ^ ω d * |s.rem d| else 0 := by
  classical
  unfold errSum
  apply Finset.sum_le_sum
  intro d hd
  have hsub := Nat.divisors_subset_of_dvd s.prodPrimes_ne_zero (Nat.dvd_of_mem_divisors hd)
  split_ifs with hdy
  · exact mul_le_mul_of_nonneg_right
      (abs_lambdaSquared_le_three_pow_cardDistinctFactors w d
        (s.squarefree_of_mem_divisors_prodPrimes hd).isRadical
        (fun e he ↦ hw e (hsub he))) (abs_nonneg _)
  · rw [lambdaSquared_eq_zero_of_support w y d (fun e he ↦ hsupp e (hsub he)) hdy,
      abs_zero, zero_mul]

/-- The strict-cutoff coefficientwise remainder estimate. No positivity assumption on the
cutoff is needed; positive-divisor weights must vanish when the cutoff is nonpositive. -/
theorem errSum_lambdaSquared_le_sum_three_pow_cardDistinctFactors_lt
    (s : BoundingSieve) (w : ℕ → ℝ) (z : ℝ)
    (hw : ∀ d ∈ s.prodPrimes.divisors, |w d| ≤ 1)
    (hsupp : ∀ d ∈ s.prodPrimes.divisors, z ≤ (d : ℝ) → w d = 0) :
    s.errSum (lambdaSquared w) ≤
      ∑ d ∈ s.prodPrimes.divisors,
        if (d : ℝ) < z ^ 2 then (3 : ℝ) ^ ω d * |s.rem d| else 0 := by
  classical
  unfold errSum
  apply Finset.sum_le_sum
  intro d hd
  have hsub := Nat.divisors_subset_of_dvd s.prodPrimes_ne_zero (Nat.dvd_of_mem_divisors hd)
  split_ifs with hdz
  · exact mul_le_mul_of_nonneg_right
      (abs_lambdaSquared_le_three_pow_cardDistinctFactors w d
        (s.squarefree_of_mem_divisors_prodPrimes hd).isRadical
        (fun e he ↦ hw e (hsub he))) (abs_nonneg _)
  · rw [lambdaSquared_eq_zero_of_support_lt w z d (fun e he ↦ hsupp e (hsub he))
      (le_of_not_gt hdz), abs_zero, zero_mul]

end BoundingSieve
