/-
Copyright (c) 2023 Arend Mellendijk, 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arend Mellendijk, The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Tactic.Positivity

/-!
# Absolute remainders of squared sieve weights

The error for arbitrary signed squared weights is bounded by the double sum of absolute
weights against the remainder at their least common multiple. A uniform remainder bound
therefore gives the square of the finite sum of absolute weights.

The estimates do not require a normalization or a cutoff for the weights.
The finite triangle-inequality argument is adapted from Arend Mellendijk's Selberg error
estimate in PrimeNumberTheoremAnd.
-/

public section

open Finset

namespace BoundingSieve

/-- The absolute remainder of squared weights is bounded by its finite double-sum majorant. -/
theorem errSum_lambdaSquared_le_sum_abs_mul (s : BoundingSieve) (w : ℕ → ℝ) :
    s.errSum (lambdaSquared w) ≤
      ∑ d ∈ s.prodPrimes.divisors, ∑ e ∈ s.prodPrimes.divisors,
        |w d| * |w e| * |s.rem (Nat.lcm d e)| := by
  classical
  calc
    _ ≤ ∑ n ∈ s.prodPrimes.divisors,
        (∑ d ∈ s.prodPrimes.divisors, ∑ e ∈ s.prodPrimes.divisors,
          if n = Nat.lcm d e then |w d| * |w e| else 0) * |s.rem n| := by
      apply sum_le_sum
      intro n hn
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      unfold lambdaSquared
      calc
        _ ≤ ∑ d ∈ n.divisors, ∑ e ∈ n.divisors,
            |if n = Nat.lcm d e then w d * w e else 0| := by
          exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun _ _ ↦ abs_sum_le_sum_abs _ _)
        _ = ∑ d ∈ n.divisors, ∑ e ∈ n.divisors,
            if n = Nat.lcm d e then |w d| * |w e| else 0 := by
          simp_rw [apply_ite abs, abs_mul, abs_zero]
        _ ≤ _ := by
          have hsub := Nat.divisors_subset_of_dvd s.prodPrimes_ne_zero (Nat.dvd_of_mem_divisors hn)
          trans ∑ d ∈ n.divisors, ∑ e ∈ s.prodPrimes.divisors,
            if n = Nat.lcm d e then |w d| * |w e| else 0
          · apply sum_le_sum
            intro d _
            exact sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ ↦ by positivity)
          · exact sum_le_sum_of_subset_of_nonneg hsub
              (fun _ _ _ ↦ sum_nonneg fun _ _ ↦ by positivity)
    _ = _ := by
      simp_rw [sum_mul, ite_mul, zero_mul]
      rw [sum_comm]
      apply sum_congr rfl
      intro d hd
      rw [sum_comm]
      apply sum_congr rfl
      intro e he
      exact sum_ite_eq_of_mem' s.prodPrimes.divisors (Nat.lcm d e) _
        (Nat.mem_divisors.mpr ⟨Nat.lcm_dvd (Nat.dvd_of_mem_divisors hd)
          (Nat.dvd_of_mem_divisors he), s.prodPrimes_ne_zero⟩)

/-- A uniform divisor remainder bound gives a square of the finite sum of absolute weights. -/
theorem errSum_lambdaSquared_le_const_mul_sum_abs_sq (s : BoundingSieve) (w : ℕ → ℝ)
    {C : ℝ} (hC : ∀ n ∈ s.prodPrimes.divisors, |s.rem n| ≤ C) :
    s.errSum (lambdaSquared w) ≤ C * (∑ d ∈ s.prodPrimes.divisors, |w d|) ^ 2 := by
  calc
    _ ≤ ∑ d ∈ s.prodPrimes.divisors, ∑ e ∈ s.prodPrimes.divisors,
        |w d| * |w e| * |s.rem (Nat.lcm d e)| := s.errSum_lambdaSquared_le_sum_abs_mul w
    _ ≤ ∑ d ∈ s.prodPrimes.divisors, ∑ e ∈ s.prodPrimes.divisors,
        |w d| * |w e| * C := by
      apply sum_le_sum
      intro d hd
      apply sum_le_sum
      intro e he
      exact mul_le_mul_of_nonneg_left
        (hC _ (Nat.mem_divisors.mpr ⟨Nat.lcm_dvd (Nat.dvd_of_mem_divisors hd)
          (Nat.dvd_of_mem_divisors he), s.prodPrimes_ne_zero⟩))
        (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = _ := by
      simp only [sq, mul_sum, sum_mul]
      apply sum_congr rfl
      intro d _
      apply sum_congr rfl
      intro e _
      ring

end BoundingSieve
