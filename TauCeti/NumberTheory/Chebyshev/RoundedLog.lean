/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.NumberTheory.Chebyshev

/-!
# Prime sums of rounded logarithms

Weighting `1 + ⌊log_p A⌋` by `log p` makes the unrounded term independent of `p`.
Chebyshev's bound absorbs the rounding cost, even when the prime cutoff is larger than `A`.
-/

public section

open Finset Real

namespace Chebyshev

/-- The logarithmic cost of rounding `log_p A` up to the next integer, summed over
any subset of the primes at most `X`. -/
theorem sum_log_mul_floor_logb_add_one_le {s : Finset ℕ} {A X : ℝ}
    (hA : 1 ≤ A) (hX : 0 ≤ X) (hs : s ⊆ Nat.primesLE ⌊X⌋₊) :
    ∑ p ∈ s, log p * ((⌊logb p A⌋₊ : ℝ) + 1) ≤ X * (log A + log 4) := by
  have hc : (s.card : ℝ) ≤ X := by
    have hsub : s ⊆ Icc 1 ⌊X⌋₊ := fun p hp ↦ mem_Icc.mpr
      ⟨(Nat.prime_of_mem_primesLE (hs hp)).one_le, Nat.le_of_mem_primesLE (hs hp)⟩
    have hcard : s.card ≤ ⌊X⌋₊ := by simpa using card_le_card hsub
    exact (Nat.cast_le.mpr hcard).trans (Nat.floor_le hX)
  have hθ : ∑ p ∈ s, log (p : ℝ) ≤ theta X := by
    rw [theta_eq_sum_primesLE]
    exact sum_le_sum_of_subset_of_nonneg hs fun p _ _ ↦ log_natCast_nonneg p
  calc
    _ ≤ ∑ p ∈ s, (log A + log (p : ℝ)) := by
      apply sum_le_sum
      intro p hp
      have hp' : 1 < (p : ℝ) := by exact_mod_cast Nat.one_lt_of_mem_primesLE (hs hp)
      have h : (⌊logb p A⌋₊ : ℝ) ≤ log A / log p := by
        rw [log_div_log]
        exact Nat.floor_le (logb_nonneg hp' hA)
      rw [mul_add, mul_one]
      have hprod := (le_div_iff₀ (log_pos hp')).mp h
      linarith only [hprod, mul_comm (log (p : ℝ)) (⌊logb p A⌋₊ : ℝ)]
    _ ≤ X * (log A + log 4) := by
      rw [sum_add_distrib, sum_const, nsmul_eq_mul, mul_add, mul_comm X (log 4)]
      exact add_le_add (mul_le_mul_of_nonneg_right hc (log_nonneg hA))
        (hθ.trans (theta_le_log4_mul_x hX))

/-- The corresponding bound for the second moment of the rounded prime logarithm. -/
theorem sum_log_mul_floor_logb_add_one_sq_le {s : Finset ℕ} {A X : ℝ}
    (hA : 1 ≤ A) (hX : 0 ≤ X) (hs : s ⊆ Nat.primesLE ⌊X⌋₊) :
    ∑ p ∈ s, log p * ((⌊logb p A⌋₊ : ℝ) + 1) ^ 2 ≤
      (logb 2 A + 1) * (X * (log A + log 4)) := by
  calc
    _ ≤ ∑ p ∈ s, (logb 2 A + 1) * (log p * ((⌊logb p A⌋₊ : ℝ) + 1)) := by
      apply sum_le_sum
      intro p hp
      have hp₂ : (2 : ℝ) ≤ p := by exact_mod_cast Nat.two_le_of_mem_primesLE (hs hp)
      have hp₁ : 1 < (p : ℝ) := by linarith
      have hlog : logb p A ≤ logb 2 A := by
        exact div_le_div_of_nonneg_left (log_nonneg hA) (log_pos one_lt_two)
          (log_le_log (by norm_num) hp₂)
      have hr : (⌊logb p A⌋₊ : ℝ) + 1 ≤ logb 2 A + 1 := by
        linarith [(Nat.floor_le (logb_nonneg hp₁ hA)).trans hlog]
      rw [pow_two, ← mul_assoc, mul_comm (logb 2 A + 1)]
      exact mul_le_mul_of_nonneg_left hr (by positivity)
    _ ≤ _ := by
      rw [← mul_sum]
      exact mul_le_mul_of_nonneg_left (sum_log_mul_floor_logb_add_one_le hA hX hs)
        (by linarith [logb_nonneg one_lt_two hA])

end Chebyshev
