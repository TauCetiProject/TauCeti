/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Chebyshev

/-!
# Chebyshev bounds for finite sets of primes

The sum of `log p` over a set of primes up to `X` is bounded by `Chebyshev.theta X`.
Inserting one more prime costs at most its logarithm, whether or not it is already in the set.
This bounds the total error when rounding exponents costs at most `log p` at each prime.
-/

public section

namespace Finset

/-- The logarithmic sum over any finite set of primes at most `X` is bounded by `θ(X)`. -/
theorem sum_prime_log_le_theta (S : Finset Nat.Primes) {X : ℝ}
    (hS : ∀ p ∈ S, (p.val : ℝ) ≤ X) :
    (∑ p ∈ S, Real.log p.val) ≤ Chebyshev.theta X := by
  let e : Nat.Primes ↪ ℕ := ⟨Subtype.val, Nat.Primes.coe_nat_injective⟩
  calc
    _ = ∑ n ∈ S.map e, Real.log (n : ℝ) := (Finset.sum_map S e _).symm
    _ ≤ Chebyshev.theta X := by
      rw [Chebyshev.theta_eq_sum_primesLE]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun p _ _ ↦ Real.log_natCast_nonneg p)
      intro p hp
      obtain ⟨q, hq, rfl⟩ := Finset.mem_map.mp hp
      exact Nat.mem_primesLE.mpr ⟨Nat.le_floor (hS q hq), q.property⟩

/-- Adding a prime `N` to a finite set of primes at most `X` gives a logarithmic sum at most
`θ(X) + log N`, including when `N` is already in the set. -/
theorem sum_insert_prime_log_le_theta_add_log (S : Finset Nat.Primes) (N : Nat.Primes)
    {X : ℝ} (hS : ∀ p ∈ S, (p.val : ℝ) ≤ X) :
    (∑ p ∈ insert N S, Real.log p.val) ≤ Chebyshev.theta X + Real.log N.val := by
  have hsmall := S.sum_prime_log_le_theta hS
  by_cases hmem : N ∈ S
  · rw [Finset.insert_eq_of_mem hmem]
    exact hsmall.trans (le_add_of_nonneg_right (Real.log_natCast_nonneg N.val))
  · rw [Finset.sum_insert hmem, add_comm]
    exact add_le_add_left hsmall _

end Finset
