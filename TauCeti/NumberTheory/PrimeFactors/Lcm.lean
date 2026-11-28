/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.PrimeFactors.Bounds

/-!
# Prime support of least common multiples with powers

The prime support of `lcm (p^(n+1)) f` is contained in that of `p*f`, so increasing the
power does not increase the bound on the sum of the logarithms of the distinct primes.
-/

public section

namespace Nat

/-- The sum of the logarithms of the prime divisors of `lcm (p^(n+1)) f` is at most
`log (p*f)`. The base `p` need not itself be prime. -/
theorem sum_log_primeFactors_lcm_pow_succ_le (p n f : ℕ) :
    (∑ ℓ ∈ ((p ^ (n + 1)).lcm f).primeFactors, Real.log ℓ) ≤ Real.log ((p * f : ℕ) : ℝ) := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  have hsupp := primeFactors_mono (lcm_dvd_mul (p ^ (n + 1)) f) (mul_ne_zero (pow_ne_zero _ hp) hf)
  rw [primeFactors_mul (pow_ne_zero _ hp) hf, primeFactors_pow_succ, ← primeFactors_mul hp hf]
    at hsupp
  exact (Finset.sum_le_sum_of_subset_of_nonneg hsupp
    (fun ℓ _ _ ↦ Real.log_natCast_nonneg ℓ)).trans (sum_primeFactors_log_le (p * f))

end Nat
