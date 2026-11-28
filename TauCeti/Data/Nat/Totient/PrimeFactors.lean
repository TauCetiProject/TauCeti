/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Totient

/-!
# Totients under multiplication without new prime factors

Increasing the exponents of primes already dividing a positive modulus multiplies the totient
by the same factor as the modulus. In particular, no new Euler factors appear.
-/

public section

namespace Nat

/-- Multiplying `n` by `m` scales the totient by `m` if every prime factor of `m` occurs in `n`.
The identity also holds when either factor is zero. -/
theorem totient_mul_eq_mul_totient_of_primeFactors_subset {n m : ℕ}
    (h : m.primeFactors ⊆ n.primeFactors) : (n * m).totient = m * n.totient := by
  by_cases hn : n = 0
  · simp [hn]
  by_cases hm : m = 0
  · simp [hm]
  have hfac : (n * m).primeFactors = n.primeFactors :=
    (primeFactors_mul hn hm).trans (Finset.union_eq_left.mpr h)
  calc
    (n * m).totient = (m * (n / ∏ p ∈ n.primeFactors, p)) * ∏ p ∈ n.primeFactors, (p - 1) := by
      rw [totient_eq_div_primeFactors_mul, hfac, mul_comm n m, Nat.mul_div_assoc _
        (prod_primeFactors_dvd n)]
    _ = m * n.totient := by rw [mul_assoc, ← totient_eq_div_primeFactors_mul]

end Nat
