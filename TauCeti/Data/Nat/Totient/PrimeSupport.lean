/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Totient

/-!
# The totient under multiplication without new prime factors

If every prime factor of `t` already divides `q`, multiplying `q` by `t` scales its totient
by `t`. This follows from Euler's product formula `Nat.totient_eq_mul_prod_factors`, since
the factors in the product depend only on which primes divide the modulus.
-/

public section

namespace Nat

/-- Multiplication by a factor supported on the prime factors of `q` scales the totient
by that factor. -/
theorem totient_mul_of_primeFactors_subset {q t : ℕ} (h : t.primeFactors ⊆ q.primeFactors) :
    (q * t).totient = q.totient * t := by
  obtain rfl | hq := eq_or_ne q 0
  · simp
  obtain rfl | ht := eq_or_ne t 0
  · simp
  have hs : (q * t).primeFactors = q.primeFactors :=
    (primeFactors_mul hq ht).trans (Finset.union_eq_left.mpr h)
  have he : ((q * t).totient : ℚ) = (q.totient : ℚ) * (t : ℚ) := by
    rw [totient_eq_mul_prod_factors (q * t), hs, totient_eq_mul_prod_factors q, Nat.cast_mul]
    ring
  exact_mod_cast he

end Nat
