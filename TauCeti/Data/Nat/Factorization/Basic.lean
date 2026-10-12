/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Data.Nat.Factorization.Basic

/-!
# Removing prime-power factors

The least prime belongs to the prime factors of a natural number greater than one, and removing
its full multiplicity gives a smaller number. Removing the `p`-part erases `p` from the prime
factors. These facts support induction by successively removing prime-power blocks.
-/

public section

namespace Nat

/-- For `1 < n` the least prime factor of `n` is one of its primes. -/
theorem minFac_mem_primeFactors {n : ℕ} (hn : 1 < n) : n.minFac ∈ n.primeFactors :=
  Nat.mem_primeFactors.2 ⟨Nat.minFac_prime hn.ne', n.minFac_dvd, by omega⟩

/-- Peeling the block at the least prime factor makes `n` strictly smaller. -/
theorem ordCompl_minFac_lt {n : ℕ} (hn : 1 < n) : ordCompl[n.minFac] n < n :=
  Nat.div_lt_self (by omega) (Nat.one_lt_pow
    ((Nat.minFac_prime hn.ne').factorization_pos_of_dvd (by omega) n.minFac_dvd).ne'
    (Nat.minFac_prime hn.ne').one_lt)

/-- Removing the `p`-part of a natural number removes `p` from its prime factors. -/
@[simp]
theorem primeFactors_ordCompl (n p : ℕ) :
    (ordCompl[p] n).primeFactors = n.primeFactors.erase p := by
  rw [← support_factorization, factorization_ordCompl, Finsupp.support_erase,
    support_factorization]

end Nat
