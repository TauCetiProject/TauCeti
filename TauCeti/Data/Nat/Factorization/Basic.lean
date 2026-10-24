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
factors. These facts support induction by successively removing prime-power blocks. For a
divisor `n ∣ m`, the `p`-free parts are related by `m / n * ordCompl[p] n =
ordCompl[p] m * p ^ (v_p(m) - v_p(n))`, which is how a power map `x ↦ x ^ (m / n)` between groups
of roots of unity acts on their `p`-primary parts.
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

/-- For a divisor `n ∣ m`, the cofactor `m / n` times the `p`-free part of `n` is the `p`-free
part of `m` times the power of `p` by which the `p`-parts of `m` and `n` differ. -/
theorem div_mul_ordCompl_of_dvd {m n : ℕ} (p : ℕ) (h : n ∣ m) :
    m / n * ordCompl[p] n = ordCompl[p] m * p ^ (m.factorization p - n.factorization p) := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  have hn : n ≠ 0 := ne_zero_of_dvd_ne_zero hm h
  have hle : n.factorization p ≤ m.factorization p := (factorization_le_iff_dvd hn hm).2 h p
  refine Nat.eq_of_mul_eq_mul_right (ordProj_pos n p) ?_
  rw [mul_assoc, mul_comm (ordCompl[p] n), ordProj_mul_ordCompl_eq_self, Nat.div_mul_cancel h,
    mul_assoc, ← pow_add, Nat.sub_add_cancel hle, mul_comm, ordProj_mul_ordCompl_eq_self]

end Nat
