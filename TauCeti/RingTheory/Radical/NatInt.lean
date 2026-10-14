/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Data.Nat.Squarefree

/-!
# The prime factorisation of the radical of a natural number

The radical `UniqueFactorizationMonoid.radical n` of a natural number `n` is the product of its
distinct prime factors, so each prime factor of `n` occurs in it exactly once. This file records
that factorisation, which turns divisibility statements involving a radical into inequalities
between exponents of primes.

## Main results

* `Nat.factorization_radical_apply`: the exponent of `p` in `radical n` is `1` when `p` is a prime
  factor of `n`, and `0` otherwise.
-/

public section

open UniqueFactorizationMonoid

namespace Nat

/-- **Each prime factor of `n` occurs exactly once in its radical**: the exponent of `p` in
`radical n` is `1` when `p` is a prime factor of `n`, and `0` otherwise. -/
theorem factorization_radical_apply (n p : ℕ) :
    (radical n).factorization p = if p ∈ n.primeFactors then 1 else 0 := by
  rw [← primeFactors_radical]
  split_ifs with h
  · exact factorization_eq_one_of_squarefree squarefree_radical (prime_of_mem_primeFactors h)
      (dvd_of_mem_primeFactors h)
  · exact Finsupp.notMem_support_iff.1 h

end Nat
