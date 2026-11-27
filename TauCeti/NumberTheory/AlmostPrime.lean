/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.AlmostPrime

/-!
# Rough numbers are almost prime

A positive integer all of whose prime factors are at least `z` is called `z`-rough. Such an `n`
is at least `z ^ Ω(n)`, where `Ω(n)` is the number of prime factors of `n` counted with
multiplicity, so a `z`-rough number below `z ^ (k + 1)` has at most `k` prime factors. This is
how a sieve that removes the multiples of the primes below `z` produces almost primes: what
survives in `[1, z ^ (k + 1))` is `Nat.IsAtMostAlmostPrime k`.

## Main results

* `Nat.pow_cardFactors_le`: `z ^ Ω(n) ≤ n` when `n ≠ 0` and every prime factor of `n` is at
  least `z`.
* `Nat.isAtMostAlmostPrime_of_lt_pow`: if moreover `n < z ^ (k + 1)`, then `n` has at most `k`
  prime factors counted with multiplicity.

## References

* K. S. Kedlaya, *Notes on analytic number theory*, Chapter 11 (Revisiting the sieve of
  Eratosthenes), §11.1.
-/

public section

open scoped ArithmeticFunction.Omega

namespace Nat

variable {z n k : ℕ}

/-- If every prime factor of `n ≠ 0` is at least `z`, then `z ^ Ω(n) ≤ n`: the number `n` is the
product of its `Ω(n)` prime factors, counted with multiplicity. -/
theorem pow_cardFactors_le (hn : n ≠ 0) (h : ∀ p ∈ n.primeFactors, z ≤ p) : z ^ Ω n ≤ n := by
  rw [ArithmeticFunction.cardFactors_apply]
  calc z ^ n.primeFactorsList.length ≤ n.primeFactorsList.prod :=
        List.pow_length_le_prod _ _ fun p hp ↦ h p (by simpa using hp)
    _ = n := prod_primeFactorsList hn

/-- A number `n ≠ 0` all of whose prime factors are at least `z` and with `n < z ^ (k + 1)` has
at most `k` prime factors, counted with multiplicity. The bound `n < z ^ (k + 1)` is strict:
`8 = 2 ^ 3` has three prime factors. -/
theorem isAtMostAlmostPrime_of_lt_pow (hn : n ≠ 0) (h : ∀ p ∈ n.primeFactors, z ≤ p)
    (hlt : n < z ^ (k + 1)) : IsAtMostAlmostPrime k n := by
  refine ⟨hn, ?_⟩
  by_contra hk
  have hz : 1 ≤ z := by
    rcases Nat.eq_zero_or_pos z with rfl | hz
    · simp at hlt
    · exact hz
  exact absurd ((Nat.pow_le_pow_right hz (not_le.1 hk)).trans (pow_cardFactors_le hn h))
    (not_le.2 hlt)

/-! ### Examples -/

example : IsAtMostAlmostPrime k 1 := isAtMostAlmostPrime_of_lt_pow (z := 2) one_ne_zero (by simp)
  (Nat.one_lt_two_pow (by omega))

example : ¬IsAtMostAlmostPrime 2 8 := by decide +kernel

end Nat
