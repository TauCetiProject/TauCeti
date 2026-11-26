/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Tactic.Ring

/-!
# The odd-exponent part of a natural number away from a modulus

Fix a natural number `m`. Every natural number `n` is `s · t² · A`, where `s` is the product of
the primes `p ∤ m` dividing `n` to an odd power and every prime factor of `A` divides `m`. The
number `s` is, for `n ≠ 0`, the squarefree part of `n` with the primes dividing `m` removed.

## Main results

* `Nat.exists_eq_prod_mul_sq_mul`: `n = (∏ p ∈ n.primeFactors with ¬ p ∣ m ∧ Odd
  (n.factorization p), p) · t² · A` for some `t` and some `A` whose prime factors divide `m`.
-/

public section

namespace Nat

/-- Every `n` is `s t² A`, where `s` is the product of the primes `p ∤ m` dividing `n` to an odd
power, and every prime factor of `A` divides `m`. For `n = 0` the product is empty, and `t = 0`,
`A = 1` serve. -/
theorem exists_eq_prod_mul_sq_mul (m n : ℕ) :
    ∃ t A : ℕ, n = (∏ p ∈ n.primeFactors with ¬ p ∣ m ∧ Odd (n.factorization p), p) *
      t ^ 2 * A ∧ ∀ p, p.Prime → p ∣ A → p ∣ m := by
  rcases eq_or_ne n 0 with rfl | hn
  · exact ⟨0, 1, by simp, fun p hp h => (hp.ne_one (Nat.dvd_one.1 h)).elim⟩
  have key : ∀ p e : ℕ, p ^ e = (if Odd e then p else 1) * (p ^ (e / 2)) ^ 2 := by
    intro p e
    rcases Nat.even_or_odd' e with ⟨k, rfl | rfl⟩
    · have hk : 2 * k / 2 = k := by omega
      simp only [Nat.not_odd_iff_even.2 (even_two_mul k), ↓reduceIte, hk]
      ring
    · have hk : (2 * k + 1) / 2 = k := by omega
      simp only [odd_two_mul_add_one k, ↓reduceIte, hk]
      ring
  refine ⟨∏ p ∈ n.primeFactors with ¬ p ∣ m, p ^ (n.factorization p / 2),
    ∏ p ∈ n.primeFactors with p ∣ m, p ^ n.factorization p, ?_, fun p hp hpA => ?_⟩
  · conv_lhs => rw [Nat.prod_primeFactors_pow_factorization hn,
      ← Finset.prod_filter_not_mul_prod_filter _ (· ∣ m)]
    rw [Finset.prod_congr rfl fun p _ => key p _, Finset.prod_mul_distrib, Finset.prod_pow,
      ← Finset.prod_filter, Finset.filter_filter]
  · obtain ⟨r, hr, hpr⟩ := (_root_.Prime.dvd_finsetProd_iff hp.prime _).1 hpA
    exact (hp.dvd_of_dvd_pow hpr).trans (Finset.mem_filter.1 hr).2

end Nat
