/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.LSeries.PrimesInAP

/-!
# The von Mangoldt function at the higher prime powers

The weights `Λ(n) / n` at the non-prime `n` are supported on the prime powers `p ^ k` with
`k ≥ 2`, and their sum `∑ₚ ∑_{k ≥ 2} log p / p ^ k` is finite. This absolute constant bounds the
higher-prime-power part of every twisted von Mangoldt series on `1 ≤ re s`.

The summability is the trivial residue class case of Mathlib's
`ArithmeticFunction.vonMangoldt.summable_residueClass_non_primes_div`.

Consequently the partial sums `∑_{n ≤ N} Λ(n) / n` and `∑_{p ≤ N} log p / p` differ by at most
this constant, uniformly in `N`.

## Main results

* `ArithmeticFunction.vonMangoldt.summable_nonprime_div`: `∑ₙ (if n is prime then 0 else Λ(n)) / n`
  converges.
* `TauCeti.sum_primesLE_log_div_le_sum_vonMangoldt_div`:
  `∑_{p ≤ N} log p / p ≤ ∑_{n ≤ N} Λ(n) / n`.
* `TauCeti.sum_vonMangoldt_div_le_sum_primesLE_log_div_add_tsum`:
  `∑_{n ≤ N} Λ(n) / n ≤ ∑_{p ≤ N} log p / p + ∑_{n not prime} Λ(n) / n`.
-/

public section

open ArithmeticFunction hiding log

namespace ArithmeticFunction.vonMangoldt

/-- The von Mangoldt weights `Λ n / n` at the non-prime `n`, which are supported on the prime
powers `p ^ k` with `k ≥ 2`, are summable. -/
theorem summable_nonprime_div :
    Summable fun n : ℕ ↦ (if n.Prime then 0 else vonMangoldt n) / n := by
  have h (n : ℕ) : residueClass (1 : ZMod 1) n = vonMangoldt n :=
    Set.indicator_of_mem (Subsingleton.elim (n : ZMod 1) 1) _
  simpa only [h] using summable_residueClass_non_primes_div (1 : ZMod 1)

end ArithmeticFunction.vonMangoldt

open Finset Real

namespace TauCeti

/-- The primes contribute at most `∑_{n ≤ N} Λ(n) / n`. -/
theorem sum_primesLE_log_div_le_sum_vonMangoldt_div (N : ℕ) :
    ∑ p ∈ Nat.primesLE N, log p / p ≤ ∑ n ∈ Ioc 0 N, Λ n / n := by
  calc ∑ p ∈ Nat.primesLE N, log p / p = ∑ p ∈ Nat.primesLE N, Λ p / p :=
        sum_congr rfl fun p hp ↦ by rw [vonMangoldt_apply_prime (Nat.prime_of_mem_primesLE hp)]
    _ ≤ ∑ n ∈ Ioc 0 N, Λ n / n := by
      refine sum_le_sum_of_subset_of_nonneg (Nat.primesLE_eq_filter_Ioc_zero N ▸ filter_subset _ _)
        fun n _ _ ↦ by positivity [vonMangoldt_nonneg (n := n)]

/-- The prime powers `p ^ k` with `k ≥ 2` contribute a bounded amount to `∑_{n ≤ N} Λ(n) / n`:
at most the convergent series `∑_{n not prime} Λ(n) / n`. -/
theorem sum_vonMangoldt_div_le_sum_primesLE_log_div_add_tsum (N : ℕ) :
    ∑ n ∈ Ioc 0 N, Λ n / n ≤
      ∑ p ∈ Nat.primesLE N, log p / p + ∑' n : ℕ, (if n.Prime then 0 else Λ n) / n := by
  have hprime : ∑ n ∈ Ioc 0 N, (if n.Prime then Λ n / n else 0) =
      ∑ p ∈ Nat.primesLE N, log p / p := by
    rw [← sum_filter, ← Nat.primesLE_eq_filter_Ioc_zero]
    exact sum_congr rfl fun p hp ↦ by rw [vonMangoldt_apply_prime (Nat.prime_of_mem_primesLE hp)]
  calc ∑ n ∈ Ioc 0 N, Λ n / n
      = ∑ n ∈ Ioc 0 N, ((if n.Prime then Λ n / n else 0) + (if n.Prime then 0 else Λ n) / n) :=
        sum_congr rfl fun n _ ↦ by split_ifs <;> simp
    _ = ∑ p ∈ Nat.primesLE N, log p / p +
          ∑ n ∈ Ioc 0 N, (if n.Prime then 0 else Λ n) / n := by
        rw [sum_add_distrib, hprime]
    _ ≤ _ := by
        gcongr
        exact vonMangoldt.summable_nonprime_div.sum_le_tsum _ fun n _ ↦ by
          positivity [vonMangoldt_nonneg (n := n)]

end TauCeti
