/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Squarefree

/-!
# Divisor sums of squarefree natural numbers over subsets of prime factors

Every positive divisor of a squarefree natural number `n` is uniquely the product `∏ p ∈ A, p` of a
subset `A ⊆ n.primeFactors`, reindexing sums over `n.divisors` as sums over
`n.primeFactors.powerset`.

## Main results

* `Nat.sum_divisors_eq_sum_powerset_primeFactors`: for `Squarefree n`,
  `∑ d ∈ n.divisors, g d = ∑ A ∈ n.primeFactors.powerset, g (∏ p ∈ A, p)`.
-/

public section

namespace Nat

/-- For a squarefree natural number `n`, summing over `n.divisors` is equivalent via
`A ↦ ∏ p ∈ A, p` to summing over subsets `A` of `n.primeFactors`. -/
theorem sum_divisors_eq_sum_powerset_primeFactors {M : Type*} [AddCommMonoid M] {n : ℕ}
    (hn : Squarefree n) (g : ℕ → M) :
    ∑ d ∈ n.divisors, g d = ∑ A ∈ n.primeFactors.powerset, g (∏ p ∈ A, p) := by
  rw [← divisors_filter_squarefree_of_squarefree hn, sum_divisors_filter_squarefree hn.ne_zero,
    factors_eq, List.toFinset_coe, toFinset_factors]
  simp only [Finset.prod_val, Function.id_def]

end Nat
