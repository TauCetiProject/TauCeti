/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Chebyshev

/-!
# Subset bounds from Chebyshev's `θ` estimate

Any finite set of primes `P ⊆ Nat.primesLE B` satisfies `∑ p ∈ P, log p ≤ log 4 * B` and
`∑ p ∈ P, log p / p ≤ log 4 * B`, obtained by comparing against `Chebyshev.theta B`.

## Main results

* `Chebyshev.sum_log_le_of_subset_primesLE`: upper bound on `∑ p ∈ P, Real.log p` for
  `P ⊆ Nat.primesLE B`.
* `Chebyshev.sum_log_div_le_of_subset_primesLE`: upper bound on `∑ p ∈ P, Real.log p / p` for
  `P ⊆ Nat.primesLE B`.
-/

public section

namespace Chebyshev

/-- The logarithmic sum over any subset `P ⊆ Nat.primesLE B` is at most `Real.log 4 * B`. -/
theorem sum_log_le_of_subset_primesLE {P : Finset ℕ} {B : ℕ} (hP : P ⊆ Nat.primesLE B) :
    ∑ p ∈ P, Real.log p ≤ Real.log 4 * B :=
  calc ∑ p ∈ P, Real.log p
      ≤ ∑ p ∈ Nat.primesLE B, Real.log p :=
        Finset.sum_le_sum_of_subset_of_nonneg hP fun p hp _ ↦
          Real.log_nonneg (by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_le)
    _ = Chebyshev.theta B := (Chebyshev.theta_eq_sum_primesLE_log B).symm
    _ ≤ Real.log 4 * B := Chebyshev.theta_le_log4_mul_x (by positivity)

/-- The reciprocal logarithmic sum `∑ p ∈ P, Real.log p / p` over any subset
`P ⊆ Nat.primesLE B` is at most `Real.log 4 * B`. -/
theorem sum_log_div_le_of_subset_primesLE {P : Finset ℕ} {B : ℕ} (hP : P ⊆ Nat.primesLE B) :
    ∑ p ∈ P, Real.log p / p ≤ Real.log 4 * B := by
  refine le_trans (Finset.sum_le_sum fun p hp ↦ ?_) (sum_log_le_of_subset_primesLE hP)
  have hp_pr := (Nat.mem_primesLE.mp (hP hp)).2
  exact div_le_self (Real.log_nonneg (by exact_mod_cast hp_pr.one_le))
    (by exact_mod_cast hp_pr.one_le)

end Chebyshev
