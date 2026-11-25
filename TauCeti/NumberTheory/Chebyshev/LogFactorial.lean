/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Chebyshev
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.SpecialFunctions.Log.Sum

/-!
# Chebyshev's identity for `log ⌊x⌋!`

For every real `x`,
`log ⌊x⌋₊! = ∑_{1 ≤ n ≤ x} Λ(n) ⌊x / n⌋₊ = ∑_{1 ≤ m ≤ x} ψ(x / m)`,
with inclusive cutoffs; all three sides vanish for `x < 2`. Writing `log k = ∑_{d ∣ k} Λ(d)` for
each `k ≤ x` and counting the pairs `(d, m)` with `d m ≤ ⌊x⌋₊` in the two possible orders gives
the two right-hand sides. Together with the factorial bounds `Real.log_floor_factorial_le` and
`Real.le_log_floor_factorial`, the first form is the starting point of Chebyshev's elementary
estimates and of Mertens' first theorem `∑_{p ≤ x} log p / p = log x + O(1)`.

## Main results

* `Chebyshev.log_floor_factorial_eq_sum_vonMangoldt`: `log ⌊x⌋₊! = ∑_{n ≤ x} Λ(n) ⌊x / n⌋₊`.
* `Chebyshev.log_floor_div_factorial_eq_sum_vonMangoldt`: the same identity at `x / m`, summed
  over all `n ≤ x`: `log ⌊x / m⌋₊! = ∑_{n ≤ x} Λ(n) ⌊x / n / m⌋₊`.
* `Chebyshev.log_floor_factorial_eq_sum_psi`: `log ⌊x⌋₊! = ∑_{m ≤ x} ψ(x / m)`.

## References

* D. Koukoulopoulos, *The Distribution of Prime Numbers*, Theorem 3.4(a) and its proof.
-/

public section

open Finset ArithmeticFunction
open scoped Chebyshev Nat

namespace Chebyshev

/-- **Chebyshev's identity**: `log ⌊x⌋₊! = ∑_{1 ≤ n ≤ x} Λ(n) ⌊x / n⌋₊` for every real `x`. -/
theorem log_floor_factorial_eq_sum_vonMangoldt (x : ℝ) :
    Real.log ⌊x⌋₊ ! = ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n * ⌊x / n⌋₊ := by
  simp_rw [Nat.floor_div_natCast, ← Real.sum_log_eq_log_factorial, ← sum_Ioc_mul_zeta_eq_sum,
    vonMangoldt_mul_zeta, log_apply]

/-- **Chebyshev's identity** at `x / m`, with the sum extended to all `n ≤ x`:
`log ⌊x / m⌋₊! = ∑_{1 ≤ n ≤ x} Λ(n) ⌊x / n / m⌋₊` for every real `x` and natural `m`. -/
theorem log_floor_div_factorial_eq_sum_vonMangoldt (x : ℝ) (m : ℕ) :
    Real.log ⌊x / m⌋₊ ! = ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n * ⌊x / n / m⌋₊ := by
  rw [log_floor_factorial_eq_sum_vonMangoldt]
  have hsub : Ioc 0 ⌊x / m⌋₊ ⊆ Ioc 0 ⌊x⌋₊ :=
    Ioc_subset_Ioc_right (by rw [Nat.floor_div_natCast]; exact Nat.div_le_self _ _)
  rw [sum_subset hsub fun n hn hn' ↦ ?_]
  · exact sum_congr rfl fun n _ ↦ by rw [div_right_comm]
  · simp only [mem_Ioc, not_and, not_le] at hn hn'
    rw [Nat.floor_div_natCast, Nat.div_eq_of_lt (hn' hn.1)]
    simp

/-- **Chebyshev's identity** in terms of `ψ`: `log ⌊x⌋₊! = ∑_{1 ≤ m ≤ x} ψ(x / m)` for every
real `x`. -/
theorem log_floor_factorial_eq_sum_psi (x : ℝ) :
    Real.log ⌊x⌋₊ ! = ∑ m ∈ Ioc 0 ⌊x⌋₊, ψ (x / m) := by
  rw [← Real.sum_log_eq_log_factorial]
  simp_rw [← log_apply, ← vonMangoldt_mul_zeta, mul_comm (Λ : ArithmeticFunction ℝ),
    sum_Ioc_mul_eq_sum_sum, psi, Nat.floor_div_natCast]
  refine sum_congr rfl fun m hm ↦ ?_
  rw [natCoe_apply, zeta_apply_ne (mem_Ioc.mp hm).1.ne', Nat.cast_one, one_mul]

end Chebyshev
