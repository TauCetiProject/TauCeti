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

`log ⌊x⌋! = ∑_{n ≤ x} Λ(n) ⌊x / n⌋ = ∑_{m ≤ x} ψ(x / m)`,

with inclusive cutoffs; all three sides vanish for `x < 2`. Both follow from
`log n = ∑_{d ∣ n} Λ(d)` (`ArithmeticFunction.vonMangoldt_sum`) by counting the pairs `(d, m)` with
`d m ≤ ⌊x⌋`: for fixed `d` there are `⌊x / d⌋` of them, and for fixed `m` the sum of `Λ(d)` over
`d ≤ x / m` is `ψ(x / m)`.

Combined with the size of `log ⌊x⌋!` (Mathlib's `Real.sum_log_le` and `Real.le_sum_log`), the first
identity is Chebyshev's route to `ψ(x) ≍ x` and to Mertens's first theorem
`∑_{n ≤ x} Λ(n) / n = log x + O(1)`.

## Main results

* `Chebyshev.log_factorial_floor_eq_sum_vonMangoldt_mul_floor`:
  `log ⌊x⌋! = ∑_{n ≤ x} Λ(n) ⌊x / n⌋`.
* `Chebyshev.log_factorial_floor_eq_sum_psi`: `log ⌊x⌋! = ∑_{m ≤ x} ψ(x / m)`.

## References

* D. Koukoulopoulos, *The Distribution of Prime Numbers*, Graduate Studies in Mathematics 203,
  AMS, 2019, proof of Theorem 3.4.
-/

public section

open Finset Real
open ArithmeticFunction hiding log
open scoped ArithmeticFunction.zeta Nat

namespace Chebyshev

/-- **Chebyshev's identity.** `log ⌊x⌋! = ∑_{n ≤ x} Λ(n) ⌊x / n⌋` for every real `x`. -/
theorem log_factorial_floor_eq_sum_vonMangoldt_mul_floor (x : ℝ) :
    log ⌊x⌋₊ ! = ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n * ⌊x / n⌋₊ := by
  rw [← sum_log_eq_log_factorial]
  have hlog : ∑ n ∈ Ioc 0 ⌊x⌋₊, log n = ∑ n ∈ Ioc 0 ⌊x⌋₊, (Λ * ζ) n := by
    simp [vonMangoldt_mul_zeta, log_apply]
  rw [hlog, sum_Ioc_mul_zeta_eq_sum]
  simp [Nat.floor_div_natCast]

/-- **Chebyshev's identity**, summed over the complementary divisor:
`log ⌊x⌋! = ∑_{m ≤ x} ψ(x / m)` for every real `x`. -/
theorem log_factorial_floor_eq_sum_psi (x : ℝ) :
    log ⌊x⌋₊ ! = ∑ m ∈ Ioc 0 ⌊x⌋₊, ψ (x / m) := by
  rw [← sum_log_eq_log_factorial]
  have hlog : ∑ n ∈ Ioc 0 ⌊x⌋₊, log n = ∑ n ∈ Ioc 0 ⌊x⌋₊, ((ζ : ArithmeticFunction ℝ) * Λ) n := by
    simp [zeta_mul_vonMangoldt, log_apply]
  rw [hlog, sum_Ioc_mul_eq_sum_sum]
  refine sum_congr rfl fun m hm ↦ ?_
  rw [natCoe_apply, zeta_apply_ne (mem_Ioc.mp hm).1.ne', Nat.cast_one, one_mul, psi,
    Nat.floor_div_natCast]

end Chebyshev
