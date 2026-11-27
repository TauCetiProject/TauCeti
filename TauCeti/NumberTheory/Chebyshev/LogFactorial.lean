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
* `Chebyshev.sum_vonMangoldt_div_le_two_mul_log`: `∑_{n ≤ x} Λ(n) / n ≤ 2 log x` for `1 ≤ x`.

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

/-- The sum of `Λ(n) / n` up to a real cutoff `x ≥ 1` is at most `2 log x`. -/
theorem sum_vonMangoldt_div_le_two_mul_log {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / n ≤ 2 * Real.log x := by
  have hx₀ : 0 < x := zero_lt_one.trans_le hx
  apply (mul_le_mul_iff_of_pos_left (half_pos hx₀)).mp
  calc
    (x / 2) * ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / n ≤ Real.log ⌊x⌋₊ ! := by
      rw [log_floor_factorial_eq_sum_vonMangoldt, mul_sum]
      refine sum_le_sum fun n hn ↦ ?_
      have hn₀ : (0 : ℝ) < n := by exact_mod_cast (mem_Ioc.mp hn).1
      have hnx : (n : ℝ) ≤ x := (Nat.le_floor_iff hx₀.le).mp (mem_Ioc.mp hn).2
      calc
        x / 2 * (Λ n / n) = Λ n * ((x / n) / 2) := by ring
        _ ≤ Λ n * (⌊x / n⌋₊ : ℝ) :=
          mul_le_mul_of_nonneg_left
            (Nat.div_two_lt_floor ((one_le_div hn₀).mpr hnx)).le vonMangoldt_nonneg
    _ ≤ (x / 2) * (2 * Real.log x) := by
      have hpow : (⌊x⌋₊ ! : ℝ) ≤ x ^ ⌊x⌋₊ := calc
        _ ≤ (⌊x⌋₊ : ℝ) ^ ⌊x⌋₊ := by exact_mod_cast Nat.factorial_le_pow ⌊x⌋₊
        _ ≤ _ := by gcongr; exact Nat.floor_le hx₀.le
      calc
        Real.log (⌊x⌋₊ ! : ℝ) ≤ Real.log (x ^ ⌊x⌋₊) := Real.log_le_log (by positivity) hpow
        _ = (⌊x⌋₊ : ℝ) * Real.log x := Real.log_pow _ _
        _ ≤ x * Real.log x :=
          mul_le_mul_of_nonneg_right (Nat.floor_le hx₀.le) (Real.log_nonneg hx)
        _ = _ := by ring

end Chebyshev
