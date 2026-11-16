/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Two-sided bounds on `log ⌊x⌋!` with half-logarithmic error

For every real `x ≥ 1`,
`x log x - x - (1 / 2) log x + (1 / 2) log π ≤ log ⌊x⌋₊! ≤ x log x - x + (1 / 2) log x + 1`,
so `|log ⌊x⌋₊! - (x log x - x)| ≤ (1 / 2) log x + 1`. These are the factorial estimates entering
Chebyshev's elementary method and Mertens' first theorem, where `log ⌊x⌋₊!` is compared with
`∑_{n ≤ x} Λ(n) ⌊x / n⌋`. Mathlib's `Real.sum_log_le` and `Real.le_sum_log` bound the same sum
with a full `log x` error on each side; the bounds here halve it.

Both bounds come from Stirling's sequence `stirlingSeq n = n! / (√(2n) (n / e) ^ n)`. It
decreases from `stirlingSeq 1 = e / √2` (`Stirling.stirlingSeq'_antitone`), which gives the upper
bound `log n! ≤ n log n - n + (1 / 2) log n + 1` at every natural number `n`, and is at
least `√π` (`Stirling.le_log_factorial_stirling`), which gives the lower bound. Passing from
`n = ⌊x⌋₊` to the real `x` uses that `t log t - t` is nondecreasing on `[1, ∞)`, with increment
at most `log x` over `[n, x]`.

## Main results

* `Real.log_factorial_le`: `log n! ≤ n log n - n + (1 / 2) log n + 1` for every `n`.
* `Real.log_floor_factorial_le`: `log ⌊x⌋₊! ≤ x log x - x + (1 / 2) log x + 1` for `1 ≤ x`.
* `Real.le_log_floor_factorial`: `x log x - x - (1 / 2) log x + (1 / 2) log π ≤ log ⌊x⌋₊!`
  for `1 ≤ x`.
* `Real.abs_log_floor_factorial_sub_le`: `|log ⌊x⌋₊! - (x log x - x)| ≤ (1 / 2) log x + 1`
  for `1 ≤ x`.
-/

public section

open Nat hiding log
open Stirling

namespace Real

variable {x : ℝ}

/-- The upper Stirling bound `log n! ≤ n log n - n + (1 / 2) log n + 1` for every natural number
`n`, with equality at `n = 1`. -/
theorem log_factorial_le (n : ℕ) : log n ! ≤ n * log n - n + log n / 2 + 1 := by
  obtain _ | m := n
  · simp
  have hlog := log_le_log (stirlingSeq'_pos m) (stirlingSeq'_antitone (Nat.zero_le m))
  simp (disch := positivity) only [Function.comp_apply, log_stirlingSeq_formula,
    log_mul, log_div, log_exp, factorial_one, cast_one, log_one] at hlog
  linarith

/-- The upper bound `log ⌊x⌋₊! ≤ x log x - x + (1 / 2) log x + 1` for real `x ≥ 1`; it is an
equality at `x = 1`. -/
theorem log_floor_factorial_le (hx : 1 ≤ x) :
    log ⌊x⌋₊ ! ≤ x * log x - x + log x / 2 + 1 := by
  have hn : (1 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast one_le_floor_iff x |>.mpr hx
  set n : ℝ := (⌊x⌋₊ : ℝ)
  have hnx : n ≤ x := floor_le (by linarith)
  -- `t log t - t` increases from `n` to `x`, since `x (log x - log n) ≥ x (1 - n / x) = x - n`.
  have hlog : 1 - n / x ≤ log x - log n := by
    rw [← log_div (by linarith) (by linarith), ← inv_div]
    exact one_sub_inv_le_log_of_pos (div_pos (by linarith) (by linarith))
  have : x * (1 - n / x) = x - n := by field_simp
  nlinarith [log_factorial_le ⌊x⌋₊, log_nonneg hn, log_le_log (by linarith) hnx,
    mul_le_mul_of_nonneg_left hlog (by linarith : 0 ≤ x)]

/-- The lower bound `x log x - x - (1 / 2) log x + (1 / 2) log π ≤ log ⌊x⌋₊!` for real `x ≥ 1`. -/
theorem le_log_floor_factorial (hx : 1 ≤ x) :
    x * log x - x - log x / 2 + log π / 2 ≤ log ⌊x⌋₊ ! := by
  have hn₀ : ⌊x⌋₊ ≠ 0 := one_le_iff_ne_zero.mp <| one_le_floor_iff x |>.mpr hx
  have hn : (1 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast one_le_floor_iff x |>.mpr hx
  set n : ℝ := (⌊x⌋₊ : ℝ)
  have _ : n ≤ x := floor_le (by linarith)
  have hxn : x < n + 1 := lt_floor_add_one x
  -- The increment of `t log t - t` from `n` to `x` is at most `(x - n) log x ≤ log x`, since
  -- `n (log x - log n) ≤ n (x / n - 1) = x - n`.
  have hlog : log x - log n ≤ x / n - 1 := by
    rw [← log_div (by linarith) (by linarith)]
    exact log_le_sub_one_of_pos (div_pos (by linarith) (by linarith))
  have : n * (x / n - 1) = x - n := by field_simp
  -- `x < n + 1 ≤ 2 n`, so `log x ≤ log 2 + log n`.
  have hx2 : log x ≤ log 2 + log n := by
    rw [← log_mul two_ne_zero (by linarith)]
    exact log_le_log (by linarith) (by linarith)
  have hst := le_log_factorial_stirling hn₀
  rw [log_mul two_ne_zero pi_ne_zero] at hst
  nlinarith [log_nonneg hx, mul_le_mul_of_nonneg_left hlog (by linarith : 0 ≤ n)]

/-- The two-sided estimate `|log ⌊x⌋₊! - (x log x - x)| ≤ (1 / 2) log x + 1` for real `x ≥ 1`. -/
theorem abs_log_floor_factorial_sub_le (hx : 1 ≤ x) :
    |log ⌊x⌋₊ ! - (x * log x - x)| ≤ log x / 2 + 1 := by
  have := log_floor_factorial_le hx
  have := le_log_floor_factorial hx
  have := log_nonneg (by linarith [two_le_pi] : 1 ≤ π)
  rw [abs_le]
  constructor <;> linarith

end Real
