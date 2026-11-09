/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Bounds on `log ⌊x⌋!` with half-logarithm error terms

Mathlib's `Real.sum_log_le` and `Real.le_sum_log` compare `log ⌊x⌋! = ∑_{n ≤ x} log n` with
`x log x - x` up to an error of `log x + 1`, and `Stirling.le_log_factorial_stirling` gives the
lower bound `n log n - n + (1/2) log (2 π n) ≤ log n!` at natural numbers. This file supplies the
matching natural-number upper bound and halves the logarithmic error terms at every real `x ≥ 1`:

`x log x - x - (1/2) log x + (1/2) log π ≤ log ⌊x⌋! ≤ x log x - x + (1/2) log x + 1`,

so that `|log ⌊x⌋! - (x log x - x)| ≤ (1/2) log x + 1`. These are the factorial estimates used in
elementary proofs of Chebyshev's and Mertens's theorems.

The natural-number upper bound `n! ≤ e √n (n / e) ^ n` holds because the Stirling sequence
`n! / (√(2n) (n / e) ^ n)` is antitone from `n = 1` (`Stirling.stirlingSeq'_antitone`), where it
equals `e / √2`.

## Main results

* `Stirling.factorial_le_exp_one_mul_sqrt_mul_pow`: `n! ≤ e √n (n / e) ^ n` for `n ≠ 0`.
* `Stirling.log_factorial_le`: `log n! ≤ n log n - n + (1/2) log n + 1` for `n ≠ 0`.
* `Real.log_factorial_floor_le`, `Real.le_log_factorial_floor`: the two bounds at real `x ≥ 1`.
* `Real.abs_log_factorial_floor_sub_le`: `|log ⌊x⌋! - (x log x - x)| ≤ (1/2) log x + 1`.

## References

* D. Koukoulopoulos, *The Distribution of Prime Numbers*, Graduate Studies in Mathematics 203,
  AMS, 2019, proof of Theorem 3.4.
-/

public section

open Nat hiding log
open Real

namespace Stirling

/-- An upper bound for `n!` complementing `Stirling.le_factorial_stirling`: since the Stirling
sequence is antitone from `n = 1`, where it equals `e / √2`, we have `n! ≤ e √n (n / e) ^ n`. -/
theorem factorial_le_exp_one_mul_sqrt_mul_pow {n : ℕ} (hn : n ≠ 0) :
    (n ! : ℝ) ≤ exp 1 * √n * (n / exp 1) ^ n := by
  obtain ⟨m, rfl⟩ := exists_eq_succ_of_ne_zero hn
  have hle : stirlingSeq (m + 1) ≤ exp 1 / √2 := by
    simpa [stirlingSeq_one] using stirlingSeq'_antitone (zero_le m)
  have hpos : 0 < √(2 * (m + 1 : ℕ)) * ((m + 1 : ℕ) / exp 1) ^ (m + 1) := by positivity
  have h2 : √(2 * (m + 1 : ℕ)) = √2 * √(m + 1 : ℕ) := by
    rw [sqrt_mul zero_le_two]
  rw [stirlingSeq, div_le_div_iff₀ hpos (by positivity)] at hle
  calc ((m + 1)! : ℝ)
      ≤ exp 1 * (√(2 * (m + 1 : ℕ)) * ((m + 1 : ℕ) / exp 1) ^ (m + 1)) / √2 := by
        rw [le_div_iff₀ (by positivity)]
        exact hle
    _ = exp 1 * √(m + 1 : ℕ) * ((m + 1 : ℕ) / exp 1) ^ (m + 1) := by
        rw [h2]
        field_simp

/-- The logarithmic form of `Stirling.factorial_le_exp_one_mul_sqrt_mul_pow`:
`log n! ≤ n log n - n + (1/2) log n + 1`. It complements the lower bound
`Stirling.le_log_factorial_stirling`. -/
theorem log_factorial_le {n : ℕ} (hn : n ≠ 0) :
    log n ! ≤ n * log n - n + log n / 2 + 1 := by
  have hn' : (0 : ℝ) < n := by positivity
  calc log n ! ≤ log (exp 1 * √n * (n / exp 1) ^ n) :=
        log_le_log (by positivity) (factorial_le_exp_one_mul_sqrt_mul_pow hn)
    _ = n * log n - n + log n / 2 + 1 := by
        rw [log_mul (by positivity) (by positivity), log_mul (by positivity) (by positivity),
          log_exp, log_sqrt hn'.le, Real.log_pow, log_div hn'.ne' (exp_pos 1).ne', log_exp]
        ring

end Stirling

namespace Real

variable {x : ℝ}

/-- The upper bound `log ⌊x⌋! ≤ x log x - x + (1/2) log x + 1` for real `x ≥ 1`, sharpening
Mathlib's `Real.sum_log_le` from `log x` to `(1/2) log x`. -/
theorem log_factorial_floor_le (hx : 1 ≤ x) :
    log ⌊x⌋₊ ! ≤ x * log x - x + log x / 2 + 1 := by
  have hn1 : (1 : ℝ) ≤ ⌊x⌋₊ := mod_cast Nat.one_le_floor_iff x |>.mpr hx
  have hnx : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hlog : log ⌊x⌋₊ ≤ log x := log_le_log (by linarith) hnx
  -- `t log t - t` increases across `[⌊x⌋, x]`, its derivative `log t` being nonnegative there.
  have hgrow : 0 ≤ ∫ t in (⌊x⌋₊ : ℝ)..x, log t :=
    intervalIntegral.integral_nonneg hnx fun t ht ↦ log_nonneg (hn1.trans ht.1)
  rw [integral_log] at hgrow
  linarith [Stirling.log_factorial_le (Nat.floor_pos.mpr hx).ne']

/-- The lower bound `x log x - x - (1/2) log x + (1/2) log π ≤ log ⌊x⌋!` for real `x ≥ 1`,
sharpening Mathlib's `Real.le_sum_log` from `log x` to `(1/2) log x`. -/
theorem le_log_factorial_floor (hx : 1 ≤ x) :
    x * log x - x - log x / 2 + log π / 2 ≤ log ⌊x⌋₊ ! := by
  have hn1 : (1 : ℝ) ≤ ⌊x⌋₊ := mod_cast Nat.one_le_floor_iff x |>.mpr hx
  have hnx : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hxn : x < ⌊x⌋₊ + 1 := Nat.lt_floor_add_one x
  have hx0 : 0 < x := by linarith
  -- Since `x < 2 ⌊x⌋`, `log ⌊x⌋ ≥ log x - log 2`.
  have hlog : log x - log 2 ≤ log ⌊x⌋₊ := by
    rw [sub_le_iff_le_add, ← log_mul (by linarith) two_ne_zero]
    exact log_le_log hx0 (by linarith)
  -- `t log t - t` grows by at most `log x` across `[⌊x⌋, x]`, an interval of length at most `1`.
  have hgrow : ∫ t in (⌊x⌋₊ : ℝ)..x, log t ≤ ∫ _ in (⌊x⌋₊ : ℝ)..x, log x :=
    intervalIntegral.integral_mono_on hnx (by simp) (by simp) fun t ht ↦
      log_le_log (by linarith [ht.1]) ht.2
  rw [integral_log, intervalIntegral.integral_const, smul_eq_mul] at hgrow
  have hlen : (x - ⌊x⌋₊) * log x ≤ log x :=
    mul_le_of_le_one_left (log_nonneg hx) (by linarith)
  have h2pi : log (2 * π) = log 2 + log π := log_mul two_ne_zero pi_ne_zero
  linarith [Stirling.le_log_factorial_stirling (Nat.floor_pos.mpr hx).ne']

/-- `log ⌊x⌋! = x log x - x + O(log x)` with the explicit error `(1/2) log x + 1`, for real
`x ≥ 1`. -/
theorem abs_log_factorial_floor_sub_le (hx : 1 ≤ x) :
    |log ⌊x⌋₊ ! - (x * log x - x)| ≤ log x / 2 + 1 := by
  have hpi : 0 ≤ log π := log_nonneg (by linarith [two_le_pi])
  rw [abs_le]
  constructor <;> linarith [log_factorial_floor_le hx, le_log_factorial_floor hx]

end Real
