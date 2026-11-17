/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic.Positivity

/-!
# Exponential and logarithmic upper bounds for binomial coefficients

This file proves the elementary bound `C(p, k) ≤ (e * p / k) ^ k` for all natural numbers `p` and
`k`, together with its logarithmic form `log C(p, k) ≤ k * log (e * p / k)` for `k ≤ p`. Both
follow by combining Mathlib's `Nat.choose_le_pow_div` (`C(p, k) ≤ p ^ k / k!`) with the single
power-series term bound `k ^ k / k! ≤ exp k` (`Real.pow_div_factorial_le_exp`).

## Main results

* `Nat.choose_le_exp_mul_div_pow`: `(p.choose k : ℝ) ≤ (Real.exp 1 * p / k) ^ k` for all `p, k`.
* `Real.log_choose_le`: `Real.log (p.choose k) ≤ k * Real.log (Real.exp 1 * p / k)` for `k ≤ p`.
-/

public section

open Nat hiding log
open Real

namespace Nat

/-- The elementary upper bound `(p.choose k : ℝ) ≤ (e * p / k) ^ k`, valid for all natural
numbers `p` and `k` (including `k = 0`, where both sides equal `1`, and `p < k`, where the left
side is `0`). -/
theorem choose_le_exp_mul_div_pow (p k : ℕ) :
    (p.choose k : ℝ) ≤ (Real.exp 1 * p / k) ^ k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hfact : (k : ℝ) ^ k / (k ! : ℝ) ≤ Real.exp 1 ^ k := by
    rw [← Real.exp_nat_mul, mul_one]
    exact Real.pow_div_factorial_le_exp (k : ℝ) hk_pos.le k
  have hinv : (1 : ℝ) / (k ! : ℝ) ≤ (Real.exp 1 / k) ^ k := by
    rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
    have hmul := (div_le_iff₀ (by positivity : (0 : ℝ) < k !)).mp hfact
    linarith
  calc
    (p.choose k : ℝ) ≤ (p : ℝ) ^ k / (k ! : ℝ) := Nat.choose_le_pow_div k p
    _ = (p : ℝ) ^ k * ((1 : ℝ) / (k ! : ℝ)) := by ring
    _ ≤ (p : ℝ) ^ k * (Real.exp 1 / k) ^ k :=
      mul_le_mul_of_nonneg_left hinv (by positivity)
    _ = (Real.exp 1 * p / k) ^ k := by
      rw [← mul_pow]
      congr 1
      ring

end Nat

namespace Real

/-- The logarithmic upper bound `log C(p, k) ≤ k * log (e * p / k)` for `k ≤ p`. The hypothesis
`k ≤ p` ensures `0 < p.choose k` (and is needed: for `p = 1, k = 3`, `log 0 = 0` while
`3 * log (e / 3) < 0`). -/
theorem log_choose_le {p k : ℕ} (hk : k ≤ p) :
    log (p.choose k) ≤ k * log (exp 1 * p / k) := by
  have hchoose_pos : (0 : ℝ) < p.choose k := Nat.cast_pos.mpr (Nat.choose_pos hk)
  calc
    log (p.choose k) ≤ log ((exp 1 * p / k) ^ k) :=
      log_le_log hchoose_pos (Nat.choose_le_exp_mul_div_pow p k)
    _ = k * log (exp 1 * p / k) := log_pow _ k

end Real
