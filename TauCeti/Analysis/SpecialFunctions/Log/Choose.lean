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

We prove `Nat.choose_le_exp_mul_div_pow` (`(p.choose k : ℝ) ≤ (e * p / k) ^ k` for all `p, k`)
and `Real.log_choose_le` (`log C(p, k) ≤ k * log (e * p / k)` for `k ≤ p`), combining
`Nat.choose_le_pow_div` with `Real.pow_div_factorial_le_exp`.
-/

public section

open Nat hiding log
open Real

namespace Nat

/-- `(p.choose k : ℝ) ≤ (e * p / k) ^ k` for all `p, k : ℕ` (including `k = 0` and `p < k`). -/
theorem choose_le_exp_mul_div_pow (p k : ℕ) :
    (p.choose k : ℝ) ≤ (Real.exp 1 * p / k) ^ k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  have hfact : (k : ℝ) ^ k / (k ! : ℝ) ≤ Real.exp 1 ^ k := by
    rw [← Real.exp_nat_mul, mul_one]
    exact Real.pow_div_factorial_le_exp (k : ℝ) (Nat.cast_nonneg k) k
  have : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  calc
    (p.choose k : ℝ) ≤ (p : ℝ) ^ k / (k ! : ℝ) := Nat.choose_le_pow_div k p
    _ = (p : ℝ) ^ k * ((k : ℝ) ^ k / (k ! : ℝ)) / (k : ℝ) ^ k := by field_simp
    _ ≤ (p : ℝ) ^ k * Real.exp 1 ^ k / (k : ℝ) ^ k := by gcongr
    _ = (Real.exp 1 * p / k) ^ k := by rw [← mul_pow, ← div_pow, mul_comm (p : ℝ)]

end Nat

namespace Real

/-- `log C(p, k) ≤ k * log (e * p / k)` for `k ≤ p` (needed so `0 < p.choose k`). -/
theorem log_choose_le {p k : ℕ} (hk : k ≤ p) :
    log (p.choose k) ≤ k * log (exp 1 * p / k) :=
  (log_le_log (Nat.cast_pos.mpr (Nat.choose_pos hk)) (Nat.choose_le_exp_mul_div_pow p k)).trans_eq
    (log_pow _ k)

end Real
