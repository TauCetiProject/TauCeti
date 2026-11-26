/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Stirling

/-!
# Exponential lower bounds for the factorial with leading factor `exp 1`

For every integer `1 ≤ n`, `exp 1 * (n / exp 1) ^ n ≤ n!` (equivalently,
`(n / exp 1) ^ n / n! ≤ (exp 1)⁻¹`), with equality at `n = 1`.

Unlike `Real.pow_div_factorial_le_exp` (`(n / exp 1) ^ n ≤ n!`), this retains an extra factor of
`exp 1`. At `n = 1` it improves on Stirling's lower bound `√(2 * π * n) * (n / exp 1) ^ n ≤ n!`
(`Stirling.le_factorial_stirling`) because `√(2 * π) < exp 1`, while for `2 ≤ n` it follows from
Stirling's bound since `exp 1 < √(4 * π) ≤ √(2 * π * n)`.

## Main results

* `Real.exp_one_mul_div_exp_one_pow_le_factorial`: `exp 1 * (n / exp 1) ^ n ≤ n!` for `1 ≤ n`.
* `Real.div_exp_one_pow_div_factorial_le`: `(n / exp 1) ^ n / n! ≤ (exp 1)⁻¹` for `1 ≤ n`.
-/

public section

namespace Real

/-- For `1 ≤ n`, `exp 1 * (n / exp 1) ^ n ≤ n!`, with equality at `n = 1`. -/
theorem exp_one_mul_div_exp_one_pow_le_factorial {n : ℕ} (hn : 1 ≤ n) :
    exp 1 * ((n : ℝ) / exp 1) ^ n ≤ n.factorial := by
  rcases hn.eq_or_lt with rfl | hn2
  · simp
  · have hn2' : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    have hexp_le : exp 1 ≤ √(2 * Real.pi * n) := by
      refine le_sqrt_of_sq_le ?_
      have hexp : exp 1 < 2.72 := exp_one_lt_d9.trans (by norm_num)
      have hpi : (2 : ℝ) ≤ Real.pi := two_le_pi
      nlinarith [exp_pos 1]
    exact (mul_le_mul_of_nonneg_right hexp_le
      (pow_nonneg (div_nonneg (Nat.cast_nonneg n) (exp_nonneg 1)) n)).trans
      (Stirling.le_factorial_stirling n)

/-- For `1 ≤ n`, `(n / exp 1) ^ n / n! ≤ (exp 1)⁻¹`. -/
theorem div_exp_one_pow_div_factorial_le {n : ℕ} (hn : 1 ≤ n) :
    ((n : ℝ) / exp 1) ^ n / n.factorial ≤ (exp 1)⁻¹ := by
  rw [div_le_iff₀ (Nat.cast_pos.mpr n.factorial_pos), le_inv_mul_iff₀ (exp_pos 1)]
  exact exp_one_mul_div_exp_one_pow_le_factorial hn

end Real
