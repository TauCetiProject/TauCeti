/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Data.Nat.Factorial.Basic

/-!
# Elementary exponential lower bounds for the factorial

From `1 + 1 / k ≤ exp (1 / k)` raised to the `k`-th power one obtains
`(k + 1) ^ k ≤ k ^ k * exp 1`, hence by induction `exp 1 * (n / exp 1) ^ n ≤ n!` for every `1 ≤ n`
(with equality at `n = 1`).

At small `n`, the constant `exp 1` improves on the Stirling lower bound `√(2 π n) * (n / e) ^ n`
because `√(2 π) < e`.

## Main results

* `Real.exp_one_mul_div_exp_one_pow_le_factorial`: `exp 1 * (n / exp 1) ^ n ≤ n!` for `1 ≤ n`.
* `Real.div_exp_one_pow_div_factorial_le`: `(n / exp 1) ^ n / n! ≤ (exp 1)⁻¹` for `1 ≤ n`.
-/

public section

namespace Real

/-- For `1 ≤ n`, `exp 1 * (n / exp 1) ^ n ≤ n!`, with equality at `n = 1`. -/
theorem exp_one_mul_div_exp_one_pow_le_factorial {n : ℕ} (hn : 1 ≤ n) :
    exp 1 * ((n : ℝ) / exp 1) ^ n ≤ n.factorial := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  induction m with
  | zero =>
    simp
  | succ k ih =>
    have hk : (0 : ℝ) < (k + 1 : ℕ) := Nat.cast_pos.mpr (Nat.succ_pos k)
    have hstep : (((k + 2 : ℕ) : ℝ) / (k + 1 : ℕ)) ^ (k + 1) ≤ exp 1 := by
      have h1 : ((k + 2 : ℕ) : ℝ) / (k + 1 : ℕ) ≤ exp (1 / (k + 1 : ℕ)) := by
        have heq : ((k + 2 : ℕ) : ℝ) / (k + 1 : ℕ) = 1 / (k + 1 : ℕ) + 1 := by
          push_cast; field_simp; ring
        rw [heq]
        exact add_one_le_exp _
      calc (((k + 2 : ℕ) : ℝ) / (k + 1 : ℕ)) ^ (k + 1)
          ≤ exp (1 / (k + 1 : ℕ)) ^ (k + 1) := pow_le_pow_left₀ (by positivity) h1 (k + 1)
        _ = exp 1 := by
          rw [← exp_nat_mul]
          congr 1
          exact mul_one_div_cancel hk.ne'
    have hpow : ((k + 2 : ℕ) : ℝ) ^ (k + 1) ≤ ((k + 1 : ℕ) : ℝ) ^ (k + 1) * exp 1 := by
      rwa [div_pow, div_le_iff₀ (pow_pos hk (k + 1)), mul_comm] at hstep
    calc exp 1 * (((k + 2 : ℕ) : ℝ) / exp 1) ^ (k + 2)
        = ((k + 2 : ℕ) : ℝ) * (((k + 2 : ℕ) : ℝ) ^ (k + 1) / exp 1 ^ (k + 1)) := by
          rw [div_pow, pow_succ ((k + 2 : ℕ) : ℝ), pow_succ (exp 1)]
          field_simp [exp_ne_zero 1]
      _ ≤ ((k + 2 : ℕ) : ℝ) * ((((k + 1 : ℕ) : ℝ) ^ (k + 1) * exp 1) / exp 1 ^ (k + 1)) := by
          gcongr
      _ = ((k + 2 : ℕ) : ℝ) * (exp 1 * (((k + 1 : ℕ) : ℝ) / exp 1) ^ (k + 1)) := by
          rw [div_pow]
          ring
      _ ≤ ((k + 2 : ℕ) : ℝ) * (k + 1).factorial := by
          gcongr
          exact ih (Nat.succ_pos k)
      _ = ((k + 2).factorial : ℝ) := by
          rw [Nat.factorial_succ (k + 1), Nat.cast_mul]

/-- For `1 ≤ n`, `(n / exp 1) ^ n / n! ≤ (exp 1)⁻¹`. -/
theorem div_exp_one_pow_div_factorial_le {n : ℕ} (hn : 1 ≤ n) :
    ((n : ℝ) / exp 1) ^ n / n.factorial ≤ (exp 1)⁻¹ := by
  have hfac : (0 : ℝ) < n.factorial := Nat.cast_pos.mpr (Nat.factorial_pos n)
  rw [div_le_iff₀ hfac, le_inv_mul_iff₀ (exp_pos 1)]
  exact exp_one_mul_div_exp_one_pow_le_factorial hn

end Real
