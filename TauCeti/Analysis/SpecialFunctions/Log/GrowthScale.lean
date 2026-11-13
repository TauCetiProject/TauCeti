/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The growth scale `(1 + r) log (2 + r)`

Growth bounds for entire functions of order one, such as `1/Γ`, are naturally obtained in the
shape `A r log (1 + r) + B r` with `r = ‖s‖`. The single scale `(1 + r) log (2 + r)` absorbs both
terms for `r ≥ 0`, since `log (2 + r) ≥ log 2 ≥ 1/2`.

## Main results

* `Real.mul_mul_log_one_add_add_mul_le`: for `A, B, r ≥ 0`,
  `A r log (1 + r) + B r ≤ (A + 2 B) (1 + r) log (2 + r)`.
-/

public section

namespace Real

/-- The growth scale `(1 + r) log (2 + r)` absorbs both `r log (1 + r)` and `r`. -/
theorem mul_mul_log_one_add_add_mul_le {A B r : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hr : 0 ≤ r) :
    A * r * log (1 + r) + B * r ≤ (A + 2 * B) * (1 + r) * log (2 + r) := by
  have hlog : log (1 + r) ≤ log (2 + r) := log_le_log (by linarith) (by linarith)
  have hlog₁ : 0 ≤ log (1 + r) := log_nonneg (by linarith)
  -- `log 2 ≥ 1 - 2⁻¹`.
  have hlog₂ : 1 / 2 ≤ log (2 + r) := by
    have h := one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    have := log_le_log (by norm_num : (0 : ℝ) < 2) (by linarith : (2 : ℝ) ≤ 2 + r)
    norm_num at h
    linarith
  have h₁ : r * log (1 + r) ≤ (1 + r) * log (2 + r) :=
    mul_le_mul (by linarith) hlog hlog₁ (by linarith)
  -- `r ≤ 1 + r` and `1 ≤ 2 log (2 + r)`.
  have h₂ : r ≤ 2 * ((1 + r) * log (2 + r)) := by nlinarith
  calc
    A * r * log (1 + r) + B * r ≤
        A * ((1 + r) * log (2 + r)) + B * (2 * ((1 + r) * log (2 + r))) := by
      rw [mul_assoc]
      exact add_le_add (mul_le_mul_of_nonneg_left h₁ hA) (mul_le_mul_of_nonneg_left h₂ hB)
    _ = (A + 2 * B) * (1 + r) * log (2 + r) := by ring

end Real
