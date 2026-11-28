/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Real.Sqrt

/-!
# Partial sums of inverse square roots

The partial sums of `1 / √(t + 1)` grow at most like `2 * √n`, because each term
`1 / √(t + 1)` is at most `2 * (√(t + 1) - √t)` and these differences telescope. Such sums
appear as the total of the step sizes `1 / √(t + 1)` in online gradient descent.

## Main results

* `Real.sum_range_inv_sqrt_succ_le`: `∑_{t < n} 1 / √(t + 1) ≤ 2 * √n`.
-/

public section

open Finset

namespace Real

/-- The partial sums of `1 / √(t + 1)` grow at most like `2 * √n`:
`∑_{t < n} 1 / √(t + 1) ≤ 2 * √n`. -/
theorem sum_range_inv_sqrt_succ_le (n : ℕ) :
    ∑ t ∈ range n, (√((t : ℝ) + 1))⁻¹ ≤ 2 * √(n : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    -- Each term `1 / √(n + 1)` is at most `2 * (√(n + 1) - √n)`.
    rw [sum_range_succ, Nat.cast_succ]
    have hb : 0 < √((n : ℝ) + 1) := Real.sqrt_pos.2 (by positivity)
    have ha2 := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) n)
    have hb2 := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ n + 1)
    have : (√((n : ℝ) + 1))⁻¹ ≤ 2 * √((n : ℝ) + 1) - 2 * √(n : ℝ) :=
      (inv_le_iff_one_le_mul₀ hb).2 (by nlinarith [sq_nonneg (√((n : ℝ) + 1) - √(n : ℝ))])
    linarith

end Real
