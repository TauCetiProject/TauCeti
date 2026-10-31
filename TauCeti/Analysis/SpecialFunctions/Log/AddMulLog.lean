/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Solving `x ≤ a + b * log x`

If a positive real `x` satisfies `x ≤ a + b * log x` with `b ≥ 0`, then
`x ≤ 2 * a + 2 * b * (log (2 * b) - 1)`. This turns the implicit bound that effective methods
in Diophantine equations produce, where a quantity is bounded by a linear function of its own
logarithm, into an explicit bound. The proof bounds `log (x / (2 * b))` by `x / (2 * b) - 1`.

## Main results

* `Real.le_two_mul_add_of_le_add_mul_log`: `x ≤ a + b * log x` implies
  `x ≤ 2 * a + 2 * b * (log (2 * b) - 1)`.

## References

* [J.-H. Evertse, *Diophantine Approximation*, lecture notes, Leiden/Mastermath, 2019],
  Chapter 5, proof of Theorem 5.12, p. 95.
-/

public section

namespace Real

/-- If `0 < x`, `0 ≤ b` and `x ≤ a + b * log x`, then `x ≤ 2 * a + 2 * b * (log (2 * b) - 1)`.
For `b = 0` this reads `x ≤ 2 * a`, by the convention `log 0 = 0`. -/
theorem le_two_mul_add_of_le_add_mul_log {a b x : ℝ} (hb : 0 ≤ b) (hx : 0 < x)
    (h : x ≤ a + b * log x) : x ≤ 2 * a + 2 * b * (log (2 * b) - 1) := by
  rcases hb.eq_or_lt with rfl | hb
  · simp only [zero_mul, add_zero, mul_zero] at h ⊢
    linarith
  have h2b : 0 < 2 * b := by positivity
  -- `log x - log (2 * b) = log (x / (2 * b)) ≤ x / (2 * b) - 1`.
  have hlog := log_le_sub_one_of_pos (div_pos hx h2b)
  rw [log_div hx.ne' h2b.ne'] at hlog
  have hmul : b * (x / (2 * b)) = x / 2 := by
    field_simp
  nlinarith [mul_le_mul_of_nonneg_left hlog hb.le]

end Real
