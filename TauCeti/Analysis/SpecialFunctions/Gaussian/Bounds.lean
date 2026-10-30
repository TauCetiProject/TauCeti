/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Complex.Exponential

/-!
# Polynomial weights against the real Gaussian

A polynomial weight `(1 + r)^m` is dominated by the Gaussian `exp (-a r²)`, `a > 0`: their
product is bounded on `r ≥ 0` by `m! exp (1 + 1/(4a))`. This follows from
`(1 + r)^m ≤ m! exp (1 + r)` and from completing the square in `1 + r - a r²`.

## Main statements

* `Real.one_add_pow_mul_exp_neg_mul_sq_le`: `(1 + r)^m exp (-a r²) ≤ m! exp (1 + 1/(4a))`.
-/

public section

open scoped Nat

/-- A polynomial in `r ≥ 0` times the Gaussian `exp (-a r²)`, `a > 0`, is bounded:
`(1 + r)^m exp (-a r²) ≤ m! exp (1 + 1/(4a))`. -/
theorem Real.one_add_pow_mul_exp_neg_mul_sq_le {a : ℝ} (ha : 0 < a) (m : ℕ) {r : ℝ}
    (hr : 0 ≤ r) : (1 + r) ^ m * Real.exp (-a * r ^ 2) ≤ m ! * Real.exp (1 + (4 * a)⁻¹) := by
  have hpow : (1 + r) ^ m ≤ m ! * Real.exp (1 + r) := by
    have := Real.pow_div_factorial_le_exp (1 + r) (by positivity) m
    rwa [div_le_iff₀ (by positivity), mul_comm] at this
  have hquad : 1 + r + -a * r ^ 2 ≤ 1 + (4 * a)⁻¹ := by
    have : 1 + (4 * a)⁻¹ - (1 + r + -a * r ^ 2) = a * (r - (2 * a)⁻¹) ^ 2 := by
      field_simp
      ring
    linarith [mul_nonneg ha.le (sq_nonneg (r - (2 * a)⁻¹))]
  calc (1 + r) ^ m * Real.exp (-a * r ^ 2) ≤ m ! * Real.exp (1 + r) * Real.exp (-a * r ^ 2) := by
        gcongr
    _ = m ! * Real.exp (1 + r + -a * r ^ 2) := by rw [Real.exp_add (1 + r)]; ring
    _ ≤ m ! * Real.exp (1 + (4 * a)⁻¹) := by gcongr
