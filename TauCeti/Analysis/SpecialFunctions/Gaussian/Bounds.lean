/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity

/-!
# Polynomial weights against a real Gaussian

A Gaussian `exp (-a r²)` with `0 < a` absorbs every polynomial weight: `(1 + r) ^ m exp (-a r²)`
is bounded for `0 ≤ r`. This is the scalar estimate behind Schwartz-type decay of Gaussians and
of the heat kernel. The proof combines `(1 + r) ^ m ≤ m! exp (1 + r)` with the completed square
`r - a r² ≤ 1 / (4a)`.

## Main statements

* `Real.one_add_pow_mul_exp_neg_mul_sq_le`: `(1 + r) ^ m exp (-a r²) ≤ m! exp (1 + 1 / (4a))`.
-/

public section

open scoped Nat

namespace Real

/-- A polynomial times a Gaussian is bounded: for `0 < a` and `0 ≤ r`,
`(1 + r) ^ m * exp (-a r²) ≤ m! exp (1 + 1 / (4a))`. -/
theorem one_add_pow_mul_exp_neg_mul_sq_le {a : ℝ} (ha : 0 < a) (m : ℕ) {r : ℝ}
    (hr : 0 ≤ r) : (1 + r) ^ m * Real.exp (-a * r ^ 2) ≤ m ! * Real.exp (1 + 1 / (4 * a)) := by
  -- `(1 + r) ^ m ≤ m! exp (1 + r)` and `r - a r² ≤ 1 / (4a)`.
  have hpow : (1 + r) ^ m ≤ m ! * Real.exp (1 + r) := by
    have := Real.pow_div_factorial_le_exp (1 + r) (by positivity) m
    rwa [div_le_iff₀ (by positivity), mul_comm] at this
  have hquad : 1 + r + -a * r ^ 2 ≤ 1 + 1 / (4 * a) := by
    have : 1 + 1 / (4 * a) - (1 + r + -a * r ^ 2) = (2 * a * r - 1) ^ 2 / (4 * a) := by
      field_simp
      ring
    exact sub_nonneg.1 (this ▸ div_nonneg (sq_nonneg _) (by positivity))
  calc (1 + r) ^ m * Real.exp (-a * r ^ 2) ≤ m ! * Real.exp (1 + r) * Real.exp (-a * r ^ 2) := by
        gcongr
    _ = m ! * Real.exp (1 + r + -a * r ^ 2) := by rw [Real.exp_add (1 + r)]; ring
    _ ≤ m ! * Real.exp (1 + 1 / (4 * a)) := by gcongr

end Real
