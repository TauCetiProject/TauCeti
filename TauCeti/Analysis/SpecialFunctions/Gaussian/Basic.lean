/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr

/-!
# Elementary Gaussian bounds

A polynomial weight times a real Gaussian is bounded, and completing the square absorbs a linear
tilt into half the Gaussian weight. This file records an explicit bound for
`(1 + r) ^ m * exp (-a r²)` on `r ≥ 0` (the scalar estimate behind the decay of Gaussian Schwartz
functions) and the uniform bound `exp (-b u² - c u) ≤ exp (c² / (2 b)) * exp (-(b / 2) u²)` for
`0 < b`.

## Main results

* `TauCeti.one_add_pow_mul_exp_neg_mul_sq_le`: an explicit bound for `(1 + r) ^ m * exp (-a r²)`.
* `TauCeti.exp_neg_mul_sq_sub_mul_le`: uniform completing-the-square bound for
  `exp (-b u² - c u)` when `0 < b`.
-/

public section

open scoped Nat

namespace TauCeti

/-- For `0 < a`, the function `r ↦ (1 + r) ^ m * exp (-a r²)` is bounded on `r ≥ 0` by the
explicit constant `m! / (a / 2) ^ m * exp a`. -/
theorem one_add_pow_mul_exp_neg_mul_sq_le {a : ℝ} (ha : 0 < a) (m : ℕ) {r : ℝ}
    (hr : 0 ≤ r) :
    (1 + r) ^ m * Real.exp (-a * r ^ 2) ≤ m ! / (a / 2) ^ m * Real.exp a := by
  set u := 1 + r
  have hu : 1 ≤ u := by simp [u, hr]
  -- `r² ≥ u² / 2 - 1`, so `exp (-a r²) ≤ exp a * exp (-(a / 2) u²)`.
  have hexp : Real.exp (-a * r ^ 2) ≤ Real.exp a * Real.exp (-(a / 2 * u ^ 2)) := by
    rw [← Real.exp_add]
    gcongr
    nlinarith [sq_nonneg (r - 1)]
  -- `u ^ m ≤ (u²) ^ m ≤ m! exp ((a / 2) u²) / (a / 2) ^ m`.
  have hpow : u ^ m ≤ m ! / (a / 2) ^ m * Real.exp (a / 2 * u ^ 2) := by
    have h := Real.pow_div_factorial_le_exp (x := a / 2 * u ^ 2) (by positivity) m
    rw [div_le_iff₀ (by positivity), mul_pow] at h
    calc u ^ m ≤ (u ^ 2) ^ m := by
          rw [← pow_mul]; exact pow_le_pow_right₀ hu (by omega)
      _ = (a / 2) ^ m * (u ^ 2) ^ m / (a / 2) ^ m := by field_simp
      _ ≤ Real.exp (a / 2 * u ^ 2) * m ! / (a / 2) ^ m := by gcongr
      _ = m ! / (a / 2) ^ m * Real.exp (a / 2 * u ^ 2) := by ring
  calc u ^ m * Real.exp (-a * r ^ 2)
      ≤ m ! / (a / 2) ^ m * Real.exp (a / 2 * u ^ 2) *
          (Real.exp a * Real.exp (-(a / 2 * u ^ 2))) := by gcongr
    _ = m ! / (a / 2) ^ m * Real.exp a := by
      rw [mul_assoc, mul_left_comm (Real.exp (a / 2 * u ^ 2)), ← Real.exp_add, add_neg_cancel,
        Real.exp_zero, mul_one]

/-- For `0 < b`, `exp (-b u² - c u) ≤ exp (c² / (2 b)) * exp (-(b / 2) u²)` uniformly in
`c u : ℝ`. -/
theorem exp_neg_mul_sq_sub_mul_le {b : ℝ} (hb : 0 < b) (c u : ℝ) :
    Real.exp (-b * u ^ 2 - c * u) ≤ Real.exp (c ^ 2 / (2 * b)) * Real.exp (-(b / 2) * u ^ 2) := by
  rw [← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have hsq : 0 ≤ b / 2 * (u + c / b) ^ 2 := by positivity
  have hexpand : b / 2 * (u + c / b) ^ 2 = b / 2 * u ^ 2 + c * u + c ^ 2 / (2 * b) := by
    field_simp
    ring
  linarith

end TauCeti
