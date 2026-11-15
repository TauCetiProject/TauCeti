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

A polynomial weight times a real Gaussian is bounded above. This file records an explicit
upper bound for `(1 + r) ^ m * exp (-a r²)`, the scalar estimate behind the decay of Gaussian
Schwartz functions.

## Main results

* `TauCeti.one_add_pow_mul_exp_neg_mul_sq_le`: an explicit upper bound for
  `(1 + r) ^ m * exp (-a r²)`.
-/

public section

open scoped Nat

namespace TauCeti

/-- For `0 < a`, the function `r ↦ (1 + r) ^ m * exp (-a r²)` is bounded above by the explicit
constant `m! / (a / 2) ^ m * exp a`. -/
theorem one_add_pow_mul_exp_neg_mul_sq_le {a : ℝ} (ha : 0 < a) (m : ℕ) {r : ℝ} :
    (1 + r) ^ m * Real.exp (-a * r ^ 2) ≤ m ! / (a / 2) ^ m * Real.exp a := by
  set u := 1 + r
  rcases lt_or_ge |u| 1 with hu | hu
  · -- `|u| < 1`: the left-hand side is at most `1`, and so is no larger than the constant.
    have h := Real.pow_div_factorial_le_exp (x := a / 2) (by positivity) m
    rw [div_le_iff₀ (by positivity)] at h
    have hC : 1 ≤ m ! / (a / 2) ^ m * Real.exp a := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity), one_mul]
      calc (a / 2) ^ m ≤ Real.exp (a / 2) * m ! := h
        _ ≤ Real.exp a * m ! := by gcongr; linarith
        _ = m ! * Real.exp a := mul_comm _ _
    refine le_trans ?_ hC
    calc u ^ m * Real.exp (-a * r ^ 2) ≤ |u| ^ m * Real.exp (-a * r ^ 2) :=
          mul_le_mul_of_nonneg_right ((le_abs_self _).trans_eq (abs_pow u m))
            (Real.exp_pos _).le
      _ ≤ 1 * 1 := mul_le_mul (pow_le_one₀ (abs_nonneg u) hu.le)
          (Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg r])) (Real.exp_pos _).le zero_le_one
      _ = 1 := one_mul 1
  · -- `r² ≥ u² / 2 - 1`, so `exp (-a r²) ≤ exp a * exp (-(a / 2) u²)`.
    have hexp : Real.exp (-a * r ^ 2) ≤ Real.exp a * Real.exp (-(a / 2 * u ^ 2)) := by
      rw [← Real.exp_add]
      gcongr
      nlinarith [sq_nonneg (r - 1)]
    -- `u ^ m ≤ (u²) ^ m ≤ m! exp ((a / 2) u²) / (a / 2) ^ m`.
    have hpow : u ^ m ≤ m ! / (a / 2) ^ m * Real.exp (a / 2 * u ^ 2) := by
      have h := Real.pow_div_factorial_le_exp (x := a / 2 * u ^ 2) (by positivity) m
      rw [div_le_iff₀ (by positivity), mul_pow] at h
      calc u ^ m ≤ |u| ^ m := (le_abs_self _).trans_eq (abs_pow u m)
        _ ≤ (|u| ^ 2) ^ m := by
            rw [← pow_mul]; exact pow_le_pow_right₀ hu (by omega)
        _ = (u ^ 2) ^ m := by rw [sq_abs]
        _ = (a / 2) ^ m * (u ^ 2) ^ m / (a / 2) ^ m := by field_simp
        _ ≤ Real.exp (a / 2 * u ^ 2) * m ! / (a / 2) ^ m := by gcongr
        _ = m ! / (a / 2) ^ m * Real.exp (a / 2 * u ^ 2) := by ring
    calc u ^ m * Real.exp (-a * r ^ 2)
        ≤ m ! / (a / 2) ^ m * Real.exp (a / 2 * u ^ 2) *
            (Real.exp a * Real.exp (-(a / 2 * u ^ 2))) := by gcongr
      _ = m ! / (a / 2) ^ m * Real.exp a := by
        rw [mul_assoc, mul_left_comm (Real.exp (a / 2 * u ^ 2)), ← Real.exp_add, add_neg_cancel,
          Real.exp_zero, mul_one]

end TauCeti
