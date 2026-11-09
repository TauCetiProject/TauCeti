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

A polynomial weight times a real Gaussian is bounded. This file records an explicit bound for
`(1 + r) ^ m * exp (-a r²)` on `r ≥ 0`, the scalar estimate behind the decay of Gaussian Schwartz
functions. It also records a linear lower bound for the growth of the Gaussian `exp (-a r²)` as `r`
decreases from `s` towards `0`, the estimate behind the Gaussian barrier of Hopf's boundary-point
lemma.

## Main results

* `TauCeti.one_add_pow_mul_exp_neg_mul_sq_le`: an explicit bound for `(1 + r) ^ m * exp (-a r²)`.
* `TauCeti.mul_exp_le_exp_neg_mul_sub_sq_sub`: for `0 ≤ a` and `0 ≤ t ≤ s`,
  `a s t exp (-a s²) ≤ exp (-a (s - t)²) - exp (-a s²)`.
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

/-- The Gaussian grows at least linearly as its argument decreases: for `0 ≤ a` and `0 ≤ t ≤ s`,
`a s t exp (-a s²) ≤ exp (-a (s - t)²) - exp (-a s²)`. -/
theorem mul_exp_le_exp_neg_mul_sub_sq_sub {a s t : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t) (hts : t ≤ s) :
    a * s * t * Real.exp (-a * s ^ 2) ≤ Real.exp (-a * (s - t) ^ 2) - Real.exp (-a * s ^ 2) := by
  have hsplit : Real.exp (-a * (s - t) ^ 2) =
      Real.exp (-a * s ^ 2) * Real.exp (a * (s ^ 2 - (s - t) ^ 2)) := by
    rw [← Real.exp_add]
    ring_nf
  have hE := Real.exp_pos (-a * s ^ 2)
  have h1 := Real.add_one_le_exp (a * (s ^ 2 - (s - t) ^ 2))
  have h2 : a * s * t ≤ a * (s ^ 2 - (s - t) ^ 2) := by
    nlinarith [mul_nonneg (mul_nonneg ha ht) (sub_nonneg.2 hts)]
  rw [hsplit]
  nlinarith [mul_le_mul_of_nonneg_left h1 hE.le, mul_le_mul_of_nonneg_left h2 hE.le]

end TauCeti
