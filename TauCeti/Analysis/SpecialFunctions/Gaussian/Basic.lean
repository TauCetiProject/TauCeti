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
functions. It also records a linear lower bound for the increment `exp (-κ (R - t)²) - exp (-κ R²)`
on `0 ≤ t ≤ R`, the growth of a Gaussian barrier along the inward normal of a sphere.

## Main results

* `TauCeti.one_add_pow_mul_exp_neg_mul_sq_le`: an explicit bound for `(1 + r) ^ m * exp (-a r²)`.
* `TauCeti.mul_le_exp_neg_mul_sub_sq_sub`: the linear lower bound
  `κ R exp (-κ R²) t ≤ exp (-κ (R - t)²) - exp (-κ R²)`.
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

/-- The Gaussian `exp (-κ s²)` grows at least linearly as `s` decreases from `R`: for `0 ≤ κ` and
`0 ≤ t ≤ R`, `κ R exp (-κ R²) t ≤ exp (-κ (R - t)²) - exp (-κ R²)`. In Hopf's lemma this is the
growth of the Gaussian barrier along the inward normal of a sphere. -/
theorem mul_le_exp_neg_mul_sub_sq_sub {κ R t : ℝ} (hκ : 0 ≤ κ) (ht : 0 ≤ t)
    (htR : t ≤ R) :
    κ * R * Real.exp (-κ * R ^ 2) * t ≤ Real.exp (-κ * (R - t) ^ 2) - Real.exp (-κ * R ^ 2) := by
  have hsplit : Real.exp (-κ * (R - t) ^ 2) =
      Real.exp (-κ * R ^ 2) * Real.exp (κ * (2 * R * t - t ^ 2)) := by
    rw [← Real.exp_add]
    ring_nf
  have h1 := Real.add_one_le_exp (κ * (2 * R * t - t ^ 2))
  have h2 : κ * (R * t) ≤ κ * (2 * R * t - t ^ 2) :=
    mul_le_mul_of_nonneg_left (by nlinarith) hκ
  rw [hsplit]
  nlinarith [Real.exp_pos (-κ * R ^ 2)]

end TauCeti
