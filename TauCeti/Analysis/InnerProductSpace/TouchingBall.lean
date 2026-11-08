/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Internally tangent balls

In a real inner product space, the closed ball of radius `R / 2` that is internally tangent to
`ball y R` at `y + R • e`, for a unit vector `e`, meets the sphere `sphere y R` only at the point
of tangency (`TauCeti.mem_ball_of_mem_closedBall_half_of_ne`). So a function continuous on
`ball y R` and at `y + R • e` is continuous on that closed ball. The classical proof of Hopf's
boundary-point lemma runs its barrier argument on this ball.

## Main declarations

* `TauCeti.mem_ball_of_mem_closedBall_half_of_ne`: the internally tangent closed ball of half the
  radius meets the sphere only at the point of tangency.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  proof of Lemma 3.4.
-/

public section

namespace TauCeti

open Metric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

open RealInnerProductSpace

/-- The closed ball of radius `R / 2` that is internally tangent to `ball y R` at `y + R • e`
meets the sphere `sphere y R` only at the point of tangency. -/
theorem mem_ball_of_mem_closedBall_half_of_ne {y e z : E} {R : ℝ} (he : ‖e‖ = 1)
    (hz : z ∈ closedBall (y + (R / 2) • e) (R / 2)) (hne : z ≠ y + R • e) :
    z ∈ ball y R := by
  rw [mem_closedBall, dist_eq_norm] at hz
  rw [mem_ball, dist_eq_norm]
  set w := z - (y + (R / 2) • e) with hwdef
  have hR : 0 ≤ R := by linarith [norm_nonneg w]
  have hne' : w - (R / 2) • e ≠ 0 := by
    intro h
    apply hne
    rw [sub_eq_zero, hwdef, sub_eq_iff_eq_add] at h
    rw [h]
    module
  have hee : ‖(R / 2) • e‖ ^ 2 = (R / 2) ^ 2 := by
    rw [norm_smul, he, mul_one, Real.norm_eq_abs, sq_abs]
  have h1 : ‖z - y‖ ^ 2 = ‖w‖ ^ 2 + 2 * ⟪w, (R / 2) • e⟫ + (R / 2) ^ 2 := by
    rw [show z - y = w + (R / 2) • e by rw [hwdef]; abel, norm_add_sq_real, hee]
  have h2 : ‖w - (R / 2) • e‖ ^ 2 = ‖w‖ ^ 2 - 2 * ⟪w, (R / 2) • e⟫ + (R / 2) ^ 2 := by
    rw [norm_sub_sq_real, hee]
  have h3 : 0 < ‖w - (R / 2) • e‖ ^ 2 := by positivity
  have h4 : ‖w‖ ^ 2 ≤ (R / 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hz 2
  have h5 : ‖z - y‖ ^ 2 < R ^ 2 := by nlinarith
  exact (pow_lt_pow_iff_left₀ (norm_nonneg _) hR two_ne_zero).mp h5

end TauCeti
