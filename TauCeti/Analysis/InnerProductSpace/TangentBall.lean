/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Module

/-!
# Internally tangent balls

Let `e` be a unit vector of a real inner product space and let `x₀ = y + R • e` be the point where
the ray from `y` in direction `e` meets the sphere of radius `R` about `y`. The ball of radius
`R / 2` about `y + (R / 2) • e` is internally tangent to `ball y R` at `x₀`: its closure meets the
complement of `ball y R` only at `x₀`. By the parallelogram law, a point `x` of that closed ball
satisfies `‖x - y‖² + ‖x - x₀‖² ≤ R²`.

This is the reduction used in boundary-point lemmas: a function continuous on `ball y R` and at
`x₀` relative to it is continuous on the closed tangent ball.

## Main declarations

* `TauCeti.eq_or_mem_ball_of_mem_closedBall_add_half_smul`: a point of the closed tangent ball is
  `x₀` or lies in `ball y R`.
-/

public section

open Metric

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The closed ball of radius `R / 2` internally tangent to `ball y R` at `y + R • e` meets the
complement of `ball y R` only at the point of tangency. -/
theorem eq_or_mem_ball_of_mem_closedBall_add_half_smul {y e x : F} {R : ℝ} (he : ‖e‖ = 1)
    (hx : x ∈ closedBall (y + (R / 2) • e) (R / 2)) :
    x = y + R • e ∨ x ∈ ball y R := by
  rw [mem_closedBall, dist_eq_norm] at hx
  have hR : 0 ≤ R / 2 := (norm_nonneg _).trans hx
  set d := x - (y + (R / 2) • e)
  have hw : ‖(R / 2) • e‖ = R / 2 := by rw [norm_smul, he, mul_one, Real.norm_of_nonneg hR]
  -- The parallelogram law: `‖x - y‖² + ‖x - x₀‖² = 2 ‖d‖² + 2 (R / 2)² ≤ R²`.
  have hpar := parallelogram_law_with_norm ℝ d ((R / 2) • e)
  have h1 : d + (R / 2) • e = x - y := by simp only [d]; module
  have h2 : d - (R / 2) • e = x - (y + R • e) := by simp only [d]; module
  rw [h1, h2, hw] at hpar
  by_cases hx₀ : x = y + R • e
  · exact Or.inl hx₀
  · right
    have hpos : 0 < ‖x - (y + R • e)‖ := norm_pos_iff.2 (sub_ne_zero.2 hx₀)
    have hlt : ‖x - y‖ ^ 2 < R ^ 2 := by
      nlinarith [mul_le_mul hx hx (norm_nonneg d) hR, mul_pos hpos hpos]
    rw [mem_ball, dist_eq_norm]
    exact lt_of_pow_lt_pow_left₀ 2 (by linarith) hlt

end TauCeti
