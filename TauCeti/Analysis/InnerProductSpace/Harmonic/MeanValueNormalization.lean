/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.InnerProductSpace.Harmonic.Ball

/-!
# Affine normalization for harmonic mean-value formulas

The mean-value property for harmonic functions is most naturally proved first on the unit ball
and unit sphere.  To use that result locally, one transports it by the affine map
`y ↦ x + r • y`.  This file records the set-theoretic part of that transport for balls,
closed balls, and spheres, together with the resulting membership equivalences.

The normalization keeps the absolute value of the scale in the geometric statements, so it also
applies to negative dilations.  The positive-radius specializations are the forms intended for
mean-value arguments.  Harmonicity itself is transported by
`harmonicOnNhd_comp_const_add_smul_ball_iff` from
`TauCeti.Analysis.InnerProductSpace.Harmonic.Ball`.

## Main declarations

* `TauCeti.preimage_const_add_smul_closedBall`: affine normalization of a closed ball.
* `TauCeti.preimage_const_add_smul_sphere`: affine normalization of a sphere.
* `TauCeti.const_add_smul_mem_ball_iff`: membership in a ball in normalized coordinates.
* `TauCeti.const_add_smul_mem_sphere_iff`: membership in a sphere in normalized coordinates.
-/

public section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The affine map `y ↦ x + c • y` pulls the closed ball of radius `|c| * r` about `x`
back to the closed ball of radius `r` about `0`. -/
@[simp]
theorem preimage_const_add_smul_closedBall (x : E) {c : ℝ} (hc : c ≠ 0) (r : ℝ) :
    ((fun y : E ↦ x + c • y) ⁻¹' Metric.closedBall x (|c| * r)) =
      Metric.closedBall 0 r := by
  ext y
  simp only [Set.mem_preimage, Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left,
    sub_zero, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_iff_right₀ (norm_pos_iff.2 hc)

/-- The affine map `y ↦ x + c • y` pulls the sphere of radius `|c| * r` about `x`
back to the sphere of radius `r` about `0`. -/
@[simp]
theorem preimage_const_add_smul_sphere (x : E) {c : ℝ} (hc : c ≠ 0) (r : ℝ) :
    ((fun y : E ↦ x + c • y) ⁻¹' Metric.sphere x (|c| * r)) = Metric.sphere 0 r := by
  ext y
  simp only [Set.mem_preimage, Metric.mem_sphere, dist_eq_norm, add_sub_cancel_left,
    sub_zero, norm_smul, Real.norm_eq_abs]
  constructor
  · exact mul_left_cancel₀ (norm_pos_iff.2 hc).ne'
  · exact congrArg ((· * ·) |c|)

/-- Membership in a scaled ball, expressed in normalized coordinates. -/
theorem const_add_smul_mem_ball_iff (x y : E) {c : ℝ} (hc : c ≠ 0) (r : ℝ) :
    x + c • y ∈ Metric.ball x (|c| * r) ↔ y ∈ Metric.ball 0 r := by
  simpa only [Set.mem_preimage] using Set.ext_iff.mp (preimage_const_add_smul_ball x hc r) y

/-- Membership in a scaled closed ball, expressed in normalized coordinates. -/
theorem const_add_smul_mem_closedBall_iff (x y : E) {c : ℝ} (hc : c ≠ 0) (r : ℝ) :
    x + c • y ∈ Metric.closedBall x (|c| * r) ↔ y ∈ Metric.closedBall 0 r := by
  simpa only [Set.mem_preimage] using
    Set.ext_iff.mp (preimage_const_add_smul_closedBall x hc r) y

/-- Membership in a scaled sphere, expressed in normalized coordinates. -/
theorem const_add_smul_mem_sphere_iff (x y : E) {c : ℝ} (hc : c ≠ 0) (r : ℝ) :
    x + c • y ∈ Metric.sphere x (|c| * r) ↔ y ∈ Metric.sphere 0 r := by
  simpa only [Set.mem_preimage] using Set.ext_iff.mp (preimage_const_add_smul_sphere x hc r) y

/-- Positive-radius specialization of affine normalization for open balls. -/
@[simp]
theorem preimage_const_add_pos_smul_ball (x : E) {r : ℝ} (hr : 0 < r) :
    ((fun y : E ↦ x + r • y) ⁻¹' Metric.ball x r) = Metric.ball 0 1 := by
  simpa [abs_of_pos hr] using preimage_const_add_smul_ball x hr.ne' 1

/-- Positive-radius specialization of affine normalization for closed balls. -/
@[simp]
theorem preimage_const_add_pos_smul_closedBall (x : E) {r : ℝ} (hr : 0 < r) :
    ((fun y : E ↦ x + r • y) ⁻¹' Metric.closedBall x r) = Metric.closedBall 0 1 := by
  simpa [abs_of_pos hr] using preimage_const_add_smul_closedBall x hr.ne' 1

/-- Positive-radius specialization of affine normalization for spheres. -/
@[simp]
theorem preimage_const_add_pos_smul_sphere (x : E) {r : ℝ} (hr : 0 < r) :
    ((fun y : E ↦ x + r • y) ⁻¹' Metric.sphere x r) = Metric.sphere 0 1 := by
  simpa [abs_of_pos hr] using preimage_const_add_smul_sphere x hr.ne' 1

/-- Membership in a positive-radius ball in unit-ball coordinates. -/
theorem const_add_pos_smul_mem_ball_iff (x y : E) {r : ℝ} (hr : 0 < r) :
    x + r • y ∈ Metric.ball x r ↔ y ∈ Metric.ball 0 1 := by
  simpa [abs_of_pos hr] using const_add_smul_mem_ball_iff x y hr.ne' 1

/-- Membership in a positive-radius closed ball in unit-ball coordinates. -/
theorem const_add_pos_smul_mem_closedBall_iff (x y : E) {r : ℝ} (hr : 0 < r) :
    x + r • y ∈ Metric.closedBall x r ↔ y ∈ Metric.closedBall 0 1 := by
  simpa [abs_of_pos hr] using const_add_smul_mem_closedBall_iff x y hr.ne' 1

/-- Membership in a positive-radius sphere in unit-sphere coordinates. -/
theorem const_add_pos_smul_mem_sphere_iff (x y : E) {r : ℝ} (hr : 0 < r) :
    x + r • y ∈ Metric.sphere x r ↔ y ∈ Metric.sphere 0 1 := by
  simpa [abs_of_pos hr] using const_add_smul_mem_sphere_iff x y hr.ne' 1

end TauCeti
