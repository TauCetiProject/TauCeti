/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Normed.Module.Basic

/-!
# Affine normalizations of metric balls and spheres

This file records how the affine map `y ↦ x + c • y` pulls metric balls, closed balls, and
spheres back to their corresponding sets centered at zero. It also provides membership forms and
unit-radius specializations for real scalars.
-/

public section

namespace TauCeti

section Preimage

variable {𝕜 E : Type*} [NormedDivisionRing 𝕜] [SeminormedAddCommGroup E]
  [Module 𝕜 E] [NormSMulClass 𝕜 E]

/-- The affine normalization map `y ↦ x + c • y` pulls the ball `Metric.ball x (‖c‖ * r)` back
to `Metric.ball 0 r`, for nonzero scale `c`. -/
@[simp]
theorem preimage_const_add_smul_ball_norm (x : E) {c : 𝕜} (hc : c ≠ 0) (r : ℝ) :
    ((fun y : E ↦ x + c • y) ⁻¹' Metric.ball x (‖c‖ * r)) = Metric.ball 0 r := by
  ext y
  simp only [Set.mem_preimage, Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, sub_zero,
    norm_smul]
  exact mul_lt_mul_iff_right₀ (norm_pos_iff.2 hc)

/-- The affine map `y ↦ x + c • y` pulls the closed ball of radius `‖c‖ * r` about `x`
back to the closed ball of radius `r` about `0`. -/
@[simp]
theorem preimage_const_add_smul_closedBall (x : E) {c : 𝕜} (hc : c ≠ 0) (r : ℝ) :
    ((fun y : E ↦ x + c • y) ⁻¹' Metric.closedBall x (‖c‖ * r)) =
      Metric.closedBall 0 r := by
  ext y
  simp only [Set.mem_preimage, Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left,
    sub_zero, norm_smul]
  exact mul_le_mul_iff_right₀ (norm_pos_iff.2 hc)

/-- The affine map `y ↦ x + c • y` pulls the sphere of radius `‖c‖ * r` about `x`
back to the sphere of radius `r` about `0`. -/
@[simp]
theorem preimage_const_add_smul_sphere (x : E) {c : 𝕜} (hc : c ≠ 0) (r : ℝ) :
    ((fun y : E ↦ x + c • y) ⁻¹' Metric.sphere x (‖c‖ * r)) = Metric.sphere 0 r := by
  ext y
  simp only [Set.mem_preimage, Metric.mem_sphere, dist_eq_norm, add_sub_cancel_left, sub_zero,
    norm_smul]
  constructor
  · exact mul_left_cancel₀ (norm_pos_iff.2 hc).ne'
  · exact congrArg ((· * ·) ‖c‖)

/-- Membership form of `preimage_const_add_smul_ball_norm`. -/
@[simp]
theorem const_add_smul_mem_ball_iff (y : E) {c : 𝕜} (hc : c ≠ 0) (r : ℝ) :
    ‖c • y‖ < ‖c‖ * r ↔ y ∈ Metric.ball 0 r := by
  simpa only [Set.mem_preimage, Metric.mem_ball, dist_self_add_left] using
    Set.ext_iff.mp (preimage_const_add_smul_ball_norm 0 hc r) y

/-- Membership form of `preimage_const_add_smul_closedBall`. -/
@[simp]
theorem const_add_smul_mem_closedBall_iff (y : E) {c : 𝕜} (hc : c ≠ 0) (r : ℝ) :
    ‖c • y‖ ≤ ‖c‖ * r ↔ y ∈ Metric.closedBall 0 r := by
  simpa only [Set.mem_preimage, Metric.mem_closedBall, dist_self_add_left] using
    Set.ext_iff.mp (preimage_const_add_smul_closedBall 0 hc r) y

/-- Membership form of `preimage_const_add_smul_sphere`. -/
@[simp]
theorem const_add_smul_mem_sphere_iff (y : E) {c : 𝕜} (hc : c ≠ 0) (r : ℝ) :
    ‖c • y‖ = ‖c‖ * r ↔ y ∈ Metric.sphere 0 r := by
  simpa only [Set.mem_preimage, mem_sphere_iff_norm, add_sub_cancel_left] using
    Set.ext_iff.mp (preimage_const_add_smul_sphere 0 hc r) y

end Preimage

/-- The real-scalar form of `preimage_const_add_smul_ball_norm`. -/
@[simp]
theorem preimage_const_add_smul_ball {E : Type*} [SeminormedAddCommGroup E] [Module ℝ E]
    [NormSMulClass ℝ E] (x : E) {c : ℝ} (hc : c ≠ 0) (r : ℝ) :
    ((fun y : E ↦ x + c • y) ⁻¹' Metric.ball x (|c| * r)) = Metric.ball 0 r := by
  simpa [Real.norm_eq_abs] using preimage_const_add_smul_ball_norm x hc r

/-- Positive-radius affine normalization of membership in a ball to the unit ball. -/
@[simp]
theorem const_add_smul_mem_ball_unit_iff {E : Type*} [SeminormedAddCommGroup E] [Module ℝ E]
    [NormSMulClass ℝ E] (y : E) {r : ℝ} (hr : 0 < r) :
    ‖r • y‖ < r ↔ y ∈ Metric.ball 0 1 := by
  simpa [Real.norm_of_nonneg hr.le] using const_add_smul_mem_ball_iff y hr.ne' 1

/-- Positive-radius affine normalization of membership in a closed ball to the unit closed ball. -/
@[simp]
theorem const_add_smul_mem_closedBall_unit_iff {E : Type*} [SeminormedAddCommGroup E]
    [Module ℝ E] [NormSMulClass ℝ E] (y : E) {r : ℝ} (hr : 0 < r) :
    ‖r • y‖ ≤ r ↔ y ∈ Metric.closedBall 0 1 := by
  simpa [Real.norm_of_nonneg hr.le] using const_add_smul_mem_closedBall_iff y hr.ne' 1

/-- Positive-radius affine normalization of membership in a sphere to the unit sphere. -/
@[simp]
theorem const_add_smul_mem_sphere_unit_iff {E : Type*} [SeminormedAddCommGroup E] [Module ℝ E]
    [NormSMulClass ℝ E] (y : E) {r : ℝ} (hr : 0 < r) :
    ‖r • y‖ = r ↔ y ∈ Metric.sphere 0 1 := by
  simpa [Real.norm_of_nonneg hr.le] using const_add_smul_mem_sphere_iff y hr.ne' 1

end TauCeti
