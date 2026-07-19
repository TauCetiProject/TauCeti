/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.Analysis.Normed.Module.Basic

/-!
# Affine normalizations of metric balls and spheres

This file records how the affine map `y ↦ c • y +ᵥ x` pulls metric balls, closed balls, and
spheres back to their corresponding sets centered at zero. It also provides a real-scalar
specialization for the open ball.
-/

public section

namespace TauCeti

section Preimage

variable {𝕜 E P : Type*} [NormedDivisionRing 𝕜] [SeminormedAddCommGroup E]
  [Module 𝕜 E] [NormSMulClass 𝕜 E] [PseudoMetricSpace P] [NormedAddTorsor E P]

/-- The affine normalization map `y ↦ c • y +ᵥ x` pulls the ball `Metric.ball x (‖c‖ * r)` back
to `Metric.ball 0 r`, for nonzero scale `c`. -/
@[simp]
theorem preimage_smul_vadd_ball_norm (x : P) {c : 𝕜} (hc : c ≠ 0) (r : ℝ) :
    ((fun y : E ↦ c • y +ᵥ x) ⁻¹' Metric.ball x (‖c‖ * r)) = Metric.ball 0 r := by
  ext y
  simp only [Set.mem_preimage, Metric.mem_ball, dist_vadd_left, dist_zero_right, norm_smul]
  exact mul_lt_mul_iff_right₀ (norm_pos_iff.2 hc)

/-- The affine map `y ↦ c • y +ᵥ x` pulls the closed ball of radius `‖c‖ * r` about `x`
back to the closed ball of radius `r` about `0`. -/
@[simp]
theorem preimage_smul_vadd_closedBall (x : P) {c : 𝕜} (hc : c ≠ 0) (r : ℝ) :
    ((fun y : E ↦ c • y +ᵥ x) ⁻¹' Metric.closedBall x (‖c‖ * r)) =
      Metric.closedBall 0 r := by
  ext y
  simp only [Set.mem_preimage, Metric.mem_closedBall, dist_vadd_left, dist_zero_right, norm_smul]
  exact mul_le_mul_iff_right₀ (norm_pos_iff.2 hc)

/-- The affine map `y ↦ c • y +ᵥ x` pulls the sphere of radius `‖c‖ * r` about `x`
back to the sphere of radius `r` about `0`. -/
@[simp]
theorem preimage_smul_vadd_sphere (x : P) {c : 𝕜} (hc : c ≠ 0) (r : ℝ) :
    ((fun y : E ↦ c • y +ᵥ x) ⁻¹' Metric.sphere x (‖c‖ * r)) = Metric.sphere 0 r := by
  ext y
  simp only [Set.mem_preimage, Metric.mem_sphere, dist_vadd_left, dist_zero_right, norm_smul]
  constructor
  · exact mul_left_cancel₀ (norm_pos_iff.2 hc).ne'
  · exact congrArg ((· * ·) ‖c‖)

end Preimage

/-- The real-scalar vector-space form of `preimage_smul_vadd_ball_norm`. -/
@[simp]
theorem preimage_const_add_smul_ball {E : Type*} [SeminormedAddCommGroup E] [Module ℝ E]
    [NormSMulClass ℝ E] (x : E) {c : ℝ} (hc : c ≠ 0) (r : ℝ) :
    ((fun y : E ↦ x + c • y) ⁻¹' Metric.ball x (|c| * r)) = Metric.ball 0 r := by
  simpa [Real.norm_eq_abs, add_comm] using preimage_smul_vadd_ball_norm x hc r

end TauCeti
