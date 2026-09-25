/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.Ball.Pointwise

/-!
# Affine normalizations of metric balls and spheres

This file records how the affine map `y ↦ c • y +ᵥ x` pulls metric balls, closed balls, and
spheres back to their corresponding sets centered at zero.

The preimage formulas need only `[Norm 𝕜] [SMul 𝕜 E] [NormSMulClass 𝕜 E]` on the
scalars and their action. Balls and closed balls require `0 < ‖c‖`; spheres only require
`‖c‖ ≠ 0`. Over a normed division ring these conditions are equivalent to `c ≠ 0`, via
`norm_pos_iff` and `norm_ne_zero_iff` respectively.

The range formula identifies a positive real scaling of the unit sphere with the sphere
of that radius in a seminormed real vector space.
-/

public section

namespace TauCeti

section Preimage

variable {𝕜 E P : Type*} [Norm 𝕜] [SeminormedAddCommGroup E]
  [SMul 𝕜 E] [NormSMulClass 𝕜 E] [PseudoMetricSpace P] [NormedAddTorsor E P]

/-- The affine normalization map `y ↦ c • y +ᵥ x` pulls the ball `Metric.ball x (‖c‖ * r)` back
to `Metric.ball 0 r`, for a scale `c` of positive norm. -/
@[simp]
theorem preimage_smul_vadd_ball_norm (x : P) {c : 𝕜} (hc : 0 < ‖c‖) (r : ℝ) :
    ((fun y : E ↦ c • y +ᵥ x) ⁻¹' Metric.ball x (‖c‖ * r)) = Metric.ball 0 r := by
  ext y
  simp only [Set.mem_preimage, Metric.mem_ball, dist_vadd_left, dist_zero_right, norm_smul]
  exact mul_lt_mul_iff_right₀ hc

/-- The affine map `y ↦ c • y +ᵥ x` pulls the closed ball of radius `‖c‖ * r` about `x`
back to the closed ball of radius `r` about `0`. -/
@[simp]
theorem preimage_smul_vadd_closedBall (x : P) {c : 𝕜} (hc : 0 < ‖c‖) (r : ℝ) :
    ((fun y : E ↦ c • y +ᵥ x) ⁻¹' Metric.closedBall x (‖c‖ * r)) =
      Metric.closedBall 0 r := by
  ext y
  simp only [Set.mem_preimage, Metric.mem_closedBall, dist_vadd_left, dist_zero_right, norm_smul]
  exact mul_le_mul_iff_right₀ hc

/-- The affine map `y ↦ c • y +ᵥ x` pulls the sphere of radius `‖c‖ * r` about `x`
back to the sphere of radius `r` about `0`, provided `‖c‖ ≠ 0`. -/
@[simp]
theorem preimage_smul_vadd_sphere (x : P) {c : 𝕜} (hc : ‖c‖ ≠ 0) (r : ℝ) :
    ((fun y : E ↦ c • y +ᵥ x) ⁻¹' Metric.sphere x (‖c‖ * r)) = Metric.sphere 0 r := by
  ext y
  simp only [Set.mem_preimage, Metric.mem_sphere, dist_vadd_left, dist_zero_right, norm_smul]
  exact mul_right_inj' hc

end Preimage

section Range

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

/-- The image of the unit sphere under scaling by a positive real `c` is the sphere of radius
`c`. -/
@[simp]
theorem range_smul_coe_sphere {c : ℝ} (hc : 0 < c) :
    Set.range (fun u : Metric.sphere (0 : E) 1 ↦ c • (u : E)) = Metric.sphere 0 c := by
  rw [Set.range_comp' (c • ·) Subtype.val, Subtype.range_coe, Set.image_smul,
    smul_sphere' hc.ne', smul_zero, Real.norm_of_nonneg hc.le, mul_one]

end Range

end TauCeti
