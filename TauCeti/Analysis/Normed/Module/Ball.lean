/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.Analysis.Normed.Group.BallSphere
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Analysis.Normed.Module.Ball.Pointwise

/-!
# Metric balls and spheres in normed spaces

This file records how the affine map `y ↦ c • y +ᵥ x` pulls metric balls, closed balls, and
spheres back to their corresponding sets centered at zero.

The preimage formulas need only `[Norm 𝕜] [SMul 𝕜 E] [NormSMulClass 𝕜 E]` on the
scalars and their action. Balls and closed balls require `0 < ‖c‖`; spheres only require
`‖c‖ ≠ 0`. Over a normed division ring these conditions are equivalent to `c ≠ 0`, via
`norm_pos_iff` and `norm_ne_zero_iff` respectively.

The range formula identifies a positive real scaling of the unit sphere with the sphere
of that radius in a seminormed real vector space. Two points on a sphere of nonzero radius
centered at zero lie on the same line exactly when they are equal or antipodal.

The normalization lemmas characterize the unit norm conditions for `R⁻¹ • z` when `R > 0`.
They need only a norm homogeneous under real scalar multiplication; no additive structure
or metric on the vector type is required.
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

section Sphere

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

/-- The image of the unit sphere under scaling by a positive real `c` is the sphere of radius
`c`. -/
@[simp]
theorem range_smul_coe_sphere {c : ℝ} (hc : 0 < c) :
    Set.range (fun u : Metric.sphere (0 : E) 1 ↦ c • (u : E)) = Metric.sphere 0 c := by
  rw [Set.range_comp' (c • ·) Subtype.val, Subtype.range_coe, Set.image_smul,
    smul_sphere' hc.ne', smul_zero, Real.norm_of_nonneg hc.le, mul_one]

/-- Two points of a sphere of nonzero radius centered at zero in a real seminormed space
lie on the same line exactly when they are equal or antipodal. -/
@[simp]
theorem coe_mem_span_singleton_iff {r : ℝ} (hr : r ≠ 0) {x p : Metric.sphere (0 : E) r} :
    (x : E) ∈ ℝ ∙ (p : E) ↔ x = p ∨ x = -p := by
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 h
    have habs : |a| = 1 := by
      apply (mul_eq_right₀ hr).1
      simpa [← ha, norm_smul] using norm_eq_of_mem_sphere x
    rcases (abs_eq zero_le_one).1 habs with rfl | rfl
    · exact Or.inl (Subtype.ext (by rw [← ha, one_smul]))
    · exact Or.inr (Subtype.ext (by rw [← ha, coe_neg_sphere, neg_one_smul]))
  · rintro (rfl | rfl)
    · exact Submodule.mem_span_singleton_self _
    · rw [coe_neg_sphere]
      exact Submodule.neg_mem _ (Submodule.mem_span_singleton_self _)

/-- The unit sphere minus `p` and `-p` is the set of its points off the line through `p`. -/
theorem compl_singleton_inter_compl_singleton_neg_eq (p : Metric.sphere (0 : E) 1) :
    ({p}ᶜ ∩ {-p}ᶜ : Set (Metric.sphere (0 : E) 1)) =
      ({x | (x : E) ∉ ℝ ∙ (p : E)} : Set (Metric.sphere (0 : E) 1)) := by
  ext x
  simp [not_or]

end Sphere

section Normalization

variable {E : Type*} [Norm E] [SMul ℝ E] [NormSMulClass ℝ E]

/-- Scaling a vector by the inverse of a positive radius puts it inside the unit norm bound
exactly when its original norm is less than that radius. -/
@[simp]
theorem norm_inv_smul_lt_one_iff {z : E} {R : ℝ} (hR : 0 < R) :
    ‖R⁻¹ • z‖ < 1 ↔ ‖z‖ < R := by
  simp [norm_smul, Real.norm_of_nonneg hR.le, inv_mul_lt_iff₀ hR]

/-- Scaling a vector by the inverse of a positive radius gives unit norm exactly when its
original norm equals that radius. -/
@[simp]
theorem norm_inv_smul_eq_one_iff {z : E} {R : ℝ} (hR : 0 < R) :
    ‖R⁻¹ • z‖ = 1 ↔ ‖z‖ = R := by
  simp [norm_smul, Real.norm_of_nonneg hR.le, inv_mul_eq_iff_eq_mul₀ hR.ne']

end Normalization

end TauCeti
