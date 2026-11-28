/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# The least-squares objective

The excess of the squared residual over its optimal value measures the distance of the
fitted value from the projection of the data onto the range. For a bounded operator on
real Hilbert spaces the gradient is the adjoint applied to the residual.
-/

public section

open InnerProductSpace

variable {F : Type*} [NormedAddCommGroup F]

/-- For a projectable range, the least-squares gap is half the squared distance from the
fitted value to the projection of the data. -/
theorem LinearMap.leastSquares_sub_iInf {𝕜 M : Type*} [RCLike 𝕜]
    [AddCommMonoid M] [Module 𝕜 M] [InnerProductSpace 𝕜 F]
    (A : M →ₗ[𝕜] F) [A.range.HasOrthogonalProjection] (b : F) (x : M) :
    ‖A x - b‖ ^ 2 / 2 - (⨅ y, ‖A y - b‖ ^ 2 / 2) =
      ‖A x - A.range.starProjection b‖ ^ 2 / 2 := by
  have split (z : M) : ‖A z - b‖ ^ 2 =
      ‖A z - A.range.starProjection b‖ ^ 2 + ‖A.rangeᗮ.starProjection b‖ ^ 2 := by
    have hp : A.range.starProjection (A z) = A z :=
      A.range.starProjection_eq_self_iff.mpr (A.mem_range_self z)
    have hq : A.rangeᗮ.starProjection (A z) = 0 := by simp [hp]
    simpa only [map_sub, hp, hq, zero_sub, norm_neg] using
      A.range.norm_sq_eq_add_norm_sq_starProjection (A z - b)
  obtain ⟨z, hz⟩ := A.range.starProjection_apply_mem b
  have infimum : (⨅ y, ‖A y - b‖ ^ 2 / 2) = ‖A.rangeᗮ.starProjection b‖ ^ 2 / 2 := by
    refine ciInf_eq_of_forall_ge_of_forall_gt_exists_lt (fun y ↦ ?_) fun r hr ↦ ⟨z, ?_⟩
    · rw [split]
      linarith [sq_nonneg ‖A y - A.range.starProjection b‖]
    · rw [split, hz]
      simpa using hr
  rw [infimum, split]
  ring

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [InnerProductSpace ℝ F] [CompleteSpace F]

/-- The least-squares gradient is the adjoint applied to the residual. -/
theorem ContinuousLinearMap.hasGradientAt_leastSquares (A : E →L[ℝ] F) (b : F) (x : E) :
    HasGradientAt (fun y ↦ ‖A y - b‖ ^ 2 / 2) (A.adjoint (A x - b)) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  simp_rw [div_eq_mul_inv]
  refine (((A.hasFDerivAt.sub_const b).norm_sq).mul_const (2 : ℝ)⁻¹).congr_fderiv ?_
  ext v
  simp [innerSL_apply_apply, toDual_apply_apply,
    ContinuousLinearMap.adjoint_inner_left, smul_eq_mul]
