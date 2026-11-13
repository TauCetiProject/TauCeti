/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars

/-!
# Derivative of a map precomposed with inversion

For a map `u` out of a normed field `𝕜'` and `w ≠ 0`, the derivative over a subfield `𝕜` of
`w ↦ u w⁻¹` at `w` is the derivative of `u` at `w⁻¹` precomposed with
multiplication by `-(w ^ 2)⁻¹`, the derivative of the inversion (`TauCeti.fderiv_comp_inv_apply`).
Multiplication by `-(w ^ 2)⁻¹` scales all norms by `‖w‖⁻²`, so the operator norm of this derivative
is that of the derivative of `u` at `w⁻¹` divided by `‖w‖ ^ 2` (`TauCeti.norm_fderiv_comp_inv`).
This is how a map near infinity is read off in the coordinate `w = z⁻¹` near zero. No
differentiability of `u` is assumed: where `u` is not differentiable at `w⁻¹`, neither is
`w ↦ u w⁻¹` at `w`, and both derivatives are `0`.
-/

public section

namespace TauCeti

variable {𝕜 𝕜' F : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜']
  [NormedAlgebra 𝕜 𝕜'] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The derivative of `w ↦ u w⁻¹` at `w ≠ 0` is the derivative of `u` at `w⁻¹` precomposed with
multiplication by `-(w ^ 2)⁻¹`. -/
theorem fderiv_comp_inv_apply {u : 𝕜' → F} {w : 𝕜'} (hw : w ≠ 0) (h : 𝕜') :
    fderiv 𝕜 (fun w ↦ u w⁻¹) w h = fderiv 𝕜 u w⁻¹ (-(w ^ 2)⁻¹ * h) := by
  by_cases hu : DifferentiableAt 𝕜 u w⁻¹
  · have hinv : HasFDerivAt (fun w : 𝕜' ↦ w⁻¹)
        ((ContinuousLinearMap.smulRight (1 : 𝕜' →L[𝕜'] 𝕜') (-(w ^ 2)⁻¹)).restrictScalars 𝕜) w :=
      (hasDerivAt_inv hw).hasFDerivAt.restrictScalars 𝕜
    have hv : HasFDerivAt (fun w ↦ u w⁻¹) ((fderiv 𝕜 u w⁻¹).comp
        ((ContinuousLinearMap.smulRight (1 : 𝕜' →L[𝕜'] 𝕜') (-(w ^ 2)⁻¹)).restrictScalars 𝕜)) w :=
      hu.hasFDerivAt.comp w hinv
    rw [hv.fderiv]
    simp [mul_comm]
  · -- `u` is `w ↦ u w⁻¹` precomposed with the inversion, so neither map is differentiable.
    have hv : ¬DifferentiableAt 𝕜 (fun w ↦ u w⁻¹) w := fun hv ↦ hu <| by
      have hinv : DifferentiableAt 𝕜 (fun w : 𝕜' ↦ w⁻¹) w⁻¹ :=
        ((hasDerivAt_inv (inv_ne_zero hw)).hasFDerivAt.restrictScalars 𝕜).differentiableAt
      rw [← inv_inv w] at hv
      simpa [Function.comp_def] using hv.comp w⁻¹ hinv
    simp [fderiv_zero_of_not_differentiableAt hu, fderiv_zero_of_not_differentiableAt hv]

/-- The operator norm of the derivative of `w ↦ u w⁻¹` at `w ≠ 0` is that of the derivative of `u`
at `w⁻¹`, divided by `‖w‖ ^ 2`: the derivative of the inversion multiplies every vector by
`-(w ^ 2)⁻¹`, which scales all norms by the same factor. -/
theorem norm_fderiv_comp_inv {u : 𝕜' → F} {w : 𝕜'} (hw : w ≠ 0) :
    ‖fderiv 𝕜 (fun w ↦ u w⁻¹) w‖ = ‖fderiv 𝕜 u w⁻¹‖ / ‖w‖ ^ 2 := by
  have hc0 : -(w ^ 2)⁻¹ ≠ 0 := by simp [hw]
  have hc : ‖-(w ^ 2)⁻¹‖ = (‖w‖ ^ 2)⁻¹ := by rw [norm_neg, norm_inv, norm_pow]
  rw [div_eq_mul_inv, ← hc]
  refine le_antisymm (ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h ↦ ?_) ?_
  · rw [fderiv_comp_inv_apply hw, mul_assoc, ← norm_mul]
    exact (fderiv 𝕜 u w⁻¹).le_opNorm _
  · -- Every value of `fderiv u w⁻¹` is a value of the derivative of `w ↦ u w⁻¹`.
    have hle : ‖fderiv 𝕜 u w⁻¹‖ ≤ ‖fderiv 𝕜 (fun w ↦ u w⁻¹) w‖ * ‖-(w ^ 2)⁻¹‖⁻¹ := by
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h ↦ ?_
      have h' := fderiv_comp_inv_apply (𝕜 := 𝕜) (u := u) hw ((-(w ^ 2)⁻¹)⁻¹ * h)
      rw [← mul_assoc, mul_inv_cancel₀ hc0, one_mul] at h'
      rw [← h', mul_assoc, ← norm_inv, ← norm_mul]
      exact (fderiv 𝕜 (fun w ↦ u w⁻¹) w).le_opNorm _
    calc ‖fderiv 𝕜 u w⁻¹‖ * ‖-(w ^ 2)⁻¹‖
        ≤ ‖fderiv 𝕜 (fun w ↦ u w⁻¹) w‖ * ‖-(w ^ 2)⁻¹‖⁻¹ * ‖-(w ^ 2)⁻¹‖ := by gcongr
      _ = ‖fderiv 𝕜 (fun w ↦ u w⁻¹) w‖ := by field_simp

end TauCeti
