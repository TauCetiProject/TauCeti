/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars

/-!
# Derivative of a map precomposed with inversion

For a map `u` out of a normed field `𝕜'`, differentiable over a subfield `𝕜` at `w⁻¹`, the
derivative of `w ↦ u w⁻¹` at `w ≠ 0` is the derivative of `u` at `w⁻¹` precomposed with
multiplication by `-(w ^ 2)⁻¹`, the derivative of the inversion. This is how a map near infinity
is read off in the coordinate `w = z⁻¹` near zero.
-/

public section

namespace TauCeti

variable {𝕜 𝕜' F : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜']
  [NormedAlgebra 𝕜 𝕜'] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The derivative of `w ↦ u w⁻¹` at `w ≠ 0` is the derivative of `u` at `w⁻¹` precomposed with
multiplication by `-(w ^ 2)⁻¹`. -/
theorem fderiv_comp_inv_apply {u : 𝕜' → F} {w : 𝕜'} (hw : w ≠ 0)
    (hu : DifferentiableAt 𝕜 u w⁻¹) (h : 𝕜') :
    fderiv 𝕜 (fun w ↦ u w⁻¹) w h = fderiv 𝕜 u w⁻¹ (-(w ^ 2)⁻¹ * h) := by
  have hinv : HasFDerivAt (fun w : 𝕜' ↦ w⁻¹)
      ((ContinuousLinearMap.smulRight (1 : 𝕜' →L[𝕜'] 𝕜') (-(w ^ 2)⁻¹)).restrictScalars 𝕜) w :=
    (hasDerivAt_inv hw).hasFDerivAt.restrictScalars 𝕜
  have hv : HasFDerivAt (fun w ↦ u w⁻¹) ((fderiv 𝕜 u w⁻¹).comp
      ((ContinuousLinearMap.smulRight (1 : 𝕜' →L[𝕜'] 𝕜') (-(w ^ 2)⁻¹)).restrictScalars 𝕜)) w :=
    hu.hasFDerivAt.comp w hinv
  rw [hv.fderiv]
  simp [mul_comm]

end TauCeti
