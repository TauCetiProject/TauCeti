/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Tensor linearization of continuous trilinear maps

A continuous trilinear map induces a linear map on the algebraic tensor product of its
three input spaces. Its value on a pure tensor is the original trilinear evaluation.
-/

public noncomputable section

open scoped TensorProduct

namespace ContinuousLinearMap

variable {𝕜 E₁ E₂ E₃ F : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
  [SeminormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]
  [SeminormedAddCommGroup E₃] [NormedSpace 𝕜 E₃]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Linearize a continuous trilinear map on the tensor product of its three input spaces. -/
def trilinearTensorLinearMap (T : E₁ →L[𝕜] E₂ →L[𝕜] E₃ →L[𝕜] F) :
    (E₁ ⊗[𝕜] E₂) ⊗[𝕜] E₃ →ₗ[𝕜] F :=
  TensorProduct.lift ((ContinuousLinearMap.coeLM 𝕜).comp
    (TensorProduct.lift T.toLinearMap₁₂))

/-- The tensor linearization evaluates a pure tensor by evaluating the trilinear map. -/
@[simp]
theorem trilinearTensorLinearMap_tmul (T : E₁ →L[𝕜] E₂ →L[𝕜] E₃ →L[𝕜] F)
    (x : E₁) (y : E₂) (z : E₃) :
    trilinearTensorLinearMap T ((x ⊗ₜ[𝕜] y) ⊗ₜ[𝕜] z) = T x y z := by
  simp only [trilinearTensorLinearMap, TensorProduct.lift.tmul, LinearMap.comp_apply,
    coeLM_apply, coe_coe, toLinearMap₁₂_apply_apply_apply]

end ContinuousLinearMap
