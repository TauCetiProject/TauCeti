/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Basic
public import TauCeti.LinearAlgebra.TensorProduct.Trilinear

/-!
# Tensor linearization of continuous trilinear maps

Forget continuity and apply the algebraic threefold tensor linearization. Bundling this
conversion as a linear map allows seminorm computations to use its linearity laws.
-/

public noncomputable section

open scoped TensorProduct

namespace ContinuousLinearMap

variable {𝕜 E₁ E₂ E₃ F : Type*} [NormedField 𝕜]
  [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
  [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]
  [NormedAddCommGroup E₃] [NormedSpace 𝕜 E₃]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Linearize a continuous trilinear map on the algebraic tensor product of its inputs.
The conversion itself is linear, without finite-dimensionality or completeness assumptions. -/
def uncurryThreefold :
    (E₁ →L[𝕜] E₂ →L[𝕜] E₃ →L[𝕜] F) →ₗ[𝕜] (E₁ ⊗[𝕜] E₂) ⊗[𝕜] E₃ →ₗ[𝕜] F :=
  (TensorProduct.uncurryThreefold (RingHom.id 𝕜) E₁ E₂ E₃ F).comp
    ((LinearMap.compRight 𝕜 toLinearMap₁₂).comp (coeLM 𝕜))

/-- The linearization of a continuous trilinear map agrees with it on triple pure tensors. -/
@[simp]
theorem uncurryThreefold_tmul (T : E₁ →L[𝕜] E₂ →L[𝕜] E₃ →L[𝕜] F)
    (x : E₁) (y : E₂) (z : E₃) :
    uncurryThreefold T ((x ⊗ₜ[𝕜] y) ⊗ₜ[𝕜] z) = T x y z := by
  simp [uncurryThreefold]

end ContinuousLinearMap
