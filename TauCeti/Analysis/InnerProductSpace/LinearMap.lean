/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# The inner product as a continuous sesquilinear map

Forgetting the continuity of the inner product `innerSL 𝕜 : E →L⋆[𝕜] E →L[𝕜] 𝕜` gives the
sesquilinear map `innerₛₗ 𝕜` (`ContinuousLinearMap.toLinearMap₁₂_innerSL`); over `ℝ` this is the
bilinear form `innerₗ E` (`ContinuousLinearMap.toLinearMap₁₂_innerSL_real`). Together with the
conversion rules of `TauCeti/Topology/Algebra/Module/Spaces/ContinuousLinearMap.lean`, this turns
metric lowerings `innerSL ℝ ∘L T` into the bilinear forms `innerₗ E ∘ₗ T`, to which the algebraic
API of bilinear forms applies.
-/

public section

namespace ContinuousLinearMap

/-- Forgetting continuity of the inner product gives the sesquilinear map `innerₛₗ 𝕜`. -/
@[simp]
theorem toLinearMap₁₂_innerSL {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] :
    toLinearMap₁₂ (innerSL 𝕜 : E →L⋆[𝕜] E →L[𝕜] 𝕜) = innerₛₗ 𝕜 :=
  LinearMap.ext₂ fun _ _ ↦ by
    rw [toLinearMap₁₂_apply_apply_apply, innerSL_apply_apply, innerₛₗ_apply_apply]

/-- Forgetting continuity of the real inner product gives the bilinear form `innerₗ E`: the real
case of `toLinearMap₁₂_innerSL`, whose right-hand side `innerₛₗ ℝ` is `innerₗ E` only by
unfolding `innerₗ`. -/
theorem toLinearMap₁₂_innerSL_real {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    toLinearMap₁₂ (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ) = innerₗ E :=
  toLinearMap₁₂_innerSL

end ContinuousLinearMap
