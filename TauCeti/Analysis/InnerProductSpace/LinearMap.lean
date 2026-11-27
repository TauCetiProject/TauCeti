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
bilinear form `innerₗ E`, which is defined as `innerₛₗ ℝ`. Together with the conversion rules
of `TauCeti/Topology/Algebra/Module/Spaces/ContinuousLinearMap.lean`, this turns metric lowerings
`innerSL ℝ ∘L T` into the bilinear forms `innerₗ E ∘ₗ T`, to which the algebraic API of bilinear
forms applies.

An operator `T` whose matrix coefficients satisfy `‖⟪η, T ξ⟫‖ ≤ C ‖ξ‖ ‖η‖` has norm at most `C`
(`ContinuousLinearMap.opNorm_le_of_norm_inner_le`).
-/

public section

open scoped InnerProductSpace

namespace ContinuousLinearMap

/-- Forgetting continuity of the inner product gives the sesquilinear map `innerₛₗ 𝕜`. -/
@[simp]
theorem toLinearMap₁₂_innerSL {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] :
    toLinearMap₁₂ (innerSL 𝕜 : E →L⋆[𝕜] E →L[𝕜] 𝕜) = innerₛₗ 𝕜 :=
  LinearMap.ext₂ fun _ _ ↦ by
    rw [toLinearMap₁₂_apply_apply_apply, innerSL_apply_apply, innerₛₗ_apply_apply]

/-- An operator whose matrix coefficients satisfy `‖⟪η, T ξ⟫‖ ≤ C ‖ξ‖ ‖η‖` has norm at most `C`.
This is `ContinuousLinearMap.opNorm_le_of_re_inner_le` with the bound on all vectors. -/
theorem opNorm_le_of_norm_inner_le {𝕜 G G' : Type*} [RCLike 𝕜] [NormedAddCommGroup G]
    [InnerProductSpace 𝕜 G] [NormedAddCommGroup G'] [InnerProductSpace 𝕜 G']
    {T : G →L[𝕜] G'} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ ξ η, ‖⟪η, T ξ⟫_𝕜‖ ≤ C * ‖ξ‖ * ‖η‖) : ‖T‖ ≤ C :=
  opNorm_le_of_re_inner_le hC fun ξ η hξ hη ↦ by
    rw [← inner_conj_symm, RCLike.conj_re]
    simpa [hξ, hη] using (RCLike.re_le_norm _).trans (h ξ η)

end ContinuousLinearMap
