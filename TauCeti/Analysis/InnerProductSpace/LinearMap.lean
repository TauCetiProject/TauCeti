/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# The real inner product as a continuous bilinear map

Forgetting the continuity of the real inner product `innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ` gives the
bilinear form `innerₗ E` (`toLinearMap₁₂_innerSL`). Together with the conversion rules of
`TauCeti/Topology/Algebra/Module/Spaces/ContinuousLinearMap.lean`, this turns metric lowerings
`innerSL ℝ ∘L T` into the bilinear forms `innerₗ E ∘ₗ T`, to which the algebraic API of bilinear
forms applies.
-/

public section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Forgetting continuity of the real inner product gives the bilinear form `innerₗ E`. -/
@[simp]
theorem toLinearMap₁₂_innerSL :
    ContinuousLinearMap.toLinearMap₁₂ (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ) = innerₗ E :=
  LinearMap.ext₂ fun _ _ ↦ by
    rw [ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply, innerSL_apply_apply,
      innerₗ_apply_apply]
