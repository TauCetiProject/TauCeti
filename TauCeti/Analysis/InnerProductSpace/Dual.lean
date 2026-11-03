/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# The Riesz isomorphism and `innerSL`

On a Hilbert space `E`, the Riesz isomorphism `InnerProductSpace.toDual 𝕜 E` is the map
`innerSL 𝕜 : E →L⋆[𝕜] StrongDual 𝕜 E`, upgraded to a conjugate-linear isometric equivalence. So its
inverse undoes `innerSL` on either side.

The Riesz operator `InnerProductSpace.continuousLinearMapOfBilin B` of a sesquilinear form `B`
depends continuously on `B`. Over `ℝ`, the Riesz operator of a bilinear form `k` is natural:
pulling `k` back along a linear isometry equivalence conjugates it.

## Main results

* `InnerProductSpace.toDual_symm_innerSL`: `(toDual 𝕜 E).symm (innerSL 𝕜 w) = w`.
* `InnerProductSpace.innerSL_toDual_symm`: `innerSL 𝕜 ((toDual 𝕜 E).symm q) = q`.
* `InnerProductSpace.continuous_continuousLinearMapOfBilin`: the Riesz operator depends
  continuously on the sesquilinear form.
* `ContinuousLinearMap.continuousLinearMapOfBilin_bilinearComp`: pulling a real bilinear form back
  along a linear isometry equivalence conjugates its Riesz operator.
-/

public section

namespace InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- The inverse Riesz isomorphism sends the functional `innerSL 𝕜 w = ⟪w, ·⟫` back to `w`. -/
@[simp]
theorem toDual_symm_innerSL (w : E) : (toDual 𝕜 E).symm (innerSL 𝕜 w) = w :=
  (toDual 𝕜 E).symm_apply_eq.2 (by ext; simp)

/-- The functional `⟪(toDual 𝕜 E).symm q, ·⟫` represented by the inverse Riesz isomorphism is
`q`. -/
@[simp]
theorem innerSL_toDual_symm (q : StrongDual 𝕜 E) : innerSL 𝕜 ((toDual 𝕜 E).symm q) = q := by
  ext v; simp [toDual_symm_apply]

/-- The Riesz operator `continuousLinearMapOfBilin B` depends continuously on the sesquilinear
form `B`: it is the composite of `B` with the inverse Riesz isomorphism. -/
theorem continuous_continuousLinearMapOfBilin :
    Continuous (continuousLinearMapOfBilin (𝕜 := 𝕜) (E := E)) :=
  (ContinuousLinearMap.compSL _ _ _ _ _
    (toDual 𝕜 E).symm.toContinuousLinearEquiv.toContinuousLinearMap).continuous

end InnerProductSpace

namespace ContinuousLinearMap

open InnerProductSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- Pulling a bilinear form `k` on `F` back along a linear isometry equivalence `e : E ≃ₗᵢ[ℝ] F`
conjugates its Riesz operator by `e`. -/
theorem continuousLinearMapOfBilin_bilinearComp (e : E ≃ₗᵢ[ℝ] F) (k : F →L[ℝ] F →L[ℝ] ℝ) :
    continuousLinearMapOfBilin (𝕜 := ℝ) (k.bilinearComp (e : E →L[ℝ] F) (e : E →L[ℝ] F)) =
      e.symm.conjStarAlgEquiv (continuousLinearMapOfBilin (𝕜 := ℝ) k) := by
  ext v
  refine ext_inner_right ℝ fun w ↦ ?_
  rw [continuousLinearMapOfBilin_apply, bilinearComp_apply,
    LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, LinearIsometryEquiv.symm_symm,
    ← LinearIsometryEquiv.inner_map_map e, e.apply_symm_apply, continuousLinearMapOfBilin_apply]
  -- Only the coercion of `e` to a continuous linear map remains to be unfolded.
  simp

end ContinuousLinearMap
