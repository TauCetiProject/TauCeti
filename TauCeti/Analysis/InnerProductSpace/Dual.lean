/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# The Riesz isomorphism and `innerSL`

On a Hilbert space `E`, the Riesz isomorphism `InnerProductSpace.toDual 𝕜 E` is the map
`innerSL 𝕜 : E →L⋆[𝕜] StrongDual 𝕜 E`, upgraded to a conjugate-linear isometric equivalence. So its
inverse undoes `innerSL` on either side.

The operator `continuousLinearMapOfBilin B` representing a bounded sesquilinear form `B` through
`⟪continuousLinearMapOfBilin B v, w⟫ = B v w` is obtained by composing `B` with the inverse Riesz
isomorphism. It therefore depends continuously on `B`, and it is the identity for the inner
product itself.

## Main results

* `InnerProductSpace.toDual_symm_innerSL`: `(toDual 𝕜 E).symm (innerSL 𝕜 w) = w`.
* `InnerProductSpace.innerSL_toDual_symm`: `innerSL 𝕜 ((toDual 𝕜 E).symm q) = q`.
* `InnerProductSpace.continuous_continuousLinearMapOfBilin`: the representing operator depends
  continuously on the form.
* `InnerProductSpace.continuousLinearMapOfBilin_innerSL`: the inner product is represented by the
  identity.
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

/-- The operator representing a bounded sesquilinear form depends continuously on the form. -/
theorem continuous_continuousLinearMapOfBilin :
    Continuous (continuousLinearMapOfBilin : (E →L⋆[𝕜] E →L[𝕜] 𝕜) → E →L[𝕜] E) := by
  unfold continuousLinearMapOfBilin
  exact (ContinuousLinearMap.compSL _ _ _ _ _
    (toDual 𝕜 E).symm.toContinuousLinearEquiv.toContinuousLinearMap).continuous

/-- The inner product is represented by the identity operator. -/
@[simp]
theorem continuousLinearMapOfBilin_innerSL :
    continuousLinearMapOfBilin (innerSL 𝕜 : E →L⋆[𝕜] E →L[𝕜] 𝕜) = 1 :=
  ContinuousLinearMap.ext fun v => (unique_continuousLinearMapOfBilin _ fun w => by simp).symm

end InnerProductSpace
