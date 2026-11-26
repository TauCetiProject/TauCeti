/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# Vector functionals on operator spaces

For vectors `ξ : E` and `ξ' : E'` in inner product spaces, the **vector functional**
`a ↦ ⟪ξ', a ξ⟫` is a continuous linear functional on the bounded operators `E →L[𝕜] E'`. Its
values are the matrix coefficients of an operator.

## Main declarations

* `TauCeti.vectorFunctional ξ ξ'`: the functional `a ↦ ⟪ξ', a ξ⟫` on `E →L[𝕜] E'`, with
  `TauCeti.vectorFunctional_apply`.
-/

public section

noncomputable section

open scoped InnerProductSpace

namespace TauCeti

variable {𝕜 E E' : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup E'] [InnerProductSpace 𝕜 E']

/-- The **vector functional** `a ↦ ⟪ξ', a ξ⟫` on the bounded operators `E →L[𝕜] E'`. -/
def vectorFunctional (ξ : E) (ξ' : E') : (E →L[𝕜] E') →L[𝕜] 𝕜 :=
  (innerSL 𝕜 ξ').comp (ContinuousLinearMap.apply 𝕜 E' ξ)

@[simp]
theorem vectorFunctional_apply (ξ : E) (ξ' : E') (a : E →L[𝕜] E') :
    vectorFunctional ξ ξ' a = ⟪ξ', a ξ⟫_𝕜 :=
  (rfl)

end TauCeti
