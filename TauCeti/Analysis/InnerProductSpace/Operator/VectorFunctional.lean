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
* `ContinuousLinearMap.opNorm_le_of_norm_inner_le`: an operator whose matrix coefficients
  satisfy `‖⟪η, T ξ⟫‖ ≤ C ‖ξ‖ ‖η‖` has norm at most `C`.
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

namespace ContinuousLinearMap

variable {𝕜 G G' : Type*} [RCLike 𝕜] [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
  [NormedAddCommGroup G'] [InnerProductSpace 𝕜 G']

/-- An operator whose matrix coefficients satisfy `‖⟪η, T ξ⟫‖ ≤ C ‖ξ‖ ‖η‖` has norm at most `C`.
This is `ContinuousLinearMap.opNorm_le_of_re_inner_le` with the bound on all vectors. -/
theorem opNorm_le_of_norm_inner_le {T : G →L[𝕜] G'} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ ξ η, ‖⟪η, T ξ⟫_𝕜‖ ≤ C * ‖ξ‖ * ‖η‖) : ‖T‖ ≤ C :=
  opNorm_le_of_re_inner_le hC fun ξ η hξ hη ↦ by
    rw [← inner_conj_symm, RCLike.conj_re]
    simpa [hξ, hη] using (RCLike.re_le_norm _).trans (h ξ η)

end ContinuousLinearMap
