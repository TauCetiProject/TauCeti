/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import TauCeti.Analysis.Calculus.ImplicitFunctionTheorem

/-!
# Linear coordinates of a surjective linear map on inner product spaces

For a surjective linear map `A` between finite-dimensional real inner product spaces, let
`x ↦ (A x, P x)` be its linear coordinates `ContinuousLinearMap.linearCoord`, with `P` a projection
onto `ker A`, and `s` its linear section `ContinuousLinearMap.linearSection`. This file records
their adjoint forms.

## Main results

* `ContinuousLinearMap.adjoint_linearSection_adjoint_apply`: `sᵀ Aᵀ = id`.
* `ContinuousLinearMap.inner_eq_inner_linearCoord`: `⟪x, ζ⟫ = ⟪A x, sᵀ ζ⟫ + ⟪P x, ζ⟫`, the
  decomposition `x = s (A x) + P x` paired with `ζ`.
-/

public section

namespace ContinuousLinearMap

open scoped InnerProduct RealInnerProductSpace

variable {E E' : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E']
  (A : E →L[ℝ] E') (hA : Function.Surjective A)

/-- `sᵀ` is a left inverse of `Aᵀ`, where `s` is the linear section `linearSection` of `A`. -/
@[simp]
theorem adjoint_linearSection_adjoint_apply (η : E') :
    ((A.linearSection hA)†) ((A†) η) = η := by
  rw [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.comp_linearSection,
    ContinuousLinearMap.adjoint_id, ContinuousLinearMap.id_apply]

/-- A vector `ζ` pairs with `x` as `sᵀ ζ` with `A x` plus `ζ` with the `ker A`-coordinate of
`x`, where `s` is the linear section `linearSection` of `A`. -/
theorem inner_eq_inner_linearCoord (x ζ : E) :
    ⟪x, ζ⟫ = ⟪A x, ((A.linearSection hA)†) ζ⟫ + ⟪((A.linearCoord hA x).2 : E), ζ⟫ := by
  conv_lhs => rw [← A.linearSection_add_linearCoord_snd hA x]
  rw [inner_add_left, ContinuousLinearMap.adjoint_inner_right]

end ContinuousLinearMap
