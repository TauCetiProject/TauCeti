/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Adjoint
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Compact

/-!
# Compactness of Hilbert-space adjoints

Between Hilbert spaces the compact operators are closed under adjoints. Together with the
two-sided ideal property (`IsCompactOperator.mul_left`, `IsCompactOperator.mul_right` in
`TauCeti.Analysis.Normed.Operator.Compact.Basic`), this makes the compact operators on a Hilbert
space a two-sided `*`-ideal. These are the algebraic rules used to manipulate the compactness
conditions in the definition of a Fredholm module, such as compactness of commutators `[F, a]` and
of the defects `(F² - 1) a`. The Banach-space dual of a compact operator is treated separately in
`TauCeti.Analysis.Normed.Operator.Compact.Adjoint`.

The adjoint statement uses approximation numbers: an operator into a Hilbert space is compact
exactly when its approximation numbers tend to zero, and an operator and its adjoint have the same
approximation numbers.

## Main declarations

* `IsCompactOperator.adjoint`: the Hilbert-space adjoint of a compact operator is compact.
* `ContinuousLinearMap.isCompactOperator_adjoint_iff`: `T†` is compact exactly when `T` is.
* `IsCompactOperator.star`: on a Hilbert space, `star T` is compact when `T` is.
* `ContinuousLinearMap.isCompactOperator_star_iff`: `star T` is compact exactly when `T` is.
* `IsCompactOperator.conjStarAlgEquiv`: conjugating by a unitary preserves compactness.
* `TauCeti.compactOperatorStarSubalgebra`: the closed nonunital `⋆`-subalgebra of compact operators
  on a Hilbert space.
-/

public section

open scoped InnerProduct

namespace IsCompactOperator

section Adjoint

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- **Compactness of the adjoint.** The Hilbert-space adjoint of a compact operator is compact. -/
theorem adjoint {T : E →L[𝕜] F} (hT : IsCompactOperator T) : IsCompactOperator (T†) := by
  rw [ContinuousLinearMap.isCompactOperator_iff_tendsto_singularValue] at hT ⊢
  rwa [funext (ContinuousLinearMap.singularValue_adjoint T)]

/-- On a Hilbert space, the star of a compact operator, its adjoint, is compact. -/
theorem star {T : E →L[𝕜] E} (hT : IsCompactOperator T) : IsCompactOperator ⇑(star T) := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  exact hT.adjoint

/-- Conjugating a compact operator by a unitary `U : E ≃ F` gives a compact operator
`U T U*`. -/
theorem conjStarAlgEquiv {T : E →L[𝕜] E} (hT : IsCompactOperator T) (U : E ≃ₗᵢ[𝕜] F) :
    IsCompactOperator (U.conjStarAlgEquiv T) := by
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply, ContinuousLinearMap.coe_comp,
    ContinuousLinearMap.coe_comp]
  exact (hT.comp_clm _).clm_comp _

end Adjoint

end IsCompactOperator

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- A bounded operator between Hilbert spaces is compact exactly when its adjoint is. -/
@[simp]
theorem isCompactOperator_adjoint_iff {T : E →L[𝕜] F} :
    IsCompactOperator (T†) ↔ IsCompactOperator T :=
  ⟨fun h ↦ by simpa using h.adjoint, IsCompactOperator.adjoint⟩

/-- On a Hilbert space, an operator is compact exactly when its star, its adjoint, is. -/
@[simp]
theorem isCompactOperator_star_iff {T : E →L[𝕜] E} :
    IsCompactOperator ⇑(star T) ↔ IsCompactOperator T := by
  rw [star_eq_adjoint, isCompactOperator_adjoint_iff]

end ContinuousLinearMap

namespace TauCeti

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- The compact operators on a Hilbert space `E` form a nonunital `⋆`-subalgebra of `E →L[𝕜] E`. -/
def compactOperatorStarSubalgebra (𝕜 E : Type*) [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E] :
    NonUnitalStarSubalgebra 𝕜 (E →L[𝕜] E) where
  toSubmodule := compactOperator (RingHom.id 𝕜) E E
  mul_mem' {_ g} hf _ := IsCompactOperator.comp_clm hf g
  star_mem' {_} hf := IsCompactOperator.star hf

/-- Membership in `compactOperatorStarSubalgebra 𝕜 E` is `IsCompactOperator`. -/
@[simp]
theorem mem_compactOperatorStarSubalgebra_iff {T : E →L[𝕜] E} :
    T ∈ compactOperatorStarSubalgebra 𝕜 E ↔ IsCompactOperator T :=
  Iff.rfl

/-- The underlying `𝕜`-submodule of `compactOperatorStarSubalgebra 𝕜 E` is `compactOperator`. -/
@[simp]
theorem toSubmodule_compactOperatorStarSubalgebra :
    (compactOperatorStarSubalgebra 𝕜 E).toSubmodule = compactOperator (RingHom.id 𝕜) E E :=
  (rfl)

/-- The `⋆`-subalgebra of compact operators on a Hilbert space is norm-closed. -/
instance instIsClosedCompactOperatorStarSubalgebra :
    IsClosed (compactOperatorStarSubalgebra 𝕜 E : Set (E →L[𝕜] E)) :=
  isClosed_setOfPred_isCompactOperator

end TauCeti
