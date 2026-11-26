/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# Closedness and completeness of projected subspaces

A subspace that admits an orthogonal projection is the range of a continuous idempotent and is
therefore closed. In a complete ambient inner-product space, such a subspace is itself complete.
Closedness, completeness and existence of an orthogonal projection are equivalent there, so
the intersection of two such subspaces admits an orthogonal projection
(`Submodule.HasOrthogonalProjection.inf`).

The sum `U ⊔ V` of two orthogonal subspaces admitting orthogonal projections equals
`(Uᗮ ⊓ Vᗮ)ᗮ` and is therefore closed (`Submodule.IsOrtho.sup_eq_orthogonal_inf_orthogonal`,
`Submodule.IsOrtho.isClosed_sup`).

The completeness observation also appears in
`ForTauCeti/Analysis/InnerProductSpace/ReducingSubspace.lean` of the
[AIQ-Kitware DKPS formalization](https://github.com/AIQ-Kitware/aiq-dkps-formalization)
(Kitware, Inc.; Apache-2.0).
-/

public section

namespace Submodule

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- A subspace admitting an orthogonal projection is closed. -/
theorem isClosed_of_hasOrthogonalProjection (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    IsClosed (U : Set E) := by
  rw [← U.range_starProjection]
  exact ContinuousLinearMap.IsIdempotentElem.isClosed_range U.isIdempotentElem_starProjection

/-- A subspace admitting an orthogonal projection is complete when the ambient space is. -/
theorem isComplete_coe_of_hasOrthogonalProjection [CompleteSpace E] (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] : IsComplete (U : Set E) :=
  (U.isClosed_of_hasOrthogonalProjection).isComplete

variable [CompleteSpace E]

/-- In a complete space, a subspace admitting an orthogonal projection is a complete space.

This is not an instance, since `HasOrthogonalProjection.ofCompleteSpace` goes the other way. -/
theorem completeSpace_coe_of_hasOrthogonalProjection (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] : CompleteSpace U :=
  U.isComplete_coe_of_hasOrthogonalProjection.completeSpace_coe

/-- In a complete space, a subspace has an orthogonal projection exactly when it is closed. -/
theorem hasOrthogonalProjection_iff_isClosed {U : Submodule 𝕜 E} :
    U.HasOrthogonalProjection ↔ IsClosed (U : Set E) :=
  ⟨fun _ ↦ U.isClosed_of_hasOrthogonalProjection, fun h ↦
    have := h.isComplete.completeSpace_coe
    .ofCompleteSpace U⟩

/-- In a complete space, a subspace has an orthogonal projection exactly when it is complete. -/
theorem hasOrthogonalProjection_iff_completeSpace {U : Submodule 𝕜 E} :
    U.HasOrthogonalProjection ↔ CompleteSpace U :=
  ⟨fun _ ↦ U.completeSpace_coe_of_hasOrthogonalProjection, fun _ ↦ .ofCompleteSpace U⟩

/-- In a complete space, the intersection of two subspaces admitting orthogonal projections is
closed and so admits an orthogonal projection. -/
instance HasOrthogonalProjection.inf (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] : (U ⊓ V).HasOrthogonalProjection :=
  hasOrthogonalProjection_iff_isClosed.mpr
    (U.isClosed_of_hasOrthogonalProjection.inter V.isClosed_of_hasOrthogonalProjection)

end Submodule

namespace Submodule.IsOrtho

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]

/-- The sum of two orthogonal subspaces admitting orthogonal projections is the orthogonal
complement of `Uᗮ ⊓ Vᗮ`. -/
theorem sup_eq_orthogonal_inf_orthogonal (h : U ⟂ V) : U ⊔ V = (Uᗮ ⊓ Vᗮ)ᗮ := by
  set M := (Uᗮ ⊓ Vᗮ)ᗮ
  have hU : U ≤ M := U.le_orthogonal_orthogonal.trans (orthogonal_le inf_le_left)
  have hV : V ≤ Uᗮ ⊓ M :=
    le_inf (isOrtho_iff_le.1 h.symm) (V.le_orthogonal_orthogonal.trans (orthogonal_le inf_le_right))
  -- Split `M` along `U`, then its part in `Uᗮ` along `V`; what is left is orthogonal to itself.
  have hM : Uᗮ ⊓ M = V := by
    rw [← sup_orthogonal_inf_of_hasOrthogonalProjection hV, ← inf_assoc, inf_comm Vᗮ,
      inf_orthogonal_eq_bot, sup_bot_eq]
  rw [← sup_orthogonal_inf_of_hasOrthogonalProjection hU, hM]

/-- The sum of two orthogonal subspaces admitting orthogonal projections is closed. -/
theorem isClosed_sup (h : U ⟂ V) : IsClosed ((U ⊔ V : Submodule 𝕜 E) : Set E) := by
  rw [h.sup_eq_orthogonal_inf_orthogonal]
  exact Submodule.isClosed_orthogonal _

end Submodule.IsOrtho
