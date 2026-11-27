/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.RingTheory.Finiteness.Cofinite
-- Private: closedness of subspaces containing a closed subspace of finite codimension is used only
-- in a proof.
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Closedness and completeness of projected subspaces

A subspace that admits an orthogonal projection is the range of a continuous idempotent and is
therefore closed. In a complete ambient inner-product space, such a subspace is itself complete.
Closedness, completeness and existence of an orthogonal projection are equivalent there, so
the intersection of two such subspaces admits an orthogonal projection
(`Submodule.HasOrthogonalProjection.inf`).

Every subspace containing a closed subspace `K` of finite codimension is closed, so it is the
whole space as soon as its orthogonal complement is trivial. Hence `K ⊔ S = ⊤` once the only
vector orthogonal to both `K` and `S` is zero (`Submodule.sup_eq_top_of_isClosed_of_coFG`): the
form in which transversality arguments show that a Fredholm range and a space of variations
together span.

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

/-- **A closed subspace of finite codimension and a subspace span when no nonzero vector is
orthogonal to both.** In a complete space, the sum `K ⊔ S` contains the closed subspace `K` of
finite codimension, so it is closed; it is therefore everything once its orthogonal complement
`Kᗮ ⊓ Sᗮ` is trivial. -/
theorem sup_eq_top_of_isClosed_of_coFG {K S : Submodule 𝕜 E} (hK : IsClosed (K : Set E))
    (hKf : K.CoFG) (h : ∀ v ∈ Kᗮ, v ∈ Sᗮ → v = 0) : K ⊔ S = ⊤ := by
  -- `CoFG` is the finite dimensionality of the quotient; put it in scope as an instance.
  have : FiniteDimensional 𝕜 (E ⧸ K) := hKf
  have := hasOrthogonalProjection_iff_isClosed.2
    (isClosed_mono_of_finiteDimensional_quotient hK (le_sup_left (b := S)))
  rw [← orthogonal_eq_bot_iff, eq_bot_iff, ← inf_orthogonal]
  exact fun v hv ↦ h v hv.1 hv.2

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
