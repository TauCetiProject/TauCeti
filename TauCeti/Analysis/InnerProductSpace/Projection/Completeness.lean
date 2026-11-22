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
Closedness, completeness and existence of an orthogonal projection are equivalent there. The
orthogonal projection onto a projected subspace `U` sends any dense set to a set with closure `U`
(`Submodule.closure_image_starProjection_of_dense`).

The sum `U ⊔ V` of two orthogonal subspaces admitting orthogonal projections equals
`(Uᗮ ⊓ Vᗮ)ᗮ` and is therefore closed (`Submodule.IsOrtho.sup_eq_orthogonal_inf_orthogonal`,
`Submodule.IsOrtho.isClosed_sup`). It also admits an orthogonal projection equal to the sum of the
two projections (`Submodule.IsOrtho.hasOrthogonalProjection_sup`,
`Submodule.IsOrtho.starProjection_sup`).

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

/-- If `S` is dense in `E`, then the closure of the image of `S` under the orthogonal projection
onto `U` equals `U`. -/
theorem closure_image_starProjection_of_dense (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    {S : Set E} (hS : Dense S) :
    closure (U.starProjection '' S) = (U : Set E) := by
  refine Set.Subset.antisymm (closure_minimal ?_ U.isClosed_of_hasOrthogonalProjection) ?_
  · rintro _ ⟨x, -, rfl⟩
    exact U.starProjection_apply_mem x
  · have hrange : Set.range U.starProjection = (U : Set E) := by
      simpa only [LinearMap.coe_range, ContinuousLinearMap.coe_coe] using
        congrArg SetLike.coe U.range_starProjection
    rw [← hrange]
    exact U.starProjection.continuous.range_subset_closure_image_dense hS

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

/-- For orthogonal subspaces `U` and `V` admitting orthogonal projections, subtracting the sum of
their orthogonal projections of `x` from `x` leaves a vector orthogonal to `U ⊔ V`. -/
theorem sub_add_starProjection_mem_orthogonal (hUV : U.IsOrtho V) (x : E) :
    x - (U.starProjection x + V.starProjection x) ∈ (U ⊔ V)ᗮ := by
  rw [← Submodule.inf_orthogonal, Submodule.mem_inf]
  refine ⟨?_, ?_⟩
  · have hVx : V.starProjection x ∈ Uᗮ := hUV.symm (V.starProjection_apply_mem x)
    simpa only [sub_add_eq_sub_sub] using
      Submodule.sub_mem _ (U.sub_starProjection_mem_orthogonal x) hVx
  · have hUx : U.starProjection x ∈ Vᗮ := hUV (U.starProjection_apply_mem x)
    simpa only [sub_add_eq_sub_sub, sub_right_comm] using
      Submodule.sub_mem _ (V.sub_starProjection_mem_orthogonal x) hUx

/-- The sum of two orthogonal subspaces admitting orthogonal projections admits an orthogonal
projection. -/
theorem hasOrthogonalProjection_sup (hUV : U.IsOrtho V) :
    (U ⊔ V).HasOrthogonalProjection :=
  ⟨fun x ↦ ⟨U.starProjection x + V.starProjection x,
    Submodule.add_mem_sup (U.starProjection_apply_mem x) (V.starProjection_apply_mem x),
    hUV.sub_add_starProjection_mem_orthogonal x⟩⟩

/-- The orthogonal projection onto the sum of two orthogonal subspaces is the sum of their
orthogonal projections. -/
theorem starProjection_sup (hUV : U.IsOrtho V) :
    letI := hUV.hasOrthogonalProjection_sup
    (U ⊔ V).starProjection = U.starProjection + V.starProjection := by
  let := hUV.hasOrthogonalProjection_sup
  ext x
  exact Submodule.eq_starProjection_of_mem_orthogonal
    (Submodule.add_mem_sup (U.starProjection_apply_mem x) (V.starProjection_apply_mem x))
    (hUV.sub_add_starProjection_mem_orthogonal x)

end Submodule.IsOrtho
