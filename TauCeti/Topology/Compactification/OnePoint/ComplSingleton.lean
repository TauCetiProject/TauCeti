/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Compactification.OnePoint.Basic

/-!
# One-point compactifications of punctured compact spaces

For a compact Hausdorff space `K` and any point `x₀ : K`, the punctured subspace
`{x : K // x ≠ x₀}` embeds into `K` with range `{x₀}ᶜ`, so Mathlib's
`OnePoint.equivOfIsEmbeddingOfRangeEq` identifies `OnePoint {x : K // x ≠ x₀}` homeomorphically with
`K` by sending `∞` to `x₀` (`TauCeti.onePointComplSingletonHomeomorph`), including when `K` is a
singleton or `x₀` is isolated.

On any compact space `K` (without Hausdorff assumptions), the subtype inclusion
`{x : K // x ≠ x₀} → K` tends to `x₀` along the cocompact filter
(`TauCeti.tendsto_subtypeVal_cocompact_nhds`).
-/

@[expose] public section

open Filter Set Topology OnePoint

namespace TauCeti

section Hausdorff

variable {K : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K]

/-- Every compact Hausdorff space `K` is canonically homeomorphic to the one-point extension
`OnePoint {x : K // x ≠ x₀}` of the complement of any point `x₀ : K`, with `∞` sent to `x₀`
(including when `K` is a singleton or `x₀` is isolated). -/
noncomputable def onePointComplSingletonHomeomorph (x₀ : K) : OnePoint {x : K // x ≠ x₀} ≃ₜ K :=
  equivOfIsEmbeddingOfRangeEq x₀ Subtype.val Topology.IsEmbedding.subtypeVal <| by
    ext x
    simp

/-- `onePointComplSingletonHomeomorph x₀` sends a finite point `x` to `x.1`. -/
@[simp]
theorem onePointComplSingletonHomeomorph_apply_coe (x₀ : K) (x : {x : K // x ≠ x₀}) :
    onePointComplSingletonHomeomorph x₀ x = x.1 := (rfl)

/-- `onePointComplSingletonHomeomorph x₀` sends `∞` to `x₀`. -/
@[simp]
theorem onePointComplSingletonHomeomorph_apply_infty (x₀ : K) :
    onePointComplSingletonHomeomorph x₀ ∞ = x₀ := (rfl)

/-- The inverse of `onePointComplSingletonHomeomorph x₀` sends `x₀` to `∞`. -/
@[simp]
theorem onePointComplSingletonHomeomorph_symm_apply_self (x₀ : K) :
    (onePointComplSingletonHomeomorph x₀).symm x₀ = ∞ := by
  rw [Homeomorph.symm_apply_eq]
  rfl

/-- Away from `x₀`, the inverse of `onePointComplSingletonHomeomorph x₀` embeds `x` into
`OnePoint {x : K // x ≠ x₀}`. -/
theorem onePointComplSingletonHomeomorph_symm_apply_of_ne {x₀ x : K} (hx : x ≠ x₀) :
    (onePointComplSingletonHomeomorph x₀).symm x = (⟨x, hx⟩ : {x : K // x ≠ x₀}) := by
  rw [Homeomorph.symm_apply_eq]
  rfl

/-- On a punctured point `x : {x : K // x ≠ x₀}`, `(onePointComplSingletonHomeomorph x₀).symm x.1`
recovers `x`. -/
@[simp]
theorem onePointComplSingletonHomeomorph_symm_apply_coe (x₀ : K) (x : {x : K // x ≠ x₀}) :
    (onePointComplSingletonHomeomorph x₀).symm x.1 = x :=
  onePointComplSingletonHomeomorph_symm_apply_of_ne x.2

end Hausdorff

/-- In a compact space `K`, the inclusion of `{x : K // x ≠ x₀}` into `K` tends to `x₀` along the
cocompact filter. -/
theorem tendsto_subtypeVal_cocompact_nhds {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (x₀ : K) :
    Tendsto (Subtype.val : {x : K // x ≠ x₀} → K) (cocompact {x : K // x ≠ x₀}) (𝓝 x₀) := by
  rw [hasBasis_cocompact.tendsto_left_iff]
  intro N hN
  obtain ⟨U, hU₁, hU₂, hU₃⟩ := mem_nhds_iff.mp hN
  refine ⟨Subtype.val ⁻¹' Uᶜ, ?_, by simpa using (mapsTo_preimage Subtype.val U).mono_right hU₁⟩
  have hsub : Uᶜ ⊆ range (Subtype.val : {x : K // x ≠ x₀} → K) := fun x hx ↦
    ⟨⟨x, fun h ↦ hx (h ▸ hU₃)⟩, rfl⟩
  rw [Topology.IsEmbedding.subtypeVal.isCompact_iff, image_preimage_eq_iff.mpr hsub]
  exact hU₂.isClosed_compl.isCompact

end TauCeti
