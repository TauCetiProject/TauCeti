/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousOn

/-!
# Injective maps, open embeddings, and punctured neighbourhoods

An injective map continuous at `x` sends the punctured neighbourhoods of `x` into the punctured
neighbourhoods of `f x` (`ContinuousAt.tendsto_nhdsNE`), and an open embedding sends the punctured
neighbourhood filter of `x` onto that of `f x` (`Topology.IsOpenEmbedding.map_nhdsNE_eq`). For the
inclusion of a subspace, such as `Subtype.val` or `Set.inclusion`, this pulls back statements
holding on a punctured neighbourhood in the ambient space to the subspace
(`TauCeti.tendsto_subtype_val_nhdsNE`). A map avoids a value `y` on a punctured neighbourhood of
`x` if and only if `x` has an open neighbourhood meeting `f ⁻¹' {y}` at most in `x`
(`TauCeti.eventually_nhdsNE_ne_iff_exists_isOpen`).
-/

public section

open Filter Function Topology

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] {f : α → β} {x : α}

/-- An injective map continuous at `x` sends punctured neighbourhoods of `x` to punctured
neighbourhoods of `f x`. -/
theorem ContinuousAt.tendsto_nhdsNE (hf : ContinuousAt f x) (hinj : Injective f) :
    Tendsto f (𝓝[≠] x) (𝓝[≠] (f x)) :=
  hf.continuousWithinAt.tendsto_nhdsWithin fun _ hy hxy ↦ hy (hinj hxy)

/-- An open embedding sends the punctured neighbourhood filter of `x` onto the punctured
neighbourhood filter of `f x`. -/
theorem Topology.IsOpenEmbedding.map_nhdsNE_eq (hf : IsOpenEmbedding f) (x : α) :
    map f (𝓝[≠] x) = 𝓝[≠] (f x) := by
  simpa [← Set.image_singleton, hf.injective.preimage_image] using
    hf.map_nhdsWithin_preimage_eq {f x}ᶜ x

namespace TauCeti

/-- The inclusion of a subtype sends punctured neighbourhoods of `x` to punctured neighbourhoods
of `↑x`. -/
theorem tendsto_subtype_val_nhdsNE {p : α → Prop} (x : Subtype p) :
    Tendsto (Subtype.val : Subtype p → α) (𝓝[≠] x) (𝓝[≠] (x : α)) :=
  continuous_subtypeVal.continuousAt.tendsto_nhdsNE Subtype.val_injective

/-- A map `f` avoids `y` on a punctured neighbourhood of `x` if and only if `x` has an open
neighbourhood meeting `f ⁻¹' {y}` at most in `x`. -/
theorem eventually_nhdsNE_ne_iff_exists_isOpen {α β : Type*} [TopologicalSpace α] {f : α → β}
    {x : α} {y : β} :
    (∀ᶠ z in 𝓝[≠] x, f z ≠ y) ↔ ∃ U : Set α, IsOpen U ∧ x ∈ U ∧ ∀ z ∈ U, f z = y → z = x := by
  rw [eventually_nhdsWithin_iff, eventually_nhds_iff]
  exact ⟨fun ⟨U, hU, hUo, hxU⟩ ↦
      ⟨U, hUo, hxU, fun z hz hfz ↦ by_contra fun hzx ↦ hU z hz hzx hfz⟩,
    fun ⟨U, hUo, hxU, hU⟩ ↦ ⟨U, fun z hz hzx hfz ↦ hzx (hU z hz hfz), hUo, hxU⟩⟩

end TauCeti
