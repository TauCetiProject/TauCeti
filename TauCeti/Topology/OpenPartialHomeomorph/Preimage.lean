/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.OpenPartialHomeomorph.Basic

/-!
# Preimages computed in a family of charts

If every point of the preimage `f ⁻¹' P` lies in the source of one of a family of open partial
homeomorphisms `e x`, then the preimage is the union of the images under the inverses `(e x).symm`
of the sets `T x` of coordinates which `f ∘ (e x).symm` carries into `P`
(`OpenPartialHomeomorph.preimage_eq_iUnion_symm_image`).
-/

public section

open Set

namespace OpenPartialHomeomorph

variable {X Y E : Type*} [TopologicalSpace X] [TopologicalSpace E] {f : X → Y}

/-- **A preimage as a union of chart images.** Let `e x` be open partial homeomorphisms with
`T x ⊆ (e x).target` such that a coordinate `w ∈ (e x).target` lies in `T x` exactly when its
image under `f ∘ (e x).symm` lies in `P`. If every point of `f ⁻¹' P` lies in some source
`(e x).source`, then `f ⁻¹' P` is the union of the sets `(e x).symm '' T x`. -/
theorem preimage_eq_iUnion_symm_image {ι : Type*} {e : ι → OpenPartialHomeomorph X E}
    {P : Set Y} {T : ι → Set E} (hT : ∀ x, T x ⊆ (e x).target)
    (hiff : ∀ x, ∀ w ∈ (e x).target, w ∈ T x ↔ f ((e x).symm w) ∈ P)
    (hfull : ∀ z, f z ∈ P → z ∈ ⋃ x, (e x).source) :
    f ⁻¹' P = ⋃ x, (e x).symm '' T x := by
  ext z
  constructor
  · intro hz
    obtain ⟨x, hx⟩ := mem_iUnion.mp (hfull z hz)
    refine mem_iUnion.mpr ⟨x, e x z, (hiff x _ ((e x).map_source hx)).2 ?_, (e x).left_inv hx⟩
    rwa [(e x).left_inv hx]
  · intro hz
    obtain ⟨x, w, hw, rfl⟩ := mem_iUnion.mp hz
    exact (hiff x w (hT x hw)).1 hw

end OpenPartialHomeomorph
