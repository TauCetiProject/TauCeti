/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.OpenPartialHomeomorph.Continuity

/-!
# Continuity and punctured neighbourhoods under open partial homeomorphisms

An open partial homeomorphism identifies a neighbourhood of a point of its source with a
neighbourhood of its image, so a point of the source is not isolated as soon as its image is not
(`OpenPartialHomeomorph.nhdsNE_neBot`). For instance, no point in the source of a chart into a
nontrivially normed field is isolated. Being injective and continuous on its source, it sends the
punctured neighbourhoods of a point of its source to those of the image
(`OpenPartialHomeomorph.tendsto_nhdsNE`).

A continuous function on the target that is constant off a compact subset of the target, read
through the open partial homeomorphism on its source and extended by that constant, is continuous
on a Hausdorff domain (`OpenPartialHomeomorph.continuous_ite_source_of_eq_off_compact`). This
transplants a compactly supported function on a chart to the whole space.
-/

public section

open Filter Set Topology

namespace OpenPartialHomeomorph

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A point of the source of an open partial homeomorphism is not isolated if its image is not. -/
theorem nhdsNE_neBot (e : OpenPartialHomeomorph X Y) {x : X} (hx : x ∈ e.source)
    [(𝓝[≠] (e x)).NeBot] : (𝓝[≠] x).NeBot := by
  have hmap := e.symm.map_nhdsWithin_eq (e.map_source hx) {e x}ᶜ
  rw [e.left_inv hx] at hmap
  have hne : (map e.symm (𝓝[≠] (e x))).NeBot := inferInstance
  refine (hmap ▸ hne).mono (nhdsWithin_mono _ ?_)
  rintro _ ⟨w, ⟨hw, hwx⟩, rfl⟩ hwx'
  exact hwx (by rw [← mem_singleton_iff.1 hwx', e.right_inv hw]; exact mem_singleton w)

/-- An open partial homeomorphism sends the punctured neighbourhoods of a point of its source to
the punctured neighbourhoods of its image. -/
theorem tendsto_nhdsNE (e : OpenPartialHomeomorph X Y) {x : X} (hx : x ∈ e.source) :
    Tendsto e (𝓝[≠] x) (𝓝[≠] (e x)) :=
  tendsto_nhdsWithin_iff.mpr
    ⟨(e.continuousAt hx).tendsto.mono_left nhdsWithin_le_nhds, e.eventually_ne_nhdsWithin hx⟩

/-- A continuous function `g` equal to `c` off a compact subset `K` of the target of `e`, read
through `e` on its source and extended by `c`, is continuous when the domain is Hausdorff. -/
theorem continuous_ite_source_of_eq_off_compact [T2Space X] (e : OpenPartialHomeomorph X Y)
    [∀ z, Decidable (z ∈ e.source)] {Z : Type*} [TopologicalSpace Z] {g : Y → Z}
    (hg : Continuous g) {K : Set Y} (hK : IsCompact K) (hKt : K ⊆ e.target) {c : Z}
    (hgK : ∀ z ∉ K, g z = c) :
    Continuous fun z : X => if z ∈ e.source then g (e z) else c := by
  have hKclosed : IsClosed (e.symm '' K) :=
    (hK.image_of_continuousOn (e.continuousOn_symm.mono hKt)).isClosed
  refine continuous_iff_continuousAt.2 fun z => ?_
  by_cases hzs : z ∈ e.source
  · refine (hg.continuousAt.comp (e.continuousAt hzs)).congr ?_
    filter_upwards [e.open_source.mem_nhds hzs] with w hw
    simp [hw]
  · have hz : z ∉ e.symm '' K := fun ⟨w, hw, hwz⟩ => hzs (hwz ▸ e.map_target (hKt hw))
    refine (continuousAt_const (y := c)).congr ?_
    filter_upwards [hKclosed.isOpen_compl.mem_nhds hz] with w hw
    by_cases hws : w ∈ e.source
    · simp only [hws, ↓reduceIte]
      exact (hgK _ fun hK => hw ⟨e w, hK, e.left_inv hws⟩).symm
    · simp [hws]

end OpenPartialHomeomorph
