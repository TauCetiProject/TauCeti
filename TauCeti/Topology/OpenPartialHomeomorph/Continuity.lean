/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.OpenPartialHomeomorph.Continuity

/-!
# Punctured neighbourhoods under open partial homeomorphisms

An open partial homeomorphism identifies a neighbourhood of a point of its source with a
neighbourhood of its image, so a point of the source is not isolated as soon as its image is not
(`OpenPartialHomeomorph.nhdsNE_neBot`). For instance, no point in the source of a chart into a
nontrivially normed field is isolated.
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

end OpenPartialHomeomorph
