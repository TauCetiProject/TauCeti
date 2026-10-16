/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Maps.Basic

import Mathlib.Topology.NhdsSet

/-!
# Fibres of closed maps near a fibre

For a closed map `f`, the fibres over points near `y` lie in any neighbourhood of the fibre over
`y` (`IsClosedMap.eventually_preimage_singleton_subset_biUnion`). In particular, after separating
the points of a finite fibre by neighbourhoods `U x`, every nearby fibre is distributed among the
`U x`, which is the first step in proving that fibre counts are locally constant.
-/

public section

open Filter Set Topology

namespace IsClosedMap

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}

/-- For a closed map `f`, if `U x` is a neighbourhood of each point `x` of the fibre over `y`,
then every fibre over a point near `y` lies in the union of the `U x`. -/
theorem eventually_preimage_singleton_subset_biUnion (hf : IsClosedMap f) {y : Y}
    {U : X → Set X} (hU : ∀ x ∈ f ⁻¹' {y}, U x ∈ 𝓝 x) :
    ∀ᶠ y' in 𝓝 y, f ⁻¹' {y'} ⊆ ⋃ x ∈ f ⁻¹' {y}, U x := by
  obtain ⟨t, ht, htU⟩ := mem_comap.1 (hf.comap_nhds_le
    (mem_nhdsSet_iff_forall.2 fun x hx ↦ mem_of_superset (hU x hx) (subset_biUnion_of_mem hx)))
  filter_upwards [ht] with y' hy' x hx
  exact htU (mem_preimage.2 ((mem_singleton_iff.1 hx) ▸ hy'))

end IsClosedMap
