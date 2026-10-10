/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.SeparatedMap

/-!
# Separated maps into Hausdorff spaces

A continuous separated map into a Hausdorff space has a Hausdorff domain: two points with the same
image are separated by the map being separated, and two points with distinct images are separated
by pulling back disjoint neighbourhoods of their images. In particular the total space of a
covering map of a Hausdorff space is Hausdorff (`IsCoveringMap.isSeparatedMap`).

## Main results

* `IsSeparatedMap.t2Space`: the domain of a continuous separated map into a Hausdorff space is
  Hausdorff.
-/

public section

open Filter Topology

namespace TauCeti

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- **The domain of a separated map into a Hausdorff space is Hausdorff.** If `f : X → Y` is
continuous and separated and `Y` is Hausdorff, then `X` is Hausdorff. -/
theorem _root_.IsSeparatedMap.t2Space [T2Space Y] {f : X → Y} (sep : IsSeparatedMap f)
    (hf : Continuous f) : T2Space X := by
  rw [t2Space_iff_disjoint_nhds]
  intro x y hxy
  by_cases h : f x = f y
  · exact isSeparatedMap_iff_disjoint_nhds.1 sep x y h hxy
  · exact disjoint_of_map ((disjoint_nhds_nhds.2 h).mono (hf.tendsto x) (hf.tendsto y))

end TauCeti
