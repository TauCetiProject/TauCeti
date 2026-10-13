/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Covering.Basic

/-!
# Hausdorff spaces over Hausdorff spaces

A continuous separated map `f : X → Y` separates the points of each fibre by disjoint open sets,
and continuity pulls back the separation of points with distinct images when `Y` is Hausdorff.
So the source of a continuous separated map to a Hausdorff space is Hausdorff. Covering maps are
separated (`IsCoveringMap.isSeparatedMap`), so the total space of a covering of a Hausdorff space
is Hausdorff.
-/

public section

open Filter Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y] {f : X → Y}

/-- The source of a continuous separated map to a Hausdorff space is Hausdorff. -/
theorem IsSeparatedMap.t2Space (sep : IsSeparatedMap f) (hf : Continuous f) : T2Space X := by
  refine t2Space_iff_disjoint_nhds.2 fun x y hxy ↦ ?_
  by_cases h : f x = f y
  · exact isSeparatedMap_iff_disjoint_nhds.1 sep x y h hxy
  · exact (Filter.disjoint_comap (disjoint_nhds_nhds.2 h)).mono (hf.tendsto x).le_comap
      (hf.tendsto y).le_comap

/-- The total space of a covering of a Hausdorff space is Hausdorff. -/
theorem IsCoveringMap.t2Space (hf : IsCoveringMap f) : T2Space X :=
  hf.isSeparatedMap.t2Space hf.continuous
