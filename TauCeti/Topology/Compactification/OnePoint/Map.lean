/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Compactification.OnePoint.Basic
public import Mathlib.Topology.Maps.Proper.CompactlyGenerated

/-!
# Maps on one-point compactifications

The extension `OnePoint.map f` sends infinity to infinity. Its range is the range of `f`,
embedded in the target compactification, together with infinity. For a proper map from an
R₁ space to a compactly coherent Hausdorff space, this extension is continuous, by Mathlib's
`isProperMap_iff_tendsto_cocompact` and `OnePoint.continuous_map`.
-/

public section

open Set

namespace TauCeti

/-- The range of the extension to one-point compactifications is the embedded range together
with the point at infinity. -/
@[simp]
theorem range_onePoint_map {X Y : Type*} (f : X → Y) :
    range (OnePoint.map f) = insert OnePoint.infty (((↑) : Y → OnePoint Y) '' range f) := by
  ext y
  induction y using OnePoint.rec <;>
    simp [OnePoint.exists, mem_range, eq_comm]

/-- A proper map from an R₁ space to a compactly coherent Hausdorff space extends continuously
to the one-point compactifications, sending infinity to infinity. -/
theorem continuous_onePoint_map_of_isProperMap
    {X Y : Type*} [TopologicalSpace X] [R1Space X]
    [TopologicalSpace Y] [T2Space Y] [CompactlyCoherentSpace Y]
    {f : X → Y} (hf : IsProperMap f) : Continuous (OnePoint.map f) :=
  OnePoint.continuous_map hf.continuous (by
    simpa only [Filter.coclosedCompact_eq_cocompact] using
      (isProperMap_iff_tendsto_cocompact.mp hf).2)

end TauCeti
