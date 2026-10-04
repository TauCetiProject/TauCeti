/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Compactification.OnePoint.Basic
public import Mathlib.Topology.Maps.Proper.Basic

/-!
# Maps on one-point compactifications

The extension `OnePoint.map f` sends infinity to infinity. Its range is the range of `f`,
embedded in the target compactification, together with infinity, and it is injective exactly
when `f` is injective. For a proper map between arbitrary topological spaces, this extension
is continuous: preimages of closed compact sets are closed and compact, so Mathlib's
`OnePoint.continuous_map` applies.
-/

public section

open Set

namespace TauCeti

/-- Extension to one-point compactifications preserves and reflects injectivity. -/
@[simp]
theorem onePointMap_injective_iff {X Y : Type*} {f : X → Y} :
    Function.Injective (OnePoint.map f) ↔ Function.Injective f := by
  constructor
  · intro hf x y h
    apply OnePoint.coe_injective
    apply hf
    simpa only [OnePoint.map_some] using congrArg OnePoint.some h
  · intro hf
    -- `OnePoint.map` is implemented by `Option.map`, so its injectivity theorem applies.
    exact Option.map_injective hf

/-- The range of the extension to one-point compactifications is the embedded range together
with the point at infinity. -/
@[simp]
theorem range_onePointMap {X Y : Type*} (f : X → Y) :
    range (OnePoint.map f) = insert OnePoint.infty (((↑) : Y → OnePoint Y) '' range f) := by
  -- `Option.range_eq` splits the domain into infinity and the finite points.
  exact (Option.range_eq (OnePoint.map f)).trans
    (congrArg (insert OnePoint.infty) (range_comp ((↑) : Y → OnePoint Y) f))

/-- A proper map between arbitrary topological spaces extends continuously
to the one-point compactifications, sending infinity to infinity. -/
theorem continuous_onePointMap_of_isProperMap
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : IsProperMap f) : Continuous (OnePoint.map f) :=
  OnePoint.continuous_map hf.continuous (by
    refine Filter.hasBasis_coclosedCompact.tendsto_right_iff.mpr ?_
    intro K hK
    exact (hf.isCompact_preimage hK.2).compl_mem_coclosedCompact_of_isClosed
      (hK.1.preimage hf.continuous))

end TauCeti
