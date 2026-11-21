/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Sets.Closeds
public import Mathlib.Topology.Separation.Regular

/-!
# Clopen subsets

This file supplies the compact-space instance on a clopen subset of a compact space, and the
separation of the two parts into which a clopen subset of a subspace cuts it: in a completely
normal space they have disjoint neighbourhoods in the ambient space
(`IsClopen.disjoint_nhdsSet_image_val_compl`).
-/

public section

open Filter Set TopologicalSpace Topology

namespace TopologicalSpace.Clopens

/-- A clopen subset of a compact space is compact. -/
instance instCompactSpace [TopologicalSpace X] [CompactSpace X] (s : Clopens X) : CompactSpace s :=
  isCompact_iff_compactSpace.mp s.isClosed.isCompact

end TopologicalSpace.Clopens

/-- A clopen subset `c` of a subspace `s` of a completely normal space and its complement in `s`
have disjoint neighbourhoods in the ambient space, although neither need be closed there. -/
theorem IsClopen.disjoint_nhdsSet_image_val_compl [TopologicalSpace X] [CompletelyNormalSpace X]
    {s : Set X} {c : Set s} (hc : IsClopen c) :
    Disjoint (𝓝ˢ (((↑) : s → X) '' c)) (𝓝ˢ ((↑) '' cᶜ)) := by
  -- A closed subset of `s` is the trace on `s` of the closure of its image.
  have key {d : Set s} (hd : IsClosed d) : Disjoint (closure (((↑) : s → X) '' d)) ((↑) '' dᶜ) := by
    rw [Set.disjoint_left]
    rintro _ hx ⟨y, hy, rfl⟩
    refine hy ?_
    rwa [← hd.closure_eq, IsInducing.subtypeVal.closure_eq_preimage_closure_image]
  refine completely_normal (key hc.isClosed) ?_
  simpa only [compl_compl] using (key hc.compl.isClosed).symm
