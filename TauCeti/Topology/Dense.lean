/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Separation.Basic

/-!
# Dense sets near non-isolated points

Mathlib's `Dense.infinite` shows that a dense set in an infinite `T1Space` is infinite. This file
gives the local version: a dense set meets every neighbourhood of a non-isolated point in
infinitely many points (`Dense.infinite_inter_of_mem_nhds`). For instance, a dense set of regular
values of a map to `ℂ` contains any number of values close to a given one.
-/

public section

open Filter Set Topology

/-- A dense set meets every neighbourhood of a non-isolated point of a `T1Space` in infinitely many
points. -/
theorem Dense.infinite_inter_of_mem_nhds {X : Type*} [TopologicalSpace X] [T1Space X]
    {s t : Set X} (hs : Dense s) {x : X} [(𝓝[≠] x).NeBot] (ht : t ∈ 𝓝 x) : (s ∩ t).Infinite := by
  intro hfin
  obtain ⟨y, hy⟩ := ((infinite_of_mem_nhds x (interior_mem_nhds.2 ht)).sdiff hfin).nonempty
  obtain ⟨z, hz, hzs⟩ := hs.inter_open_nonempty _ (isOpen_interior.sdiff hfin.isClosed) ⟨y, hy⟩
  exact hz.2 ⟨hzs, interior_subset hz.1⟩
