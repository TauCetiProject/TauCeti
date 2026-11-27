/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Separation.Basic

/-!
# Avoiding finitely many points, and dense sets near non-isolated points

In a `T1Space` the complement of a point is open (Mathlib's `isOpen_ne`). Intersecting finitely
many such complements and pulling back along a continuous map shows that the points where a
continuous map into a `T1Space` avoids finitely many given values form an open set
(`TauCeti.isOpen_forall_ne`). For instance, the real coordinates of the complex plane minus
finitely many points form an open subset of `ℝ × ℝ`.

Mathlib's `Dense.infinite` shows that a dense set in an infinite `T1Space` is infinite. This file
also gives the local version: a dense set meets every neighbourhood of a non-isolated point in
infinitely many points (`Dense.infinite_inter_of_mem_nhds`). For instance, a dense set of regular
values of a map to `ℂ` contains any number of values close to a given one.
-/

public section

open Filter Set Topology

namespace TauCeti

/-- The points where a continuous map into a `T1Space` avoids finitely many values `c i` form an
open set. -/
theorem isOpen_forall_ne {X Y ι : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T1Space Y]
    [Finite ι] {f : X → Y} (hf : Continuous f) {c : ι → Y} :
    IsOpen {x : X | ∀ i, f x ≠ c i} := by
  rw [Set.ofPred_forall]
  exact isOpen_iInter_of_finite fun _ ↦ isOpen_ne.preimage hf

end TauCeti

/-- A dense set meets every neighbourhood of a non-isolated point of a `T1Space` in infinitely many
points. -/
theorem Dense.infinite_inter_of_mem_nhds {X : Type*} [TopologicalSpace X] [T1Space X]
    {s t : Set X} (hs : Dense s) {x : X} [(𝓝[≠] x).NeBot] (ht : t ∈ 𝓝 x) : (s ∩ t).Infinite := by
  intro hfin
  obtain ⟨y, hy⟩ := ((infinite_of_mem_nhds x (interior_mem_nhds.2 ht)).sdiff hfin).nonempty
  obtain ⟨z, hz, hzs⟩ := hs.inter_open_nonempty _ (isOpen_interior.sdiff hfin.isClosed) ⟨y, hy⟩
  exact hz.2 ⟨hzs, interior_subset hz.1⟩
