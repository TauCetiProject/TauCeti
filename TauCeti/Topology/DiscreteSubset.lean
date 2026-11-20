/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.DiscreteSubset

/-!
# Punctured neighbourhoods of discrete subsets

If the trace `U ∩ S` of `S` on `U` is discrete, every point `x ∈ U ∩ S` is isolated in `U ∩ S`, so
`U \ S` belongs to the relative punctured neighbourhood filter `𝓝[U \ {x}] x`
(`IsDiscrete.sdiff_mem_nhdsWithin`). When `U` is open, `𝓝[U \ {x}] x = 𝓝[≠] x`, giving the ambient
punctured neighbourhood membership `U \ S ∈ 𝓝[≠] x` (`IsOpen.sdiff_mem_nhdsNE_of_isDiscrete`).

## Main results

* `IsDiscrete.sdiff_mem_nhdsWithin`: `U \ S ∈ 𝓝[U \ {x}] x` whenever `U ∩ S` is discrete and
  `x ∈ U ∩ S`.
* `IsOpen.sdiff_mem_nhdsNE_of_isDiscrete`: `U \ S ∈ 𝓝[≠] x` whenever `U` is open, `U ∩ S` is
  discrete, and `x ∈ U ∩ S`.
-/

public section

open Filter Set Topology

/-- If `U ∩ S` is discrete, then `U \ S` is a punctured neighbourhood within `U` of every point of
`U ∩ S`. -/
theorem IsDiscrete.sdiff_mem_nhdsWithin {X : Type*} [TopologicalSpace X] {U S : Set X}
    (hS : IsDiscrete (U ∩ S)) {x : X} (hxU : x ∈ U) (hxS : x ∈ S) :
    U \ S ∈ 𝓝[U \ {x}] x := by
  have hdisj : (U ∩ S)ᶜ ∈ 𝓝[≠] x :=
    disjoint_principal_right.1 (disjoint_iff.2 (isDiscrete_iff_nhdsNE.1 hS x ⟨hxU, hxS⟩))
  rw [Set.sdiff_eq, Set.inter_comm, nhdsWithin_inter']
  filter_upwards [mem_inf_of_left hdisj, mem_inf_of_right (mem_principal_self U)] with y hyS hyU
  exact ⟨hyU, fun h ↦ hyS ⟨hyU, h⟩⟩

/-- If `U` is open and `U ∩ S` is discrete, then `U \ S` is a punctured neighbourhood of every point
of `U ∩ S`. -/
theorem IsOpen.sdiff_mem_nhdsNE_of_isDiscrete {X : Type*} [TopologicalSpace X] {U S : Set X}
    (hU : IsOpen U) (hS : IsDiscrete (U ∩ S)) {x : X} (hxU : x ∈ U) (hxS : x ∈ S) :
    U \ S ∈ 𝓝[≠] x := by
  have h := hS.sdiff_mem_nhdsWithin hxU hxS
  rwa [Set.sdiff_eq, Set.inter_comm,
    nhdsWithin_inter_of_mem' (nhdsWithin_le_nhds (hU.mem_nhds hxU))] at h
