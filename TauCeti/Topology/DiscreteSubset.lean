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

In a T1 space, a set is closed and discrete exactly when it meets some neighbourhood of each point
in a finite set (`TauCeti.isClosed_and_isDiscrete_iff_forall_finite_inter`).

## Main results

* `IsDiscrete.sdiff_mem_nhdsWithin`: `U \ S ∈ 𝓝[U \ {x}] x` whenever `U ∩ S` is discrete and
  `x ∈ U ∩ S`.
* `IsOpen.sdiff_mem_nhdsNE_of_isDiscrete`: `U \ S ∈ 𝓝[≠] x` whenever `U` is open, `U ∩ S` is
  discrete, and `x ∈ U ∩ S`.
* `TauCeti.isClosed_and_isDiscrete_iff_forall_finite_inter`: in a T1 space, a set is closed and
  discrete exactly when it meets some neighbourhood of each point in a finite set.
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

namespace TauCeti

/-- In a T1 space, a set is closed and discrete if and only if it meets some neighbourhood of each
point in a finite set. -/
theorem isClosed_and_isDiscrete_iff_forall_finite_inter {X : Type*} [TopologicalSpace X]
    [T1Space X] {s : Set X} : IsClosed s ∧ IsDiscrete s ↔ ∀ x, ∃ U ∈ 𝓝 x, (s ∩ U).Finite := by
  simp_rw [isClosed_and_discrete_iff, disjoint_principal_right]
  refine forall_congr' fun x ↦ ⟨fun h ↦ ⟨insert x sᶜ, insert_mem_nhds_iff.2 h, ?_⟩, ?_⟩
  · -- The only point of `s` in `insert x sᶜ` is `x`.
    exact (finite_singleton x).subset fun y ⟨hys, hy⟩ ↦ hy.resolve_right (not_not.2 hys)
  · -- Removing the finitely many points of `s ∩ U` from `U` leaves a punctured neighbourhood.
    rintro ⟨U, hU, hfin⟩
    exact mem_of_superset (nhdsNE_of_nhdsNE_sdiff_finite (mem_nhdsWithin_of_mem_nhds hU)
      hfin.to_subtype) fun y hy hys ↦ hy.2 ⟨hys, hy.1⟩

end TauCeti
