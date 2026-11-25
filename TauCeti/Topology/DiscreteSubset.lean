/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Topology.DiscreteSubset
public import Mathlib.Topology.Separation.Hausdorff

/-!
# Punctured neighbourhoods of discrete subsets

If the trace `U ∩ S` of `S` on `U` is discrete, every point `x ∈ U ∩ S` is isolated in `U ∩ S`, so
`U \ S` belongs to the relative punctured neighbourhood filter `𝓝[U \ {x}] x`
(`IsDiscrete.sdiff_mem_nhdsWithin`). When `U` is open, `𝓝[U \ {x}] x = 𝓝[≠] x`, giving the ambient
punctured neighbourhood membership `U \ S ∈ 𝓝[≠] x` (`IsOpen.sdiff_mem_nhdsNE_of_isDiscrete`).

A point `x` of a T1 space is isolated as soon as some function `f` into a Hausdorff space, tending
to `y` along the cofinite filter, is continuous at `x` with `f x ≠ y`
(`Filter.Tendsto.isOpen_singleton_of_cofinite`): near `x` the values of `f` stay away from `y`,
which happens only finitely often. For instance, a summable real-valued function that is continuous
at `x` and nonzero there is one such `f`, with `y = 0`.

On a connected compact space, a dependent function `s` which is not identically zero, and which near
every point either vanishes identically or has no zero other than that point, has finitely many
zeros (`TauCeti.finite_setOf_eq_zero_of_forall_eventually`): the set of points near which `s`
vanishes is open and closed, hence empty, so the nonzero set of `s` is codiscrete, and a codiscrete
subset of a compact space is cofinite.

## Main results

* `IsDiscrete.sdiff_mem_nhdsWithin`: `U \ S ∈ 𝓝[U \ {x}] x` whenever `U ∩ S` is discrete and
  `x ∈ U ∩ S`.
* `IsOpen.sdiff_mem_nhdsNE_of_isDiscrete`: `U \ S ∈ 𝓝[≠] x` whenever `U` is open, `U ∩ S` is
  discrete, and `x ∈ U ∩ S`.
* `Filter.Tendsto.isOpen_singleton_of_cofinite`: in a T1 space, `{x}` is open if some `f` into a
  Hausdorff space with `f → y` along the cofinite filter is continuous at `x` with `f x ≠ y`.
* `TauCeti.finite_setOf_eq_zero_of_forall_eventually`: on a connected compact space, a function
  which is not identically zero, and near each point vanishes identically or has no other zero, has
  finitely many zeros.
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

/-- A point `x` of a T1 space is isolated if some function `f` into a Hausdorff space tends to `y`
along the cofinite filter and is continuous at `x` with `f x ≠ y`: a neighbourhood of `x` on which
`f` stays away from `y` is finite. For instance, `f` can be a summable real-valued function that
is continuous at `x` and nonzero there, with `y = 0`. -/
theorem Filter.Tendsto.isOpen_singleton_of_cofinite {X Y : Type*} [TopologicalSpace X] [T1Space X]
    [TopologicalSpace Y] [T2Space Y] {f : X → Y} {y : Y} (hf : Tendsto f cofinite (𝓝 y)) {x : X}
    (hx : ContinuousAt f x) (hne : f x ≠ y) : IsOpen ({x} : Set X) := by
  obtain ⟨U, V, hU, hV, hxU, hyV, hUV⟩ := t2_separation hne
  exact isOpen_singleton_of_finite_mem_nhds x (hx.preimage_mem_nhds (hU.mem_nhds hxU))
    ((mem_cofinite.1 (hf (hV.mem_nhds hyV))).subset fun _ hz ↦ Set.disjoint_left.1 hUV hz)

namespace TauCeti

/-- **A function which vanishes identically or has no other zero near each point has finitely many
zeros.** Let `M` be a connected compact space and `s` a dependent function on `M` with values in
types with a zero, such as a section of a bundle. If near every point `x` either `s` vanishes
identically, or `s` has no zero other than possibly `x`, and `s` does not vanish identically, then
`s` has finitely many zeros. -/
theorem finite_setOf_eq_zero_of_forall_eventually {M : Type*} [TopologicalSpace M] [CompactSpace M]
    [ConnectedSpace M] {E : M → Type*} [∀ x, Zero (E x)] {s : ∀ x, E x}
    (hdich : ∀ x, (∀ᶠ y in 𝓝 x, s y = 0) ∨ ∀ᶠ y in 𝓝[≠] x, s y ≠ 0) (hne : ∃ x, s x ≠ 0) :
    {x | s x = 0}.Finite := by
  -- The set `A` of points near which `s` vanishes is open, and closed: near a point outside `A`,
  -- `s` vanishes at most at that point.
  set A := {x | ∀ᶠ y in 𝓝 x, s y = 0}
  have hAc : IsOpen Aᶜ := isOpen_iff_mem_nhds.2 fun x hx ↦ by
    have h := eventually_nhdsWithin_iff.1 ((hdich x).resolve_left hx)
    filter_upwards [h] with y hy hyA
    by_cases hyx : y = x
    · exact hx (hyx ▸ hyA)
    · exact hy hyx hyA.self_of_nhds
  -- Since `M` is connected and `s` does not vanish identically, `A` is empty.
  have hA : A = ∅ := by
    refine (isClopen_iff.1 ⟨isOpen_compl_iff.1 hAc, isOpen_setOfPred_eventually_nhds⟩).resolve_right
      fun hA ↦ ?_
    obtain ⟨x, hx⟩ := hne
    exact hx (hA ▸ mem_univ x : x ∈ A).self_of_nhds
  -- So the zeros of `s` are isolated, and a codiscrete subset of a compact space is cofinite.
  have h : {y | s y ≠ 0} ∈ codiscrete M := mem_codiscrete_iff_forall_mem_nhdsNE.2 fun x ↦
    (hdich x).resolve_left (show x ∉ A by rw [hA]; exact notMem_empty x)
  simpa [compl_ofPred] using cofinite_le_codiscrete h

end TauCeti
