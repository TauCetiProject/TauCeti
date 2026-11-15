/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.DerivedSet
public import Mathlib.Topology.DiscreteSubset

/-!
# Openness and derived-set characterizations for `Filter.codiscreteWithin`

This file records basic topological properties of `Filter.codiscreteWithin` complementing
`Mathlib.Topology.DiscreteSubset` and `Mathlib.Topology.DerivedSet`:

* `IsOpen.inter_of_mem_codiscreteWithin`: intersecting an open set `U` with any set
  `s ∈ codiscreteWithin U` yields an open set `U ∩ s`, with no separation axiom required.
* `TauCeti.compl_mem_codiscreteWithin_of_subset_compl_derivedSet`,
  `TauCeti.subset_compl_derivedSet_of_compl_mem_codiscreteWithin`, and
  `TauCeti.compl_mem_codiscreteWithin_iff_subset_compl_derivedSet`: relate
  `Eᶜ ∈ codiscreteWithin s` to disjointness of `s` from the derived set `derivedSet E`, allowing
  any `T₁` space subset `s` containing `E` with `Eᶜ ∈ codiscreteWithin s` to be thickened to the
  canonical open superset `(derivedSet E)ᶜ` within which `Eᶜ` remains codiscrete.
-/

public section

open Filter Set Topology

variable {X : Type*} [TopologicalSpace X]

/-- Intersecting an open set `U` with a set `s ∈ codiscreteWithin U` yields an open set. -/
theorem IsOpen.inter_of_mem_codiscreteWithin {U s : Set X} (hU : IsOpen U)
    (hs : s ∈ codiscreteWithin U) : IsOpen (U ∩ s) := by
  rw [isOpen_iff_mem_nhds]
  rintro x ⟨hxU, hxs⟩
  obtain ⟨V, hV, hVs⟩ := mem_nhdsWithin.mp
    (mem_codiscreteWithin_iff_forall_mem_nhdsWithin.mp hs x hxU)
  filter_upwards [hV.mem_nhds hVs.1, hU.mem_nhds hxU] with y hyV hyU
  rcases eq_or_ne y x with rfl | hyx
  · exact ⟨hxU, hxs⟩
  · exact ⟨hyU, hVs.2 ⟨hyV, hyU, hyx⟩⟩

namespace TauCeti

/-- The complement of `E` is codiscrete within any set avoiding `derivedSet E`. -/
theorem compl_mem_codiscreteWithin_of_subset_compl_derivedSet {E s : Set X}
    (hs : s ⊆ (derivedSet E)ᶜ) : Eᶜ ∈ codiscreteWithin s := by
  rw [mem_codiscreteWithin_accPt]
  exact fun x hx hacc ↦
    hs hx (hacc.mono (principal_mono.mpr fun y hy ↦ by_contra fun hyE ↦ hy.2 hyE))

/-- If `E ⊆ s` and `Eᶜ ∈ codiscreteWithin s`, then `s` contains no accumulation point of `E`. -/
theorem subset_compl_derivedSet_of_compl_mem_codiscreteWithin {E s : Set X}
    (hEs : E ⊆ s) (hE : Eᶜ ∈ codiscreteWithin s) : s ⊆ (derivedSet E)ᶜ := by
  intro x hx hxacc
  refine mem_codiscreteWithin_accPt.mp hE x hx (hxacc.mono (principal_mono.mpr fun y hy ↦ ?_))
  exact ⟨hEs hy, not_not.mpr hy⟩

/-- For `E ⊆ s`, `Eᶜ ∈ codiscreteWithin s` holds if and only if `s` is disjoint from `derivedSet E`.
-/
theorem compl_mem_codiscreteWithin_iff_subset_compl_derivedSet {E s : Set X} (hEs : E ⊆ s) :
    Eᶜ ∈ codiscreteWithin s ↔ s ⊆ (derivedSet E)ᶜ :=
  ⟨subset_compl_derivedSet_of_compl_mem_codiscreteWithin hEs,
    compl_mem_codiscreteWithin_of_subset_compl_derivedSet⟩

end TauCeti
