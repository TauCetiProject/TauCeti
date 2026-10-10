/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Topology.Constructible.Basic
public import Mathlib.Topology.JacobsonSpace
public import Mathlib.Topology.NoetherianSpace

/-!
# Local closedness detected at closed points

In a Noetherian Jacobson space, every nonempty constructible set contains a closed
point at which it is locally closed. Consequently, local closedness of a constructible
set can be checked just at its closed points. This permits arguments about rational
points of algebraic group orbits to control the whole topological image, including
its nonclosed points.

The argument uses `Topology.IsConstructible.dense_interior` in the closure of the set,
and Mathlib's closed-point existence theorem for locally closed subsets of Jacobson spaces.

## References

* J. S. Milne, *Algebraic Groups* (2017), §7.c, locally closed orbits.
-/

public section

open Set Topology TopologicalSpace
open scoped Set.Notation

namespace Topology.IsConstructible

variable {X : Type*} [TopologicalSpace X] [NoetherianSpace X] [JacobsonSpace X]
  {s : Set X}

/-- A nonempty constructible set contains a closed point at which it is locally closed. -/
theorem exists_isLocallyClosedAt_mem_closedPoints (hs : IsConstructible s) (hne : s.Nonempty) :
    ∃ x ∈ s ∩ closedPoints X, IsLocallyClosedAt s x := by
  have hrel : IsConstructible (closure s ↓∩ s) :=
    hs.preimage_of_isClosedEmbedding isClosed_closure.isClosedEmbedding_subtypeVal
      (NoetherianSpace.isCompact _)
  have hd : Dense (closure s ↓∩ s) := by
    rw [Subtype.dense_iff, Subtype.image_preimage_coe,
      inter_eq_right.mpr (subset_closure (s := s))]
  obtain ⟨x, hx⟩ := hne
  have : Nonempty (closure s) := ⟨⟨x, subset_closure hx⟩⟩
  obtain ⟨y, hy⟩ := (hrel.dense_interior hd).nonempty
  obtain ⟨U, hU, hUeq⟩ := isOpen_induced_iff.mp
    (isOpen_interior : IsOpen (interior (closure s ↓∩ s)))
  have hyU : y ∈ Subtype.val ⁻¹' U := by
    rw [hUeq]
    exact hy
  have hsub : U ∩ closure s ⊆ s := by
    intro z hz
    exact interior_subset (s := closure s ↓∩ s)
      (hUeq ▸ hz.1 : (⟨z, hz.2⟩ : closure s) ∈ interior (closure s ↓∩ s))
  obtain ⟨z, hz, hzclosed⟩ := nonempty_inter_closedPoints (Z := U ∩ closure s)
    ⟨y.val, hyU, y.property⟩ (hU.isLocallyClosed.inter isClosed_closure.isLocallyClosed)
  exact ⟨z, ⟨hsub hz, hzclosed⟩,
    isLocallyClosedAt_iff_exists_inter_closure_subset.mpr ⟨U, hU.mem_nhds hz.1, hsub⟩⟩

/-- A constructible set in a Noetherian Jacobson space is locally closed precisely when
it is locally closed at each of its closed points. -/
theorem isLocallyClosed_iff_forall_mem_closedPoints (hs : IsConstructible s) :
    IsLocallyClosed s ↔ ∀ x ∈ s ∩ closedPoints X, IsLocallyClosedAt s x := by
  refine ⟨fun h x hx ↦ h.isLocallyClosedAt hx.1, fun h ↦ ?_⟩
  rw [isLocallyClosed_iff_isLocallyClosedAt]
  intro x hx
  by_contra hbad
  have hconstructible : IsConstructible (s \ interior (coborder s)) :=
    hs.sdiff ((NoetherianSpace.isCompact _).isConstructible isOpen_interior)
  have hne : (s \ interior (coborder s)).Nonempty := by
    refine ⟨x, hx, ?_⟩
    simpa only [interior_coborder, mem_ofPred_eq] using hbad
  obtain ⟨y, hy, _⟩ := hconstructible.exists_isLocallyClosedAt_mem_closedPoints hne
  exact hy.1.2 (by simpa only [interior_coborder, mem_ofPred_eq] using h y ⟨hy.1.1, hy.2⟩)

end Topology.IsConstructible
