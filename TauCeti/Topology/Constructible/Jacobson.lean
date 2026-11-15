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
# Constructible sets detected at closed points of Jacobson spaces

Constructible subsets of any Jacobson space are determined by their closed points:
every nonempty constructible set contains a closed point, and inclusion or equality can
be tested on closed points. The existence proof uses Mathlib's Boolean-subalgebra induction
to reduce to differences of open sets.

In a Noetherian Jacobson space, every nonempty constructible set contains a closed
point at which it is locally closed. Consequently, local closedness of a constructible
set can be checked just at its closed points. This permits arguments about rational
points of algebraic group orbits to control the whole topological image, including
its nonclosed points.

The Noetherian local-closedness argument uses `Topology.IsConstructible.dense_interior` in the
closure of the set, and Mathlib's closed-point existence theorem for locally closed subsets of
Jacobson spaces.

## References

* J. S. Milne, *Algebraic Groups* (2017), §7.c, locally closed orbits.
-/

public section

open Set Topology TopologicalSpace
open scoped Set.Notation

namespace Topology.IsConstructible

section Jacobson

variable {X : Type*} [TopologicalSpace X] [JacobsonSpace X] {s t : Set X}

/-- Every nonempty constructible subset of a Jacobson space contains a closed point. -/
theorem nonempty_inter_closedPoints (hs : IsConstructible s) (hne : s.Nonempty) :
    (s ∩ closedPoints X).Nonempty := by
  induction s, hs using BooleanSubalgebra.closure_sdiff_sup_induction with
  | isSublattice =>
    exact ⟨fun _ hs _ ht ↦ ⟨hs.1.union ht.1, hs.2.union ht.2⟩,
      fun _ hs _ ht ↦ ⟨hs.1.inter ht.1, hs.2.inter_isOpen ht.2 ht.1⟩⟩
  | bot_mem => exact ⟨isOpen_empty, .empty⟩
  | top_mem => exact ⟨isOpen_univ, .univ⟩
  | sdiff U hU V hV =>
    exact _root_.nonempty_inter_closedPoints hne
      (hU.1.isLocallyClosed.inter hV.1.isClosed_compl.isLocallyClosed)
  | sup s _ t _ hs ht =>
    obtain ⟨x, hx | hx⟩ := hne
    · obtain ⟨y, hy, hyc⟩ := hs ⟨x, hx⟩
      exact ⟨y, Or.inl hy, hyc⟩
    · obtain ⟨y, hy, hyc⟩ := ht ⟨x, hx⟩
      exact ⟨y, Or.inr hy, hyc⟩

/-- Inclusion between constructible sets in a Jacobson space is detected at closed points. -/
theorem subset_iff_inter_closedPoints_subset (hs : IsConstructible s)
    (ht : IsConstructible t) :
    s ⊆ t ↔ s ∩ closedPoints X ⊆ t ∩ closedPoints X := by
  refine ⟨fun h ↦ Set.inter_subset_inter_left _ h, fun h x hx ↦ ?_⟩
  by_contra hxt
  obtain ⟨y, ⟨hys, hyt⟩, hyc⟩ := (hs.sdiff ht).nonempty_inter_closedPoints ⟨x, hx, hxt⟩
  exact hyt (h ⟨hys, hyc⟩).1

/-- Constructible sets in a Jacobson space are determined by their closed points. -/
theorem eq_iff_inter_closedPoints_eq (hs : IsConstructible s) (ht : IsConstructible t) :
    s = t ↔ s ∩ closedPoints X = t ∩ closedPoints X := by
  rw [Set.Subset.antisymm_iff, Set.Subset.antisymm_iff,
    hs.subset_iff_inter_closedPoints_subset ht, ht.subset_iff_inter_closedPoints_subset hs]

end Jacobson

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
  obtain ⟨z, hz, hzclosed⟩ := _root_.nonempty_inter_closedPoints (Z := U ∩ closure s)
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
