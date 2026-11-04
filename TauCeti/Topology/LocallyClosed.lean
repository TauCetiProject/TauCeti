/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.GDelta.Basic
public import Mathlib.Topology.LocallyClosed

/-!
# Interiors of locally closed sets

A locally closed set is nowhere dense exactly when its interior is empty
(`IsLocallyClosed.isNowhereDense_iff`). Since finite unions of nowhere dense sets are nowhere dense,
a nonempty space covered by finitely many locally closed sets has one of them with nonempty
interior (`TauCeti.nonempty_interior_of_iUnion_of_isLocallyClosed`). This is the finite analogue
of the Baire category argument `nonempty_interior_of_iUnion_of_closed`, valid in every
topological space.

A set with empty interior need not be nowhere dense: the rationals have empty interior and are
dense in the real line. They are not locally closed.
-/

public section

open Set

variable {X ι : Type*} [TopologicalSpace X] {s : Set X}

/-- A locally closed set is nowhere dense exactly when its interior is empty. -/
theorem IsLocallyClosed.isNowhereDense_iff (hs : IsLocallyClosed s) :
    IsNowhereDense s ↔ interior s = ∅ := by
  refine ⟨fun h ↦ subset_empty_iff.1 (h ▸ interior_mono subset_closure), fun h ↦ ?_⟩
  rw [IsNowhereDense, ← not_nonempty_iff_eq_empty]
  rintro ⟨x, hx⟩
  -- The open set `interior (closure s)` meets `s`, and its trace on the open set `coborder s`
  -- lies in `closure s ∩ coborder s = s`.
  obtain ⟨y, hyU, hys⟩ := mem_closure_iff.1 (interior_subset hx) _ isOpen_interior hx
  have hsub : interior (closure s) ∩ coborder s ⊆ s := fun z hz ↦
    closure_inter_coborder.subset ⟨interior_subset hz.1, hz.2⟩
  have hopen : IsOpen (interior (closure s) ∩ coborder s) :=
    isOpen_interior.inter (isLocallyClosed_iff_isOpen_coborder.1 hs)
  have hy : y ∈ interior s := interior_maximal hsub hopen ⟨hyU, subset_coborder hys⟩
  simp [h] at hy

namespace TauCeti

/-- **Finite covers by locally closed sets.** If a nonempty space is the union of finitely many
locally closed sets, one of them has nonempty interior. -/
theorem nonempty_interior_of_iUnion_of_isLocallyClosed [Nonempty X] [Finite ι] {f : ι → Set X}
    (hf : ∀ i, IsLocallyClosed (f i)) (hU : ⋃ i, f i = univ) :
    ∃ i, (interior (f i)).Nonempty := by
  by_contra! h
  have hnd : IsNowhereDense (⋃ i, f i) :=
    IsNowhereDense.iUnion fun i ↦ (hf i).isNowhereDense_iff.2 (h i)
  rw [hU, IsNowhereDense, closure_univ, interior_univ] at hnd
  exact univ_nonempty.ne_empty hnd

end TauCeti
