/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.WellFoundedSet

/-!
# Recognizing partially well-ordered sets

In a linear order, a set which has only finitely many elements below each of its elements is
partially well-ordered. This is how supports of series which are finite below every cutoff, such
as Novikov series, become supports of Hahn series.

In a partial order, a partially well-ordered set lies above finitely many of its own elements,
namely its minimal ones. When every `Ici a` is itself partially well-ordered, this characterizes
the partially well-ordered sets as those covered by finitely many `Ici a`. For exponents ordered
by a finitely generated cone, this identifies supports of Hahn series with sets bounded by
finitely many translated cones.

## Main results

* `Set.IsPWO.of_finite_inter_Iic`: a set of a linear order meeting each `Iic a`, for `a` in the
  set, in a finite set is partially well-ordered.
* `Set.IsPWO.exists_finset_subset_biUnion_Ici`: a partially well-ordered set is covered by the
  sets `Ici a` for finitely many of its elements `a`.
* `Set.isPWO_iff_exists_finset_subset_biUnion_Ici`: if every `Ici a` is partially well-ordered,
  a set is partially well-ordered exactly when finitely many `Ici a` cover it.
-/

public section

namespace Set

variable {α : Type*} [LinearOrder α] {s : Set α}

/-- In a linear order, a set with only finitely many elements below each of its elements is
partially well-ordered. -/
theorem IsPWO.of_finite_inter_Iic (hs : ∀ a ∈ s, (s ∩ Iic a).Finite) : s.IsPWO := by
  rw [IsPWO, partiallyWellOrderedOn_iff_exists_lt]
  intro f hf
  by_cases h : ∃ n, 0 < n ∧ f 0 ≤ f n
  · obtain ⟨n, hn, h⟩ := h
    exact ⟨0, n, hn, h⟩
  push Not at h
  -- Otherwise the whole sequence stays below `f 0`, in a finite set, so it repeats a value.
  have hmem (n : ℕ) : f n ∈ s ∩ Iic (f 0) := by
    refine ⟨hf n, ?_⟩
    rcases n.eq_zero_or_pos with rfl | hn
    · exact le_rfl
    · exact (h n hn).le
  obtain ⟨m, n, hmn, hfmn⟩ := (hs (f 0) (hf 0)).exists_lt_map_eq_of_forall_mem hmem
  exact ⟨m, n, hmn, hfmn.le⟩

section PartialOrder

variable {α : Type*} [PartialOrder α] {s : Set α}

/-- A partially well-ordered set is covered by the sets `Ici a` for finitely many of its elements
`a`: its minimal elements form a finite antichain, and every element lies above one of them. -/
theorem IsPWO.exists_finset_subset_biUnion_Ici (hs : s.IsPWO) :
    ∃ t : Finset α, ↑t ⊆ s ∧ s ⊆ ⋃ a ∈ t, Ici a := by
  have hfin : {a | Minimal (· ∈ s) a}.Finite :=
    (setOfPred_minimal_antichain _).finite_of_partiallyWellOrderedOn
      (hs.mono fun _ ha ↦ ha.prop)
  refine ⟨hfin.toFinset, fun a ha ↦ (hfin.mem_toFinset.mp ha).prop, fun a ha ↦ ?_⟩
  obtain ⟨b, hba, hb⟩ := hs.exists_le_minimal ha
  exact mem_biUnion (hfin.mem_toFinset.mpr hb) hba

/-- If every `Ici a` is partially well-ordered, a set is partially well-ordered exactly when
finitely many sets `Ici a` cover it. -/
theorem isPWO_iff_exists_finset_subset_biUnion_Ici (h : ∀ a : α, (Ici a).IsPWO) :
    s.IsPWO ↔ ∃ t : Finset α, s ⊆ ⋃ a ∈ t, Ici a := by
  refine ⟨fun hs ↦ hs.exists_finset_subset_biUnion_Ici.imp fun _ ht ↦ ht.2, ?_⟩
  rintro ⟨t, ht⟩
  refine ((t.isPWO_sup (f := Ici)).mpr fun a _ ↦ h a).mono ?_
  rwa [Finset.sup_set_eq_biUnion]

end PartialOrder

end Set
