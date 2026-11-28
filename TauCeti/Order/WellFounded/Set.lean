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

A set partially well-ordered by any relation lies above finitely many of its own elements. In a
partial order, when every `Ici a` is itself partially well-ordered, this characterizes
the partially well-ordered sets as those covered by finitely many `Ici a`. For exponents ordered
by a finitely generated cone, this identifies supports of Hahn series with sets bounded by
finitely many translated cones.

## Main results

* `Set.IsPWO.of_finite_inter_Iic`: a set of a linear order meeting each `Iic a`, for `a` in the
  set, in a finite set is partially well-ordered.
* `Set.PartiallyWellOrderedOn.exists_finset_subset_forall_exists`: a set partially well-ordered
  by `r` has finitely many elements `a` such that each of its elements `b` satisfies `r a b` for
  one of them.
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

/-- A set partially well-ordered by a relation `r` lies above finitely many of its own elements:
some finite `t ⊆ s` has, below each `b ∈ s`, an element `a` with `r a b`. Otherwise one could
choose a sequence in `s` with no element related to a later one. -/
theorem PartiallyWellOrderedOn.exists_finset_subset_forall_exists {α : Type*}
    {r : α → α → Prop} {s : Set α} (hs : s.PartiallyWellOrderedOn r) :
    ∃ t : Finset α, ↑t ⊆ s ∧ ∀ b ∈ s, ∃ a ∈ t, r a b := by
  by_contra! h
  obtain ⟨f, hfs, hf⟩ := exists_seq_of_forall_finset_exists (· ∈ s) (fun a b ↦ ¬r a b)
    fun t ht ↦ h t ht
  obtain ⟨m, n, hmn, hr⟩ := hs.exists_lt hfs
  exact hf m n hmn hr

section PartialOrder

variable {α : Type*} [PartialOrder α] {s : Set α}

/-- If every `Ici a` is partially well-ordered, a set is partially well-ordered exactly when
finitely many sets `Ici a` cover it. -/
theorem isPWO_iff_exists_finset_subset_biUnion_Ici (h : ∀ a : α, (Ici a).IsPWO) :
    s.IsPWO ↔ ∃ t : Finset α, s ⊆ ⋃ a ∈ t, Ici a := by
  refine ⟨fun hs ↦ ?_, ?_⟩
  · obtain ⟨t, -, ht⟩ := PartiallyWellOrderedOn.exists_finset_subset_forall_exists hs
    refine ⟨t, fun b hb ↦ ?_⟩
    obtain ⟨a, ha, hab⟩ := ht b hb
    exact mem_iUnion₂.2 ⟨a, ha, mem_Ici.2 hab⟩
  rintro ⟨t, ht⟩
  refine ((t.isPWO_sup (f := Ici)).mpr fun a _ ↦ h a).mono ?_
  rwa [Finset.sup_set_eq_biUnion]

end PartialOrder

end Set
