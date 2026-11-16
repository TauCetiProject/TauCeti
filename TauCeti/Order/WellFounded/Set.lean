/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.WellFoundedSet

/-!
# Partially well-ordered sets: finiteness criteria and finite generating sets

In a linear order, a set which has only finitely many elements below each of its elements is
partially well-ordered (`Set.IsPWO.of_finite_inter_Iic`). This is how supports of series which are
finite below every cutoff, such as Novikov series, become supports of Hahn series.

Conversely, in any preorder, every partially well-ordered set `s` admits a finite subset `V ⊆ s`
such that every element of `s` lies above some element of `V` (`Set.IsPWO.exists_finset_subset_le`).

## Main results

* `Set.IsPWO.of_finite_inter_Iic`: a set of a linear order meeting each `Iic a`, for `a` in the
  set, in a finite set is partially well-ordered.
* `Set.IsPWO.exists_finset_subset_le`: every partially well-ordered subset of a preorder contains a
  finite subset below all of its elements.
-/

public section

namespace Set

section LinearOrder

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

end LinearOrder

section Preorder

/-- Every partially well-ordered subset `s` of a preorder admits a finite subset `V ⊆ s` such that
every element of `s` lies above some element of `V`. -/
theorem IsPWO.exists_finset_subset_le {α : Type*} [Preorder α] {s : Set α} (hs : s.IsPWO) :
    ∃ V : Finset α, (V : Set α) ⊆ s ∧ ∀ x ∈ s, ∃ v ∈ V, v ≤ x := by
  classical
  by_contra h
  push Not at h
  choose g hgmem hgnot using fun (V : Finset α) (hV : (V : Set α) ⊆ s) ↦ h V hV
  let seq : ℕ → {a : α // a ∈ s} := Nat.strongRec fun n ih ↦
    let V : Finset α := Finset.univ.image fun i : Fin n ↦ (ih i.1 i.2).1
    have hV : (V : Set α) ⊆ s := by
      intro x hx
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hx)
      exact (ih i.1 i.2).2
    ⟨g V hV, hgmem V hV⟩
  have hseq_eq (n : ℕ) :
      seq n =
        ⟨g (Finset.univ.image fun i : Fin n ↦ (seq i.1).1)
            (fun x hx ↦ by
              obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hx)
              exact (seq i.1).2),
          hgmem _ _⟩ :=
    Nat.strongRec_eq _ n
  obtain ⟨a, b, hab, hle⟩ := Set.partiallyWellOrderedOn_iff_exists_lt.mp hs
    (fun n ↦ (seq n).1) (fun n ↦ (seq n).2)
  have hnot : ¬ (seq a).1 ≤ (seq b).1 := by
    rw [hseq_eq b]
    exact hgnot _ _ (seq a).1 (Finset.mem_image.mpr ⟨⟨a, hab⟩, Finset.mem_univ _, rfl⟩)
  exact hnot hle

end Preorder

end Set
