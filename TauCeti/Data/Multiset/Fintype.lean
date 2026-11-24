/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Multiset.Fintype

/-!
# Multisets and finite types

Mathlib coerces a multiset `m` to the type of its elements, where an element is a value of `m`
together with an occurrence index below its multiplicity. When `m` has no duplicates every value
occurs once, so an element is determined by its value: this file records that the coercion to
the ambient type is injective. It also records that the occurrence index of an element is below
the multiplicity of its value.

The file also describes the two-element submultisets of the multiset `univ.val.map f` of values
of a family `f` indexed by a finite type: they are the pairs of values of `f` at two distinct
indices (`Multiset.cons_le_map_univ_val_iff`). A condition on ordered pairs of entries at distinct
indices therefore depends only on the multiset of values of the family.
-/

public section

namespace Multiset

variable {α : Type*} [DecidableEq α] {m : Multiset α}

/-- The occurrence index `j` of an element `⟨a, j⟩` of a multiset is below the multiplicity of
`a`. -/
theorem ToType.add_one_le_count (i : m.ToType) : (i.2 : ℕ) + 1 ≤ m.count i.1 :=
  Nat.succ_le_of_lt i.2.isLt

/-- For a multiset without duplicates, an element is determined by its value. -/
theorem Nodup.coe_injective (h : m.Nodup) : Function.Injective fun x : m ↦ (x : α) := by
  intro x y hxy
  apply (coeEmbedding m).injective
  have hx := x.2.isLt
  have hy := y.2.isLt
  simp only [count_eq_one_of_mem h coe_mem] at hx hy
  simp only [coeEmbedding_apply, Prod.mk.injEq]
  exact ⟨hxy, by lia⟩

/-- **Pairs of entries at distinct indices.** For a family `f` indexed by a finite type, the
two-element multiset `{a, b}` lies below the multiset of values of `f` exactly when `a` and `b` are
the values of `f` at two distinct indices. -/
theorem cons_le_map_univ_val_iff {ι β : Type*} [Fintype ι] {f : ι → β} {a b : β} :
    a ::ₘ {b} ≤ Finset.univ.val.map f ↔ ∃ i j, i ≠ j ∧ f i = a ∧ f j = b := by
  classical
  constructor
  · intro h
    obtain ⟨i, -, rfl⟩ := mem_map.1 (mem_of_le h (mem_cons_self _ _))
    rw [← cons_erase (mem_map_of_mem f (Finset.mem_univ_val i)), cons_le_cons_iff,
      ← map_erase_of_mem f _ (Finset.mem_univ_val i), singleton_le] at h
    obtain ⟨j, hj, rfl⟩ := mem_map.1 h
    exact ⟨i, j, (Finset.univ.nodup.mem_erase_iff.1 hj).1.symm, rfl, rfl⟩
  · rintro ⟨i, j, hij, rfl, rfl⟩
    have hle : i ::ₘ {j} ≤ Finset.univ.val :=
      (le_iff_subset (nodup_cons.2 ⟨by simpa using hij, nodup_singleton j⟩)).2
        fun x _ ↦ Finset.mem_univ_val x
    simpa using map_le_map (f := f) hle

end Multiset
