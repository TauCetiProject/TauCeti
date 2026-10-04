/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.List.Rotate
public import Mathlib.GroupTheory.Perm.List

/-!
# Transporting list rotations

This file records how list rotations interact with filtering and how the permutation formed by a
noduplicate list interacts with mapping by an equivalence.

These lemmas transport a cyclic order, and the successor permutation it induces, across a
renaming of indices. They are needed when comparing a combinatorial construction built from a
list with the same construction built from a cyclic rotation of that list: filtering both lists
by the same predicate gives cyclically rotated sublists, which therefore form the same
permutation, and renaming the entries by an equivalence conjugates that permutation. For
example, `TauCeti.KnotTheory.BraidWord.Cyclic` uses them to identify the closures of cyclically
rotated braid words.

## Main results

* `List.formPerm_map_equiv`: mapping a noduplicate list by an equivalence conjugates its
  formed permutation.
* `List.IsRotated.filter`: filtering preserves cyclic rotation of lists.
-/

public section

namespace List

/-- Mapping a noduplicate list by an equivalence conjugates the permutation formed by the list. -/
theorem formPerm_map_equiv {α β : Type*} [DecidableEq α] [DecidableEq β]
    (l : List α) (e : α ≃ β) (hl : l.Nodup) :
    (l.map e).formPerm = e.permCongr l.formPerm := by
  ext x
  by_cases hx : x ∈ l.map e
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    simp only [List.length_map] at hi
    rw [List.formPerm_apply_getElem _ (hl.map e.injective), List.getElem_map,
      Equiv.permCongr_apply]
    simp only [List.getElem_map, Equiv.symm_apply_apply, List.length_map]
    rw [List.formPerm_apply_getElem _ hl]
  · rw [List.formPerm_apply_of_notMem hx, Equiv.permCongr_apply,
      List.formPerm_apply_of_notMem]
    · exact (e.apply_symm_apply x).symm
    · intro hmem
      apply hx
      exact List.mem_map.2 ⟨e.symm x, hmem, e.apply_symm_apply x⟩

/-- Filtering cyclically rotated lists by the same Boolean predicate preserves their cyclic
rotation. -/
theorem IsRotated.filter {α : Type*} {l l' : List α} (h : l ~r l') (p : α → Bool) :
    l.filter p ~r l'.filter p := by
  obtain ⟨k, rfl⟩ := h
  rw [List.rotate_eq_drop_append_take_mod, List.filter_append]
  have hrot := List.isRotated_append
    (l := (l.take (k % l.length)).filter p)
    (l' := (l.drop (k % l.length)).filter p)
  simpa only [← List.filter_append, List.take_append_drop] using hrot

end List
