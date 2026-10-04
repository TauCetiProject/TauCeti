/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.List.Rotate
public import Mathlib.GroupTheory.Perm.List

import TauCeti.Data.Fin.Basic

/-!
# Transporting list rotations

This file records how list rotations act on their finite index types and interact with filtering,
and how the permutation formed by a list interacts with mapping by an equivalence.

These lemmas transport a cyclic order, and the successor permutation it induces, across a
renaming of indices. They are needed when comparing a combinatorial construction built from a
list with the same construction built from a cyclic rotation of that list: filtering both lists
by the same predicate gives cyclically rotated sublists, which therefore form the same
permutation, and renaming the entries by an equivalence conjugates that permutation. For
example, `TauCeti.KnotTheory.BraidWord.Cyclic` uses them to identify the closures of cyclically
rotated braid words.

## Main results

* `List.rotateIndexEquiv`: identify the entries before and after rotating a list.
* `List.formPerm_map_equiv`: mapping a list by an equivalence conjugates its formed permutation.
* `List.IsRotated.filter`: filtering preserves cyclic rotation of lists.
-/

public section

namespace List

/-- The equivalence which sends the index of an entry in `l.rotate k` to its original index in
`l`. It is the cast along preservation of length followed by addition of `k` modulo the list
length. -/
def rotateIndexEquiv {α : Type*} (l : List α) (k : ℕ) :
    Fin (l.rotate k).length ≃ Fin l.length :=
  (finCongr (List.length_rotate l k)).trans (finRotate l.length ^ k)

/-- Looking up an entry after rotation and translating its index gives the same entry in the
original list. -/
theorem getElem_rotateIndexEquiv {α : Type*} (l : List α) (k : ℕ)
    (j : Fin (l.rotate k).length) :
    (l.rotate k)[j.1] = l[(l.rotateIndexEquiv k j).1] := by
  rw [List.getElem_rotate]
  congr 1
  simp [rotateIndexEquiv, Fin.coe_finRotate_pow]

/-- Translating every index of a rotated list gives the correspondingly rotated list of the
original indices. -/
theorem map_finRange_rotateIndexEquiv {α : Type*} (l : List α) (k : ℕ) :
    (List.finRange (l.rotate k).length).map (l.rotateIndexEquiv k) =
      (List.finRange l.length).rotate k := by
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    simp only [List.length_map, List.length_finRange] at hi
    simp only [List.getElem_map, List.getElem_finRange, List.getElem_rotate]
    apply Fin.ext
    simp [rotateIndexEquiv, Fin.coe_finRotate_pow]

/-- Mapping a list by an equivalence conjugates the permutation formed by the list. -/
theorem formPerm_map_equiv {α β : Type*} [DecidableEq α] [DecidableEq β]
    (l : List α) (e : α ≃ β) :
    (l.map e).formPerm = e.permCongr l.formPerm := by
  induction l with
  | nil =>
    rw [List.map_nil, List.formPerm_nil, List.formPerm_nil, Equiv.Perm.one_def,
      Equiv.Perm.one_def, Equiv.permCongr_refl]
  | cons x l ih =>
    cases l with
    | nil =>
      rw [List.map_singleton, List.formPerm_singleton, List.formPerm_singleton,
        Equiv.Perm.one_def, Equiv.Perm.one_def, Equiv.permCongr_refl]
    | cons y l =>
      simp only [List.map_cons, List.formPerm_cons_cons, Equiv.permCongr_mul]
      rw [Equiv.permCongr_def, Equiv.symm_trans_swap_trans]
      exact congrArg (Equiv.swap (e x) (e y) * ·) ih

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
