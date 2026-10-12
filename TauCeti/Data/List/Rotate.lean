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
* `List.formPerm_map_apply`: mapping a list by an injective function intertwines the formed
  permutations on the image.
* `List.formPerm_append_apply_of_mem_right` and `List.formPerm_append_apply_getLast_left`: the
  permutation formed by `T ++ V` on the entries of `V`, and on the last entry of `T`.
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

/-- Mapping a list by an injective function intertwines the permutations formed by the two lists:
on the image of `f`, the permutation formed by `l.map f` is `l.formPerm` transported along `f`. -/
theorem formPerm_map_apply {α β : Type*} [DecidableEq α] [DecidableEq β] {f : α → β}
    (hf : Function.Injective f) (l : List α) (x : α) :
    (l.map f).formPerm (f x) = f (l.formPerm x) := by
  induction l with
  | nil => simp
  | cons y l ih =>
    cases l with
    | nil => simp
    | cons z l =>
      rw [List.map_cons, List.map_cons, List.formPerm_cons_cons, List.formPerm_cons_cons,
        Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ← List.map_cons, ih, hf.swap_apply]

/-- On an entry `x` of `V`, the permutation formed by `T ++ V` agrees with the one formed by `V`,
except that the last entry of `V`, which `V.formPerm` sends back to the head of `V`, is sent to
the head of `T ++ V` instead. -/
theorem formPerm_append_apply_of_mem_right {α : Type*} [DecidableEq α] {T V : List α} {x : α}
    (h : (T ++ V).Nodup) (hx : x ∈ V) :
    (T ++ V).formPerm x =
      if V.formPerm x = V.head (ne_nil_of_mem hx) then (T ++ V).head (by simp [ne_nil_of_mem hx])
      else V.formPerm x := by
  induction T with
  | nil => split_ifs with hc <;> simp [hc]
  | cons t T ih =>
    rw [cons_append, nodup_cons] at h
    obtain ⟨u, us, hU⟩ : ∃ u us, T ++ V = u :: us :=
      exists_cons_of_ne_nil (by simp [ne_nil_of_mem hx])
    have hmem : V.formPerm x ∈ V := formPerm_apply_mem_of_mem hx
    have ht : V.formPerm x ≠ t := fun he ↦ h.1 (he ▸ mem_append_right T hmem)
    have ih' := ih h.2
    simp only [cons_append, head_cons]
    rw [hU, formPerm_cons_cons, Equiv.Perm.mul_apply, ← hU, ih']
    simp only [hU, head_cons] at ih' ⊢
    split_ifs with hc
    · exact Equiv.swap_apply_right t u
    · refine Equiv.swap_apply_of_ne_of_ne ht fun hu ↦ ?_
      rcases T with _ | ⟨t', T⟩
      · simp only [nil_append] at hU
        subst hU
        exact hc hu
      · simp only [cons_append, cons.injEq] at hU
        rw [← hU.1] at hu
        exact (nodup_append.1 h.2).2.2 t' mem_cons_self _ hmem hu.symm

/-- The permutation formed by `T ++ V` sends the last entry of `T` to the head of `V`, or to the
head of `T` if `V` is empty. -/
theorem formPerm_append_apply_getLast_left {α : Type*} [DecidableEq α] {T V : List α}
    (h : (T ++ V).Nodup) (hT : T ≠ []) :
    (T ++ V).formPerm (T.getLast hT) = (V ++ T).head (by simp [hT]) := by
  rw [formPerm_eq_of_isRotated h isRotated_append]
  obtain ⟨z, zs, hz⟩ : ∃ z zs, V ++ T = z :: zs := exists_cons_of_ne_nil (by simp [hT])
  have hl : T.getLast hT = (z :: zs).getLast (cons_ne_nil z zs) := by
    simp only [← hz]
    exact (getLast_append_of_ne_nil _ hT).symm
  simp only [hz, hl, formPerm_apply_getLast, head_cons]

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
