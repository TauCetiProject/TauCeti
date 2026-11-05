/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.List.Basic

/-!
# Splittings of a list

`List.splittings l` lists the `2 ^ l.length` ways of distributing the entries of `l` between two
lists while keeping their relative order: each entry goes either to the first list or to the
second. Two different distributions may produce the same pair of lists, and such a pair is then
listed once for each distribution.

These pairs index the terms of the general Leibniz rule: the iterated derivative of a product
along a word of directions is the sum, over the splittings of the word, of the product of the
derivatives of the two factors along the two parts.
-/

public section

namespace List

variable {α : Type*}

/-- The ways of distributing the entries of a list between two lists, keeping their relative
order. The splittings in which the head goes to the first list come first. -/
def splittings : List α → List (List α × List α)
  | [] => [([], [])]
  | a :: l =>
    (l.splittings.map fun p => (a :: p.1, p.2)) ++ l.splittings.map fun p => (p.1, a :: p.2)

@[simp]
theorem splittings_nil : ([] : List α).splittings = [([], [])] := (rfl)

theorem splittings_cons (a : α) (l : List α) :
    (a :: l).splittings =
      (l.splittings.map fun p => (a :: p.1, p.2)) ++ l.splittings.map fun p => (p.1, a :: p.2) :=
  (rfl)

@[simp]
theorem length_splittings (l : List α) : l.splittings.length = 2 ^ l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [splittings_cons, length_append, length_map, ih, length_cons, Nat.pow_succ]
    omega

/-- The two parts of a splitting have as many entries, together, as the list. -/
theorem length_add_length_of_mem_splittings {l : List α} {p : List α × List α}
    (hp : p ∈ l.splittings) : p.1.length + p.2.length = l.length := by
  induction l generalizing p with
  | nil => simp_all
  | cons a l ih =>
    simp only [splittings_cons, mem_append, mem_map] at hp
    rcases hp with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩ <;> simp [← ih hq] <;> omega

/-- Both parts of a splitting are sublists of the list. -/
theorem sublist_of_mem_splittings {l : List α} {p : List α × List α} (hp : p ∈ l.splittings) :
    p.1 <+ l ∧ p.2 <+ l := by
  induction l generalizing p with
  | nil => simp_all
  | cons a l ih =>
    simp only [splittings_cons, mem_append, mem_map] at hp
    rcases hp with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
    · exact ⟨(ih hq).1.cons_cons a, (ih hq).2.cons a⟩
    · exact ⟨(ih hq).1.cons a, (ih hq).2.cons_cons a⟩

/-- Sending every entry to the first list is a splitting. -/
theorem mem_splittings_self_nil (l : List α) : (l, []) ∈ l.splittings := by
  induction l with
  | nil => simp
  | cons a l ih => exact mem_append_left _ (mem_map.2 ⟨_, ih, rfl⟩)

/-- Sending every entry to the second list is a splitting. -/
theorem mem_splittings_nil_self (l : List α) : ([], l) ∈ l.splittings := by
  induction l with
  | nil => simp
  | cons a l ih => exact mem_append_right _ (mem_map.2 ⟨_, ih, rfl⟩)

/-- Exchanging the two parts of every splitting lists the splittings again, up to order. -/
theorem map_swap_splittings_perm (l : List α) : l.splittings.map Prod.swap ~ l.splittings := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [splittings_cons, map_append, map_map, map_map]
    refine perm_append_comm.trans (Perm.append ?_ ?_)
    · exact (Perm.of_eq (by simp [Function.comp_def])).trans (ih.map fun p => (a :: p.1, p.2))
    · exact (Perm.of_eq (by simp [Function.comp_def])).trans (ih.map fun p => (p.1, a :: p.2))

end List
