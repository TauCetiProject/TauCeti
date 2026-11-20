/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Multiset.Defs
public import Mathlib.Data.Multiset.Sort

/-!
# Sorting multisets

A list is the sorted form of a multiset exactly when it is sorted and has that multiset as its
underlying multiset. This is how a stored list of numbers is checked against the sorting of a
multiset of computed values.

If every element of a multiset `s` precedes every element of a multiset `t`, then sorting `s + t`
lists the sorted elements of `s` followed by the sorted elements of `t`. This is how an ordered
monomial over an ordered disjoint union of index sets splits into a product of ordered monomials
over the two pieces.

Sorting `a ::ₘ s` inserts `a` into the sorted list of `s` at its place. This is how a generator
multiplied onto an ordered monomial moves into position.

In a commutative monoid, a product over the sorted list of a multiset, possibly filtered, is the
product over the multiset itself.
-/

public section

namespace Multiset

variable {α : Type*} (r : α → α → Prop) [DecidableRel r] [IsTrans α r] [Std.Antisymm r]
  [Std.Total r]

/-- Sorting the sum of two multisets, every element of the first related to every element of the
second, appends the two sorted lists. -/
theorem sort_add {s t : Multiset α} (h : ∀ a ∈ s, ∀ b ∈ t, r a b) :
    (s + t).sort r = s.sort r ++ t.sort r := by
  refine List.Perm.eq_of_pairwise' (r := r) (pairwise_sort _ _) ?_ ?_
  · exact List.pairwise_append.2 ⟨pairwise_sort _ _, pairwise_sort _ _,
      fun a ha b hb ↦ h a ((mem_sort _).1 ha) b ((mem_sort _).1 hb)⟩
  · rw [← coe_eq_coe, ← coe_add, sort_eq, sort_eq, sort_eq]

/-- A list is the sorted form of a multiset exactly when it is sorted and its underlying multiset
is the given one. -/
theorem eq_sort_iff {l : List α} {s : Multiset α} :
    l = s.sort r ↔ l.Pairwise r ∧ (l : Multiset α) = s := by
  constructor
  · rintro rfl
    exact ⟨pairwise_sort _ _, sort_eq _ _⟩
  · rintro ⟨hl, rfl⟩
    exact (List.mergeSort_eq_self r hl).symm

/-- Sorting a multiset with one more element inserts that element into the sorted list. -/
theorem sort_cons_eq_orderedInsert (a : α) (s : Multiset α) :
    (a ::ₘ s).sort r = (s.sort r).orderedInsert r a :=
  Quot.inductionOn s fun l => by simp [List.mergeSort_eq_insertionSort]

/-- In a commutative monoid, the product over the sorted list of a multiset is the product over
the multiset. -/
@[to_additive (attr := simp) /-- In an additive commutative monoid, the sum over the sorted list
of a multiset is the sum over the multiset. -/]
theorem prod_map_sort {M : Type*} [CommMonoid M] (g : α → M) (s : Multiset α) :
    ((s.sort r).map g).prod = (s.map g).prod := by
  rw [← prod_coe, ← map_coe, sort_eq]

/-- In a commutative monoid, the product over a filter of the sorted list of a multiset is the
product over the same filter of the multiset. -/
@[to_additive (attr := simp) /-- In an additive commutative monoid, the sum over a filter of the
sorted list of a multiset is the sum over the same filter of the multiset. -/]
theorem prod_map_filter_sort {M : Type*} [CommMonoid M] (p : α → Prop) [DecidablePred p]
    (g : α → M) (s : Multiset α) :
    (((s.sort r).filter p).map g).prod = ((s.filter p).map g).prod := by
  rw [← prod_coe, ← map_coe, ← filter_coe, sort_eq]

end Multiset
