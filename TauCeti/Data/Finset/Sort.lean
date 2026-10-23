/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Data.Finset.Sort

/-!
# Sorting finsets

Sorting the finset `{a, b}` of two distinct elements with `r a b` gives the list `[a, b]`.

For a map `f` that is monotone on a finset `s` of a linear order, the points of `s` sorted in
increasing order are the concatenation, over the values `y` of `f` on `s` in increasing order, of
the sorted fibres `{x ∈ s | f x = y}`. Consequently the ordered product of a word along `s` is the
ordered product, over the values of `f` on `s`, of the ordered products along the fibres.
-/

public section

namespace Finset

variable {α : Type*} (r : α → α → Prop) [DecidableRel r] [IsTrans α r] [Std.Antisymm r]
  [Std.Total r] [DecidableEq α]

/-- Sorting a two-element finset `{a, b}` with `r a b` lists `a` before `b`. -/
theorem sort_pair {a b : α} (hab : r a b) (hne : a ≠ b) : sort {a, b} r = [a, b] := by
  rw [sort_insert r (fun c hc => mem_singleton.1 hc ▸ hab) (notMem_singleton.2 hne),
    sort_singleton]

section LinearOrder

variable {α β : Type*} [LinearOrder α] [LinearOrder β] {s : Finset α} {f : α → β}

/-- For a map `f` that is monotone on `s`, listing the values of `f` on `s` in increasing order and
replacing each value `y` by the increasing list of the points of `s` over `y` lists `s` in
increasing order. -/
theorem flatten_map_sort_filter_eq_sort (hf : MonotoneOn f s) :
    ((s.image f).sort.map fun y => {x ∈ s | f x = y}.sort).flatten = s.sort := by
  refine List.SortedLT.eq_of_mem_iff ?_ (sortedLT_sort s) fun x => ?_
  · rw [List.sortedLT_iff_pairwise, List.pairwise_flatten, List.pairwise_map]
    refine ⟨fun l hl => ?_, (sortedLT_sort _).pairwise.imp fun {y z} hyz x hx w hw => ?_⟩
    · obtain ⟨y, -, rfl⟩ := List.mem_map.1 hl
      exact (sortedLT_sort _).pairwise
    · rw [mem_sort, mem_filter] at hx hw
      exact lt_of_not_ge fun h => hyz.not_ge (hx.2 ▸ hw.2 ▸ hf hw.1 hx.1 h)
  · rw [mem_sort, List.mem_flatten]
    simp only [List.mem_map]
    constructor
    · rintro ⟨_, ⟨y, -, rfl⟩, hx⟩
      exact (mem_filter.1 ((mem_sort _).1 hx)).1
    · intro hx
      exact ⟨_, ⟨f x, (mem_sort _).2 (mem_image_of_mem f hx), rfl⟩,
        (mem_sort _).2 (mem_filter.2 ⟨hx, rfl⟩)⟩

/-- For a map `f` that is monotone on `s`, the product of a word `a` along `s` in increasing order
is the product, over the values `y` of `f` on `s` in increasing order, of the products of `a` along
the fibres `{x ∈ s | f x = y}` in increasing order. -/
theorem prod_map_sort_eq_prod_map_sort_image {M : Type*} [Monoid M] (hf : MonotoneOn f s)
    (a : α → M) :
    (s.sort.map a).prod =
      ((s.image f).sort.map fun y => ({x ∈ s | f x = y}.sort.map a).prod).prod := by
  rw [← flatten_map_sort_filter_eq_sort hf, List.map_flatten, List.prod_flatten, List.map_map,
    List.map_map, Function.comp_def, Function.comp_def]

end LinearOrder

end Finset
