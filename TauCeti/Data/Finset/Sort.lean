/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Chain

/-!
# Sorting finsets

Sorting the finset `{a, b}` of two distinct elements with `r a b` gives the list `[a, b]`, and
sorting `s.erase a` gives the sorted list of `s` with `a` erased.

For a map `f` that is monotone on a finset `s` of a linear order, the points of `s` sorted in
increasing order are the concatenation, over the values `y` of `f` on `s` in increasing order, of
the sorted fibres `{x ∈ s | f x = y}`. Consequently the ordered product of a word along `s` is the
ordered product, over the values of `f` on `s`, of the ordered products along the fibres.

Consecutive entries of the sorted list of `s` are the pairs of positions of `s` with no position of
`s` strictly between them, so a chain condition on the sorted list is a condition on such adjacent
pairs.
-/

public section

namespace Finset

variable {α : Type*} (r : α → α → Prop) [DecidableRel r] [IsTrans α r] [Std.Antisymm r]
  [Std.Total r] [DecidableEq α]

/-- Sorting a two-element finset `{a, b}` with `r a b` lists `a` before `b`. -/
theorem sort_pair {a b : α} (hab : r a b) (hne : a ≠ b) : sort {a, b} r = [a, b] := by
  rw [sort_insert r (fun c hc => mem_singleton.1 hc ▸ hab) (notMem_singleton.2 hne),
    sort_singleton]

/-- Sorting `s.erase a` erases `a` from the sorted list of `s`. -/
theorem sort_erase (s : Finset α) (a : α) : sort (s.erase a) r = (sort s r).erase a :=
  List.Perm.eq_of_pairwise' (pairwise_sort _ r) ((pairwise_sort s r).erase a) <|
    Multiset.coe_eq_coe.1 <| by rw [sort_eq, erase_val, ← Multiset.coe_erase, sort_eq]

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
      exact hf.reflect_lt hx.1 hw.1 (hx.2 ▸ hw.2 ▸ hyz)
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

/-- A relation holds between the images of consecutive entries of `s` sorted in increasing order
exactly when it holds between the images of any two positions `x < y` of `s` with no position of
`s` strictly between them. -/
theorem isChain_map_sort_iff {γ : Type*} {r : γ → γ → Prop} {g : α → γ} :
    (s.sort.map g).IsChain r ↔
      ∀ x ∈ s, ∀ y ∈ s, x < y → (∀ z ∈ s, z ≤ x ∨ y ≤ z) → r (g x) (g y) := by
  have hl := sortedLT_sort s
  have hmem : ∀ {x}, x ∈ s.sort ↔ x ∈ s := mem_sort _
  rw [List.isChain_map, List.isChain_iff_getElem]
  refine ⟨fun h x hx y hy hxy hadj => ?_, fun h i hi => ?_⟩
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem (hmem.2 hx)
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem (hmem.2 hy)
    have hik : i < k := hl.getElem_lt_getElem_iff.1 hxy
    obtain rfl : k = i + 1 := by
      by_contra hne
      have hi1 : i + 1 < s.sort.length := by omega
      rcases hadj _ (hmem.1 (List.getElem_mem hi1)) with h' | h'
      · exact absurd (hl.getElem_le_getElem_iff.1 h') (by omega)
      · exact absurd (hl.getElem_le_getElem_iff.1 h') (by omega)
    exact h i hk
  · refine h _ (hmem.1 (List.getElem_mem _)) _ (hmem.1 (List.getElem_mem _))
      (hl.getElem_lt_getElem_iff.2 (by omega)) fun z hz => ?_
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem (hmem.2 hz)
    rw [hl.getElem_le_getElem_iff, hl.getElem_le_getElem_iff]
    omega

end LinearOrder

end Finset
