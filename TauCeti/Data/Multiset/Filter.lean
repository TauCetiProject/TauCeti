/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Multiset.Filter

/-!
# Filtering a finite sum of multisets

Filtering a multiset is additive, so it distributes over a finite sum of multisets. Mathlib
records the binary case as `Multiset.filter_add`; this file records the finite-sum case, used to
recover the part of a concatenated unordered tuple lying in a given set from the parts of its
summands.

It also counts the factors of a product of `if p x then a else 1` over a multiset: the product is
`a` raised to the number of elements satisfying `p`. More generally, a product over the elements
satisfying `p` is a product over all elements with the others replaced by `1`
(`Multiset.prod_map_filter`). Finally, filtering a multiset of pairs on the second coordinate and
projecting to the first recovers the multiplicities of the pairs
(`Multiset.count_map_fst_filter_snd_eq`). In particular, tagging the elements of a family of
multisets `μ j` with an injective label `g j` and adding them up, the part with label `g i`
recovers `μ i` (`Multiset.map_fst_filter_sum_map_prodMk`).
-/

public section

namespace Multiset

variable {α ι : Type*} (p : α → Prop) [DecidablePred p]

/-- Filtering distributes over a finite sum of multisets. -/
@[simp]
theorem filter_sum (s : Finset ι) (f : ι → Multiset α) :
    filter p (∑ i ∈ s, f i) = ∑ i ∈ s, filter p (f i) :=
  map_sum (⟨⟨filter p, filter_zero p⟩, filter_add p⟩ : Multiset α →+ Multiset α) f s

/-- The product of `if p x then a else 1` over a multiset is `a` raised to the number of its
elements satisfying `p`, counted with multiplicity. -/
theorem prod_map_ite_one {M : Type*} [CommMonoid M] (s : Multiset α) (a : M) :
    (s.map fun x ↦ if p x then a else 1).prod = a ^ (s.filter p).card :=
  Quot.inductionOn s fun l ↦ by simp [List.prod_map_ite]

/-- The product of `f` over the elements satisfying `p` is the product over all elements of
`if p x then f x else 1`. -/
@[to_additive /-- The sum of `f` over the elements satisfying `p` is the sum over all elements of
`if p x then f x else 0`. -/]
theorem prod_map_filter {M : Type*} [CommMonoid M] (s : Multiset α) (f : α → M) :
    ((s.filter p).map f).prod = (s.map fun x ↦ if p x then f x else 1).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih => by_cases h : p a <;> simp [h, ih]

/-- Filtering a multiset of pairs on the second coordinate `b` and projecting to the first
coordinate counts `a` as often as the pair `(a, b)` occurs. -/
@[simp]
theorem count_map_fst_filter_snd_eq {β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Multiset (α × β)) (a : α) (b : β) :
    ((s.filter (·.2 = b)).map Prod.fst).count a = s.count (a, b) := by
  rw [count_map, filter_filter, count_eq_card_filter_eq]
  congr 1
  refine filter_congr fun x _ ↦ ?_
  rcases x with ⟨x, y⟩
  simp only [Prod.mk.injEq]
  tauto

section Tagged

variable {β : Type*} [Fintype ι] [DecidableEq β] (μ : ι → Multiset α) {g : ι → β}

/-- Tagging the elements of each `μ j` with an injective label `g j`, the pair `(a, g i)` occurs in
the sum as often as `a` occurs in `μ i`. -/
theorem count_sum_map_prodMk_of_injective [DecidableEq α] (hg : Function.Injective g) (a : α)
    (i : ι) :
    (∑ j, (μ j).map fun x ↦ (x, g j)).count (a, g i) = (μ i).count a := by
  rw [count_sum', Finset.sum_eq_single i]
  · exact count_map_eq_count' _ _ (fun x y hxy ↦ (Prod.ext_iff.1 hxy).1) a
  · intro j _ hj
    refine count_eq_zero_of_notMem fun hmem ↦ hj ?_
    obtain ⟨x, _, hx⟩ := mem_map.1 hmem
    exact hg (Prod.ext_iff.1 hx).2
  · simp

/-- Tagging the elements of each `μ j` with the label `g j`, no pair in the sum carries a label
outside the range of `g`. -/
theorem count_sum_map_prodMk_of_notMem_range [DecidableEq α] (a : α) {b : β}
    (hb : b ∉ Set.range g) :
    (∑ j, (μ j).map fun x ↦ (x, g j)).count (a, b) = 0 := by
  rw [count_sum']
  refine Finset.sum_eq_zero fun j _ ↦ count_eq_zero_of_notMem fun hmem ↦ hb ?_
  obtain ⟨x, _, hx⟩ := mem_map.1 hmem
  exact ⟨j, (Prod.ext_iff.1 hx).2⟩

/-- Tagging the elements of each `μ j` with an injective label `g j` and adding them up, the
elements with label `g i` are those of `μ i`. -/
theorem map_fst_filter_sum_map_prodMk (hg : Function.Injective g) (i : ι) :
    ((∑ j, (μ j).map fun x ↦ (x, g j)).filter (·.2 = g i)).map Prod.fst = μ i := by
  classical
  exact ext.2 fun a ↦ by rw [count_map_fst_filter_snd_eq, count_sum_map_prodMk_of_injective μ hg]

end Tagged

end Multiset
