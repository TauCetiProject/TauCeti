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
(`Multiset.count_map_fst_filter_snd_eq`).
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
theorem count_map_fst_filter_snd_eq {β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Multiset (α × β)) (a : α) (b : β) :
    ((s.filter (·.2 = b)).map Prod.fst).count a = s.count (a, b) := by
  rw [count_map, filter_filter, count_eq_card_filter_eq]
  congr 1
  refine filter_congr fun x _ ↦ ?_
  rcases x with ⟨x, y⟩
  simp only [Prod.mk.injEq]
  tauto

end Multiset
