/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Basic

/-!
# Cardinality bounds for finsets

* `Finset.two_le_card_filter_eq_of_no_singleton_fiber_on` and
  `TauCeti.two_le_card_filter_eq_of_no_singleton_fiber`: if every element of a finset (or finite
  type) shares its value under a map with another element, every fiber over the image has at least
  two elements.
* `TauCeti.two_mul_card_image_le_of_no_singleton_fiber`: a map with no singleton fiber has
  at most half as many image elements as domain elements.
* `Finset.card_sdiff_insert_add_one`: adding an element `a ∈ T \ S` to `S` lowers the number of
  elements of `T` outside `S` by one.
* `Finset.subset_induction`: downward induction on `S ⊆ T`, from `T` itself and steps from
  `S ∪ {a}` to `S`. Mathlib's `Finset.induction_on'` is the upward analogue.
* `Finset.card_sdiff_lt_of_card_eq_min`: if `F ⊆ U` has `min k #U` elements of a nonempty `U`
  and `T ⊆ U` has fewer than `k`, then fewer elements of `T` lie outside `F` than in `F`.
-/

public section

namespace Finset

/-- If every element of `s` shares its value under `f` with another element of `s`, then
every fiber of `f` on `s` over `s.image f` has at least two elements. -/
theorem two_le_card_filter_eq_of_no_singleton_fiber_on {ι β : Type*} [DecidableEq β]
    {f : ι → β} (s : Finset ι) (h : ∀ a ∈ s, ∃ b ≠ a, b ∈ s ∧ f b = f a) :
    ∀ y ∈ s.image f, 2 ≤ #{a ∈ s | f a = y} := by
  intro y hy
  obtain ⟨a, ha, rfl⟩ := mem_image.1 hy
  obtain ⟨b, hba, hb, hfb⟩ := h a ha
  exact one_lt_card.2 ⟨a, mem_filter.2 ⟨ha, rfl⟩, b, mem_filter.2 ⟨hb, hfb⟩, hba.symm⟩

variable {ι : Type*} [DecidableEq ι]

/-- Adding an element `a ∈ T \ S` to `S` lowers the number of elements of `T` outside `S` by
one. -/
theorem card_sdiff_insert_add_one {S T : Finset ι} {a : ι} (ha : a ∈ T \ S) :
    #(T \ insert a S) + 1 = #(T \ S) := by
  rw [sdiff_insert, card_erase_add_one ha]

/-- Downward induction on `S ⊆ T`: a property holding at `T`, and passing from `S ∪ {a}` to `S`,
holds for every `S ⊆ T`. -/
theorem subset_induction {T : Finset ι} {P : ∀ S, S ⊆ T → Prop}
    (self : P T Subset.rfl)
    (step : ∀ S a, a ∉ S → ∀ h : insert a S ⊆ T,
      P (insert a S) h → P S ((S.subset_insert a).trans h)) (S : Finset ι) (h : S ⊆ T) :
    P S h := by
  induction hk : #(T \ S) generalizing S with
  | zero =>
    obtain rfl := Subset.antisymm h (sdiff_eq_empty_iff_subset.1 (card_eq_zero.1 hk))
    exact self
  | succ k ih =>
    obtain ⟨a, ha⟩ := card_pos.1 (by omega : 0 < #(T \ S))
    have h' : insert a S ⊆ T := insert_subset (mem_sdiff.1 ha).1 h
    exact step S a (mem_sdiff.1 ha).2 h'
      (ih _ h' (by have := card_sdiff_insert_add_one ha; omega))

/-- If `F` has `min k #U` of the elements of a nonempty set `U`, and `T ⊆ U` has fewer than `k`
elements, then fewer elements of `T` lie outside `F` than in `F`. -/
theorem card_sdiff_lt_of_card_eq_min {F T U : Finset ι} {k : ℕ}
    (hFU : F ⊆ U) (hTU : T ⊆ U) (hU : U.Nonempty) (hF : #F = min k #U) (hT : #T < k) :
    #(T \ F) < #F := by
  by_cases hkU : k ≤ #U
  · exact (card_le_card sdiff_subset).trans_lt (by omega)
  · rw [eq_of_subset_of_card_le hFU (by omega), sdiff_eq_empty_iff_subset.2 hTU, card_empty]
    exact hU.card_pos

end Finset

namespace TauCeti

open Finset

variable {ι β : Type*} [Fintype ι] [DecidableEq β] {f : ι → β}

/-- If every element of a finite type shares its value under `f` with another element, then
every fiber of `f` over its image has at least two elements. -/
theorem two_le_card_filter_eq_of_no_singleton_fiber (h : ∀ a, ∃ b ≠ a, f b = f a) :
    ∀ y ∈ univ.image f, 2 ≤ #{a | f a = y} :=
  univ.two_le_card_filter_eq_of_no_singleton_fiber_on fun a _ ↦
    let ⟨b, hba, hb⟩ := h a; ⟨b, hba, mem_univ b, hb⟩

/-- A map whose fibers contain at least two elements has at most half as many image elements
as domain elements. -/
theorem two_mul_card_image_le_of_no_singleton_fiber (h : ∀ a, ∃ b ≠ a, f b = f a) :
    2 * #(univ.image f) ≤ Fintype.card ι := by
  simpa only [card_univ] using
    mul_card_image_le_card univ 2 (two_le_card_filter_eq_of_no_singleton_fiber h)

end TauCeti
