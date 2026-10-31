/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fintype.BigOperators

/-!
# Sums over finite types

A sum of values that are all equal to `d` on the indices satisfying `p`, and zero elsewhere, is
the number of such indices times `d` (`Fintype.sum_ite_eq_card_nsmul`).

For a finite type `ι` and finite coordinate sets `s i`, a sum over maps taking their `i`th value
in `s i` of a quantity depending only on two distinct coordinates is a sum over the pairs of
values, with each pair counted once for every choice of the remaining coordinates.
Counting arguments use
this to reduce a sum over labelled copies of a pattern to a sum over one pair of its vertices.

More generally, any sum over such a box splits at two distinct coordinates `i` and `j`: sum over
the maps with prescribed values at `i` and `j`, and then over all values of the two coordinates,
substituted with `Function.update`. Telescoping arguments use this to test one pair of
coordinates while the others stay fixed.
-/

public section

open Finset

namespace Fintype

/-- A sum of values `f i` over the indices satisfying `p`, all of which are equal to `d`, is the
number of such indices times `d`. -/
theorem sum_ite_eq_card_nsmul {ι M : Type*} [Fintype ι] [AddCommMonoid M] {p : ι → Prop}
    [DecidablePred p] {f : ι → M} {d : M} (hf : ∀ i, p i → f i = d) :
    (∑ i, if p i then f i else 0) = Fintype.card {i // p i} • d := by
  rw [Fintype.card_subtype, ← sum_filter]
  exact sum_eq_card_nsmul fun i hi ↦ hf i (mem_filter.1 hi).2

/-- A sum of a function of two distinct coordinates over a finite box counts each pair
of values once for every choice of the remaining coordinates. -/
theorem sum_piFinset_apply_apply {ι κ M : Type*} [Fintype ι] [DecidableEq ι] [AddCommMonoid M]
    {i j : ι} (hij : i ≠ j) (s : ι → Finset κ) (F : κ → κ → M) :
    ∑ g ∈ piFinset s, F (g i) (g j) =
      (∏ k ∈ univ \ {i, j}, #(s k)) • ∑ x ∈ s i, ∑ y ∈ s j, F x y := by
  classical
  have hfib (p : κ × κ) (hp : p ∈ s i ×ˢ s j) :
      #{g ∈ piFinset s | (g i, g j) = p} = ∏ k ∈ univ \ {i, j}, #(s k) := by
    rw [mem_product] at hp
    have hj : p.2 ∈ Function.update s i {p.1} j := by
      simpa [Function.update_of_ne hij.symm] using hp.2
    simp only [Prod.ext_iff, ← filter_filter]
    rw [← piFinset_update_singleton_eq_filter_piFinset_eq s i hp.1,
      ← piFinset_update_singleton_eq_filter_piFinset_eq _ j hj, card_piFinset]
    simp_rw [Function.apply_update (fun _ ↦ Finset.card (α := κ))]
    rw [prod_update_of_mem (mem_univ j), prod_update_of_mem (by simpa using hij)]
    simp only [card_singleton, one_mul]
    congr 1
    ext k
    simp [and_comm]
  rw [← sum_fiberwise_of_maps_to (g := fun g : ι → κ ↦ (g i, g j)) (t := s i ×ˢ s j)
    fun g hg ↦ mem_product.2 ⟨mem_piFinset.1 hg i, mem_piFinset.1 hg j⟩]
  calc ∑ p ∈ s i ×ˢ s j, ∑ g ∈ piFinset s with (g i, g j) = p, F (g i) (g j)
      = ∑ p ∈ s i ×ˢ s j, (∏ k ∈ univ \ {i, j}, #(s k)) • F p.1 p.2 := by
        refine Finset.sum_congr rfl fun p hp ↦ ?_
        rw [← hfib p hp, ← sum_const]
        exact Finset.sum_congr rfl fun g hg ↦ by rw [← (mem_filter.1 hg).2]
    _ = (∏ k ∈ univ \ {i, j}, #(s k)) • ∑ x ∈ s i, ∑ y ∈ s j, F x y := by
        rw [sum_nsmul, sum_product]

/-- A sum over a finite box splits at two distinct coordinates `i` and `j`: for values
`a ∈ s i` and `b ∈ s j`, each map in the box arises exactly once by overwriting the `i`th and `j`th
values of a map in the box taking the values `a` at `i` and `b` at `j`. -/
theorem sum_piFinset_eq_sum_filter_sum_sum_update {ι κ M : Type*} [Fintype ι] [DecidableEq ι]
    [DecidableEq κ] [AddCommMonoid M] {i j : ι} (hij : i ≠ j) (s : ι → Finset κ) {a b : κ}
    (ha : a ∈ s i) (hb : b ∈ s j) (F : (ι → κ) → M) :
    ∑ g ∈ piFinset s, F g =
      ∑ h ∈ piFinset s with h i = a ∧ h j = b, ∑ x ∈ s i, ∑ y ∈ s j,
        F (Function.update (Function.update h i x) j y) := by
  simp_rw [← sum_product']
  refine sum_nbij' (fun g ↦ (Function.update (Function.update g i a) j b, g i, g j))
    (fun q ↦ Function.update (Function.update q.1 i q.2.1) j q.2.2) ?_ ?_ ?_ ?_ ?_
  · intro g hg
    simp only [mem_piFinset, mem_product, mem_filter] at hg ⊢
    refine ⟨⟨fun l ↦ ?_, by simp [hij]⟩, hg i, hg j⟩
    simp only [Function.update_apply]
    split_ifs <;> simp_all
  · rintro ⟨h, x, y⟩ hq
    simp only [mem_piFinset, mem_product, mem_filter] at hq ⊢
    intro l
    simp only [Function.update_apply]
    split_ifs <;> simp_all
  · intro g _
    ext l
    simp only [Function.update_apply]
    split_ifs <;> simp_all
  · rintro ⟨h, x, y⟩ hq
    simp only [mem_piFinset, mem_product, mem_filter] at hq
    obtain ⟨⟨-, rfl, rfl⟩, -, -⟩ := hq
    ext l <;> simp only [Function.update_apply] <;> split_ifs <;> simp_all
  · intro g _
    congr 1
    ext l
    simp only [Function.update_apply]
    split_ifs <;> simp_all

end Fintype
