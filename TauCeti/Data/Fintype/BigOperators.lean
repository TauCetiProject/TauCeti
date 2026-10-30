/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fintype.BigOperators

/-!
# Sums over maps of a function of two coordinates

For a finite type `ι` and finite coordinate sets `s i`, a sum over maps taking their `i`th value
in `s i` of a quantity depending only on two distinct coordinates is a sum over the pairs of
values, with each pair counted once for every choice of the remaining coordinates.
Counting arguments use
this to reduce a sum over labelled copies of a pattern to a sum over one pair of its vertices.
-/

public section

open Finset

namespace Fintype

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

end Fintype
