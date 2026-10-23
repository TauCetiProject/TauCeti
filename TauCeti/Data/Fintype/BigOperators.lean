/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fintype.BigOperators

/-!
# Sums over maps of a function of two coordinates

For a finite type `ι` and a finset `s`, a sum over the maps `g : ι → s` of a quantity depending only
on the values at two distinct coordinates `i` and `j` is a sum over the pairs of values, with each
pair counted once for each choice of the remaining `card ι - 2` coordinates. Counting arguments use
this to reduce a sum over labelled copies of a pattern to a sum over one pair of its vertices.
-/

public section

open Finset

namespace Fintype

/-- A sum over the maps `g : ι → s` of a function of the values `g i` and `g j` at two distinct
coordinates counts each pair of values `#s ^ (card ι - 2)` times. This is the two-coordinate
analogue of `Fintype.sum_piFinset_apply`. -/
theorem sum_piFinset_apply_apply {ι κ M : Type*} [Fintype ι] [DecidableEq ι] [AddCommMonoid M]
    {i j : ι} (hij : i ≠ j) (s : Finset κ) (F : κ → κ → M) :
    ∑ g ∈ piFinset fun _ : ι ↦ s, F (g i) (g j) =
      #s ^ (card ι - 2) • ∑ x ∈ s, ∑ y ∈ s, F x y := by
  classical
  -- The maps taking the values `p` at `(i, j)` form a box with `card ι - 2` free coordinates.
  have hfib (p : κ × κ) (hp : p ∈ s ×ˢ s) :
      #{g ∈ piFinset fun _ : ι ↦ s | (g i, g j) = p} = #s ^ (card ι - 2) := by
    rw [mem_product] at hp
    have hj : p.2 ∈ Function.update (fun _ : ι ↦ s) i {p.1} j := by
      simpa [Function.update_of_ne hij.symm] using hp.2
    simp only [Prod.ext_iff, ← filter_filter]
    rw [← piFinset_update_singleton_eq_filter_piFinset_eq (fun _ : ι ↦ s) i hp.1,
      ← piFinset_update_singleton_eq_filter_piFinset_eq _ j hj, card_piFinset]
    simp_rw [Function.apply_update (fun _ ↦ Finset.card (α := κ))]
    rw [prod_update_of_mem (mem_univ j), prod_update_of_mem (by simpa using hij)]
    simp [card_sdiff, hij, Nat.sub_sub]
  rw [← sum_fiberwise_of_maps_to (g := fun g : ι → κ ↦ (g i, g j)) (t := s ×ˢ s)
    fun g hg ↦ mem_product.2 ⟨mem_piFinset.1 hg i, mem_piFinset.1 hg j⟩]
  calc ∑ p ∈ s ×ˢ s, ∑ g ∈ piFinset (fun _ : ι ↦ s) with (g i, g j) = p, F (g i) (g j)
      = ∑ p ∈ s ×ˢ s, #s ^ (card ι - 2) • F p.1 p.2 := by
        refine Finset.sum_congr rfl fun p hp ↦ ?_
        rw [← hfib p hp, ← sum_const]
        exact Finset.sum_congr rfl fun g hg ↦ by rw [← (mem_filter.1 hg).2]
    _ = #s ^ (card ι - 2) • ∑ x ∈ s, ∑ y ∈ s, F x y := by
        rw [sum_nsmul, sum_product]

end Fintype
