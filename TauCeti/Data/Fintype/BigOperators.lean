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
    have hbox : {g ∈ piFinset fun _ : ι ↦ s | (g i, g j) = p} =
        piFinset fun k ↦ if k = i then {p.1} else if k = j then {p.2} else s := by
      ext g
      simp only [mem_filter, mem_piFinset, Prod.ext_iff]
      refine ⟨fun ⟨_, h₁, h₂⟩ k ↦ ?_, fun h ↦ ⟨fun k ↦ ?_, by simpa using h i,
        by simpa [hij.symm] using h j⟩⟩
      · split_ifs with hki hkj
        · simp [hki, h₁]
        · simp [hkj, h₂]
        · exact ‹∀ k, g k ∈ s› k
      · have := h k
        split_ifs at this with hki hkj
        · exact (mem_singleton.1 this) ▸ hp.1
        · exact (mem_singleton.1 this) ▸ hp.2
        · exact this
    rw [hbox, card_piFinset]
    have hcard (k : ι) : #(if k = i then {p.1} else if k = j then {p.2} else s) =
        if k ∈ ({i, j} : Finset ι) then 1 else #s := by
      by_cases hki : k = i <;> by_cases hkj : k = j <;> simp [hki, hkj, hij.symm]
    simp only [hcard, prod_ite, prod_const_one, one_mul, prod_const]
    congr 1
    rw [filter_not, filter_mem_eq_inter, univ_inter, card_sdiff, inter_univ, card_pair hij,
      card_univ]
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
