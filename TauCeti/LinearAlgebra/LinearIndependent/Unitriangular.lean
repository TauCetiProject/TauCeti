/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Order.Preorder.Finite

/-!
# Linear independence under a unitriangular change

Let `x` be a family indexed by a preorder, and let every `z j` be `x j` plus a combination of the
earlier `x l`. If `x` is linearly independent, then so is `z`. The family `x` need not span the
ambient module, the index type is any preorder, and no subtraction is needed: over a semiring with
cancellative addition, write `z j = x j + ∑ l, d j l • x l` with `d j` supported below `j`. Two
combinations of the `z l` with equal values give, by independence of `x`, equal coefficient
families `f + ∑ l, f l • d l` and `g + ∑ l, g l • d l`. At a maximal index `j` where `f` and `g`
differ, the two sums have the same coefficient at `j`, so cancelling it gives `f j = g j`.

## Main results

* `LinearIndependent.of_eq_add_mem_span_image_Iio`: a unitriangular change of a linearly
  independent family is linearly independent.

## Attribution

The statement is adapted from Tau Ceti pull request
[#34591](https://github.com/TauCetiProject/TauCeti/pull/34591).
-/

public section

open Submodule

variable {R M ι : Type*} [Semiring R] [IsCancelAdd R] [AddCommMonoid M] [Module R M]
  [Preorder ι]

/-- **A unitriangular change of a linearly independent family is linearly independent.** Let `x`
be a family indexed by a preorder and let every `z j` be `x j` plus a combination of the earlier
`x l`. If `x` is linearly independent, then so is `z`. -/
theorem LinearIndependent.of_eq_add_mem_span_image_Iio {x z : ι → M}
    (hx : LinearIndependent R x) (h : ∀ j, ∃ u ∈ span R (x '' Set.Iio j), z j = x j + u) :
    LinearIndependent R z := by
  classical
  -- Write `z j = x j + ∑ l, d j l • x l` with `d j` supported below `j`.
  have h' (j : ι) : ∃ d ∈ Finsupp.supported R R (Set.Iio j),
      z j = x j + Finsupp.linearCombination R x d := by
    obtain ⟨u, hu, hzu⟩ := h j
    obtain ⟨d, hd, rfl⟩ := (Finsupp.mem_span_image_iff_linearCombination R).1 hu
    exact ⟨d, hd, hzu⟩
  choose d hd hdz using h'
  -- The combinations of `z` are those of `x` after the change `f ↦ f + ∑ l, f l • d l`.
  have hz : Finsupp.linearCombination R z =
      Finsupp.linearCombination R x ∘ₗ (LinearMap.id + Finsupp.linearCombination R d) := by
    ext j
    simp [hdz]
  intro f g hfg
  rw [hz] at hfg
  have hfg' : f + Finsupp.linearCombination R d f = g + Finsupp.linearCombination R d g := hx hfg
  by_contra hne
  obtain ⟨i, hi⟩ := DFunLike.ne_iff.1 hne
  set s := f.support ∪ g.support
  -- A maximal index `j` where `f` and `g` differ.
  obtain ⟨j, hjmax⟩ := (s.filter fun l ↦ f l ≠ g l).exists_maximal
    ⟨i, Finset.mem_filter.2 ⟨by by_contra hs; simp_all [s], hi⟩⟩
  obtain ⟨-, hj⟩ := Finset.mem_filter.1 hjmax.prop
  have hsum (h : ι →₀ R) (hs : h.support ⊆ s) :
      Finsupp.linearCombination R d h j = ∑ l ∈ s, h l * d l j := by
    rw [Finsupp.linearCombination_apply_of_mem_supported R (Finset.coe_subset.2 hs),
      Finsupp.finsetSum_apply]
    simp
  -- The changes of `f` and `g` agree at `j`: above `j` the coefficients agree, and `d l` vanishes
  -- at `j` unless `j < l`.
  have hd_eq : Finsupp.linearCombination R d f j = Finsupp.linearCombination R d g j := by
    rw [hsum f Finset.subset_union_left, hsum g Finset.subset_union_right]
    refine Finset.sum_congr rfl fun l hl ↦ ?_
    by_cases hjl : j < l
    · by_contra hfl
      exact hjmax.not_gt (Finset.mem_filter.2 ⟨hl, fun h ↦ hfl (by rw [h])⟩) hjl
    · rw [(Finsupp.mem_supported' _ _).1 (hd l) j hjl, mul_zero, mul_zero]
  have hj' := DFunLike.congr_fun hfg' j
  rw [Finsupp.add_apply, Finsupp.add_apply, hd_eq] at hj'
  exact hj (add_right_cancel hj')
