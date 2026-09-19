/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Regrouping a finite sum by the fibres of a map

A sum over a finite type can be taken fibrewise along any map out of it: sum over the values the
map actually takes, and within each value over the indices sent there.

Mathlib's `Fintype.sum_fiberwise` says this with the outer sum ranging over the whole codomain,
which needs the codomain finite. The version here indexes the outer sum by the *image* instead,
so it applies to a map into an arbitrary type — the situation whenever the codomain is a
quotient or a subtype with no finiteness available.

Regrouping along the coordinate projections of a finite dependent product turns a sum whose
summand is weighted by a sum of coordinate functions into a sum of one-coordinate sums against
the fibrewise masses; this is the algebraic core of multi-marginal linear programming.

Fibres over values the map does not take are empty, so a bound below `0` that holds for the
fibre sums over the range holds for the fibre sum over every value of the codomain.

## Main results

* `TauCeti.sum_eq_sum_image_fiber`: `∑ i, F i` is the sum, over the values `g` takes, of the sums
  of `F` over the fibres of `g`.
* `TauCeti.sum_sum_eval_mul`: summing `(∑ i, φ i (z i)) * f z` over a finite dependent product
  regroups, coordinate by coordinate, into `∑ i, ∑ a, φ i a * ∑ z with z i = a, f z`.
* `TauCeti.lt_sum_filter_eq_of_forall_apply`: a negative lower bound for the fibre sums of `g`
  over its range is a lower bound for the fibre sum over every value.
-/

public section

namespace TauCeti

open Finset

/-- **A finite sum is the sum over the values actually taken of the sums over their fibres.**
Summing `F` over all of `ι` is summing, over each `k` in the image of `g`, the contribution of
the indices `g` sends to `k`.

The outer index is `Finset.univ.image g` rather than all of `κ`, so no finiteness of `κ` is
needed; that is the difference from `Fintype.sum_fiberwise`. -/
theorem sum_eq_sum_image_fiber {ι κ M : Type*} [Fintype ι] [DecidableEq κ] [AddCommMonoid M]
    (g : ι → κ) (F : ι → M) :
    ∑ i, F i = ∑ k ∈ univ.image g, ∑ i : {i // g i = k}, F i := by
  rw [← sum_fiberwise_of_maps_to (g := g) fun i _ ↦ mem_image_of_mem _ (mem_univ i)]
  exact sum_congr rfl fun k _ ↦
    sum_subtype (p := fun i ↦ g i = k) (univ.filter fun i ↦ g i = k) (fun i ↦ by simp) F

/-- **Regrouping a product-indexed sum by coordinates.** Summing `f` against a weight that is a
sum of one-coordinate functions is the same as summing, for each coordinate `i` and each value
`a` there, the value `φ i a` against the mass `f` puts on the fibre `{z | z i = a}`. -/
theorem sum_sum_eval_mul {ι : Type*} {X : ι → Type*} {R : Type*} [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)] [NonUnitalNonAssocSemiring R]
    (φ : ∀ i, X i → R) (f : (∀ i, X i) → R) :
    ∑ z : ∀ i, X i, (∑ i, φ i (z i)) * f z =
      ∑ i, ∑ a, φ i a * ∑ z with z i = a, f z := by
  simp_rw [sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [← sum_fiberwise univ (Function.eval i) fun z ↦ φ i (z i) * f z]
  refine sum_congr rfl fun a _ ↦ ?_
  rw [mul_sum]
  refine sum_congr rfl fun z hz ↦ ?_
  have hz' : z i = a := (mem_filter.1 hz).2
  rw [hz']

/-- **A negative lower bound on the fibre sums over the range bounds every fibre sum.** A value
`k` outside the range of `g` has an empty fibre, so the sum over it is the empty sum `0`, which
lies above `c` by hypothesis. -/
theorem lt_sum_filter_eq_of_forall_apply {ι κ M : Type*} [Fintype ι] [DecidableEq κ]
    [AddCommMonoid M] [Preorder M] {g : ι → κ} {F : ι → M} {c : M} (hc : c < 0)
    (h : ∀ j, c < ∑ i with g i = g j, F i) (k : κ) :
    c < ∑ i with g i = k, F i := by
  by_cases hk : k ∈ Set.range g
  · obtain ⟨j, rfl⟩ := hk
    exact h j
  · rwa [sum_eq_zero fun i hi => (hk ⟨i, (mem_filter.mp hi).2⟩).elim]

end TauCeti
