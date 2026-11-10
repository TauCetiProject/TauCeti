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

A sum (or product) over a finite type can be taken fibrewise along any map out of it: sum over
the values the map actually takes, and within each value over the indices sent there.

Mathlib's `Fintype.sum_fiberwise` says this with the outer sum ranging over the whole codomain,
which needs the codomain finite. The version here indexes the outer sum by the *image* instead,
so it applies to a map into an arbitrary type — the situation whenever the codomain is a
quotient or a subtype with no finiteness available.

Regrouping along the coordinate projections of a finite dependent product turns a sum whose
summand is weighted by a sum of coordinate functions into a sum of one-coordinate sums against
the fibrewise masses; this is the algebraic core of multi-marginal linear programming.

Fibres over values the map does not take are empty, so a property holding at `0` (or `1`) and
for the fibre sums over the range holds for the fibre sum over every value of the codomain.

## Main results

* `TauCeti.prod_eq_prod_image_fiber`, `TauCeti.sum_eq_sum_image_fiber`: `∏ i, F i` is the
  product, over the values `g` takes, of the products of `F` over the fibres of `g`.
* `TauCeti.prod_pow_card_filter_eq_prod_comp`, `TauCeti.sum_card_filter_nsmul_eq_sum_comp`: for
  `g` mapping `s` into `t`, `∏ i ∈ s, f (g i)` is the product over `j ∈ t` of `f j` raised to the
  size of the fibre of `g` over `j`.
* `TauCeti.sum_sum_eval_mul`: summing `(∑ i, φ i (z i)) * f z` over a finite dependent product
  regroups, coordinate by coordinate, into `∑ i, ∑ a, φ i a * ∑ z with z i = a, f z`.
* `TauCeti.forall_prod_filter_eq_of_forall_apply`,
  `TauCeti.forall_sum_filter_eq_of_forall_apply`: a property holding at the unit and at fibre
  products over the range holds at every fibre product; for instance a lower bound `c ≤ 0` on
  the fibre sums over the range bounds every fibre sum.
-/

public section

namespace TauCeti

open Finset

/-- **A finite product is the product over the values actually taken of the products over their
fibres.** Multiplying `F` over all of `ι` is multiplying, over each `k` in the image of `g`, the
contribution of the indices `g` sends to `k`.

The outer index is `Finset.univ.image g` rather than all of `κ`, so no finiteness of `κ` is
needed; that is the difference from `Fintype.prod_fiberwise`. -/
@[to_additive /-- **A finite sum is the sum over the values actually taken of the sums over their
fibres.** Summing `F` over all of `ι` is summing, over each `k` in the image of `g`, the
contribution of the indices `g` sends to `k`.

The outer index is `Finset.univ.image g` rather than all of `κ`, so no finiteness of `κ` is
needed; that is the difference from `Fintype.sum_fiberwise`. -/]
theorem prod_eq_prod_image_fiber {ι κ M : Type*} [Fintype ι] [DecidableEq κ] [CommMonoid M]
    (g : ι → κ) (F : ι → M) :
    ∏ i, F i = ∏ k ∈ univ.image g, ∏ i : {i // g i = k}, F i := by
  rw [← prod_fiberwise_of_maps_to (g := g) fun i _ ↦ mem_image_of_mem _ (mem_univ i)]
  exact prod_congr rfl fun k _ ↦ prod_subtype _ (by simp) _

/-- **A product of values along a map, counted by fibres.** If `g` maps `s` into `t`, then
`∏ i ∈ s, f (g i)` is the product over `j ∈ t` of `f j` raised to the number of `i ∈ s` that `g`
sends to `j`. Unlike `Finset.prod_comp`, the outer index is any `t` containing the image. -/
@[to_additive sum_card_filter_nsmul_eq_sum_comp /-- **A sum of values along a map, counted by
fibres.** If `g` maps `s` into `t`, then `∑ i ∈ s, f (g i)` is the sum over `j ∈ t` of `f j` taken
as many times as there are `i ∈ s` that `g` sends to `j`. Unlike `Finset.sum_comp`, the outer index
is any `t` containing the image. -/]
theorem prod_pow_card_filter_eq_prod_comp {ι κ M : Type*} [DecidableEq κ] [CommMonoid M]
    {s : Finset ι} {t : Finset κ} {g : ι → κ} (h : ∀ i ∈ s, g i ∈ t) (f : κ → M) :
    ∏ j ∈ t, f j ^ #{i ∈ s | g i = j} = ∏ i ∈ s, f (g i) := by
  simp_rw [← prod_const]
  exact prod_fiberwise_of_maps_to' h f

/-- **Regrouping a product-indexed sum by coordinates.** Summing `f` against a weight that is a
sum of one-coordinate functions is the same as summing, for each coordinate `i` and each value
`a` there, the value `φ i a` against the mass `f` puts on the fibre `{z | z i = a}`. -/
theorem sum_sum_eval_mul {ι : Type*} {X : ι → Type*} {R : Type*} [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)] [NonUnitalNonAssocSemiring R]
    (φ : ∀ i, X i → R) (f : (∀ i, X i) → R) :
    ∑ z : ∀ i, X i, (∑ i, φ i (z i)) * f z =
      ∑ i, ∑ a, φ i a * ∑ z with z i = a, f z := by
  simp_rw [sum_mul, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [← sum_fiberwise univ (Function.eval i) fun z ↦ φ i (z i) * f z]
  exact sum_congr rfl fun a _ ↦ sum_congr rfl fun z hz ↦ by rw [(mem_filter.1 hz).2]

/-- A property holding at one and at every fibre product over the range holds at every fibre
product, since fibres outside the range are empty. -/
@[to_additive /-- A property holding at zero and at every fibre sum over the range holds at every
fibre sum, since fibres outside the range are empty. -/]
theorem forall_prod_filter_eq_of_forall_apply {ι κ M : Type*} [Fintype ι] [DecidableEq κ]
    [CommMonoid M] {g : ι → κ} {F : ι → M} {p : M → Prop} (unit : p 1)
    (h : ∀ j, p (∏ i with g i = g j, F i)) (k : κ) :
    p (∏ i with g i = k, F i) := by
  by_cases hk : k ∈ Set.range g
  · obtain ⟨j, rfl⟩ := hk
    exact h j
  · rwa [prod_eq_one fun i hi ↦ (hk ⟨i, (mem_filter.mp hi).2⟩).elim]

end TauCeti
