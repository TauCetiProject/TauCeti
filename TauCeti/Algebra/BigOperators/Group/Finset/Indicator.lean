/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.Indicator
public import Mathlib.Data.Set.Pairwise.Basic

/-!
# Finite products of indicators

At a point `x ∈ t i`, a finite product `∏ j ∈ s, (t j).mulIndicator (f j) x` over pairwise disjoint
sets `t j` reduces to its `i`-th factor `f i x`, since every other factor is `1`
(`Finset.prod_mulIndicator_apply_of_mem`). Additively, a sum of indicators of pairwise disjoint
sets takes at `x ∈ t i` the value of its `i`-th summand (`Finset.sum_indicator_apply_of_mem`).
This is how step functions `∑ i, 1_{t i} • c i` on a finite partition are evaluated.
For pairwise disjoint sets, a product of multiplicative indicators is one plus the sum of
the corresponding indicators of `f i - 1` (`Finset.prod_mulIndicator_eq_one_add_sum_indicator`).

If `g` is injective on `s`, the function `s.mulIndicator (f ∘ g)` reads `f` along `g` on `s` and
is `1` off `s`, so it takes each value of `f` at most once. Hence a finite product over `t` of
`h (s.mulIndicator (f ∘ g) j)`, for any `h` with `h 1 = 1`, is the product of `h (f k)` over the
image under `g` of the points of `t` in `s` (`Finset.prod_apply_mulIndicator_comp_eq_prod_image`).
With `h = ‖·‖ ^ r` this compares the `ℓᵖ` sums of a reindexed sequence with those of the original.
-/

public section

open Set

namespace Finset

variable {ι κ β : Type*} [CommMonoid β]

/-- On a family of pairwise disjoint sets, a product of multiplicative indicators takes at
`x ∈ t i` the value of the `i`-th factor. -/
@[to_additive /-- On a family of pairwise disjoint sets, a sum of indicators takes at `x ∈ t i`
the value of the `i`-th summand. -/]
theorem prod_mulIndicator_apply_of_mem {s : Finset ι} {t : ι → Set κ}
    (hs : (s : Set ι).PairwiseDisjoint t) {i : ι} (hi : i ∈ s) {x : κ} (hx : x ∈ t i)
    (f : ι → κ → β) : ∏ j ∈ s, (t j).mulIndicator (f j) x = f i x := by
  rw [prod_eq_single_of_mem i hi fun j hj hji ↦ mulIndicator_of_notMem
    (Set.disjoint_left.1 (hs hi hj hji.symm) hx) _, mulIndicator_of_mem hx]

/-- A product of multiplicative indicators of pairwise disjoint sets is one plus the sum
of the indicators of each factor minus one. -/
theorem prod_mulIndicator_eq_one_add_sum_indicator [AddCommGroup β]
    (s : Finset ι) {t : ι → Set κ} (hs : (s : Set ι).PairwiseDisjoint t)
    (f : ι → κ → β) (x : κ) :
    ∏ i ∈ s, (t i).mulIndicator (f i) x =
      1 + ∑ i ∈ s, (t i).indicator (fun x ↦ f i x - 1) x := by
  classical
  by_cases hx : ∃ i ∈ s, x ∈ t i
  · obtain ⟨i, hi, hx⟩ := hx
    rw [prod_mulIndicator_apply_of_mem hs hi hx,
      sum_indicator_apply_of_mem hs hi hx]
    simp
  · have hn : ∀ i ∈ s, x ∉ t i := by simpa using hx
    rw [prod_eq_one (fun i hi ↦ mulIndicator_of_notMem (hn i hi) _),
      sum_eq_zero (fun i hi ↦ indicator_of_notMem (hn i hi) _), add_zero]

/-- If `g` is injective on `s` and `h 1 = 1`, a product over `t` of `h` applied to the function
reading `f` along `g` on `s` and equal to `1` off `s` is the product of `h ∘ f` over the image
under `g` of the points of `t` in `s`. -/
@[to_additive /-- If `g` is injective on `s` and `h 0 = 0`, a sum over `t` of `h` applied to the
function reading `f` along `g` on `s` and vanishing off `s` is the sum of `h ∘ f` over the image
under `g` of the points of `t` in `s`. -/]
theorem prod_apply_mulIndicator_comp_eq_prod_image {M : Type*} [One M] [DecidableEq κ]
    {h : M → β} (h1 : h 1 = 1) {f : κ → M} {g : ι → κ} {s : Set ι} [DecidablePred (· ∈ s)]
    (hg : s.InjOn g) (t : Finset ι) :
    ∏ j ∈ t, h (s.mulIndicator (f ∘ g) j) = ∏ k ∈ {j ∈ t | j ∈ s}.image g, h (f k) := by
  rw [prod_image fun j hj j' hj' ↦ hg (mem_filter.1 hj).2 (mem_filter.1 hj').2, prod_filter]
  exact prod_congr rfl fun j _ ↦ by by_cases hj : j ∈ s <;> simp [hj, h1]

end Finset
