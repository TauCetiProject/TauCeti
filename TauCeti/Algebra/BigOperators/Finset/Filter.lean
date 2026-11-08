/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Filtered products

Weakening the condition `P` of a filtered product over `s` to `P i ∨ i = c`, for a point `c`
with `¬P c`, multiplies the product by the factor at `c` exactly when `c ∈ s`. This is the
bookkeeping that adds a closed endpoint to a sum over the points of a finite set in an open
interval.

For a family `u` in a commutative monoid with levels `k : ι → ℕ`, if the products
`∏_{i ∈ s} u i ^ (k i - j)` equal one for all `j`, then so do the products of the `u i` of each
level `m ≥ 1`.

## Main results

* `Finset.prod_filter_or_eq_of_not`, `Finset.sum_filter_or_eq_of_not`: adjoining one point to
  the condition of a filtered product or sum.
* `Finset.prod_subtype_eq_prod_of_mem`, `Finset.sum_subtype_eq_sum_of_mem`: reindexing a product or
  sum over `Subtype p` to a finite superset `s` when the factors on `s` outside `p` are trivial.
* `Finset.prod_filter_eq_one_of_forall_prod_pow_tsub_eq_one`: the level products of a family are
  trivial when all its truncated power products are.
-/

public section

namespace TauCeti

/-- Adjoining a point `c` with `¬P c` to the condition `P` of a filtered product over `s`
multiplies it by the factor at `c` exactly when `c ∈ s`. -/
@[to_additive /-- Adjoining a point `c` with `¬P c` to the condition `P` of a filtered sum over
`s` adds the term at `c` exactly when `c ∈ s`. -/]
theorem _root_.Finset.prod_filter_or_eq_of_not {ι M : Type*} [DecidableEq ι] [CommMonoid M]
    (s : Finset ι) (f : ι → M) (P : ι → Prop) [DecidablePred P] {c : ι} (hc : ¬P c) :
    ∏ i ∈ s with P i ∨ i = c, f i = (∏ i ∈ s with P i, f i) * if c ∈ s then f c else 1 := by
  rw [Finset.filter_or, Finset.prod_union (by grind [Finset.disjoint_filter]), Finset.filter_eq']
  split_ifs <;> simp

/-- If `s` contains every element satisfying `p` and `f` equals `1` on `s` outside `p`, then the
product of `f` over `Subtype p` equals its product over `s`. Unlike `Finset.prod_congr_set`, the
ambient type `ι` need not be finite. -/
@[to_additive /-- If `s` contains every element satisfying `p` and `f` vanishes on `s` outside `p`,
then the sum of `f` over `Subtype p` equals its sum over `s`. Unlike `Finset.sum_congr_set`, the
ambient type `ι` need not be finite. -/]
theorem _root_.Finset.prod_subtype_eq_prod_of_mem {ι M : Type*} [CommMonoid M]
    {p : ι → Prop} [Fintype (Subtype p)] (s : Finset ι)
    (hs : ∀ x, p x → x ∈ s) (f : ι → M) (hf : ∀ x ∈ s, ¬p x → f x = 1) :
    (∏ x : Subtype p, f x) = ∏ x ∈ s, f x := by
  classical
  rw [← Finset.prod_subtype (s.filter p) (by grind)]
  exact Finset.prod_filter_of_ne fun x hx hfx => by_contra (hfx <| hf x hx ·)

/-- If `∏_{i ∈ s} u i ^ (k i - j) = 1` for every `j`, then the product of the `u i` with `k i = m`
is `1` for every `m ≥ 1`. -/
theorem _root_.Finset.prod_filter_eq_one_of_forall_prod_pow_tsub_eq_one {ι M : Type*}
    [CommMonoid M] (s : Finset ι) (k : ι → ℕ) (u : ι → M)
    (h : ∀ j, ∏ i ∈ s, u i ^ (k i - j) = 1) {m : ℕ} (hm : 0 < m) :
    ∏ i ∈ s with k i = m, u i = 1 := by
  -- Lowering `j` by one multiplies the product by the factors with `j < k i`, so these
  -- products are all trivial.
  have hgt (j : ℕ) : ∏ i ∈ s with j < k i, u i = 1 := by
    have hj : ∏ i ∈ s, u i ^ (k i - j) =
        (∏ i ∈ s, u i ^ (k i - (j + 1))) * ∏ i ∈ s with j < k i, u i := by
      rw [Finset.prod_filter, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ ↦ ?_
      split_ifs with hji
      · rw [← pow_succ]
        congr 1
        omega
      · rw [mul_one]
        congr 1
        omega
    rwa [h, h, one_mul, eq_comm] at hj
  -- The factors with `m - 1 < k i` are those with `k i = m` and those with `m < k i`.
  calc ∏ i ∈ s with k i = m, u i
      = (∏ i ∈ s with k i = m, u i) * ∏ i ∈ s with m < k i, u i := by rw [hgt, mul_one]
    _ = ∏ i ∈ s with m - 1 < k i, u i := by
        simp only [Finset.prod_filter, ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun i _ ↦ ?_
        split_ifs <;> first | omega | simp
    _ = 1 := hgt _

end TauCeti
