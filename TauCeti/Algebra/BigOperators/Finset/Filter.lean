/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Adjoining one point to the condition of a filtered product

Weakening the condition `P` of a filtered product over `s` to `P i ∨ i = c`, for a point `c`
with `¬P c`, multiplies the product by the factor at `c` exactly when `c ∈ s`. This is the
bookkeeping that adds a closed endpoint to a sum over the points of a finite set in an open
interval.

## Main results

* `Finset.prod_filter_or_eq_of_not`, `Finset.sum_filter_or_eq_of_not`: adjoining one point to
  the condition of a filtered product or sum.
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
  rw [Finset.filter_or, Finset.prod_union (Finset.disjoint_filter.mpr fun i _ hi (hic : i = c) =>
    hc (hic ▸ hi)), Finset.filter_eq']
  split_ifs <;> simp

end TauCeti
