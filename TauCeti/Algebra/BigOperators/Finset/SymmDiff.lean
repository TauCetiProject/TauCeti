/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Products over a symmetric difference

In a commutative monoid, the product of `f` over the symmetric difference `S ∆ D` of two finite
index sets is the product of the two sub-products `∏_S f` and `∏_D f`, provided the factors over
the shared indices `S ∩ D` are involutions: those terms occur twice on the right and cancel.

## Main results

* `TauCeti.prod_symmDiff`: `∏_{S ∆ D} f = (∏_S f) * (∏_D f)` when `f i ^ 2 = 1` on `S ∩ D`.
-/

public section

open scoped symmDiff

namespace TauCeti

variable {G ι : Type*}

/-- Sub-products over a symmetric difference, when the factors shared by the two index sets are
involutions: `∏_{S ∆ D} f = (∏_S f) * (∏_D f)`, because the terms of `S ∩ D` occur twice on the
right and cancel. -/
theorem prod_symmDiff [CommMonoid G] [DecidableEq ι] (f : ι → G) {S D : Finset ι}
    (hsq : ∀ i ∈ S ∩ D, f i ^ 2 = 1) :
    ∏ i ∈ S ∆ D, f i = (∏ i ∈ S, f i) * ∏ i ∈ D, f i := by
  rw [← Finset.prod_union_inter, ← Finset.prod_sdiff Finset.inter_subset_union, mul_assoc, ← sq,
    ← Finset.prod_pow, Finset.prod_eq_one hsq, mul_one, symmDiff_eq_sup_sdiff_inf]

end TauCeti
