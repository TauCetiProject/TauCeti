/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Group.Int.Units
public import Mathlib.Algebra.Ring.Int.Units
public import Mathlib.Data.Set.Card

/-!
# Finite products and sums of integer signs

A finite product of integers taking values in `{-1, 1}` differs from `1` exactly when
it equals `-1`. The statement includes the empty product and imposes sign hypotheses
only on the factors in the indexing finset.

A finite sum of integer units is the number of terms equal to `1` minus the number of terms
equal to `-1`.
-/

public section

namespace Int

/-- A finite product of integer signs differs from `1` exactly when it equals `-1`. -/
theorem prod_ne_one_iff_eq_neg_one {ι : Type*} {s : Finset ι} {f : ι → ℤ}
    (hf : ∀ i ∈ s, f i = 1 ∨ f i = -1) :
    (∏ i ∈ s, f i) ≠ 1 ↔ (∏ i ∈ s, f i) = -1 :=
  isUnit_ne_iff_eq_neg
    (IsUnit.prod_iff.mpr fun i hi ↦ isUnit_iff.mpr (hf i hi)) isUnit_one

/-- The sum of a family of integer units over a finite type is the number of indices at which it
is `1` minus the number of indices at which it is `-1`. -/
theorem finsum_units_eq_ncard_sub_ncard {ι : Type*} [Finite ι] (s : ι → ℤˣ) :
    ∑ᶠ i, (s i : ℤ) = ({i | s i = 1}.ncard : ℤ) - {i | s i = -1}.ncard := by
  classical
  have := Fintype.ofFinite ι
  rw [finsum_eq_sum_of_fintype, ← Finset.coe_filter_univ, ← Finset.coe_filter_univ,
    Set.ncard_coe_finset, Set.ncard_coe_finset, Finset.natCast_card_filter,
    Finset.natCast_card_filter, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rcases units_eq_one_or (s i) with h | h <;> simp [h, Units.ext_iff]

end Int
