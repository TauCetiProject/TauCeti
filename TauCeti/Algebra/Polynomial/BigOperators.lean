/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.BigOperators

/-!
# Finite products of polynomials

If each factor `f i` of a finite product has degree at most `n i`, then the product has degree at
most `∑ i, n i`, and its coefficient in that degree is the product of the coefficients of the
factors in the degrees `n i`. Mathlib proves this for a uniform bound `n`
(`Polynomial.coeff_prod_of_natDegree_le`) and for two factors
(`Polynomial.coeff_mul_add_eq_of_natDegree_le`); here the bounds may vary with the factor. This is
what is needed to read off the top coefficient of a determinant whose columns have different
degree bounds.

This file also groups products of linear factors according to their constant terms.
-/

public section

namespace Polynomial

open Finset

variable {ι R : Type*} [CommSemiring R]

/-- If each factor `f i` has degree at most `n i`, the coefficient of the product in degree
`∑ i ∈ s, n i` is the product of the coefficients of the factors in the degrees `n i`. -/
theorem coeff_prod_sum_eq_of_natDegree_le (s : Finset ι) (f : ι → R[X]) (n : ι → ℕ)
    (h : ∀ i ∈ s, (f i).natDegree ≤ n i) :
    (∏ i ∈ s, f i).coeff (∑ i ∈ s, n i) = ∏ i ∈ s, (f i).coeff (n i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hs : ∀ i ∈ s, (f i).natDegree ≤ n i := fun i hi ↦ h i (mem_insert_of_mem hi)
    rw [prod_insert ha, sum_insert ha, prod_insert ha,
      coeff_mul_add_eq_of_natDegree_le (h a (mem_insert_self a s))
        ((natDegree_prod_le (s := s) (f := f)).trans (sum_le_sum hs)), ih hs]

noncomputable section ProductGrouping

variable [Fintype ι]

/-- A local classical equality decision used to group the constant terms. -/
local instance instDecidableEqProductGrouping : DecidableEq R := Classical.decEq R

/-- The product of the linear factors whose constant term equals `a` is the corresponding power
of `X + C a`. -/
theorem pow_card_filter_eq_prod_X_add_C (f : ι → R) (a : R) :
    (X + C a) ^ #{i | f i = a} = ∏ i with f i = a, (X + C (f i)) := by
  rw [← prod_const]
  exact prod_congr rfl fun i hi ↦ by rw [(mem_filter.1 hi).2]

/-- Group a product of linear factors according to whether their constant term equals `a`. -/
theorem prod_X_add_C_eq_pow_card_filter_mul_prod_filter_ne (f : ι → R) (a : R) :
    ∏ i, (X + C (f i)) =
      (X + C a) ^ #{i | f i = a} * ∏ i with f i ≠ a, (X + C (f i)) := by
  rw [pow_card_filter_eq_prod_X_add_C, prod_filter_mul_prod_filter_not]

end ProductGrouping

end Polynomial
