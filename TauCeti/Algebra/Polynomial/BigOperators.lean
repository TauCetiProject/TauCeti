/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.BigOperators

/-!
# The top coefficient of a finite product of polynomials

If each factor `f i` of a finite product has degree at most `n i`, then the product has degree at
most `∑ i, n i`, and its coefficient in that degree is the product of the coefficients of the
factors in the degrees `n i`. Mathlib proves this for a uniform bound `n`
(`Polynomial.coeff_prod_of_natDegree_le`) and for two factors
(`Polynomial.coeff_mul_add_eq_of_natDegree_le`); here the bounds may vary with the factor. This is
what is needed to read off the top coefficient of a determinant whose columns have different
degree bounds.
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

end Polynomial
