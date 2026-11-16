/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Coefficient vectors under variable embeddings

The embedding `Polynomial.toMvPolynomial i` reindexes the native coefficient vector
by sending an exponent `n` to the multivariate exponent `Finsupp.single i n`.
This description lets coefficient constructions commute with placement in one coordinate.
In particular, the partial degree of the placed polynomial in `Xᵢ` is its natural degree.
-/

public section

namespace Polynomial

variable {R σ : Type*} [CommSemiring R]

/-- Placement in one coordinate reindexes the native coefficient vector by the
corresponding single-coordinate exponent embedding. -/
theorem coeff_toMvPolynomial_eq_embDomain (p : Polynomial R) (i : σ) :
    AddMonoidAlgebra.coeff (p.toMvPolynomial i) =
      p.coeff.embDomain ⟨Finsupp.single i, Finsupp.single_injective i⟩ := by
  classical
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [_root_.map_add, AddMonoidAlgebra.coeff_add, Finsupp.embDomain_add, hp, hq]
  | monomial n c =>
    rw [Polynomial.coeff_monomial, Finsupp.embDomain_single]
    simp [← Polynomial.C_mul_X_pow_eq_monomial, MvPolynomial.C_mul_X_pow_eq_monomial,
      ← MvPolynomial.single_eq_monomial, AddMonoidAlgebra.coeff_single]

/-- Placement in the coordinate `Xᵢ` turns the natural degree into the partial degree in `Xᵢ`. -/
@[simp]
theorem degreeOf_toMvPolynomial (p : Polynomial R) (i : σ) :
    (p.toMvPolynomial i).degreeOf i = p.natDegree := by
  -- The exponents of the placed polynomial are the `Finsupp.single i n` with `n ∈ p.support`.
  rw [MvPolynomial.degreeOf_eq_sup, ← MvPolynomial.finsupp_support_eq_support,
    coeff_toMvPolynomial_eq_embDomain, Finsupp.support_embDomain, Finset.sup_map]
  -- Their `i`-th entries are the exponents `n`, whose supremum is the natural degree.
  rw [← supDegree_eq_natDegree, AddMonoidAlgebra.supDegree]
  exact Finset.sup_congr rfl fun _ _ ↦ Finsupp.single_eq_same

end Polynomial
