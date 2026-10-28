/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DualNumber
public import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Evaluating multivariate polynomials at dual numbers

Evaluating a polynomial `p` over `R` at the point of `R[ε]`, `ε² = 0`, whose coordinate `i` is
`ε` and whose other coordinates are `0` reads off two coefficients of `p`: its constant
coefficient and its coefficient of the variable `Xᵢ`,

  `p(ε eᵢ) = p(0) + (coefficient of Xᵢ in p) ε`.

As this evaluation is a ring homomorphism, it extracts the linear coefficient of `Xᵢ` from an
element that is only known through a universal property, such as the image of an element of the
Lazard ring in a polynomial ring.

## Main results

* `MvPolynomial.aeval_single_eps`: `p(ε eᵢ) = p(0) + (coefficient of Xᵢ in p) ε`.
-/

public section

namespace MvPolynomial

variable {σ R : Type*} [CommSemiring R] [DecidableEq σ]

/-- Evaluating `p` at the point `ε eᵢ` of the dual numbers gives
`p(0) + (coefficient of Xᵢ in p) ε`. -/
theorem aeval_single_eps (i : σ) (p : MvPolynomial σ R) :
    aeval (Pi.single i (DualNumber.eps : DualNumber R)) p =
      algebraMap R (DualNumber R) (constantCoeff p) +
        p.coeff (Finsupp.single i 1) • DualNumber.eps := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    rw [aeval_C, constantCoeff_C, coeff_C,
      ite_eq_right (Finsupp.single_ne_zero.2 one_ne_zero).symm, zero_smul, add_zero]
  | add p q hp hq =>
    rw [map_add, hp, hq, map_add, map_add]
    simp only [AddMonoidAlgebra.coeff_add, Finsupp.coe_add, Pi.add_apply, add_smul]
    abel
  | mul_X p k hp =>
    rw [map_mul, hp, aeval_X, coeff_mul_X', map_mul, constantCoeff_X, mul_zero, map_zero,
      zero_add]
    by_cases hk : k = i
    · subst hk
      ext <;> simp [constantCoeff_eq, TrivSqZeroExt.algebraMap_eq_inl]
    · simp [hk]

end MvPolynomial
