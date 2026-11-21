/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Basic

/-!
# Products of two variables as monomials

A product `Xᵢ Xⱼ` of two variables is the monomial with coefficient `1` and exponent `eᵢ + eⱼ`.
This is the form in which quadratic binomials `Xᵢ Xⱼ - Xₖ Xₗ` appear as the binomials
`X^u - X^v` of toric ideals and of the SAGBI criterion.

## Main results

* `MvPolynomial.X_mul_X_eq_monomial`: `Xᵢ Xⱼ = monomial (eᵢ + eⱼ) 1`.
-/

public section

namespace MvPolynomial

/-- A product of two variables is the monomial with exponent `eᵢ + eⱼ`. -/
theorem X_mul_X_eq_monomial {σ R : Type*} [CommSemiring R] (i j : σ) :
    (X i * X j : MvPolynomial σ R) = monomial (Finsupp.single i 1 + Finsupp.single j 1) 1 := by
  rw [X, X, monomial_mul_monomial, one_mul]

end MvPolynomial
