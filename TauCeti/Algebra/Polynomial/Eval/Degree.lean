/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# Rescaling the variable of a monomial

Substituting `C q * X` for the variable of the monomial `a Xⁿ` multiplies its coefficient by `qⁿ`.
This is the monomial case of Mathlib's `Polynomial.comp_C_mul_X_coeff`, stated as an equality of
polynomials so that it can be used to rewrite monomials directly.
-/

public section

namespace Polynomial

variable {R : Type*} [Semiring R]

/-- Rescaling the variable of a monomial: `(a Xⁿ)(qX) = a qⁿ Xⁿ`. -/
theorem monomial_comp_C_mul_X (q a : R) (n : ℕ) :
    (monomial n a).comp (C q * X) = monomial n (a * q ^ n) := by
  ext k
  simp only [comp_C_mul_X_coeff, coeff_monomial, Finsupp.single_apply]
  split_ifs with h
  · rw [h]
  · rw [zero_mul]

end Polynomial
