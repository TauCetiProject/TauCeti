/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Laurent

/-!
# Coefficients of products in Laurent polynomials

Multiplying a Laurent polynomial on the left by `T n` shifts its coefficients by `n`, and
multiplying it by a constant, in particular by a natural number, scales every coefficient. The
constant `1` has a single coefficient, at exponent `0`. These hold over an arbitrary semiring.

## Main results

* `LaurentPolynomial.coeff_T_mul`: `(T n * f).coeff d = f.coeff (d - n)`.
* `LaurentPolynomial.coeff_C_mul` and `LaurentPolynomial.coeff_natCast_mul`: constants scale
  coefficients.
* `LaurentPolynomial.coeff_one`: the coefficients of `1`.
-/

public section

namespace LaurentPolynomial

variable {R : Type*} [Semiring R]

/-- Left multiplication by `T n` shifts coefficients by `n`. This is not a `simp` lemma: `simp`
moves `T n` to the right with `LaurentPolynomial.T_mul`. -/
theorem coeff_T_mul (n : ℤ) (f : R[T;T⁻¹]) (d : ℤ) : (T n * f).coeff d = f.coeff (d - n) := by
  simpa only [T, one_mul, sub_eq_add_neg, add_comm] using
    AddMonoidAlgebra.coeff_single_mul_apply f (1 : R) n d

/-- Left multiplication by a constant scales every coefficient. -/
@[simp]
theorem coeff_C_mul (t : R) (f : R[T;T⁻¹]) (d : ℤ) : (C t * f).coeff d = t * f.coeff d := by
  rw [← single_eq_C]
  exact AddMonoidAlgebra.coeff_single_zero_mul f t d

/-- Left multiplication by a natural number scales every coefficient. -/
@[simp]
theorem coeff_natCast_mul (m : ℕ) (f : R[T;T⁻¹]) (d : ℤ) :
    ((m : R[T;T⁻¹]) * f).coeff d = m * f.coeff d := by
  rw [← map_natCast (C : R →+* R[T;T⁻¹]) m, coeff_C_mul]

/-- The constant Laurent polynomial `1` has coefficient `1` at exponent `0` and `0` elsewhere. -/
@[simp]
theorem coeff_one (d : ℤ) : (1 : R[T;T⁻¹]).coeff d = if d = 0 then 1 else 0 := by
  rw [← map_one (C : R →+* R[T;T⁻¹]), C_apply]

end LaurentPolynomial
