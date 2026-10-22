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
* `LaurentPolynomial.mul_coeff_zero_of_coeff_mem`: if the nonconstant coefficients of two Laurent
  polynomials lie in a square-zero ideal, the constant coefficient of their product is the
  product of their constant coefficients.
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

/-- If all nonconstant coefficients of two Laurent polynomials lie in a square-zero ideal, the
constant coefficient of their product is the product of their constant coefficients. Thus the
constant coefficient is a ring homomorphism on the Laurent polynomials that are constant modulo
such an ideal. -/
theorem mul_coeff_zero_of_coeff_mem {R : Type*} [CommSemiring R] {I : Ideal R} (hI : I ^ 2 = ⊥)
    {f g : R[T;T⁻¹]} (hf : ∀ n ≠ 0, f.coeff n ∈ I) (hg : ∀ n ≠ 0, g.coeff n ∈ I) :
    (f * g).coeff 0 = f.coeff 0 * g.coeff 0 := by
  rw [AddMonoidAlgebra.coeff_mul_apply_left, Finsupp.sum_eq_single 0]
  · simp
  · intro n _ hn
    have hmem : f.coeff n * g.coeff (-n + 0) ∈ I ^ 2 :=
      pow_two I ▸ Ideal.mul_mem_mul (hf n hn) (hg _ (by simpa using hn))
    simpa [hI] using hmem
  · simp

end LaurentPolynomial
