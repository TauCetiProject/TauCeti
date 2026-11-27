/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Data.Nat.Choose.Sum

/-!
# Binomial expansions of Laurent polynomials

In `R[T;T⁻¹]` over any semiring `R`, `(1 + T k) ^ n` expands by the binomial theorem
(`LaurentPolynomial.one_add_T_pow`), and multiplying on the right by `T b` shifts all exponents
by `b` (`LaurentPolynomial.one_add_T_pow_mul_T`).
-/

public section

namespace LaurentPolynomial

open scoped LaurentPolynomial

variable {R : Type*} [Semiring R]

/-- Binomial expansion of `(1 + T k) ^ n` in `R[T;T⁻¹]` over any semiring `R`. -/
theorem one_add_T_pow (k : ℤ) (n : ℕ) :
    (1 + T k : R[T;T⁻¹]) ^ n =
      ∑ j ∈ Finset.range (n + 1), (n.choose j : R[T;T⁻¹]) * T ((j : ℤ) * k) := by
  rw [add_comm (1 : R[T;T⁻¹]) (T k), (Commute.one_right (T k)).add_pow]
  exact Finset.sum_congr rfl fun j _ => by
    rw [one_pow, mul_one, T_pow, (Nat.cast_comm (n.choose j) _).symm]

/-- Shifted binomial expansion of `(1 + T k) ^ n * T b` in `R[T;T⁻¹]` over any semiring `R`. -/
theorem one_add_T_pow_mul_T (k : ℤ) (n : ℕ) (b : ℤ) :
    (1 + T k : R[T;T⁻¹]) ^ n * T b =
      ∑ j ∈ Finset.range (n + 1), (n.choose j : R[T;T⁻¹]) * T (b + (j : ℤ) * k) := by
  rw [one_add_T_pow, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by rw [mul_assoc, ← T_add, add_comm ((j : ℤ) * k) b]

end LaurentPolynomial
