/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Algebra.Polynomial.QDerivative

/-!
# Checks for the `q`-derivative of a polynomial

The values below fix the conventions of `Polynomial.qDerivative` in low degree. The
`q`-derivative of `X ^ 2` is `(1 + q) X`, which the twisted Leibniz rule recovers as
`X + q X` from `X ^ 2 = X * X`, whereas the untwisted Leibniz rule would give `2 X`. The
`q`-derivative is linear over the coefficients, so it kills `q` itself and sends `q X ^ 2` to
`q (1 + q) X`. At `q = 1` it is the ordinary derivative, and over `ℤ` with `q = 2` the
coefficient of `X ^ 2` in `∇_2 (X ^ 3)` is `[3]_2 = 7`, not `3`.
-/

open Polynomial Finset

namespace TauCeti.QDerivativeChecks

variable {R : Type*} [CommRing R] (q : R)

/-- `∇_q X = 1` and `∇_q (X ^ 2) = (1 + q) X`. -/
example : qDerivative q (X : R[X]) = 1 ∧ qDerivative q (X ^ 2 : R[X]) = C (1 + q) * X := by
  refine ⟨qDerivative_X q, ?_⟩
  rw [qDerivative_X_pow, sum_range_succ, sum_range_one]
  simp

/-- The twisted Leibniz rule computes `∇_q (X * X)` as `X + q X`. -/
example : qDerivative q (X : R[X]) * X + X.comp (C q * X) * qDerivative q X = X + C q * X := by
  simp

/-- The `q`-derivative kills the coefficient `q` and sends `q X ^ 2` to `q (1 + q) X`. -/
example : qDerivative q (C q : R[X]) = 0 ∧
    qDerivative q (C q * X ^ 2 : R[X]) = C (q * (1 + q)) * X := by
  refine ⟨qDerivative_C q q, ?_⟩
  rw [qDerivative_C_mul_X_pow, sum_range_succ, sum_range_one]
  simp

/-- At `q = 1`, `∇_1 (X ^ 2) = 2 X`, the ordinary derivative. -/
example : qDerivative (1 : R) (X ^ 2 : R[X]) = C 2 * X := by
  rw [qDerivative_one_eq_derivative, derivative_X_sq]

/-- Over `ℤ` with `q = 2`, `∇_2 (X ^ 3) = 7 X ^ 2`, since `[3]_2 = 1 + 2 + 4`. -/
example : qDerivative (2 : ℤ) (X ^ 3 : ℤ[X]) = C 7 * X ^ 2 := by
  rw [qDerivative_X_pow, sum_range_succ, sum_range_succ, sum_range_one]
  norm_num

end TauCeti.QDerivativeChecks
