/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Algebra.Polynomial.Derivative
import TauCeti.Algebra.Polynomial.ExpDerivFactor
import TauCeti.RingTheory.PowerSeries.Exp.Derivative

/-!
# Examples for the operator `(D + c) ^ m` on polynomials

Normalisation checks for `Polynomial.expDerivFactor` and the derivatives of exponential
polynomials:

* `expDerivFactor c 1 X = 1 + c X`; with the wrong sign `(D - c)` it would be `1 - c X`, which
  differs already for `c = 1` over `ℚ`.
* `expDerivFactor 0 m P` is the `m`-th derivative of `P`: `expDerivFactor 0 2 (X ^ 3) = 6 X`.
* `expDerivFactor c m 1 = c ^ m`, a constant: the derivative of a constant contributes nothing.
* Over `ℚ`, the derivative of `X exp (2 X)` is `(1 + 2 X) exp (2 X)`.
-/

namespace TauCeti.ExpDerivFactorExample

open Polynomial

/-- `expDerivFactor c 1 X = 1 + c X`. -/
example {R : Type*} [CommRing R] (c : R) : expDerivFactor c 1 X = 1 + C c * X := by
  simp [expDerivFactor_one]

/-- The sign of `c` matters: `(D + 1) X = 1 + X`, not `1 - X`, over `ℚ`. -/
example : expDerivFactor (1 : ℚ) 1 X ≠ 1 - X := by
  rw [expDerivFactor_one, derivative_X, map_one, one_mul]
  intro h
  have := congrArg (fun q : ℚ[X] ↦ q.coeff 1) h
  norm_num [coeff_one, coeff_X] at this

/-- For `c = 0` the operator is the iterated derivative: `(D + 0) ^ 2 X ^ 3 = 6 X`. -/
example {R : Type*} [CommRing R] : expDerivFactor (0 : R) 2 (X ^ 3) = C 6 * X := by
  rw [expDerivFactor_zero_left, iterate_derivative_X_pow_eq_C_mul]
  norm_num [Nat.descFactorial]

/-- On the constant `1`, `(D + c) ^ m` is multiplication by `c ^ m`. -/
example {R : Type*} [CommRing R] (c : R) (m : ℕ) : expDerivFactor c m 1 = C (c ^ m) :=
  expDerivFactor_apply_one c m

/-- Over `ℚ`, the derivative of `X exp (2 X)` is `(1 + 2 X) exp (2 X)`. -/
example : PowerSeries.derivative (R := ℚ)
      (((X : ℚ[X]) : PowerSeries ℚ) * PowerSeries.rescale 2 (PowerSeries.exp ℚ)) =
    ((1 + C 2 * X : ℚ[X]) : PowerSeries ℚ) * PowerSeries.rescale 2 (PowerSeries.exp ℚ) := by
  have := PowerSeries.iterate_derivative_coe_mul_rescale_exp (X : ℚ[X]) 2 1
  rwa [Function.iterate_one, expDerivFactor_one, derivative_X] at this

end TauCeti.ExpDerivFactorExample
