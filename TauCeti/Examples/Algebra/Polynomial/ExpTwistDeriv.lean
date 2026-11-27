/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Tactic.NormNum
import TauCeti.Algebra.Polynomial.ExpTwistDeriv

/-!
# Examples of the exponentially twisted derivative

Concrete evaluations of `Polynomial.expTwistDeriv c m = (d/dX + c) ^ m` from
`TauCeti.Algebra.Polynomial.ExpTwistDeriv`:

* `expTwistDeriv c 1 X = 1 + c X`, fixing the sign: the opposite convention `d/dX - c` would give
  `1 - c X`.
* With `c = 0` the operator is an ordinary iterated derivative: `expTwistDeriv 0 3 (X ^ 4) = 24 X`.
* `expTwistDeriv 7 1 (X ^ 2) = 2 X + 7 X ^ 2`, the polynomial factor of the derivative of
  `X ^ 2 e^{7X}`.
-/

open Polynomial

namespace TauCeti.Examples.ExpTwistDeriv

/-- The first twisted derivative of `X` is `1 + c X`. -/
example (c : ℚ) : expTwistDeriv c 1 (X : ℚ[X]) = 1 + C c * X := by
  rw [expTwistDeriv_succ, expTwistDeriv_zero, derivative_X, smul_eq_C_mul]

/-- With `c = 0` the twisted derivative is the iterated derivative. -/
example : expTwistDeriv (0 : ℚ) 3 (X ^ 4 : ℚ[X]) = 24 * X := by
  simp only [expTwistDeriv_eq_iterate, map_zero, zero_mul, add_zero, Function.iterate_succ,
    Function.iterate_zero, Function.comp_apply, id, derivative_X_pow, derivative_C_mul_X_pow]
  norm_num [map_ofNat]

/-- The polynomial factor of the derivative of `X ^ 2 e^{7X}` is `2 X + 7 X ^ 2`. -/
example : expTwistDeriv (7 : ℚ) 1 (X ^ 2 : ℚ[X]) = 2 * X + 7 * X ^ 2 := by
  rw [expTwistDeriv_succ, expTwistDeriv_zero, derivative_X_pow, smul_eq_C_mul]
  norm_num [map_ofNat]

end TauCeti.Examples.ExpTwistDeriv
