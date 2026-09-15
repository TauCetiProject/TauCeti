/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.Tactic.Module

/-!
# A matrix between two quadratic factors, expanded in the parameter

A divided-power exponential of a square-zero or cube-zero matrix is a quadratic polynomial
`1 + u X + u² Y` in its parameter. Placing a matrix between two such factors and collecting the
powers of the parameter is a purely algebraic expansion, with five coefficient matrices built
from the four matrices involved. It is the computation that turns a conjugation, or a congruence,
by a divided-power exponential into finitely many identities between products.

The two factors are allowed to have different linear and quadratic terms, so the same expansion
serves a conjugation, where the right factor is the inverse of the left one, and a congruence,
where it is the transpose.

## Main results

* `Matrix.mul_mul_of_one_add_smul_add_smul`: the expansion.
-/

public section

namespace Matrix

/-- **A matrix between two quadratic factors, expanded in the parameter.** -/
theorem mul_mul_of_one_add_smul_add_smul {n R : Type*} [Fintype n] [DecidableEq n]
    [CommSemiring R]
    (X Y X' Y' M : Matrix n n R) (u : R) :
    (1 + u • X + u ^ 2 • Y) * M * (1 + u • X' + u ^ 2 • Y') =
      M + u • (X * M + M * X') + u ^ 2 • (X * M * X' + (Y * M + M * Y')) +
        u ^ 3 • (X * M * Y' + Y * M * X') + u ^ 4 • (Y * M * Y') := by
  simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm]
  module

end Matrix
