/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RingTheory.MvPolynomial.PolynomialOperator

/-!
# Checks for the polynomial `sl₂`-operators

In two variables `x = X 0` and `y = X 1`, the raising operator is `E = x ∂_y`, the lowering
operator is `F = y ∂_x`, and `H = x ∂_x - y ∂_y`. The values below fix these conventions in low
degree: `E` raises towards the `x`-end of a weight string and `F` lowers towards the `y`-end, both
kill constants, and the total operators on a tensor product act on both factors by the Leibniz
rule.

In bidegree `(1, 1)` the total raising operator kills `x ⊗ x` and `x ⊗ y - y ⊗ x`, sends `y ⊗ y`
to `x ⊗ y + y ⊗ x`, and sends the symmetric tensor `x ⊗ y + y ⊗ x` to `2 (x ⊗ x)`.
-/

open MvPolynomial TensorProduct

namespace TauCeti.PolynomialOperatorChecks

variable {R : Type*} [CommRing R]

/-! ### One factor -/

/-- `E` and `F` kill the constants. -/
example : polynomialOperator R (0 : Fin 2) 1 1 = 0 ∧ polynomialOperator R (1 : Fin 2) 0 1 = 0 := by
  simp [polynomialOperator_apply]

/-- In degree one, `E y = x` and `F x = y`, while `E x = F y = 0`. -/
example :
    polynomialOperator R (0 : Fin 2) 1 (X 1) = X 0 ∧
      polynomialOperator R (1 : Fin 2) 0 (X 0) = X 1 ∧
      polynomialOperator R (0 : Fin 2) 1 (X 0) = 0 ∧
      polynomialOperator R (1 : Fin 2) 0 (X 1) = 0 := by
  simp

/-- In degree two, `E (x y) = x²` and `F (x y) = y²`. -/
example :
    polynomialOperator R (0 : Fin 2) 1 (X 0 * X 1) = X 0 ^ 2 ∧
      polynomialOperator R (1 : Fin 2) 0 (X 0 * X 1) = X 1 ^ 2 := by
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  constructor
  · simpa using polynomialOperator_X_pow_mul_X_pow_succ (R := R) h01 1 0
  · simpa [mul_comm] using polynomialOperator_X_pow_mul_X_pow_succ (R := R) h01.symm 1 0

/-- `H (x y) = 0` and `H (x²) = 2 x²`: the weights of `x y` and `x²` are `0` and `2`. -/
example :
    (polynomialOperator R (0 : Fin 2) 0 - polynomialOperator R (1 : Fin 2) 1) (X 0 * X 1) = 0 ∧
      (polynomialOperator R (0 : Fin 2) 0 - polynomialOperator R (1 : Fin 2) 1) (X 0 ^ 2) =
        2 • X 0 ^ 2 := by
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  constructor
  · simpa using polynomialOperator_self_sub_polynomialOperator_self_X_pow_mul_X_pow (R := R) h01 1 1
  · simpa [two_smul] using
      polynomialOperator_self_sub_polynomialOperator_self_X_pow_mul_X_pow (R := R) h01 2 0

/-- The lowering operator `y ∂_x` sends `x²` to `2 x y`: used as a raising operator it would move
the top of the degree-two string downwards. -/
example : polynomialOperator R (1 : Fin 2) 0 (X 0 ^ 2) = 2 • (X 0 * X 1) := by
  simp [polynomialOperator_apply, two_smul]
  ring

/-! ### The total operators on a tensor product -/

/-- The total lowering operator sends `x ⊗ x` to `y ⊗ x + x ⊗ y`. -/
example :
    tensorPolynomialOperator R (1 : Fin 2) 0 (X 0 ⊗ₜ X 0) = X 1 ⊗ₜ X 0 + X 0 ⊗ₜ X 1 := by
  simp

/-- The total lowering operator kills `y ⊗ y` and sends `y ⊗ x` to `y ⊗ y`. -/
example :
    tensorPolynomialOperator R (1 : Fin 2) 0 (X 1 ⊗ₜ X 1) = 0 ∧
      tensorPolynomialOperator R (1 : Fin 2) 0 (X 1 ⊗ₜ X 0) = X 1 ⊗ₜ X 1 := by
  simp

/-- In bidegree `(0, 0)` the total raising operator kills `1 ⊗ 1`. -/
example : tensorPolynomialOperator R (0 : Fin 2) 1 (1 ⊗ₜ 1) = 0 := by
  simp [polynomialOperator_apply]

/-- In bidegree `(1, 1)` the total raising operator kills `x ⊗ x`, but sends `y ⊗ y` to
`x ⊗ y + y ⊗ x`. -/
example :
    tensorPolynomialOperator R (0 : Fin 2) 1 (X 0 ⊗ₜ X 0) = 0 ∧
      tensorPolynomialOperator R (0 : Fin 2) 1 (X 1 ⊗ₜ X 1) = X 0 ⊗ₜ X 1 + X 1 ⊗ₜ X 0 := by
  simp

/-- The total raising operator kills the alternating tensor `x ⊗ y - y ⊗ x` and sends the
symmetric tensor `x ⊗ y + y ⊗ x` to `2 (x ⊗ x)`. -/
example :
    tensorPolynomialOperator R (0 : Fin 2) 1 (X 0 ⊗ₜ X 1 - X 1 ⊗ₜ X 0) = 0 ∧
      tensorPolynomialOperator R (0 : Fin 2) 1 (X 0 ⊗ₜ X 1 + X 1 ⊗ₜ X 0) =
        2 • (X 0 ⊗ₜ X 0) := by
  simp [two_smul]

end TauCeti.PolynomialOperatorChecks
