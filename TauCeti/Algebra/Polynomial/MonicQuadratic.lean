/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Degree.SmallDegree
public import Mathlib.Algebra.Polynomial.Monic

/-!
# The monic quadratic `X² - X + c`

Over a nontrivial commutative ring, the polynomial `X² - X + C c` is monic of degree `2`. This is
the shape of the minimal polynomial of the half-integer generator `(1 + √d)/2` of a quadratic
field, for `c = (1 - d)/4`, and these two facts are what its uses need.

## Main results

* `Polynomial.natDegree_X_sq_sub_X_add_C`: `X² - X + C c` has degree `2`.
* `Polynomial.monic_X_sq_sub_X_add_C`: `X² - X + C c` is monic.
-/

public section

namespace Polynomial

variable {R : Type*} [CommRing R] [Nontrivial R] (c : R)

omit [Nontrivial R] in
private theorem X_sq_sub_X_add_C_eq :
    (X ^ 2 - X + C c : R[X]) = C 1 * X ^ 2 + C (-1) * X + C c := by
  rw [C_neg, C_1, one_mul, neg_one_mul, sub_eq_add_neg]

/-- The quadratic `X² - X + c` has degree `2`. -/
theorem natDegree_X_sq_sub_X_add_C : (X ^ 2 - X + C c : R[X]).natDegree = 2 := by
  rw [X_sq_sub_X_add_C_eq, natDegree_quadratic one_ne_zero]

/-- The quadratic `X² - X + c` is monic. -/
theorem monic_X_sq_sub_X_add_C : (X ^ 2 - X + C c : R[X]).Monic := by
  rw [Monic, X_sq_sub_X_add_C_eq, leadingCoeff_quadratic one_ne_zero]

end Polynomial
