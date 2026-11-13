/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.FieldDivision

/-!
# Degree of a normalized polynomial

Over a commutative ring `R` without zero divisors carrying a `NormalizationMonoid`, `normalize p`
is `p` times a unit constant, so it has the same degree as `p`. Mathlib states this
(`Polynomial.degree_normalize`, `Polynomial.natDegree_normalize`) only over a field; here it is
proved for any such ring, for instance for `ℤ[X]`.
-/

public section

namespace Polynomial

variable {R : Type*} [CommRing R] [NoZeroDivisors R] [NormalizationMonoid R]

/-- Normalizing a polynomial preserves its degree. This generalizes Mathlib's
`Polynomial.degree_normalize` from fields to any commutative ring without zero divisors carrying
a `NormalizationMonoid`. -/
@[simp]
theorem degree_normalize' (p : R[X]) : (normalize p).degree = p.degree := by
  rw [normalize_apply, coe_normUnit]
  exact degree_mul_C_of_isUnit (Units.isUnit _) p

/-- Normalizing a polynomial preserves its natural degree. This generalizes Mathlib's
`Polynomial.natDegree_normalize` from fields to any commutative ring without zero divisors
carrying a `NormalizationMonoid`. -/
@[simp]
theorem natDegree_normalize' (p : R[X]) :
    (normalize p).natDegree = p.natDegree :=
  natDegree_eq_of_degree_eq (degree_normalize' p)

end Polynomial
