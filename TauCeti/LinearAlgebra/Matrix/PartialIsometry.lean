/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.Algebra.Ring.Idempotent

/-!
# Rectangular partial isometries

A rectangular matrix whose initial Gram matrix is idempotent satisfies the partial-isometry
identity. This gives the support identities used to compose rectangular equivalences of
projections. The coefficients may lie in any star-ordered ring with proper star.

## References

* B. Blackadar, *K-Theory for Operator Algebras*, §4.6.
-/

public section

namespace Matrix

variable {m n R : Type*} [Fintype m] [Fintype n] [NonUnitalRing R] [StarRing R]
  [PartialOrder R] [StarOrderedRing R] [IsProperStar R]

/-- A rectangular matrix with idempotent initial Gram matrix is a partial isometry. -/
theorem mul_conjTranspose_mul_self_of_isIdempotentElem (v : Matrix m n R)
    (hv : IsIdempotentElem (vᴴ * v)) : v * vᴴ * v = v := by
  apply sub_eq_zero.mp
  apply (conjTranspose_mul_self_eq_zero).mp
  have h : vᴴ * (v * (vᴴ * v)) = vᴴ * v := by
    simpa only [Matrix.mul_assoc] using hv.eq
  simp only [conjTranspose_sub, conjTranspose_mul, conjTranspose_conjTranspose,
    Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, h, sub_self]

end Matrix
