/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# Basic rules for the quadratic form of a matrix

Elementary evaluation and scaling rules for Mathlib's `Matrix.toQuadraticForm'`, kept apart from
the signature theory so that consumers needing only these rules do not import it.

## Main results

* `Matrix.toQuadraticForm'_apply`: the form evaluated at a vector is `x ⬝ᵥ A *ᵥ x`.
* `Matrix.toQuadraticForm'_smul`: scaling a matrix scales its quadratic form.
-/

public section

namespace Matrix

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The quadratic form attached to a matrix, evaluated at a vector. -/
theorem toQuadraticForm'_apply (A : Matrix ι ι R) (x : ι → R) :
    A.toQuadraticForm' x = x ⬝ᵥ A *ᵥ x := by
  simp [Matrix.toQuadraticForm', Matrix.toLinearMap₂'_apply']

/-- Scaling a matrix scales its quadratic form. -/
@[simp]
theorem toQuadraticForm'_smul (c : R) (A : Matrix ι ι R) :
    (c • A).toQuadraticForm' = c • A.toQuadraticForm' := by
  ext x
  rw [toQuadraticForm'_apply, _root_.smul_apply, smul_eq_mul, toQuadraticForm'_apply,
    Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

end Matrix
