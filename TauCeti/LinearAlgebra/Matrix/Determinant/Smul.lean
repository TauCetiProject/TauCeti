/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# The determinant of a scalar multiple

Mathlib's `Matrix.det_smul` computes `det (c • A) = c ^ card n * det A`. Over a ring without zero
divisors this shows that a nonzero multiple of a nonsingular matrix is nonsingular
(`Matrix.det_smul_ne_zero`), the form in which a rescaling `c • A` of an invertible matrix enters
an argument.

## Main results

* `Matrix.det_smul_ne_zero`: `c ≠ 0` and `det A ≠ 0` imply `det (c • A) ≠ 0`.
-/

public section

namespace Matrix

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R] [NoZeroDivisors R]

/-- Scaling a nonsingular matrix by a nonzero scalar keeps it nonsingular. -/
theorem det_smul_ne_zero {c : R} (hc : c ≠ 0) {A : Matrix n n R} (hA : A.det ≠ 0) :
    (c • A).det ≠ 0 := by
  rw [det_smul]
  exact mul_ne_zero (pow_ne_zero _ hc) hA

end Matrix
