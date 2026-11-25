/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# The general linear group in rank one

For a singleton index type `n` (`[Unique n]`) an invertible matrix has a single entry, which is
its determinant. So every element of `GL n R` is the scalar matrix of its determinant.

## Main results

* `Matrix.GeneralLinearGroup.eq_scalar_det`: for `[Unique n]`, `M = scalar n (det M)`.
-/

public section

namespace Matrix.GeneralLinearGroup

variable {n R : Type*} [Fintype n] [DecidableEq n] [Unique n] [CommRing R]

/-- In rank one an invertible matrix is the scalar matrix of its determinant. -/
theorem eq_scalar_det (M : GL n R) : M = scalar n (det M) :=
  ext fun i j ↦ by
    simp [Subsingleton.elim i default, Subsingleton.elim j default, det_unique]

end Matrix.GeneralLinearGroup
