/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Coordinate action of unitary matrices

`Matrix.UnitaryGroup.toLinearEquiv_apply` describes the linear equivalence associated to a unitary
matrix by its matrix-vector action.
-/

public section

universe u v

namespace Matrix.UnitaryGroup

variable {R : Type u} [CommRing R] [StarRing R]
variable {n : Type v} [Fintype n] [DecidableEq n]

/-- The linear equivalence associated to a unitary matrix acts by matrix-vector
multiplication. -/
@[simp]
theorem toLinearEquiv_apply (U : Matrix.unitaryGroup n R) (x : n → R) :
    Matrix.UnitaryGroup.toLinearEquiv U x = Matrix.toLin' (U : Matrix n n R) x := rfl

end Matrix.UnitaryGroup

