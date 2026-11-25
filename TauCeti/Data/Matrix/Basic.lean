/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Basic

/-!
# Change of coefficients of scalar matrices

This file complements the `RingHom.mapMatrix` API of `Mathlib.Data.Matrix.Basic`.

## Main results

* `RingHom.mapMatrix_smul_one`: `f.mapMatrix` sends the scalar matrix `a • 1` to `f a • 1`.
-/

public section

namespace RingHom

/-- `f.mapMatrix` sends the scalar matrix `a • 1` to `f a • 1`. -/
theorem mapMatrix_smul_one {m α β : Type*} [Fintype m] [DecidableEq m]
    [NonAssocSemiring α] [NonAssocSemiring β] (f : α →+* β) (a : α) :
    f.mapMatrix (a • (1 : Matrix m m α)) = f a • 1 := by
  rw [f.mapMatrix_apply, Matrix.map_smul' _ _ _ (map_mul f),
    Matrix.map_one _ (map_zero f) (map_one f)]

end RingHom
