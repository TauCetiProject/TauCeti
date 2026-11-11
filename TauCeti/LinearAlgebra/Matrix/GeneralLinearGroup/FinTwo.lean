/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Entries of invertible `2 × 2` matrices

The determinant `a d - b c` of an invertible matrix `!![a, b; c, d]` over a nontrivial commutative
ring is nonzero, so a vanishing diagonal entry forces the off-diagonal entries to be nonzero.

## Main results

* `Matrix.GeneralLinearGroup.zero_one_ne_zero_of_one_one_eq_zero`: for an invertible
  `!![a, b; c, 0]`, the entry `b` is nonzero.
-/

public section

open Matrix

namespace Matrix.GeneralLinearGroup

variable {R : Type*} [CommRing R] [Nontrivial R]

/-- For an invertible `!![a, b; c, 0]`, the entry `b` is nonzero. -/
theorem zero_one_ne_zero_of_one_one_eq_zero {A : GL (Fin 2) R} (hA : A 1 1 = 0) :
    A 0 1 ≠ 0 := by
  intro hb
  simpa [det_fin_two, hA, hb] using A.det_ne_zero

end Matrix.GeneralLinearGroup
