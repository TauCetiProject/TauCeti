/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-!
# The `2 × 2` transvections as matrix literals

Mathlib's `Matrix.SpecialLinearGroup.transvection hij b` has underlying matrix
`1 + single i j b` (`Matrix.SpecialLinearGroup.transvection_coe`). In size two there are exactly
two transvections, the lower one `!![1, 0; c, 1]` and the upper one `!![1, b; 0, 1]`; this file
states them as matrix literals, so that `simp` reads their entries directly.

## Main results

* `Matrix.SpecialLinearGroup.coe_transvection_one_zero`: the lower transvection is
  `!![1, 0; c, 1]`.
* `Matrix.SpecialLinearGroup.coe_transvection_zero_one`: the upper transvection is
  `!![1, b; 0, 1]`.
-/

public section

namespace Matrix.SpecialLinearGroup

variable {R : Type*} [CommRing R]

@[simp]
theorem coe_transvection_one_zero (h : (1 : Fin 2) ≠ 0) (c : R) :
    (transvection h c : Matrix (Fin 2) (Fin 2) R) = !![1, 0; c, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [transvection_coe]

@[simp]
theorem coe_transvection_zero_one (h : (0 : Fin 2) ≠ 1) (b : R) :
    (transvection h b : Matrix (Fin 2) (Fin 2) R) = !![1, b; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [transvection_coe]

end Matrix.SpecialLinearGroup
