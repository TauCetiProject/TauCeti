/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Tactic.LinearCombination

/-!
# Rows and columns of invertible `2 × 2` matrices are coprime

The determinant `a d - b c` of an invertible `2 × 2` matrix `!![a, b; c, d]` over a commutative
ring is a unit, so each row and each column of the matrix generates the unit ideal. These are the
`GL₂` versions of Mathlib's `Matrix.SpecialLinearGroup.isCoprime_row` and
`Matrix.SpecialLinearGroup.isCoprime_col`, where the determinant is `1`; the proofs follow those.

Over `ℤ` this says that the image of a primitive vector under `GL (Fin 2) ℤ` is again primitive,
for instance that an integral change of basis of the first homology of a torus carries the
coordinate curves to simple closed curves.

## Main results

* `Matrix.GeneralLinearGroup.isCoprime_row`: the two entries of a row are coprime.
* `Matrix.GeneralLinearGroup.isCoprime_col`: the two entries of a column are coprime.
-/

public section

namespace Matrix.GeneralLinearGroup

variable {R : Type*} [CommRing R]

/-- The two entries of a row of an invertible `2 × 2` matrix are coprime. -/
theorem isCoprime_row (A : GL (Fin 2) R) (i : Fin 2) : IsCoprime (A i 0) (A i 1) := by
  obtain ⟨u, hu⟩ : IsUnit (A : Matrix (Fin 2) (Fin 2) R).det := isUnits_det_units A
  have hdet : ((u⁻¹ : Rˣ) : R) * (A 0 0 * A 1 1 - A 0 1 * A 1 0) = 1 := by
    rw [← det_fin_two, ← hu, Units.inv_mul]
  refine match i with
  | 0 => ⟨u⁻¹ * A 1 1, -(u⁻¹ * A 1 0), ?_⟩
  | 1 => ⟨-(u⁻¹ * A 0 1), u⁻¹ * A 0 0, ?_⟩ <;>
  · linear_combination hdet

/-- The two entries of a column of an invertible `2 × 2` matrix are coprime. -/
theorem isCoprime_col (A : GL (Fin 2) R) (j : Fin 2) : IsCoprime (A 0 j) (A 1 j) := by
  obtain ⟨u, hu⟩ : IsUnit (A : Matrix (Fin 2) (Fin 2) R).det := isUnits_det_units A
  have hdet : ((u⁻¹ : Rˣ) : R) * (A 0 0 * A 1 1 - A 0 1 * A 1 0) = 1 := by
    rw [← det_fin_two, ← hu, Units.inv_mul]
  refine match j with
  | 0 => ⟨u⁻¹ * A 1 1, -(u⁻¹ * A 0 1), ?_⟩
  | 1 => ⟨-(u⁻¹ * A 1 0), u⁻¹ * A 0 0, ?_⟩ <;>
  · linear_combination hdet

end Matrix.GeneralLinearGroup
