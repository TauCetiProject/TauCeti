/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import TauCeti.LinearAlgebra.Matrix.Antitranspose

/-!
# The antitranspose on the special linear group

The antitranspose `(a b; c d) ↦ (d b; c a)`, the reflection of a matrix in its antidiagonal,
preserves determinants and reverses products, so it restricts to an anti-involution of
`SL(m, R)`. On `SL(2, ℤ)` it fixes the translation `T`.

## Main declarations

* `Matrix.SpecialLinearGroup.antitranspose`: the antitranspose on `SL(m, R)`.
* `Matrix.SpecialLinearGroup.antitranspose_mul`: it reverses products.
* `Matrix.SpecialLinearGroup.antitranspose_antitranspose`: it is an involution.
* `Matrix.SpecialLinearGroup.antitranspose_T`: it fixes `ModularGroup.T`.
-/

public section

open scoped MatrixGroups

namespace Matrix.SpecialLinearGroup

variable {R : Type*} [CommRing R] {m : ℕ}

/-- The antitranspose of a matrix of determinant one, its reflection in the antidiagonal. -/
def antitranspose (g : SL(m, R)) : SL(m, R) :=
  ⟨(g : Matrix (Fin m) (Fin m) R).antitranspose, by rw [det_antitranspose, g.det_coe]⟩

@[simp]
theorem coe_antitranspose (g : SL(m, R)) :
    (antitranspose g : Matrix (Fin m) (Fin m) R) = (g : Matrix (Fin m) (Fin m) R).antitranspose :=
  (rfl)

/-- The antitranspose reverses products. -/
theorem antitranspose_mul (g h : SL(m, R)) :
    antitranspose (g * h) = antitranspose h * antitranspose g :=
  Subtype.ext (Matrix.antitranspose_mul _ _)

@[simp]
theorem antitranspose_antitranspose (g : SL(m, R)) : antitranspose (antitranspose g) = g :=
  Subtype.ext (Matrix.antitranspose_antitranspose _)

/-- The antitranspose fixes the translation `T = (1 1; 0 1)`. -/
@[simp]
theorem antitranspose_T : antitranspose ModularGroup.T = ModularGroup.T := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

end Matrix.SpecialLinearGroup
