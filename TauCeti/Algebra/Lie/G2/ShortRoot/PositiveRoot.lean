/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.G2.ShortRoot.Basic

/-!
# Positive root matrices in the seven-dimensional representation of type G2

`TauCeti.Algebra.Lie.G2.ShortRoot.Basic` defines the simple raising matrices
`TauCeti.G2ShortRoot.raisingMatrix 0` (`α₁`, short) and `raisingMatrix 1` (`α₂`, long) on the
seven-weight diagram of the fundamental `G₂`-module `V(ϖ₁)`. Iterated commutators divide integrally
on `ℤ⁷`, yielding explicit `7 × 7` integer matrices for all six positive roots
`α₁, α₂, α₁ + α₂, 2α₁ + α₂, 3α₁ + α₂, 3α₁ + 2α₂` together with their integral divided squares
`e_γ² / 2`.

## Main definitions and results

* `TauCeti.G2ShortRoot.positiveRootMatrix` and `positiveRootDividedSquareMatrix`: the six positive
  root matrices of `G₂` on `ℤ⁷` and their divided squares `e_γ² / 2` (extending `raisingMatrix`).
* `TauCeti.G2ShortRoot.positiveRootMatrix_mul_self` and `positiveRootMatrix_pow_three`: each matrix
  squares to `2 • positiveRootDividedSquareMatrix i` and cubes to zero.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IX.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §19.3.
-/

public section

open scoped Matrix

namespace TauCeti.G2ShortRoot

/-- The six positive root matrices of `G₂` on `ℤ⁷`, ordered as `α₁` (short), `α₂` (long),
`α₁ + α₂` (`⁅e_{α₁}, e_{α₂}⁆`), `2α₁ + α₂` (`(ad e_{α₁})² e_{α₂} / 2`), `3α₁ + α₂`
(`(ad e_{α₁})³ e_{α₂} / 6`), and `3α₁ + 2α₂` (`(ad ⁅e_{α₁}, e_{α₂}⁆)² e_{α₁} / 6`). -/
def positiveRootMatrix : Fin 6 → Matrix (Fin 7) (Fin 7) ℤ :=
  ![raisingMatrix 0, raisingMatrix 1,
    Matrix.single 0 2 1 - 2 • Matrix.single 1 3 1 + Matrix.single 3 5 1 - Matrix.single 4 6 1,
    -(2 • Matrix.single 0 3 1) + Matrix.single 1 4 1 + Matrix.single 2 5 1 - Matrix.single 3 6 1,
    Matrix.single 0 4 1 - Matrix.single 2 6 1, -Matrix.single 0 5 1 - Matrix.single 1 6 1]

/-- The explicit six-tuple defining `positiveRootMatrix`. -/
theorem positiveRootMatrix_def : positiveRootMatrix =
    ![raisingMatrix 0, raisingMatrix 1,
      Matrix.single 0 2 1 - 2 • Matrix.single 1 3 1 + Matrix.single 3 5 1 - Matrix.single 4 6 1,
      -(2 • Matrix.single 0 3 1) + Matrix.single 1 4 1 + Matrix.single 2 5 1 - Matrix.single 3 6 1,
      Matrix.single 0 4 1 - Matrix.single 2 6 1, -Matrix.single 0 5 1 - Matrix.single 1 6 1] :=
  (rfl)

/-- The integral divided-square matrices `e_γ² / 2` for the six positive roots of `G₂`: unit
matrices on the three short roots `α₁, α₁ + α₂, 2α₁ + α₂`, and `0` on the three long roots. -/
def positiveRootDividedSquareMatrix : Fin 6 → Matrix (Fin 7) (Fin 7) ℤ :=
  ![Matrix.single 2 4 1, 0, -Matrix.single 1 5 1, Matrix.single 0 6 1, 0, 0]

/-- The explicit six-tuple defining `positiveRootDividedSquareMatrix`. -/
theorem positiveRootDividedSquareMatrix_def : positiveRootDividedSquareMatrix =
    ![Matrix.single 2 4 1, 0, -Matrix.single 1 5 1, Matrix.single 0 6 1, 0, 0] := (rfl)

/-- At index `0` (the short simple root `α₁`), `positiveRootMatrix` is `raisingMatrix 0`. -/
@[simp] theorem positiveRootMatrix_zero : positiveRootMatrix 0 = raisingMatrix 0 := (rfl)

/-- At index `1` (the long simple root `α₂`), `positiveRootMatrix` is `raisingMatrix 1`. -/
@[simp] theorem positiveRootMatrix_one : positiveRootMatrix 1 = raisingMatrix 1 := (rfl)

/-- Each positive root matrix of `G₂` on `ℤ⁷` squares to twice its divided-square matrix. -/
theorem positiveRootMatrix_mul_self (i : Fin 6) :
    positiveRootMatrix i * positiveRootMatrix i = 2 • positiveRootDividedSquareMatrix i := by
  revert i; decide

/-- Each positive root matrix of `G₂` on `ℤ⁷` cubes to zero. -/
@[simp] theorem positiveRootMatrix_pow_three (i : Fin 6) : positiveRootMatrix i ^ 3 = 0 := by
  revert i; decide

end TauCeti.G2ShortRoot
