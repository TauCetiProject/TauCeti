/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.LinearAlgebra.Matrix.Swap
public import TauCeti.LinearAlgebra.Matrix.OrthogonalGroup.Basic

/-!
# Coordinate rotations in the special orthogonal group

For two distinct coordinates, the signed transposition which sends the first basis vector to the
second and the second to the negative of the first is special orthogonal. Its square changes the
sign of exactly those two coordinates. These elementary matrices give a convenient, ring-valued
interface for arguments with the standard representation of a special orthogonal group.

## Main declarations

* `TauCeti.Matrix.SpecialOrthogonalGroup.coordinateRotation`: the signed coordinate transposition.
* `TauCeti.Matrix.SpecialOrthogonalGroup.coordinateHalfTurn`: its square, negating two coordinates.

## References

* J. S. Milne, *Algebraic Groups* (2017), §2.3.
-/

public section

open Matrix

namespace TauCeti.Matrix.SpecialOrthogonalGroup

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {R : Type*} [CommRing R]

attribute [local instance] starRingOfComm

/-- The special orthogonal matrix which sends the `i`-th basis vector to the `j`-th basis
vector, sends the `j`-th basis vector to the negative of the `i`-th basis vector, and fixes the
remaining basis vectors. -/
def coordinateRotation (i j : n) (hij : i ≠ j) : Matrix.specialOrthogonalGroup n R :=
  ⟨Matrix.swap R i j * Matrix.diagonal (Function.update 1 j (-1)), by
    rw [← coe_orthogonalDiagonalReflection, mem_specialOrthogonalGroup_iff, det_mul,
      det_orthogonalDiagonalReflection]
    refine ⟨Submonoid.mul_mem _ ?_ (orthogonalDiagonalReflection R j).2, ?_⟩
    · rw [mem_orthogonalGroup_iff', transpose_swap, swap_mul_self]
    · simp [swap, det_permutation, hij]⟩

/-- The underlying matrix of a coordinate rotation is the signed swap matrix used in its
definition. -/
theorem coe_coordinateRotation (i j : n) (hij : i ≠ j) :
    (coordinateRotation (R := R) i j hij : Matrix n n R) =
      Matrix.swap R i j * Matrix.diagonal (Function.update 1 j (-1)) := (rfl)

/-- A coordinate rotation exchanges the selected coordinates with the sign on the first output
coordinate. -/
@[simp]
theorem coordinateRotation_mulVec (i j : n) (hij : i ≠ j) (w : n → R) (a : n) :
    ((coordinateRotation (R := R) i j hij : Matrix n n R) *ᵥ w) a =
      if a = i then -w j else if a = j then w i else w a := by
  rw [coe_coordinateRotation, ← Matrix.mulVec_mulVec, Matrix.swap_mulVec]
  simp only [Function.comp_apply, Matrix.mulVec_diagonal, Function.update_apply,
    Equiv.swap_apply_def, Pi.one_apply]
  grind

/-- A coordinate rotation sends the `i`-th basis vector to the `j`-th basis vector. -/
@[simp]
theorem coordinateRotation_col_left (i j : n) (hij : i ≠ j) :
    (coordinateRotation (R := R) i j hij : Matrix n n R).col i = Pi.single j 1 := by
  ext a
  rw [← Matrix.mulVec_single_one, coordinateRotation_mulVec]
  grind

/-- A coordinate rotation sends the `j`-th basis vector to the negative of the `i`-th basis
vector. -/
@[simp]
theorem coordinateRotation_col_right (i j : n) (hij : i ≠ j) :
    (coordinateRotation (R := R) i j hij : Matrix n n R).col j = -Pi.single i 1 := by
  ext a
  rw [← Matrix.mulVec_single_one, coordinateRotation_mulVec]
  grind [Pi.neg_apply]

/-- Squaring a coordinate rotation gives the half-turn which negates the two selected
coordinates. -/
def coordinateHalfTurn (i j : n) (hij : i ≠ j) : Matrix.specialOrthogonalGroup n R :=
  coordinateRotation (R := R) i j hij ^ 2

/-- A coordinate half-turn negates exactly the two selected coordinates. -/
@[simp]
theorem coordinateHalfTurn_mulVec (i j : n) (hij : i ≠ j) (w : n → R) (a : n) :
    ((coordinateHalfTurn (R := R) i j hij : Matrix n n R) *ᵥ w) a =
      if a = i ∨ a = j then -w a else w a := by
  rw [coordinateHalfTurn, pow_two, Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
  simp only [coordinateRotation_mulVec]
  grind

end TauCeti.Matrix.SpecialOrthogonalGroup
