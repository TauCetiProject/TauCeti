/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.LinearAlgebra.Matrix.Permutation
public import Mathlib.LinearAlgebra.UnitaryGroup

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

universe u

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {R : Type u} [CommRing R]

attribute [local instance] starRingOfComm

/-- The special orthogonal matrix which sends the `i`-th basis vector to the `j`-th basis
vector, sends the `j`-th basis vector to the negative of the `i`-th basis vector, and fixes the
remaining basis vectors. -/
def coordinateRotation (i j : n) (hij : i ≠ j) : Matrix.specialOrthogonalGroup n R :=
  ⟨(Equiv.swap i j).permMatrix R * Matrix.diagonal (Function.update 1 j (-1)), by
    rw [Matrix.mem_specialOrthogonalGroup_iff]
    constructor
    · rw [Matrix.mem_orthogonalGroup_iff]
      have hdiag : Matrix.diagonal (Function.update 1 j (-1 : R)) *
          Matrix.diagonal (Function.update 1 j (-1 : R)) = 1 := by
        ext a b
        by_cases hab : a = b
        · subst b
          by_cases haj : a = j <;> simp [haj]
        · simp [hab]
      rw [Matrix.transpose_mul, Matrix.diagonal_transpose, Matrix.transpose_permMatrix]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (Matrix.diagonal _) (Matrix.diagonal _), hdiag,
        Matrix.one_mul]
      simp [← Matrix.permMatrix_mul]
    · rw [Matrix.det_mul, Matrix.det_permutation, Matrix.det_diagonal]
      rw [Finset.prod_update_of_mem (Finset.mem_univ j)]
      simp [hij]⟩

/-- The underlying matrix of a coordinate rotation is the signed permutation matrix used in its
definition. -/
theorem coe_coordinateRotation (i j : n) (hij : i ≠ j) :
    (coordinateRotation (R := R) i j hij : Matrix n n R) =
      (Equiv.swap i j).permMatrix R * Matrix.diagonal (Function.update 1 j (-1)) := (rfl)

/-- A coordinate rotation exchanges the selected coordinates with the sign on the first output
coordinate. -/
@[simp]
theorem coordinateRotation_mulVec (i j : n) (hij : i ≠ j) (w : n → R) (a : n) :
    ((coordinateRotation (R := R) i j hij : Matrix n n R) *ᵥ w) a =
      if a = i then -w j else if a = j then w i else w a := by
  rw [coe_coordinateRotation, ← Matrix.mulVec_mulVec, Matrix.permMatrix_mulVec]
  simp only [Function.comp_apply, Matrix.mulVec_diagonal, Function.update_apply]
  by_cases hai : a = i
  · subst a
    simp
  · by_cases haj : a = j
    · subst a
      simp [hij, hij.symm]
    · simp [hai, haj, Equiv.swap_apply_of_ne_of_ne]

/-- A coordinate rotation sends the `i`-th basis vector to the `j`-th basis vector. -/
@[simp]
theorem coordinateRotation_col_left (i j : n) (hij : i ≠ j) :
    (coordinateRotation (R := R) i j hij : Matrix n n R).col i = Pi.single j 1 := by
  rw [← Matrix.mulVec_single_one]
  ext a
  rw [coordinateRotation_mulVec]
  by_cases hai : a = i
  · subst a
    simp [hij]
  · by_cases haj : a = j <;> simp [hai, haj, hij.symm]

/-- A coordinate rotation sends the `j`-th basis vector to the negative of the `i`-th basis
vector. -/
@[simp]
theorem coordinateRotation_col_right (i j : n) (hij : i ≠ j) :
    (coordinateRotation (R := R) i j hij : Matrix n n R).col j = -Pi.single i 1 := by
  rw [← Matrix.mulVec_single_one]
  ext a
  rw [coordinateRotation_mulVec]
  by_cases hai : a = i
  · subst a
    simp
  · by_cases haj : a = j <;> simp [hai, haj, hij.symm]

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
  by_cases hai : a = i
  · subst a
    simp [hij, hij.symm]
  · by_cases haj : a = j
    · subst a
      simp [hij.symm]
    · simp [hai, haj]

end TauCeti.Matrix.SpecialOrthogonalGroup
