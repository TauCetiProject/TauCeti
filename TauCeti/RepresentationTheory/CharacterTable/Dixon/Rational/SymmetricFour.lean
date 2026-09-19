/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.Dixon.ClassData.SymmetricFour
public import TauCeti.RepresentationTheory.CharacterTable.Dixon.IntegerChecker

/-!
# An exact character-table certificate for the symmetric group on four letters

This file gives the integer character table of `S₄ = Equiv.Perm (Fin 4)` and certifies it
against the computed class algebra.  Columns use the cycle-type order `1⁴`, `2·1²`, `2²`,
`3·1`, `4` fixed by `TauCeti.symmetricGroupFourClassData`.  The rows are the trivial and sign
characters, the two-dimensional character, and the standard three-dimensional character and its
sign twist.

The central-character table is checked directly against the class multiplication constants.  The
division-free identities

`degree i * omega i j = classSize j * character i j`

then relate it to the ordinary table.  The remaining finite checks are positivity and divisibility
of the degrees, the degree-square sum, and weighted row orthogonality.  Together these are exactly
`TauCeti.ClassData.IsIntegerCharacterTableSpec`; its general soundness theorem identifies the
complexification of the displayed matrix with the character table up to row order.  In particular,
the repeated degree `3` causes no ambiguity: the two rows are distinguished by their values on odd
classes.

## Main definitions

* `TauCeti.symmetricGroupFourCentralCharacterTable`: the integral central-character table.
* `TauCeti.symmetricGroupFourCharacterDegrees`: the degrees `1, 1, 2, 3, 3`.
* `TauCeti.symmetricGroupFourCharacterTable`: the integral ordinary character table.

## Main results

* `TauCeti.isIntegerCharacterTableSpec_symmetricGroupFour`: the exact certificate.
* `TauCeti.integerCharacterTableChecker_symmetricGroupFour`: the executable checker succeeds.
* `TauCeti.isCharacterTableSpec_symmetricGroupFour`: the embedded table satisfies the complex
  character-table specification.

## References

* G. James and M. Liebeck, *Representations and Characters of Groups*, Section 11.3.
* J. D. Dixon, *High speed computation of group characters*, Numerische Mathematik 10 (1967),
  446--450.
-/

public section

namespace TauCeti

open Matrix

/-- The indices of the five conjugacy classes and five character rows of `S₄`. -/
abbrev SymmetricGroupFourClassIndex := Fin symmetricGroupFourClassData.numClasses

/-- **The integral central-character table of `S₄`.**  An entry is the scalar by which the
corresponding class sum acts on the irreducible representation. -/
def symmetricGroupFourCentralCharacterTable :
    Matrix SymmetricGroupFourClassIndex SymmetricGroupFourClassIndex ℤ :=
  !![1,  6,  3,  8,  6;
     1, -6,  3,  8, -6;
     1,  0,  3, -4,  0;
     1,  2, -1,  0, -2;
     1, -2, -1,  0,  2]

/-- The entries of the integral central-character table. -/
@[simp]
theorem symmetricGroupFourCentralCharacterTable_apply
    (i j : SymmetricGroupFourClassIndex) :
    symmetricGroupFourCentralCharacterTable i j =
      !![1,  6,  3,  8,  6;
         1, -6,  3,  8, -6;
         1,  0,  3, -4,  0;
         1,  2, -1,  0, -2;
         1, -2, -1,  0,  2] i j := by
  rfl

/-- The character degrees of `S₄`, ordered with the rows of the displayed tables. -/
def symmetricGroupFourCharacterDegrees : SymmetricGroupFourClassIndex → ℕ :=
  ![1, 1, 2, 3, 3]

/-- The character degrees, entrywise. -/
@[simp]
theorem symmetricGroupFourCharacterDegrees_apply (i : SymmetricGroupFourClassIndex) :
    symmetricGroupFourCharacterDegrees i = ![1, 1, 2, 3, 3] i := by
  rfl

/-- **The integral ordinary character table of `S₄`.**  Rows are the trivial character, the
sign character, the two-dimensional character, the standard character, and its sign twist. -/
def symmetricGroupFourCharacterTable :
    Matrix SymmetricGroupFourClassIndex SymmetricGroupFourClassIndex ℤ :=
  !![1,  1,  1,  1,  1;
     1, -1,  1,  1, -1;
     2,  0,  2, -1,  0;
     3,  1, -1,  0, -1;
     3, -1, -1,  0,  1]

/-- The entries of the ordinary character table. -/
@[simp]
theorem symmetricGroupFourCharacterTable_apply (i j : SymmetricGroupFourClassIndex) :
    symmetricGroupFourCharacterTable i j =
      !![1,  1,  1,  1,  1;
         1, -1,  1,  1, -1;
         2,  0,  2, -1,  0;
         3,  1, -1,  0, -1;
         3, -1, -1,  0,  1] i j := by
  rfl

/-- Every displayed central-character row satisfies the class-algebra eigenrow equations. -/
theorem isModularEigenrow_symmetricGroupFourCentralCharacterTable_int
    (i : SymmetricGroupFourClassIndex) :
    symmetricGroupFourClassData.IsModularEigenrow
      (fun j => symmetricGroupFourCentralCharacterTable i j) := by
  rw [symmetricGroupFourClassData.isModularEigenrow_iff]
  simp only [symmetricGroupFourCentralCharacterTable_apply]
  fin_cases i <;> decide

/-- **Division-free conversion from central characters to ordinary characters.** -/
theorem symmetricGroupFour_degree_mul_centralCharacterTable
    (i j : SymmetricGroupFourClassIndex) :
    (symmetricGroupFourCharacterDegrees i : ℤ) *
        symmetricGroupFourCentralCharacterTable i j =
      (symmetricGroupFourClassData.classFinset j).card *
        symmetricGroupFourCharacterTable i j := by
  simp only [symmetricGroupFourCharacterDegrees_apply,
    symmetricGroupFourCentralCharacterTable_apply, symmetricGroupFourCharacterTable_apply]
  fin_cases i <;> fin_cases j <;> decide

/-- The displayed degrees are positive and divide the order of `S₄`. -/
theorem symmetricGroupFour_characterDegrees_pos_and_dvd
    (i : SymmetricGroupFourClassIndex) :
    0 < symmetricGroupFourCharacterDegrees i ∧
      symmetricGroupFourCharacterDegrees i ∣ Nat.card (Equiv.Perm (Fin 4)) := by
  rw [Nat.card_perm, Nat.card_fin]
  simp only [symmetricGroupFourCharacterDegrees_apply]
  fin_cases i <;> decide

/-- The squares of the displayed degrees sum to the order of `S₄`. -/
theorem symmetricGroupFour_sum_characterDegrees_sq :
    ∑ i, symmetricGroupFourCharacterDegrees i ^ 2 = Nat.card (Equiv.Perm (Fin 4)) := by
  rw [Nat.card_perm, Nat.card_fin]
  simp only [symmetricGroupFourCharacterDegrees_apply]
  decide

/-- The ordinary character rows satisfy class-size weighted orthogonality. -/
theorem symmetricGroupFour_characterTable_orthogonal
    (i j : SymmetricGroupFourClassIndex) :
    ∑ k, (symmetricGroupFourClassData.classFinset k).card *
        symmetricGroupFourCharacterTable i k * symmetricGroupFourCharacterTable j k =
      if i = j then Nat.card (Equiv.Perm (Fin 4)) else 0 := by
  rw [Nat.card_perm, Nat.card_fin]
  simp only [symmetricGroupFourCharacterTable_apply]
  fin_cases i <;> fin_cases j <;> decide

/-- **The displayed tables form an exact integer character-table certificate for `S₄`.** -/
theorem isIntegerCharacterTableSpec_symmetricGroupFour :
    symmetricGroupFourClassData.IsIntegerCharacterTableSpec
      symmetricGroupFourCentralCharacterTable symmetricGroupFourCharacterTable
      symmetricGroupFourCharacterDegrees where
  central_one i := by fin_cases i <;> decide
  central_eigen := isModularEigenrow_symmetricGroupFourCentralCharacterTable_int
  degree_pos i := (symmetricGroupFour_characterDegrees_pos_and_dvd i).1
  degree_dvd i := by
    simpa only [Nat.card_eq_fintype_card] using
      (symmetricGroupFour_characterDegrees_pos_and_dvd i).2
  sum_degree_sq := by
    simpa only [Nat.card_eq_fintype_card] using symmetricGroupFour_sum_characterDegrees_sq
  degree_mul_central := symmetricGroupFour_degree_mul_centralCharacterTable
  row_orthogonal i j := by
    simpa only [Nat.card_eq_fintype_card, Nat.cast_ite, Nat.cast_zero] using
      symmetricGroupFour_characterTable_orthogonal i j

/-- **The executable exact checker accepts the displayed `S₄` tables.** -/
theorem integerCharacterTableChecker_symmetricGroupFour :
    symmetricGroupFourClassData.integerCharacterTableChecker
      symmetricGroupFourCentralCharacterTable symmetricGroupFourCharacterTable
      symmetricGroupFourCharacterDegrees = true := by
  rw [symmetricGroupFourClassData.integerCharacterTableChecker_eq_true_iff]
  exact isIntegerCharacterTableSpec_symmetricGroupFour

/-- **The exact integer table of `S₄`, cast to `ℂ`, satisfies the character-table
specification.**  Consequently it is the ordinary complex character table up to row order. -/
theorem isCharacterTableSpec_symmetricGroupFour :
    IsCharacterTableSpec (Equiv.Perm (Fin 4))
      (symmetricGroupFourClassData.complexTableOfInteger symmetricGroupFourCharacterTable) :=
  isIntegerCharacterTableSpec_symmetricGroupFour.isCharacterTableSpec

end TauCeti
