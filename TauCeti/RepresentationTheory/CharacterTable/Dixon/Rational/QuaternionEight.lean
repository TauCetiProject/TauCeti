/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.Dixon.ClassData.CentralCharacterCount
public import TauCeti.RepresentationTheory.CharacterTable.Dixon.ClassData.Quaternion
public import TauCeti.RepresentationTheory.CharacterTable.Dixon.Quaternion
public import TauCeti.RepresentationTheory.CharacterTable.Dixon.Rational.Solver

/-!
# The rational Dixon computation for the quaternion group of order eight

This file runs the rational stage of the Dixon--Schneider character-table algorithm for
`QuaternionGroup 2`.  Its five numbered conjugacy classes have sizes `[1, 1, 2, 2, 2]`.
Reducing modulo the certified good prime `5`, the simultaneous eigenrow search returns exactly
the reductions of the five rows displayed in `TauCeti.quaternionGroupTwoCentralCharacterTable`.

Each displayed row is checked against the computed structure constants, while the good-prime
count theorem supplies completeness of the modular search.  Signed least representatives modulo
`5` then recover the integral central-character rows.  The displayed candidate degrees and ordinary
table are verified by the division-free conversion identity, the degree-square sum, and weighted
row orthogonality.  The ordinary table is the same matrix as the table of `DihedralGroup 4`, the
classical example of nonisomorphic groups with equal character tables.

## Main definitions

* `TauCeti.quaternionGroupTwoCentralCharacterTable`: the five integral central-character rows.
* `TauCeti.quaternionGroupTwoModularCentralRows`: their reductions modulo `5`.
* `TauCeti.quaternionGroupTwoCharacterTable`: the displayed ordinary integral character table.

## Main results

* `TauCeti.quaternionGroupTwo_centralCharacterSearch`: the modular search returns exactly the
  displayed reductions.
* `TauCeti.quaternionGroupTwo_valMinAbs_centralCharacterTable`: signed least representatives lift
  every modular entry to the displayed integer.
* `TauCeti.quaternionGroupTwo_degree_mul_centralCharacterTable`: the division-free conversion to
  the ordinary character table.
* `TauCeti.isIntegerCharacterTableSpec_quaternionGroupTwo`: the exact integral certificate.
* `TauCeti.integerCharacterTableChecker_quaternionGroupTwo`: the executable checker accepts the
  displayed tables and degrees.
* `TauCeti.isSome_dixonRationalCharacterTable_quaternionGroupTwo`: the assembled rational solver
  succeeds on the certified prime.
* `TauCeti.isCharacterTableSpec_quaternionGroupTwo`: the displayed ordinary table, cast to `ℂ`,
  satisfies the character-table specification.

## References

This closes the `Q₈ = QuaternionGroup 2` part of "Rational tables (first executable milestone)"
in Layer 6 of the
[character theory roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md).

* J. D. Dixon, *High speed computation of group characters*, Numerische Mathematik 10 (1967),
  446--450.
* G. Schneider, *Dixon's character table algorithm revisited*, J. Symbolic Comput. 9 (1990),
  601--606.
* The formal template is
  `TauCeti.RepresentationTheory.CharacterTable.Dixon.Rational.DihedralFour`; this file and its
  quaternion class-data and good-prime prerequisites adapt the corresponding dihedral development.
-/

public section

namespace TauCeti

open Matrix

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The numbered conjugacy classes of the quaternion group of order eight. -/
abbrev QuaternionGroupTwoClassIndex := Fin (quaternionClassData 2).numClasses

/-- **The integral central-character table of the quaternion group of order eight.** Columns
follow `TauCeti.quaternionClassData 2`: the identity, the central element of order two, and the
three classes consisting of a pair of quaternion units. -/
def quaternionGroupTwoCentralCharacterTable :
    Matrix QuaternionGroupTwoClassIndex QuaternionGroupTwoClassIndex ℤ :=
  !![1,  1,  2,  2,  2;
     1,  1,  2, -2, -2;
     1,  1, -2,  2, -2;
     1,  1, -2, -2,  2;
     1, -1,  0,  0,  0]

/-- The entries of the integral central-character table. -/
@[simp]
theorem quaternionGroupTwoCentralCharacterTable_apply
    (i j : QuaternionGroupTwoClassIndex) :
    quaternionGroupTwoCentralCharacterTable i j =
      !![1,  1,  2,  2,  2;
         1,  1,  2, -2, -2;
         1,  1, -2,  2, -2;
         1,  1, -2, -2,  2;
         1, -1,  0,  0,  0] i j := by
  rfl

/-- The five central-character rows reduced modulo the certified Dixon prime `5`. -/
def quaternionGroupTwoModularCentralRows :
    Finset (QuaternionGroupTwoClassIndex → ZMod 5) :=
  (quaternionClassData 2).rowsOfMap (fun x : ℤ => (x : ZMod 5))
    quaternionGroupTwoCentralCharacterTable

/-- A modular row is displayed exactly when it is the reduction of a row of the integral table. -/
@[simp]
theorem mem_quaternionGroupTwoModularCentralRows_iff
    {a : QuaternionGroupTwoClassIndex → ZMod 5} :
    a ∈ quaternionGroupTwoModularCentralRows ↔
      ∃ i, (fun j => (quaternionGroupTwoCentralCharacterTable i j : ZMod 5)) = a := by
  simp [quaternionGroupTwoModularCentralRows]

/-- Each integral row is a simultaneous eigenrow of the integral class-multiplication matrices. -/
theorem isModularEigenrow_quaternionGroupTwoCentralCharacterTable_int
    (i : QuaternionGroupTwoClassIndex) :
    (quaternionClassData 2).IsModularEigenrow
      (fun j => quaternionGroupTwoCentralCharacterTable i j) := by
  rw [(quaternionClassData 2).isModularEigenrow_iff]
  simp only [quaternionGroupTwoCentralCharacterTable_apply]
  fin_cases i <;> decide

/-- Reindexing an integral row by the actual conjugacy classes gives a class-algebra eigenrow. -/
theorem isClassEigenrow_quaternionGroupTwoCentralCharacterTable
    (i : QuaternionGroupTwoClassIndex) :
    IsClassEigenrow ((quaternionClassData 2).reindexModularRow
      fun j => quaternionGroupTwoCentralCharacterTable i j) :=
  ((quaternionClassData 2).isModularEigenrow_iff_isClassEigenrow _).mp
    (isModularEigenrow_quaternionGroupTwoCentralCharacterTable_int i)

/-- Every displayed reduction is a simultaneous eigenrow over `ZMod 5`. -/
theorem isModularEigenrow_quaternionGroupTwoCentralCharacterTable_zmod
    (i : QuaternionGroupTwoClassIndex) :
    (quaternionClassData 2).IsModularEigenrow
      (fun j => (quaternionGroupTwoCentralCharacterTable i j : ZMod 5)) := by
  rw [(quaternionClassData 2).isModularEigenrow_iff]
  simp only [quaternionGroupTwoCentralCharacterTable_apply]
  fin_cases i <;> decide

/-- The explicit set of modular rows has five elements. -/
@[simp]
theorem card_quaternionGroupTwoModularCentralRows :
    quaternionGroupTwoModularCentralRows.card = 5 := by
  decide

/-- **The executable modular central-character search for `QuaternionGroup 2` returns precisely
the five displayed reductions.** -/
theorem quaternionGroupTwo_centralCharacterSearch :
    (quaternionClassData 2).centralCharacterSearch (F := ZMod 5) =
      quaternionGroupTwoModularCentralRows := by
  rw [quaternionGroupTwoModularCentralRows]
  apply (quaternionClassData 2).centralCharacterSearch_eq_rowsOfMap_of_isGoodDixonPrime
    isGoodDixonPrime_quaternionGroup_two_five (fun x : ℤ => (x : ZMod 5))
    quaternionGroupTwoCentralCharacterTable
  · intro i
    fin_cases i <;> decide
  · exact isModularEigenrow_quaternionGroupTwoCentralCharacterTable_zmod
  · simpa only [quaternionGroupTwoModularCentralRows, numClasses_quaternionClassData_two] using
      card_quaternionGroupTwoModularCentralRows

/-- **Signed least representatives modulo `5` recover the integral central-character table.** -/
theorem quaternionGroupTwo_valMinAbs_centralCharacterTable
    (i j : QuaternionGroupTwoClassIndex) :
    ((quaternionGroupTwoCentralCharacterTable i j : ZMod 5)).valMinAbs =
      quaternionGroupTwoCentralCharacterTable i j := by
  rw [quaternionGroupTwoCentralCharacterTable_apply]
  apply ZMod.valMinAbs_intCast_of_two_mul_natAbs_lt
  fin_cases i <;> fin_cases j <;> decide

/-- **The rational lift is exactly the displayed integral central-character table, up to row
order.** -/
theorem quaternionGroupTwo_liftedCentralRows :
    (quaternionClassData 2).liftedCentralRows 5 =
      Finset.univ.image fun i => quaternionGroupTwoCentralCharacterTable i := by
  apply (quaternionClassData 2).liftedCentralRows_eq_image_of_centralCharacterSearch_eq
    quaternionGroupTwoCentralCharacterTable
    (by rw [quaternionGroupTwo_centralCharacterSearch, quaternionGroupTwoModularCentralRows])
  intro i j
  rw [quaternionGroupTwoCentralCharacterTable_apply]
  fin_cases i <;> fin_cases j <;> decide

/-- The degrees attached to the five central-character rows. -/
def quaternionGroupTwoCharacterDegrees : QuaternionGroupTwoClassIndex → ℕ :=
  ![1, 1, 1, 1, 2]

/-- The degrees attached to the central-character rows, entrywise. -/
@[simp]
theorem quaternionGroupTwoCharacterDegrees_apply (i : QuaternionGroupTwoClassIndex) :
    quaternionGroupTwoCharacterDegrees i = ![1, 1, 1, 1, 2] i := by
  rfl

/-- **The displayed candidate integral character table for the quaternion group of order eight.**
The results below verify its conversion from the displayed central-character table, degree-square
sum, and weighted row orthogonality. -/
def quaternionGroupTwoCharacterTable :
    Matrix QuaternionGroupTwoClassIndex QuaternionGroupTwoClassIndex ℤ :=
  !![1,  1,  1,  1,  1;
     1,  1,  1, -1, -1;
     1,  1, -1,  1, -1;
     1,  1, -1, -1,  1;
     2, -2,  0,  0,  0]

/-- The entries of the ordinary integral character table. -/
@[simp]
theorem quaternionGroupTwoCharacterTable_apply (i j : QuaternionGroupTwoClassIndex) :
    quaternionGroupTwoCharacterTable i j =
      !![1,  1,  1,  1,  1;
         1,  1,  1, -1, -1;
         1,  1, -1,  1, -1;
         1,  1, -1, -1,  1;
         2, -2,  0,  0,  0] i j := by
  rfl

/-- **Division-free conversion from central characters to ordinary characters.** For every row
`i` and numbered conjugacy class `j`, `degree i * omega i j = |K_j| * chi i j`. -/
theorem quaternionGroupTwo_degree_mul_centralCharacterTable
    (i j : QuaternionGroupTwoClassIndex) :
    (quaternionGroupTwoCharacterDegrees i : ℤ) *
        quaternionGroupTwoCentralCharacterTable i j =
      ((quaternionClassData 2).classFinset j).card * quaternionGroupTwoCharacterTable i j := by
  simp only [quaternionGroupTwoCharacterDegrees_apply,
    quaternionGroupTwoCentralCharacterTable_apply, quaternionGroupTwoCharacterTable_apply]
  fin_cases i <;> fin_cases j <;> decide

/-- The displayed degrees are positive and divide the order of `QuaternionGroup 2`. -/
theorem quaternionGroupTwo_characterDegrees_pos_and_dvd (i : QuaternionGroupTwoClassIndex) :
    0 < quaternionGroupTwoCharacterDegrees i ∧
      quaternionGroupTwoCharacterDegrees i ∣ Nat.card (QuaternionGroup 2) := by
  rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
  simp only [quaternionGroupTwoCharacterDegrees_apply]
  fin_cases i <;> decide

/-- The squares of the displayed degrees sum to the group order. -/
theorem quaternionGroupTwo_sum_characterDegrees_sq :
    ∑ i, quaternionGroupTwoCharacterDegrees i ^ 2 = Nat.card (QuaternionGroup 2) := by
  rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
  simp only [quaternionGroupTwoCharacterDegrees_apply]
  decide

/-- The ordinary character rows satisfy the class-size weighted orthogonality relations. -/
theorem quaternionGroupTwo_characterTable_orthogonal (i j : QuaternionGroupTwoClassIndex) :
    ∑ k, ((quaternionClassData 2).classFinset k).card *
        quaternionGroupTwoCharacterTable i k * quaternionGroupTwoCharacterTable j k =
      if i = j then Nat.card (QuaternionGroup 2) else 0 := by
  rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
  simp only [quaternionGroupTwoCharacterTable_apply]
  fin_cases i <;> fin_cases j <;> decide

/-- **The rational Dixon output for the quaternion group of order eight has an exact
character-table certificate.** The certificate assembles the integral class-algebra
eigenvectors, character degrees, conversion identity, and weighted row orthogonality. -/
theorem isIntegerCharacterTableSpec_quaternionGroupTwo :
    (quaternionClassData 2).IsIntegerCharacterTableSpec
      quaternionGroupTwoCentralCharacterTable quaternionGroupTwoCharacterTable
      quaternionGroupTwoCharacterDegrees where
  central_one i := by fin_cases i <;> decide
  central_eigen := isModularEigenrow_quaternionGroupTwoCentralCharacterTable_int
  degree_pos i := (quaternionGroupTwo_characterDegrees_pos_and_dvd i).1
  degree_dvd i := by
    simpa only [Nat.card_eq_fintype_card] using
      (quaternionGroupTwo_characterDegrees_pos_and_dvd i).2
  sum_degree_sq := by
    simpa only [Nat.card_eq_fintype_card] using quaternionGroupTwo_sum_characterDegrees_sq
  degree_mul_central := quaternionGroupTwo_degree_mul_centralCharacterTable
  row_orthogonal i j := by
    simpa only [Nat.card_eq_fintype_card, Nat.cast_ite, Nat.cast_zero] using
      quaternionGroupTwo_characterTable_orthogonal i j

/-- The executable exact checker accepts the rational Dixon output for `QuaternionGroup 2`. -/
theorem integerCharacterTableChecker_quaternionGroupTwo :
    (quaternionClassData 2).integerCharacterTableChecker
      quaternionGroupTwoCentralCharacterTable quaternionGroupTwoCharacterTable
      quaternionGroupTwoCharacterDegrees = true := by
  rw [(quaternionClassData 2).integerCharacterTableChecker_eq_true_iff]
  exact isIntegerCharacterTableSpec_quaternionGroupTwo

/-- **The assembled rational Dixon--Schneider solver succeeds on the certified prime for
`QuaternionGroup 2`.** -/
theorem isSome_dixonRationalCharacterTable_quaternionGroupTwo :
    ((quaternionClassData 2).dixonRationalCharacterTable? 5).isSome = true := by
  rw [(quaternionClassData 2).isSome_dixonRationalCharacterTable_iff]
  refine ⟨⟨quaternionGroupTwoCentralCharacterTable, quaternionGroupTwoCharacterTable,
    quaternionGroupTwoCharacterDegrees⟩, ?_, isIntegerCharacterTableSpec_quaternionGroupTwo⟩
  intro i
  rw [quaternionGroupTwo_liftedCentralRows]
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩

/-- **The exact rational Dixon output for `QuaternionGroup 2`, cast to `ℂ`, satisfies the
character-table specification.** Consequently it is the ordinary complex character table up to
a row permutation. -/
theorem isCharacterTableSpec_quaternionGroupTwo :
    IsCharacterTableSpec (QuaternionGroup 2)
      ((quaternionClassData 2).complexTableOfInteger quaternionGroupTwoCharacterTable) :=
  isIntegerCharacterTableSpec_quaternionGroupTwo.isCharacterTableSpec

end TauCeti
