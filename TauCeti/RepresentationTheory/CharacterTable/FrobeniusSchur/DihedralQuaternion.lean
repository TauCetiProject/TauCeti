/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.Dixon.Rational.Dihedral.Four
public import TauCeti.RepresentationTheory.CharacterTable.Dixon.Rational.QuaternionEight
public import TauCeti.RepresentationTheory.CharacterTable.FrobeniusSchur.InvolutionCount

/-!
# `D₄` and `Q₈`: equal character tables, different Frobenius-Schur indicators

The dihedral group `DihedralGroup 4` and the quaternion group `QuaternionGroup 2` are the two
nonabelian groups of order eight.  Their complex character tables were computed independently by
the Dixon--Schneider algorithm in
`TauCeti/RepresentationTheory/CharacterTable/Dixon/Rational/Dihedral/Four.lean` and
`TauCeti/RepresentationTheory/CharacterTable/Dixon/Rational/QuaternionEight.lean`, and the two
computations returned the *same* matrix of integers: five classes of sizes `1, 1, 2, 2, 2` and
five irreducible characters of degrees `1, 1, 1, 1, 2`.

This file turns that numerical coincidence into a statement about the groups.  Both displayed
tables are certified by `TauCeti.IsCharacterTableSpec`, and a matrix satisfying that specification
is the character table up to a permutation of its rows
(`TauCeti.characterTable_unique_rows`).  Transporting along the two class numberings therefore
identifies the two character tables outright: there are a relabelling `σ` of the irreducible
characters and a relabelling `e` of the conjugacy classes, matching identity class with identity
class, under which `characterTable ℂ (DihedralGroup 4)` *is*
`characterTable ℂ (QuaternionGroup 2)`.

The two groups are nevertheless not isomorphic, and the character table cannot see the difference.
What does see it is the Frobenius-Schur indicator.  Counting square roots of the identity gives
`#{g ∈ D₄ : g² = 1} = 6` but `#{g ∈ Q₈ : g² = 1} = 2`, while the involution-counting formula
`#{g : g² = 1} = ∑_χ ν₂(χ) χ(1)` of
`TauCeti/RepresentationTheory/CharacterTable/FrobeniusSchur/InvolutionCount.lean` expresses that
count from the degrees — which the two tables share — weighted by the indicators.  So under *any*
identification of the two tables the indicators must disagree on some row.  The disagreement is
located concretely in the two sibling files
`TauCeti/RepresentationTheory/CharacterTable/FrobeniusSchur/Dihedral.lean` and
`TauCeti/RepresentationTheory/CharacterTable/FrobeniusSchur/Quaternion.lean`: the two-dimensional
irreducible of `D₄` is orthogonal, with indicator `1`, and that of `Q₈` is quaternionic, with
indicator `-1`.

## Main results

* `TauCeti.dihedralGroupFourCharacterTable_eq_submatrix_quaternionGroupTwoCharacterTable`: **the
  two displayed integral tables are the same matrix**, once the two class numberings are matched.
* `TauCeti.exists_equiv_characterTable_dihedralGroupFour_eq_characterTable_quaternionGroupTwo`:
  **the complex character tables of `D₄` and `Q₈` agree** after a relabelling of rows and of
  columns which fixes the identity class.
* `TauCeti.card_squareRoot_one_dihedralGroupFour` and
  `TauCeti.card_squareRoot_one_quaternionGroupTwo`: the two counts `6` and `2` of solutions of
  `g² = 1`.
* `TauCeti.isEmpty_mulEquiv_dihedralGroupFour_quaternionGroupTwo`: **the two groups are not
  isomorphic**, those counts being an isomorphism invariant.
* `TauCeti.exists_frobeniusSchurIndicatorRow_ne_of_characterTable_eq`: **for every identification
  of the two character tables the Frobenius-Schur indicators disagree on some row**, and
  `TauCeti.exists_characterTable_eq_and_frobeniusSchurIndicatorRow_ne` packages it with the
  existence of such an identification.

## Implementation notes

The step shared by the two groups — reading a certified numbered integer table as the character
table after a row relabelling — is the private
`TauCeti.exists_equiv_characterTable_classOf_eq`.  It is stated for an arbitrary `ClassData`, but
kept private: it is the assembly step of this comparison and has no consumer of its own, the
general uniqueness statement being `TauCeti.characterTable_unique_rows`.

`TauCeti.exists_frobeniusSchurIndicatorRow_ne_of_characterTable_eq` takes the identification as a
hypothesis rather than producing one, so that it says the indicators are invisible to *every*
matching of the tables, not merely to the one this file happens to construct.  The hypothesis that
the column relabelling fixes the identity class is what makes the two degree columns correspond;
without it "the same table" would not constrain the degrees.

## References

This is the `D₄`/`Q₈` clause of "Rational tables (first executable milestone)" and the
`D₄`/`Q₈` clause of "Frobenius-Schur type (Layer 7)" in the worked examples of the
[character theory roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md):
"the classic pair with the same character table yet non-isomorphic, distinguished by the
Frobenius-Schur indicator".

* J.-P. Serre, *Linear Representations of Finite Groups*, GTM 42 (1977), §§5.3 and 13.2.
* I. M. Isaacs, *Character Theory of Finite Groups* (1976), Chapter 4 and Theorem 4.5.
-/

public section

namespace TauCeti

open scoped Matrix

universe v

/-- A certified numbered integer table is the character table, after a relabelling of its rows:
the row `i` and numbered class `j` entry of the table is the value of the `ρ i`-th irreducible
character on the `j`-th class.  This packages
`TauCeti.characterTable_unique_rows` with the transport
`TauCeti.ClassData.complexTableOfInteger_apply_classOf` of a numbered table to the conjugacy
classes. -/
private theorem exists_equiv_characterTable_classOf_eq {G : Type v} [Group G] [Fintype G]
    [DecidableEq G] (d : ClassData G) (T : Matrix (Fin d.numClasses) (Fin d.numClasses) ℤ)
    (hT : IsCharacterTableSpec G (d.complexTableOfInteger T)) :
    ∃ ρ : Fin d.numClasses ≃ Fin (Nat.card (ConjClasses G)),
      ∀ i j, characterTable ℂ G (ρ i) (d.classOf j) = (T i j : ℂ) := by
  obtain ⟨σ, hσ⟩ := characterTable_unique_rows hT
  refine ⟨(finCongr d.numClasses_eq_card_conjClasses).trans σ, fun i j => ?_⟩
  have h := congrFun₂ hσ (finCongr d.numClasses_eq_card_conjClasses i) (d.classOf j)
  rw [d.complexTableOfInteger_apply_classOf] at h
  exact h.symm

/-! ### The two displayed tables coincide -/

/-- **`D₄` and `Q₈` have the same number of conjugacy classes**, namely five. -/
theorem numClasses_dihedralClassData_four_eq_numClasses_quaternionClassData_two :
    (dihedralClassData 4).numClasses = (quaternionClassData 2).numClasses :=
  numClasses_dihedralClassData_four.trans numClasses_quaternionClassData_two.symm

/-- **The displayed integral character tables of `D₄` and `Q₈` are the same matrix.**  The two
Dixon--Schneider computations number their classes so that the sizes come out as `1, 1, 2, 2, 2`
in both cases, and with that numbering the two tables agree entry by entry. -/
theorem dihedralGroupFourCharacterTable_eq_submatrix_quaternionGroupTwoCharacterTable :
    dihedralGroupFourCharacterTable =
      quaternionGroupTwoCharacterTable.submatrix
        (finCongr numClasses_dihedralClassData_four_eq_numClasses_quaternionClassData_two)
        (finCongr numClasses_dihedralClassData_four_eq_numClasses_quaternionClassData_two) := by
  ext i j
  rw [Matrix.submatrix_apply, quaternionGroupTwoCharacterTable_apply,
    dihedralGroupFourCharacterTable_apply]
  fin_cases i <;> fin_cases j <;> decide

/-- The identity class is the first numbered class of `D₄`. -/
private theorem classOf_zero_dihedralClassData_four :
    (dihedralClassData 4).classOf ⟨0, by decide⟩ = ConjClasses.mk (1 : DihedralGroup 4) := by
  rw [ClassData.classOf_eq_mk]
  congr 1

/-- The identity class is the first numbered class of `Q₈`. -/
private theorem classOf_zero_quaternionClassData_two :
    (quaternionClassData 2).classOf ⟨0, by decide⟩ = ConjClasses.mk (1 : QuaternionGroup 2) := by
  rw [ClassData.classOf_eq_mk]
  congr 1

/-! ### The two character tables coincide -/

/-- **The complex character tables of `D₄` and `Q₈` agree.**  There is a relabelling `σ` of the
irreducible characters and a relabelling `e` of the conjugacy classes, carrying the identity class
to the identity class, under which the character table of `DihedralGroup 4` is the character table
of `QuaternionGroup 2`.

Both tables are certified by the Dixon--Schneider checker as the same matrix of integers, and a
certified matrix is the character table up to a permutation of its rows, so the two character
tables differ only by the two relabellings. -/
theorem exists_equiv_characterTable_dihedralGroupFour_eq_characterTable_quaternionGroupTwo :
    ∃ (σ : Fin (Nat.card (ConjClasses (DihedralGroup 4))) ≃
            Fin (Nat.card (ConjClasses (QuaternionGroup 2))))
      (e : ConjClasses (DihedralGroup 4) ≃ ConjClasses (QuaternionGroup 2)),
      e (ConjClasses.mk 1) = ConjClasses.mk 1 ∧
        characterTable ℂ (DihedralGroup 4) =
          (characterTable ℂ (QuaternionGroup 2)).submatrix σ e := by
  obtain ⟨ρD, hρD⟩ := exists_equiv_characterTable_classOf_eq (dihedralClassData 4)
    dihedralGroupFourCharacterTable isCharacterTableSpec_dihedralGroupFour
  obtain ⟨ρQ, hρQ⟩ := exists_equiv_characterTable_classOf_eq (quaternionClassData 2)
    quaternionGroupTwoCharacterTable isCharacterTableSpec_quaternionGroupTwo
  set c := finCongr numClasses_dihedralClassData_four_eq_numClasses_quaternionClassData_two with hc
  refine ⟨ρD.symm.trans (c.trans ρQ),
    (dihedralClassData 4).equivConjClasses.symm.trans
      (c.trans (quaternionClassData 2).equivConjClasses), ?_, ?_⟩
  · have h0 : (dihedralClassData 4).equivConjClasses.symm
        (ConjClasses.mk (1 : DihedralGroup 4)) = ⟨0, by decide⟩ := by
      rw [Equiv.symm_apply_eq, ClassData.equivConjClasses_apply,
        classOf_zero_dihedralClassData_four]
    simp only [Equiv.trans_apply, h0, hc, finCongr_apply, Fin.cast_mk]
    rw [ClassData.equivConjClasses_apply]
    exact classOf_zero_quaternionClassData_two
  · ext r C
    obtain ⟨i, rfl⟩ := ρD.surjective r
    obtain ⟨j, rfl⟩ := (dihedralClassData 4).equivConjClasses.surjective C
    simp only [Matrix.submatrix_apply, Equiv.trans_apply, Equiv.symm_apply_apply]
    rw [ClassData.equivConjClasses_apply, hρD, ClassData.equivConjClasses_apply, hρQ]
    exact_mod_cast congrArg (Int.cast (R := ℂ))
      (congrFun₂ dihedralGroupFourCharacterTable_eq_submatrix_quaternionGroupTwoCharacterTable i j)

/-! ### The groups are not isomorphic, and the indicators know it -/

/-- **`D₄` has six square roots of the identity**: the identity itself, the square of the
rotation, and the four reflections. -/
theorem card_squareRoot_one_dihedralGroupFour :
    Nat.card {g : DihedralGroup 4 // g * g = 1} = 6 := by
  rw [Nat.card_eq_fintype_card]
  decide

/-- **`Q₈` has two square roots of the identity**: the identity and the central element of order
two.  Every other element has order four. -/
theorem card_squareRoot_one_quaternionGroupTwo :
    Nat.card {g : QuaternionGroup 2 // g * g = 1} = 2 := by
  rw [Nat.card_eq_fintype_card]
  decide

/-- **`D₄` and `Q₈` are not isomorphic**, although their character tables agree: an isomorphism
would match their square roots of the identity, of which there are six and two. -/
theorem isEmpty_mulEquiv_dihedralGroupFour_quaternionGroupTwo :
    IsEmpty (DihedralGroup 4 ≃* QuaternionGroup 2) := by
  refine ⟨fun f => ?_⟩
  have h : Nat.card {g : DihedralGroup 4 // g * g = 1} =
      Nat.card {g : QuaternionGroup 2 // g * g = 1} :=
    Nat.card_congr (f.toEquiv.subtypeEquiv fun a => by simp [← map_mul])
  rw [card_squareRoot_one_dihedralGroupFour, card_squareRoot_one_quaternionGroupTwo] at h
  omega

/-- **The Frobenius-Schur indicators of `D₄` and `Q₈` disagree under every identification of their
character tables.**  Given relabellings `σ` of the rows and `e` of the columns carrying the
identity class to the identity class and identifying the two tables, some row of the table of
`DihedralGroup 4` has a different indicator from the row of `QuaternionGroup 2` it is matched with.

Matching the identity columns makes the degrees correspond, so if the indicators corresponded too
then the involution-counting formula `#{g : g² = 1} = ∑_χ ν₂(χ) χ(1)` would return the same number
for both groups; it returns `6` and `2`. -/
theorem exists_frobeniusSchurIndicatorRow_ne_of_characterTable_eq
    (σ : Fin (Nat.card (ConjClasses (DihedralGroup 4))) ≃
          Fin (Nat.card (ConjClasses (QuaternionGroup 2))))
    (e : ConjClasses (DihedralGroup 4) ≃ ConjClasses (QuaternionGroup 2))
    (he : e (ConjClasses.mk 1) = ConjClasses.mk 1)
    (hT : characterTable ℂ (DihedralGroup 4) =
      (characterTable ℂ (QuaternionGroup 2)).submatrix σ e) :
    ∃ i, frobeniusSchurIndicatorRow ℂ (G := DihedralGroup 4) i ≠
      frobeniusSchurIndicatorRow ℂ (G := QuaternionGroup 2) (σ i) := by
  by_contra hcon
  have hnu : ∀ i, frobeniusSchurIndicatorRow ℂ (G := DihedralGroup 4) i =
      frobeniusSchurIndicatorRow ℂ (G := QuaternionGroup 2) (σ i) :=
    fun i => not_not.mp fun h => hcon ⟨i, h⟩
  have hdeg : ∀ i, (characterDegree ℂ (G := DihedralGroup 4) i : ℂ) =
      (characterDegree ℂ (G := QuaternionGroup 2) (σ i) : ℂ) := fun i => by
    rw [← characterTable_one, ← characterTable_one, hT, Matrix.submatrix_apply, he]
  have key : ((6 : ℕ) : ℂ) = ((2 : ℕ) : ℂ) :=
    calc ((6 : ℕ) : ℂ)
        = (Nat.card {g : DihedralGroup 4 // g * g = 1} : ℂ) := by
          rw [card_squareRoot_one_dihedralGroupFour]
      _ = ∑ i, frobeniusSchurIndicatorRow ℂ (G := DihedralGroup 4) i *
            (characterDegree ℂ (G := DihedralGroup 4) i : ℂ) :=
          card_squareRoot_one_eq_sum_frobeniusSchurIndicatorRow_mul_characterDegree ℂ
            (DihedralGroup 4)
      _ = ∑ i, frobeniusSchurIndicatorRow ℂ (G := QuaternionGroup 2) (σ i) *
            (characterDegree ℂ (G := QuaternionGroup 2) (σ i) : ℂ) :=
          Finset.sum_congr rfl fun i _ => by rw [hnu i, hdeg i]
      _ = ∑ j, frobeniusSchurIndicatorRow ℂ (G := QuaternionGroup 2) j *
            (characterDegree ℂ (G := QuaternionGroup 2) j : ℂ) :=
          Fintype.sum_equiv σ _ _ fun _ => rfl
      _ = (Nat.card {g : QuaternionGroup 2 // g * g = 1} : ℂ) :=
          (card_squareRoot_one_eq_sum_frobeniusSchurIndicatorRow_mul_characterDegree ℂ
            (QuaternionGroup 2)).symm
      _ = ((2 : ℕ) : ℂ) := by rw [card_squareRoot_one_quaternionGroupTwo]
  norm_num at key

/-- **The Frobenius-Schur indicator is not a function of the character table.**  The character
tables of `D₄` and `Q₈` are identified by a relabelling of rows and columns, and no such
identification matches the indicators. -/
theorem exists_characterTable_eq_and_frobeniusSchurIndicatorRow_ne :
    ∃ σ : Fin (Nat.card (ConjClasses (DihedralGroup 4))) ≃
            Fin (Nat.card (ConjClasses (QuaternionGroup 2))),
      (∃ e : ConjClasses (DihedralGroup 4) ≃ ConjClasses (QuaternionGroup 2),
          characterTable ℂ (DihedralGroup 4) =
            (characterTable ℂ (QuaternionGroup 2)).submatrix σ e) ∧
        ∃ i, frobeniusSchurIndicatorRow ℂ (G := DihedralGroup 4) i ≠
          frobeniusSchurIndicatorRow ℂ (G := QuaternionGroup 2) (σ i) := by
  obtain ⟨σ, e, he, hT⟩ :=
    exists_equiv_characterTable_dihedralGroupFour_eq_characterTable_quaternionGroupTwo
  exact ⟨σ, ⟨e, hT⟩, exists_frobeniusSchurIndicatorRow_ne_of_characterTable_eq σ e he hT⟩

end TauCeti
