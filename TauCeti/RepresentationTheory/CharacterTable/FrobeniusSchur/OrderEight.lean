/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.Dixon.Rational.Dihedral.Four
public import TauCeti.RepresentationTheory.CharacterTable.Dixon.Rational.QuaternionEight
public import TauCeti.RepresentationTheory.CharacterTable.FrobeniusSchur.Dihedral
public import TauCeti.RepresentationTheory.CharacterTable.FrobeniusSchur.Quaternion
public import TauCeti.RepresentationTheory.CharacterTable.FrobeniusSchur.TotallyOrthogonal
public import TauCeti.RepresentationTheory.FDRep.FrobeniusSchur

/-!
# The Frobenius-Schur indicators of `D₄` and `Q₈`

The dihedral group `D₄ = DihedralGroup 4` and the quaternion group `Q₈ = QuaternionGroup 2` have
the same complex character table: four rows of degree `1` and one row of degree `2`, given by the
same integer matrix (`TauCeti.dihedralGroupFourCharacterTable` and
`TauCeti.quaternionGroupTwoCharacterTable`). The Frobenius-Schur indicator `ν₂(χ) = |G|⁻¹ ∑_g χ(g²)`
separates them, and the involution count `#{g : g² = x} = ∑_χ ν₂(χ) χ(x)` computes it.

* `D₄` has six solutions of `g² = 1`, the identity, the central rotation and the four reflections,
  and its degrees sum to `1 + 1 + 1 + 1 + 2 = 6`. So `D₄` is totally orthogonal: every row has
  indicator `1`, the degree-`2` row included (`6 = 1 + 1 + 1 + 1 + 2 · 1`).
* `Q₈` has only two solutions of `g² = 1`, namely `±1`, while each of the six elements of order
  four squares to `-1`. The two counts give `2 = ν₀ + ν₁ + ν₂ + ν₃ + 2ν₄` and
  `6 = ν₀ + ν₁ + ν₂ + ν₃ - 2ν₄`, where `ν₄` is the indicator of the degree-`2` row. Hence `ν₄ = -1`
  and the four linear rows have indicator `1`: the two-dimensional irreducible representation of
  `Q₈` is quaternionic.

The unweighted sums `∑_χ ν₂(χ)` are `5` for `D₄` and `3` for `Q₈`, against the degree-weighted
sums `6` and `2`. The categorical second Frobenius-Schur indicator of the two-dimensional
irreducible object of `FDRep ℂ G`, for the standard pivotal structure, is `1` for `D₄` and `-1` for
`Q₈`.

## Main statements

* `TauCeti.frobeniusSchurIndicatorRow_dihedralGroupFour_eq_one`: every row of the character table
  of `D₄` has indicator `1`.
* `TauCeti.frobeniusSchurIndicatorRow_quaternionGroupTwo`: a row of the character table of `Q₈` has
  indicator `1` if it has degree `1`, and `-1` otherwise.
* `TauCeti.sum_frobeniusSchurIndicatorRow_dihedralGroupFour` and
  `TauCeti.sum_frobeniusSchurIndicatorRow_quaternionGroupTwo`: the unweighted sums `5` and `3`.
* `TauCeti.frobeniusSchurIndicator_indFDRep_ofLinearCharacter_dihedralGroupFourRotationChar_two`
  and
  `TauCeti.frobeniusSchurIndicator_indFDRep_ofLinearCharacter_quaternionGroupTwoRotationChar_two`:
  the categorical indicators `1` and `-1` of the two-dimensional irreducible representations.

## References

* I. M. Isaacs, *Character Theory of Finite Groups* (1976), Chapter 4.
* J.-P. Serre, *Linear Representations of Finite Groups*, GTM 42 (1977), §13.2.
-/

public section

namespace TauCeti

open Matrix

/-! ### The dihedral group `D₄` -/

/-- `D₄` has five conjugacy classes. -/
private theorem card_conjClasses_dihedralGroupFour : Nat.card (ConjClasses (DihedralGroup 4)) = 5 :=
  (dihedralClassData 4).numClasses_eq_card_conjClasses.symm.trans numClasses_dihedralClassData_four

/-- `D₄` has six solutions of `g² = 1`: the identity, the central rotation `r 2` and the four
reflections. -/
theorem card_squareRoot_one_dihedralGroupFour :
    Nat.card {g : DihedralGroup 4 // g * g = 1} = 6 := by
  rw [Nat.card_eq_fintype_card]
  decide

/-- The character degrees of `D₄` sum to `6`. -/
@[simp]
theorem sum_characterDegree_dihedralGroupFour :
    ∑ i, characterDegree ℂ (G := DihedralGroup 4) i = 6 := by
  rw [isIntegerCharacterTableSpec_dihedralGroupFour.sum_characterDegree_eq_sum_degree]
  simp only [dihedralGroupFourCharacterDegrees_apply]
  decide

/-- **`D₄` is totally orthogonal**: every row of the character table of `DihedralGroup 4`, the
two-dimensional one included, has Frobenius-Schur indicator `1`. -/
@[simp]
theorem frobeniusSchurIndicatorRow_dihedralGroupFour_eq_one
    (i : Fin (Nat.card (ConjClasses (DihedralGroup 4)))) :
    frobeniusSchurIndicatorRow ℂ i = 1 :=
  (card_squareRoot_one_eq_sum_characterDegree_iff ℂ (DihedralGroup 4)).mp
    (by rw [card_squareRoot_one_dihedralGroupFour, sum_characterDegree_dihedralGroupFour]) i

/-- **The unweighted sum of the row indicators of `D₄` is `5`**, the number of rows, whereas the
degree-weighted sum is `#{g : g² = 1} = 6`. -/
theorem sum_frobeniusSchurIndicatorRow_dihedralGroupFour :
    ∑ i : Fin (Nat.card (ConjClasses (DihedralGroup 4))), frobeniusSchurIndicatorRow ℂ i = 5 := by
  simp only [frobeniusSchurIndicatorRow_dihedralGroupFour_eq_one, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, card_conjClasses_dihedralGroupFour, nsmul_eq_mul, mul_one]
  norm_num

/-- **The categorical second Frobenius-Schur indicator of the two-dimensional irreducible
representation of `D₄` is `1`**, as is its character-theoretic indicator. -/
theorem frobeniusSchurIndicator_indFDRep_ofLinearCharacter_dihedralGroupFourRotationChar_two :
    TauCeti.frobeniusSchurIndicator ℂ
      (indFDRep (FDRep.ofLinearCharacter dihedralGroupFourRotationChar)) 2 = 1 := by
  rw [FDRep.frobeniusSchurIndicator_fdRep_two]
  simp

/-! ### The quaternion group `Q₈` -/

/-- `Q₈` has two solutions of `g² = 1`, namely `1` and `-1 = a 2`. -/
theorem card_squareRoot_one_quaternionGroupTwo :
    Nat.card {g : QuaternionGroup 2 // g * g = 1} = 2 := by
  rw [Nat.card_eq_fintype_card]
  decide

/-- The six elements of order four of `Q₈` all square to `-1 = a 2`. -/
private theorem card_squareRoot_a_two_quaternionGroupTwo :
    Nat.card {g : QuaternionGroup 2 // g * g = QuaternionGroup.a 2} = 6 := by
  rw [Nat.card_eq_fintype_card]
  decide

/-- The rows of the character table of `Q₈`, numbered along the displayed integer table
`TauCeti.quaternionGroupTwoCharacterTable`, have indicators `1, 1, 1, 1, -1` and degrees
`1, 1, 1, 1, 2`. -/
private theorem exists_equiv_frobeniusSchurIndicatorRow_quaternionGroupTwo :
    ∃ τ : Fin 5 ≃ Fin (Nat.card (ConjClasses (QuaternionGroup 2))), ∀ j,
      frobeniusSchurIndicatorRow ℂ (τ j) = ![1, 1, 1, 1, -1] j ∧
        characterDegree ℂ (τ j) = ![1, 1, 1, 1, 2] j := by
  obtain ⟨σ, hσ⟩ := characterTable_unique_rows isCharacterTableSpec_quaternionGroupTwo
  -- Number the rows of the character table along the displayed integer table.
  let τ : Fin 5 ≃ Fin (Nat.card (ConjClasses (QuaternionGroup 2))) :=
    (finCongr (numClasses_quaternionClassData_two.symm.trans
      (quaternionClassData 2).numClasses_eq_card_conjClasses)).trans σ
  have hval (j : Fin 5) (g : QuaternionGroup 2) :
      characterTable ℂ (QuaternionGroup 2) (τ j) (ConjClasses.mk g) =
        (quaternionGroupTwoCharacterTable (Fin.cast numClasses_quaternionClassData_two.symm j)
          ((quaternionClassData 2).index g) : ℂ) := by
    have h := congrFun (congrFun hσ (finCongr (numClasses_quaternionClassData_two.symm.trans
      (quaternionClassData 2).numClasses_eq_card_conjClasses) j)) (ConjClasses.mk g)
    simp only [submatrix_apply, id_eq, ClassData.complexTableOfInteger_apply] at h
    simpa [τ] using h.symm
  have hone : ∀ j : Fin 5,
      quaternionGroupTwoCharacterTable (Fin.cast numClasses_quaternionClassData_two.symm j)
        ((quaternionClassData 2).index 1) = ![1, 1, 1, 1, 2] j := by
    simp only [quaternionGroupTwoCharacterTable_apply]
    decide
  have hneg : ∀ j : Fin 5,
      quaternionGroupTwoCharacterTable (Fin.cast numClasses_quaternionClassData_two.symm j)
        ((quaternionClassData 2).index (QuaternionGroup.a 2)) = ![1, 1, 1, 1, -2] j := by
    simp only [quaternionGroupTwoCharacterTable_apply]
    decide
  -- The involution count at `1` and at `-1 = a 2`, read along `τ`.
  have h1 := card_squareRoot_eq_sum_frobeniusSchurIndicatorRow_mul_characterTable ℂ
    (QuaternionGroup 2) 1
  have h2 := card_squareRoot_eq_sum_frobeniusSchurIndicatorRow_mul_characterTable ℂ
    (QuaternionGroup 2) (QuaternionGroup.a 2)
  rw [card_squareRoot_one_quaternionGroupTwo, ← τ.sum_comp] at h1
  rw [card_squareRoot_a_two_quaternionGroupTwo, ← τ.sum_comp] at h2
  simp only [hval, hone, hneg, Fin.sum_univ_five] at h1 h2
  norm_num at h1 h2
  -- Subtracting the two counts isolates the degree-`2` row; the linear rows then sum to `4`, and
  -- each of their indicators is at most `1`.
  have h4 : frobeniusSchurIndicatorRow ℂ (τ 4) = -1 := by linear_combination (h2 - h1) / 4
  have hsum : frobeniusSchurIndicatorRow ℂ (τ 0) + frobeniusSchurIndicatorRow ℂ (τ 1) +
      frobeniusSchurIndicatorRow ℂ (τ 2) + frobeniusSchurIndicatorRow ℂ (τ 3) = 4 := by
    linear_combination -h1 - 2 * h4
  have hlin : frobeniusSchurIndicatorRow ℂ (τ 0) = 1 ∧ frobeniusSchurIndicatorRow ℂ (τ 1) = 1 ∧
      frobeniusSchurIndicatorRow ℂ (τ 2) = 1 ∧ frobeniusSchurIndicatorRow ℂ (τ 3) = 1 := by
    rcases frobeniusSchurIndicatorRow_eq_one_or_eq_zero_or_eq_neg_one ℂ (τ 0) with h0 | h0 | h0 <;>
    rcases frobeniusSchurIndicatorRow_eq_one_or_eq_zero_or_eq_neg_one ℂ (τ 1) with h1 | h1 | h1 <;>
    rcases frobeniusSchurIndicatorRow_eq_one_or_eq_zero_or_eq_neg_one ℂ (τ 2) with h2 | h2 | h2 <;>
    rcases frobeniusSchurIndicatorRow_eq_one_or_eq_zero_or_eq_neg_one ℂ (τ 3) with h3 | h3 | h3 <;>
    rw [h0, h1, h2, h3] at hsum <;> norm_num at hsum
    exact ⟨h0, h1, h2, h3⟩
  -- The degree of the row `τ j` is the identity-column entry of the displayed table.
  have hdeg (j : Fin 5) : (characterDegree ℂ (τ j) : ℂ) = ((![1, 1, 1, 1, 2] j : ℤ) : ℂ) := by
    rw [← characterTable_one, hval, hone]
  refine ⟨τ, fun j => ?_⟩
  have hd := hdeg j
  fin_cases j
  · exact ⟨by simpa using hlin.1, by simpa using hd⟩
  · exact ⟨by simpa using hlin.2.1, by simpa using hd⟩
  · exact ⟨by simpa using hlin.2.2.1, by simpa using hd⟩
  · exact ⟨by simpa using hlin.2.2.2, by simpa using hd⟩
  · refine ⟨by simpa using h4, ?_⟩
    have h2 : characterDegree ℂ (τ 4) = 2 :=
      Nat.cast_injective (R := ℂ) (by simpa using hd)
    simpa using h2

/-- **The Frobenius-Schur indicators of `Q₈`**: a row of the character table of
`QuaternionGroup 2` has indicator `1` if it has degree `1`, and `-1` if it is the row of degree `2`.
So the four linear characters are orthogonal and the two-dimensional irreducible representation is
quaternionic, although `Q₈` has the same character table as the totally orthogonal group `D₄`. -/
theorem frobeniusSchurIndicatorRow_quaternionGroupTwo
    (i : Fin (Nat.card (ConjClasses (QuaternionGroup 2)))) :
    frobeniusSchurIndicatorRow ℂ i = if characterDegree ℂ i = 1 then 1 else -1 := by
  obtain ⟨τ, hτ⟩ := exists_equiv_frobeniusSchurIndicatorRow_quaternionGroupTwo
  obtain ⟨j, rfl⟩ := τ.surjective i
  rw [(hτ j).1, (hτ j).2]
  fin_cases j <;> simp

/-- **The unweighted sum of the row indicators of `Q₈` is `3`**, four orthogonal rows minus one
quaternionic row, whereas the degree-weighted sum is `#{g : g² = 1} = 2`. -/
theorem sum_frobeniusSchurIndicatorRow_quaternionGroupTwo :
    ∑ i : Fin (Nat.card (ConjClasses (QuaternionGroup 2))), frobeniusSchurIndicatorRow ℂ i = 3 := by
  obtain ⟨τ, hτ⟩ := exists_equiv_frobeniusSchurIndicatorRow_quaternionGroupTwo
  rw [← τ.sum_comp]
  simp only [fun j => (hτ j).1, Fin.sum_univ_five]
  norm_num

/-- **The categorical second Frobenius-Schur indicator of the two-dimensional irreducible
representation of `Q₈` is `-1`**, as is its character-theoretic indicator. -/
theorem frobeniusSchurIndicator_indFDRep_ofLinearCharacter_quaternionGroupTwoRotationChar_two :
    TauCeti.frobeniusSchurIndicator ℂ
      (indFDRep (FDRep.ofLinearCharacter quaternionGroupTwoRotationChar)) 2 = -1 := by
  rw [FDRep.frobeniusSchurIndicator_fdRep_two]
  simp

end TauCeti
