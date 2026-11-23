/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.Dixon.Rational.QuaternionEight
public import TauCeti.RepresentationTheory.CharacterTable.FrobeniusSchur.Induced
public import TauCeti.RepresentationTheory.CharacterTable.FrobeniusSchur.InvolutionCount
public import TauCeti.RepresentationTheory.FDRep.FrobeniusSchur
public import TauCeti.RepresentationTheory.Induction.Mackey.Quaternion.Basic

/-!
# The Frobenius-Schur indicators of `Q₈`

The cyclic subgroup formed by the elements `a i` has index two in `QuaternionGroup 2`.  Every
element outside it acts by inversion, and the square of `xa 0` is the central rotation `a 2`.
Consequently
`TauCeti.frobeniusSchurIndicator_indFDRep_ofLinearCharacter_eq_apply_sq_of_conj_eq_inv`
reduces the Frobenius-Schur indicator of the induced faithful character to its value at `a 2`.
That value is `i² = -1`.

The induced representation is the two-dimensional irreducible of `Q₈`, by
`TauCeti.simple_indFDRep_ofLinearCharacter_quaternionGroupTwoRotationChar` and
`TauCeti.finrank_indFDRep_ofLinearCharacter_quaternionGroupTwoRotationChar`.  Thus this calculation
identifies it as quaternionic; the existence of its invariant nondegenerate alternating form then
follows from `TauCeti.Representation.frobeniusSchurIndicator_eq_neg_one_iff`.

`Q₈` has the same complex character table as `D₄`, the displayed integer table
`TauCeti.quaternionGroupTwoCharacterTable`, with four rows of degree `1` and one of degree `2`.
Averaging each row over the squares, `ν₂(χ) = |G|⁻¹ ∑_g χ(g²)`, gives indicator `1` on the four
linear rows and `-1` on the row of degree `2`. So the unweighted sum `∑_χ ν₂(χ)` is `3`, against
the degree-weighted sum `#{g : g² = 1} = 2`.

## Main statements

* The first theorem says that **the representation of `Q₈` induced from its faithful rotation
  character has Frobenius-Schur indicator `-1`.**
* `TauCeti.frobeniusSchurIndicatorRow_quaternionGroupTwo`: a row of the character table of `Q₈` has
  indicator `1` if it has degree `1`, and `-1` otherwise.
* `TauCeti.sum_frobeniusSchurIndicatorRow_quaternionGroupTwo`: the unweighted sum of the row
  indicators of `Q₈` is `3`.
* `TauCeti.frobeniusSchurIndicator_indFDRep_ofLinearCharacter_quaternionGroupTwoRotationChar_two`:
  the categorical second indicator of the two-dimensional irreducible object of `FDRep ℂ Q₈`, for
  the standard pivotal structure, is `-1`.

## References

* I. M. Isaacs, *Character Theory of Finite Groups* (1976), Chapter 4.
* J.-P. Serre, *Linear Representations of Finite Groups*, GTM 42 (1977), §13.2.
-/

public section

namespace TauCeti

/-- **The representation of `Q₈` over `ℂ` induced from the faithful linear character of the
rotation subgroup sending `a 1` to `i` has Frobenius-Schur indicator `-1`.**  This distinguishes it
from the two-dimensional irreducible of `D₄`, whose indicator is `1`; the two groups have the same
complex character table, but their two-dimensional representations have different real types. -/
@[simp]
theorem
    frobeniusSchurIndicator_indFDRep_ofLinearCharacter_quaternionGroupTwoRotationChar_eq_neg_one :
    Representation.frobeniusSchurIndicator
      (indFDRep (FDRep.ofLinearCharacter quaternionGroupTwoRotationChar)).ρ = -1 := by
  have hcard : (Nat.card (QuaternionGroup 2) : ℂ) = 8 := by
    rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
    norm_num
  have hψ : quaternionGroupTwoRotationChar ^ 2 ≠ 1 := by
    obtain ⟨x, hx⟩ := (simple_indFDRep_ofLinearCharacter_quaternionRotations_iff
      quaternionGroupTwoRotationChar).mp
      simple_indFDRep_ofLinearCharacter_quaternionGroupTwoRotationChar
    exact fun hcontra => hx (by
      simpa using congrFun (congrArg DFunLike.coe hcontra) x)
  have hsq :
      (⟨(QuaternionGroup.xa (0 : ZMod 4)) ^ 2,
          Subgroup.sq_mem_of_index_two (index_quaternionRotations 2) _⟩ :
        quaternionRotations 2) =
        ⟨QuaternionGroup.a (2 : ZMod 4), by simp⟩ :=
    Subtype.ext (QuaternionGroup.xa_sq 0)
  rw [← FDRep.frobeniusSchurIndicator_def,
    frobeniusSchurIndicator_indFDRep_ofLinearCharacter_eq_apply_sq_of_conj_eq_inv
      (s := QuaternionGroup.xa (0 : ZMod 4)) (index_quaternionRotations 2)
      (fun _ hx => conj_eq_inv_of_notMem_quaternionRotations
        (xa_notMem_quaternionRotations 0) hx)
      (isUnit_iff_ne_zero.mpr (by rw [hcard]; norm_num)) hψ]
  rw [hsq, coe_quaternionGroupTwoRotationChar_a]
  rw [ZMod.val_two_eq_two_mod]
  norm_num [Complex.I_sq]

/-- `Q₈` has two solutions of `g² = 1`, namely `1` and `-1 = a 2`. -/
theorem card_squareRoot_one_quaternionGroupTwo :
    Nat.card {g : QuaternionGroup 2 // g * g = 1} = 2 := by
  rw [Nat.card_eq_fintype_card]
  decide

/-- **The Frobenius-Schur indicators of `Q₈`**: a row of the character table of
`QuaternionGroup 2` has indicator `1` if it has degree `1`, and `-1` if it is the row of degree `2`.
So the four linear characters are orthogonal and the two-dimensional irreducible representation is
quaternionic, although `Q₈` has the same character table as the totally orthogonal group `D₄`. -/
theorem frobeniusSchurIndicatorRow_quaternionGroupTwo
    (i : Fin (Nat.card (ConjClasses (QuaternionGroup 2)))) :
    frobeniusSchurIndicatorRow ℂ i = if characterDegree ℂ i = 1 then 1 else -1 := by
  obtain ⟨τ, hval, hdeg⟩ :=
    isIntegerCharacterTableSpec_quaternionGroupTwo.exists_equiv_characterTable
  obtain ⟨j, rfl⟩ := τ.surjective i
  -- Each displayed integer row, summed over the squares, is `8` times its indicator.
  have hsum : ∀ j, ∑ g : QuaternionGroup 2,
      quaternionGroupTwoCharacterTable j ((quaternionClassData 2).index (g ^ 2)) =
        8 * if quaternionGroupTwoCharacterDegrees j = 1 then 1 else -1 := by
    simp only [quaternionGroupTwoCharacterTable_apply, quaternionGroupTwoCharacterDegrees_apply]
    decide
  have hcard : (Nat.card (QuaternionGroup 2) : ℂ) = 8 := by
    rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
    norm_num
  rw [frobeniusSchurIndicatorRow_eq_inv_mul_sum_characterTable, hcard, hdeg]
  simp only [hval, ← Int.cast_sum, hsum]
  split_ifs <;> norm_num

/-- **The unweighted sum of the row indicators of `Q₈` is `3`**, four orthogonal rows minus one
quaternionic row, whereas the degree-weighted sum is `#{g : g² = 1} = 2`. -/
theorem sum_frobeniusSchurIndicatorRow_quaternionGroupTwo :
    ∑ i : Fin (Nat.card (ConjClasses (QuaternionGroup 2))), frobeniusSchurIndicatorRow ℂ i = 3 := by
  obtain ⟨τ, -, hdeg⟩ :=
    isIntegerCharacterTableSpec_quaternionGroupTwo.exists_equiv_characterTable
  have hsum : ∑ j : QuaternionGroupTwoClassIndex,
      (if quaternionGroupTwoCharacterDegrees j = 1 then 1 else -1 : ℤ) = 3 := by
    simp only [quaternionGroupTwoCharacterDegrees_apply]
    decide
  rw [← τ.sum_comp]
  simp only [frobeniusSchurIndicatorRow_quaternionGroupTwo, hdeg]
  exact_mod_cast hsum

/-- **The categorical second Frobenius-Schur indicator of the two-dimensional irreducible
representation of `Q₈` is `-1`**, as is its character-theoretic indicator. -/
@[simp]
theorem frobeniusSchurIndicator_indFDRep_ofLinearCharacter_quaternionGroupTwoRotationChar_two :
    TauCeti.frobeniusSchurIndicator ℂ
      (indFDRep (FDRep.ofLinearCharacter quaternionGroupTwoRotationChar)) 2 = -1 := by
  rw [FDRep.frobeniusSchurIndicator_fdRep_two]
  simp

end TauCeti
