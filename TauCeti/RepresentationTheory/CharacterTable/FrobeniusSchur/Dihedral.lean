/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.Dixon.Rational.Dihedral.Four
public import TauCeti.RepresentationTheory.CharacterTable.FrobeniusSchur.Induced
public import TauCeti.RepresentationTheory.CharacterTable.FrobeniusSchur.TotallyOrthogonal
public import TauCeti.RepresentationTheory.FDRep.FrobeniusSchur
public import TauCeti.RepresentationTheory.Induction.Mackey.Dihedral

/-!
# The Frobenius-Schur indicators of `D₄`

The rotation subgroup of `D₄` has index two and is inverted by every reflection, so the
Frobenius-Schur indicator of the representation induced from a linear character of it is given by
`TauCeti.frobeniusSchurIndicator_indFDRep_ofLinearCharacter_eq_apply_sq_of_conj_eq_inv`.  This
file evaluates that formula at the faithful character sending `r 1` to `i`, whose induced
representation is the two-dimensional irreducible of `D₄` by
`TauCeti.simple_indFDRep_ofLinearCharacter_dihedralGroupFourRotationChar`: the indicator is `1`.

The same conclusion holds for every row of the character table. `D₄` has six solutions of
`g² = 1`, the identity, the central rotation and the four reflections, and its character degrees
sum to `1 + 1 + 1 + 1 + 2 = 6`. By the involution count `#{g : g² = 1} = ∑_χ ν₂(χ) χ(1)`, `D₄` is
totally orthogonal: every row has indicator `1`. The unweighted sum `∑_χ ν₂(χ)` is therefore `5`,
against the degree-weighted sum `6`.

## Main statements

* `TauCeti.frobeniusSchurIndicator_indFDRep_ofLinearCharacter_dihedralGroupFourRotationChar_eq_one`:
  **the representation of `D₄` induced from the faithful character of its rotation subgroup has
  Frobenius-Schur indicator `1`.**  It is a `simp` lemma, stated on the underlying representation
  so that it matches after `TauCeti.FDRep.frobeniusSchurIndicator_def` has fired.
* `TauCeti.frobeniusSchurIndicatorRow_dihedralGroupFour_eq_one`: every row of the character table
  of `D₄` has indicator `1`.
* `TauCeti.sum_frobeniusSchurIndicatorRow_dihedralGroupFour`: the unweighted sum of the row
  indicators of `D₄` is `5`.
* `TauCeti.frobeniusSchurIndicator_indFDRep_ofLinearCharacter_dihedralGroupFourRotationChar_two`:
  the categorical second indicator of the two-dimensional irreducible object of `FDRep ℂ D₄`, for
  the standard pivotal structure, is `1`.

## References

* I. M. Isaacs, *Character Theory of Finite Groups* (1976), Chapter 4.
* J.-P. Serre, *Linear Representations of Finite Groups*, GTM 42 (1977), §13.2.
-/

public section

namespace TauCeti

/-- **The representation of `D₄` over `ℂ` induced from the faithful linear character of the
rotation subgroup sending `r 1` to `i` has Frobenius-Schur indicator `1`.**  That representation
is the two-dimensional irreducible of `D₄`, by
`TauCeti.simple_indFDRep_ofLinearCharacter_dihedralGroupFourRotationChar` and
`TauCeti.finrank_indFDRep_ofLinearCharacter_dihedralGroupFourRotationChar`.  The value is stated
on the module spine, which is where the `simp` lemma `TauCeti.FDRep.frobeniusSchurIndicator_def`
sends the `FDRep`-level indicator, so `simp` normalizes either spelling to `1`. -/
@[simp]
theorem frobeniusSchurIndicator_indFDRep_ofLinearCharacter_dihedralGroupFourRotationChar_eq_one :
    Representation.frobeniusSchurIndicator
      (indFDRep (FDRep.ofLinearCharacter dihedralGroupFourRotationChar)).ρ = 1 := by
  have hcard : (Nat.card (DihedralGroup 4) : ℂ) = 8 := by
    rw [Nat.card_eq_fintype_card, DihedralGroup.card]; norm_num
  -- Irreducibility of the induced representation is exactly the failure of some value of the
  -- character to square to `1`, so the witness comes from the Mackey criterion already proved.
  have hψ : dihedralGroupFourRotationChar ^ 2 ≠ 1 := by
    obtain ⟨x, hx⟩ := (simple_indFDRep_ofLinearCharacter_dihedralRotations_iff
      dihedralGroupFourRotationChar).mp
      simple_indFDRep_ofLinearCharacter_dihedralGroupFourRotationChar
    exact fun hcontra => hx (by
      simpa using congrFun (congrArg DFunLike.coe hcontra) x)
  have hsq : (DihedralGroup.sr (0 : ZMod 4)) ^ 2 = 1 := by
    rw [pow_two, DihedralGroup.sr_mul_sr]; simp
  -- The reflection `sr 0` squares to the identity, so the value the general formula returns is
  -- that of the character at `1`.
  have hone : (⟨(DihedralGroup.sr (0 : ZMod 4)) ^ 2,
      Subgroup.sq_mem_of_index_two (index_dihedralRotations 4) _⟩ : dihedralRotations 4) = 1 :=
    Subtype.ext hsq
  rw [← FDRep.frobeniusSchurIndicator_def,
    frobeniusSchurIndicator_indFDRep_ofLinearCharacter_eq_apply_sq_of_conj_eq_inv
      (s := DihedralGroup.sr (0 : ZMod 4)) (index_dihedralRotations 4)
      (fun _ hx => conj_eq_inv_of_notMem_dihedralRotations (sr_notMem_dihedralRotations 0) hx)
      (isUnit_iff_ne_zero.mpr (by rw [hcard]; norm_num)) hψ]
  rw [hone, map_one, Units.val_one]

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
@[simp]
theorem frobeniusSchurIndicator_indFDRep_ofLinearCharacter_dihedralGroupFourRotationChar_two :
    TauCeti.frobeniusSchurIndicator ℂ
      (indFDRep (FDRep.ofLinearCharacter dihedralGroupFourRotationChar)) 2 = 1 := by
  rw [FDRep.frobeniusSchurIndicator_fdRep_two]
  simp

end TauCeti
