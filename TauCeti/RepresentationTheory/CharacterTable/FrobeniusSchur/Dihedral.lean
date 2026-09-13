/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.FrobeniusSchur.Induced
public import TauCeti.RepresentationTheory.Induction.Mackey.Dihedral

/-!
# The Frobenius-Schur indicator of the two-dimensional representation of `D₄`

The rotation subgroup of `D₄` has index two and is inverted by every reflection, so the
Frobenius-Schur indicator of the representation induced from a linear character of it is given by
`TauCeti.frobeniusSchurIndicator_indFDRep_ofLinearCharacter_of_conj_eq_inv`.  This file evaluates
that formula at the faithful character sending `r 1` to `i`, whose induced representation is the
two-dimensional irreducible of `D₄` by
`TauCeti.simple_indFDRep_ofLinearCharacter_dihedralGroupFourRotationChar`: the indicator is `1`.

## Main statements

* `TauCeti.frobeniusSchurIndicator_indFDRep_ofLinearCharacter_dihedralGroupFourRotationChar`:
  **the representation of `D₄` induced from the faithful character of its rotation subgroup has
  Frobenius-Schur indicator `1`.**  It is a `simp` lemma, stated on the underlying representation
  so that it matches after `TauCeti.FDRep.frobeniusSchurIndicator_def` has fired.

## References

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
theorem frobeniusSchurIndicator_indFDRep_ofLinearCharacter_dihedralGroupFourRotationChar :
    Representation.frobeniusSchurIndicator
      (indFDRep (FDRep.ofLinearCharacter dihedralGroupFourRotationChar)).ρ = 1 := by
  have hcard : (Nat.card (DihedralGroup 4) : ℂ) = 8 := by
    rw [Nat.card_eq_fintype_card, DihedralGroup.card]; norm_num
  have hψ : dihedralGroupFourRotationChar ^ 2 ≠ 1 := fun hcontra => by
    have h := congrFun (congrArg DFunLike.coe hcontra)
      (⟨DihedralGroup.r 1, r_mem_dihedralRotations 1⟩ : dihedralRotations 4)
    rw [MonoidHom.one_apply] at h
    have hI : Complex.I ^ 2 = 1 := by
      rw [← coe_dihedralGroupFourRotationChar_r_one, ← Units.val_pow_eq_pow_val]
      simpa using congrArg (fun u : ℂˣ => (u : ℂ)) h
    rw [Complex.I_sq] at hI
    exact absurd hI (by norm_num)
  have hsq : (DihedralGroup.sr (0 : ZMod 4)) ^ 2 = 1 := by
    rw [pow_two, DihedralGroup.sr_mul_sr]; simp
  -- The reflection `sr 0` squares to the identity, so the value the general formula returns is
  -- that of the character at `1`.
  have hone : (⟨(DihedralGroup.sr (0 : ZMod 4)) ^ 2,
      Subgroup.sq_mem_of_index_two (index_dihedralRotations 4) _⟩ : dihedralRotations 4) = 1 :=
    Subtype.ext hsq
  rw [← FDRep.frobeniusSchurIndicator_def,
    frobeniusSchurIndicator_indFDRep_ofLinearCharacter_of_conj_eq_inv
      (s := DihedralGroup.sr (0 : ZMod 4)) (index_dihedralRotations 4)
      (fun _ hx => conj_eq_inv_of_notMem_dihedralRotations (sr_notMem_dihedralRotations 0) hx)
      (isUnit_iff_ne_zero.mpr (by rw [hcard]; norm_num)) hψ]
  rw [hone, map_one, Units.val_one]

end TauCeti
