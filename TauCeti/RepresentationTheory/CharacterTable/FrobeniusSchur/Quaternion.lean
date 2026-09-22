/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.FrobeniusSchur.Induced
public import TauCeti.RepresentationTheory.Induction.Mackey.Quaternion

/-!
# The Frobenius-Schur indicator of the two-dimensional representation of `Q₈`

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

## Main statement

* The main theorem says that **the representation of `Q₈` induced from its faithful rotation
  character has Frobenius-Schur indicator `-1`.**

## References

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

end TauCeti
