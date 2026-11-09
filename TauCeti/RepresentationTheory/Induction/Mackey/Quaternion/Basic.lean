/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import TauCeti.GroupTheory.SpecificGroups.Quaternion.Character
public import TauCeti.RepresentationTheory.Induction.LinearCharacter
public import TauCeti.RepresentationTheory.Induction.Mackey.LinearCharacter

/-!
# Inducing a linear character from a quaternion rotation subgroup

The cyclic subgroup formed by the elements `a i` has index two in `QuaternionGroup n`, and every
element outside it acts by inversion.  The Mackey criterion for an inverted subgroup of index two,
`TauCeti.simple_indFDRep_ofLinearCharacter_iff_of_conj_eq_inv`, therefore says that a linear
character induces irreducibly exactly when it is not its own inverse.  The induced representation
is always two-dimensional.

For `QuaternionGroup 2`, the character sending `a 1` to `i` meets this condition and gives its
two-dimensional irreducible complex representation.

## Main results

* `TauCeti.simple_indFDRep_ofLinearCharacter_quaternionRotations_iff`: the Mackey criterion for
  quaternion rotations.
* `TauCeti.simple_indFDRep_ofLinearCharacter_quaternionGroupTwoRotationChar`: its induction is
  irreducible.
* `TauCeti.finrank_indFDRep_ofLinearCharacter_quaternionGroupTwoRotationChar`: its induction has
  dimension two.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, Chapter 7.4.
-/

public section

open CategoryTheory

namespace TauCeti

universe u

section General

variable {k : Type u} [Field k] {n : ℕ}

/-- A representation induced from a linear character of the quaternion rotations is
two-dimensional. -/
theorem finrank_indFDRep_ofLinearCharacter_quaternionRotations
    (ψ : quaternionRotations n →* kˣ) :
    Module.finrank k (indFDRep (FDRep.ofLinearCharacter ψ)) = 2 := by
  rw [finrank_indFDRep_ofLinearCharacter, index_quaternionRotations]

end General

section Criterion

variable {k : Type} [Field k] {n : ℕ} [NeZero n] [IsAlgClosed k] [CharZero k]

/-- Induction from the quaternion rotation subgroup is irreducible exactly when some value of the
linear character is not a square root of one.  The rotation subgroup has index two and is inverted
by every `xa i`, so this is
`TauCeti.simple_indFDRep_ofLinearCharacter_iff_of_conj_eq_inv`. -/
theorem simple_indFDRep_ofLinearCharacter_quaternionRotations_iff
    (ψ : quaternionRotations n →* kˣ) :
    Simple (indFDRep (FDRep.ofLinearCharacter ψ)) ↔ ∃ x, ψ x ^ 2 ≠ 1 :=
  simple_indFDRep_ofLinearCharacter_iff_of_conj_eq_inv (index_quaternionRotations n)
    (xa_notMem_quaternionRotations 0)
    (fun _ hx => conj_eq_inv_of_notMem_quaternionRotations
      (xa_notMem_quaternionRotations 0) hx) ψ

end Criterion

section QuaternionTwo

/-- The character of the rotations of `Q₈` sending `a 1` to `i` induces irreducibly. -/
theorem simple_indFDRep_ofLinearCharacter_quaternionGroupTwoRotationChar :
    Simple (indFDRep (FDRep.ofLinearCharacter quaternionGroupTwoRotationChar)) := by
  refine (simple_indFDRep_ofLinearCharacter_quaternionRotations_iff
    quaternionGroupTwoRotationChar).mpr
    ⟨⟨QuaternionGroup.a 1, a_mem_quaternionRotations (n := 2) 1⟩, fun hc => ?_⟩
  have h : Complex.I ^ 2 = 1 := by
    rw [← coe_quaternionGroupTwoRotationChar_a_one, ← Units.val_pow_eq_pow_val, hc, Units.val_one]
  rw [Complex.I_sq] at h
  norm_num at h

/-- The irreducible representation of `Q₈` induced from its faithful rotation character has
dimension two. -/
theorem finrank_indFDRep_ofLinearCharacter_quaternionGroupTwoRotationChar :
    Module.finrank ℂ
      (indFDRep (FDRep.ofLinearCharacter quaternionGroupTwoRotationChar)) = 2 :=
  finrank_indFDRep_ofLinearCharacter_quaternionRotations quaternionGroupTwoRotationChar

end QuaternionTwo

end TauCeti
