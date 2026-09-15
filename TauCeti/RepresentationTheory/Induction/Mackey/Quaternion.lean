/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import TauCeti.GroupTheory.SpecificGroups.Quaternion.Character
public import TauCeti.RepresentationTheory.Induction.LinearCharacter
public import TauCeti.RepresentationTheory.Induction.Mackey.LinearCharacter

/-!
# Inducing a linear character from a quaternion rotation subgroup

The cyclic subgroup formed by the elements `a i` has index two in `QuaternionGroup n`, and every
element outside it acts by inversion.  The Mackey criterion therefore says that a linear character
induces irreducibly exactly when it is not its own inverse.  The induced representation is always
two-dimensional.

For `QuaternionGroup 2`, the character sending `a 1` to `i` meets this condition and gives its
two-dimensional irreducible complex representation.

## Main results

* `TauCeti.simple_indFDRep_ofLinearCharacter_quaternionRotations_iff`: the Mackey criterion for
  quaternion rotations.
* `TauCeti.quaternionGroupTwoRotationChar`: the character of the rotations of `Q₈` sending `a 1`
  to `i`.
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
linear character is not a square root of one. -/
theorem simple_indFDRep_ofLinearCharacter_quaternionRotations_iff
    (ψ : quaternionRotations n →* kˣ) :
    Simple (indFDRep (FDRep.ofLinearCharacter ψ)) ↔ ∃ x, ψ x ^ 2 ≠ 1 := by
  rw [simple_indFDRep_ofLinearCharacter_iff]
  have key : ∀ {s : QuaternionGroup n}, s ∉ quaternionRotations n →
      ∀ x : quaternionRotations n, (ψ (MulAut.conjNormal s x) ≠ ψ x ↔ ψ x ^ 2 ≠ 1) := by
    intro s hs x
    rw [conjNormal_eq_inv_of_notMem_quaternionRotations hs, map_inv, ne_eq, ne_eq,
      inv_eq_iff_mul_eq_one, ← sq]
  refine ⟨fun h => ?_, fun ⟨x, hx⟩ s hs => ⟨x, (key hs x).mpr hx⟩⟩
  obtain ⟨x, hx⟩ := h (QuaternionGroup.xa 0) (xa_notMem_quaternionRotations 0)
  exact ⟨x, (key (xa_notMem_quaternionRotations 0) x).mp hx⟩

end Criterion

section QuaternionTwo

private theorem unitI_pow_four : (Units.mk0 Complex.I Complex.I_ne_zero) ^ 4 = 1 := by
  apply Units.ext
  simp

/-- The faithful character of the cyclic rotation subgroup of `Q₈` sending `a 1` to `i`. -/
noncomputable def quaternionGroupTwoRotationChar : quaternionRotations 2 →* ℂˣ :=
  quaternionRotationChar unitI_pow_four

/-- The value of `TauCeti.quaternionGroupTwoRotationChar` at `a i` is `i ^ i.val`. -/
@[simp]
theorem coe_quaternionGroupTwoRotationChar_a (i : ZMod 4) :
    (quaternionGroupTwoRotationChar
      ⟨QuaternionGroup.a i, by simp⟩ : ℂ) =
        Complex.I ^ i.val := by
  rw [quaternionGroupTwoRotationChar, quaternionRotationChar_a,
    Units.val_pow_eq_pow_val, Units.val_mk0]

/-- The character `TauCeti.quaternionGroupTwoRotationChar` sends `a 1` to `i`. -/
theorem coe_quaternionGroupTwoRotationChar_a_one :
    (quaternionGroupTwoRotationChar
      ⟨QuaternionGroup.a 1, a_mem_quaternionRotations (n := 2) 1⟩ : ℂ) = Complex.I := by
  rw [coe_quaternionGroupTwoRotationChar_a, ZMod.val_one_eq_one_mod]
  norm_num

/-- The character `TauCeti.quaternionGroupTwoRotationChar` is faithful. -/
theorem quaternionGroupTwoRotationChar_injective :
    Function.Injective quaternionGroupTwoRotationChar := by
  apply quaternionRotationChar_injective
  apply IsPrimitiveRoot.coe_units_iff.mp
  rw [Units.val_mk0]
  exact Complex.isPrimitiveRoot_I

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
