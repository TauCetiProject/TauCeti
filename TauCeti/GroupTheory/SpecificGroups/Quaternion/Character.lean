/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RootsOfUnity.Complex
public import TauCeti.GroupTheory.SpecificGroups.Cyclic.Character
public import TauCeti.GroupTheory.SpecificGroups.Quaternion.Basic

/-!
# Characters of the rotation subgroup of a quaternion group

The rotation subgroup of `QuaternionGroup n` is cyclic of order `2 * n`, its coordinate
`TauCeti.quaternionRotationsMulEquiv` identifying it with `Multiplicative (ZMod (2 * n))`.  A
`(2 * n)`-th root of unity therefore defines a linear character by sending `a i` to the
corresponding power: this file specializes `TauCeti.zmodCoordChar` to that coordinate.

## Main definitions

* `TauCeti.quaternionRotationChar`: the character sending `a i` to `ζ ^ i`.
* `TauCeti.quaternionGroupTwoRotationChar`: the faithful character of the rotations of `Q₈`
  sending `a 1` to `i`.

## Main results

* `TauCeti.quaternionRotationChar_injective`: a primitive root defines a faithful character.
-/

public section

namespace TauCeti

variable {n : ℕ} {M : Type*} [CommMonoid M] {ζ : M} [NeZero n]

/-- The character of the quaternion rotation subgroup attached to a `(2 * n)`-th root of unity
`ζ`, sending `a i` to `ζ ^ i`.  It is `TauCeti.zmodCoordChar` for the cyclic coordinate
`TauCeti.quaternionRotationsMulEquiv`. -/
def quaternionRotationChar (hζ : ζ ^ (2 * n) = 1) : quaternionRotations n →* M :=
  zmodCoordChar (quaternionRotationsMulEquiv n) hζ

@[simp]
theorem quaternionRotationChar_apply (hζ : ζ ^ (2 * n) = 1) (x : quaternionRotations n) :
    quaternionRotationChar hζ x =
      ζ ^ (Multiplicative.toAdd (quaternionRotationsMulEquiv n x)).val :=
  zmodCoordChar_apply _ hζ x

/-- The character sends `a i` to `ζ ^ i`. -/
theorem quaternionRotationChar_a (hζ : ζ ^ (2 * n) = 1) (i : ZMod (2 * n)) :
    quaternionRotationChar hζ ⟨QuaternionGroup.a i, a_mem_quaternionRotations i⟩ = ζ ^ i.val := by
  rw [quaternionRotationChar_apply, quaternionRotationsMulEquiv_a, toAdd_ofAdd]

/-- A primitive `(2 * n)`-th root of unity defines a faithful character of the quaternion
rotation subgroup: this is `TauCeti.zmodCoordChar_injective` for the rotation coordinate. -/
theorem quaternionRotationChar_injective (h : IsPrimitiveRoot ζ (2 * n)) :
    Function.Injective (quaternionRotationChar h.pow_eq_one) :=
  zmodCoordChar_injective _ h

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

end QuaternionTwo

end TauCeti
