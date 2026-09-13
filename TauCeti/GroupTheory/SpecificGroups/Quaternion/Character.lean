/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
public import TauCeti.GroupTheory.SpecificGroups.Quaternion.Basic

/-!
# Characters of the rotation subgroup of a quaternion group

The rotation subgroup of `QuaternionGroup n` is cyclic of order `2 * n`.  A `(2 * n)`-th root
of unity therefore defines a linear character by sending `a i` to the corresponding power.

## Main definitions

* `TauCeti.quaternionRotationChar`: the character sending `a i` to `ζ ^ i`.

## Main results

* `TauCeti.quaternionRotationChar_injective`: a primitive root defines a faithful character.
-/

public section

namespace TauCeti

variable {n : ℕ} {M : Type*} [CommMonoid M] {ζ : M} [NeZero n]

/-- The character of the quaternion rotation subgroup attached to a `(2 * n)`-th root of unity
`ζ`, sending `a i` to `ζ ^ i`. -/
def quaternionRotationChar (hζ : ζ ^ (2 * n) = 1) : quaternionRotations n →* M :=
  (AddChar.toMonoidHomEquiv (AddChar.zmodChar (2 * n) hζ)).comp
    (quaternionRotationsMulEquiv n).toMonoidHom

@[simp]
theorem quaternionRotationChar_apply (hζ : ζ ^ (2 * n) = 1) (x : quaternionRotations n) :
    quaternionRotationChar hζ x =
      ζ ^ (Multiplicative.toAdd (quaternionRotationsMulEquiv n x)).val := by
  simp [quaternionRotationChar, AddChar.zmodChar_apply]

/-- The character sends `a i` to `ζ ^ i`. -/
theorem quaternionRotationChar_a (hζ : ζ ^ (2 * n) = 1) (i : ZMod (2 * n)) :
    quaternionRotationChar hζ ⟨QuaternionGroup.a i, a_mem_quaternionRotations i⟩ = ζ ^ i.val := by
  rw [quaternionRotationChar_apply, quaternionRotationsMulEquiv_a, toAdd_ofAdd]

/-- A primitive `(2 * n)`-th root of unity defines a faithful character of the quaternion
rotation subgroup. -/
theorem quaternionRotationChar_injective (h : IsPrimitiveRoot ζ (2 * n)) :
    Function.Injective (quaternionRotationChar h.pow_eq_one) := by
  refine (injective_iff_map_eq_one _).mpr fun x hx => ?_
  rw [quaternionRotationChar_apply] at hx
  have hzero := ((AddChar.zmodChar_primitive_of_primitive_root (2 * n) h).zmod_char_eq_one_iff
    (2 * n) (Multiplicative.toAdd (quaternionRotationsMulEquiv n x))).mp
      (by rwa [AddChar.zmodChar_apply])
  exact (quaternionRotationsMulEquiv n).map_eq_one_iff.mp (toAdd_eq_zero.mp hzero)

end TauCeti
