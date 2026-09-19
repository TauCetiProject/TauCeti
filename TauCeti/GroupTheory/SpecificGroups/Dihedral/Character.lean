/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.Cyclic.Character
public import TauCeti.GroupTheory.SpecificGroups.Dihedral.Basic

/-!
# Characters of the rotation subgroup of a dihedral group

The rotation subgroup `TauCeti.dihedralRotations n` of `DihedralGroup n` is cyclic, its coordinate
`TauCeti.dihedralRotationsMulEquiv` identifying it with `Multiplicative (ZMod n)`. A character of
it is therefore named by a single `n`-th root of unity `ζ`: this file specializes
`MulEquiv.zmodCoordChar` to that coordinate to get `TauCeti.dihedralRotationChar`, the character
sending the rotation `r i` to `ζ ^ i`, and reads off that a *primitive* root of unity gives a
faithful character.

This is separated from `TauCeti.GroupTheory.SpecificGroups.Dihedral.Basic` because
`MulEquiv.zmodCoordChar` rests on `AddChar.zmodChar`, which lives in the number-theoretic part of
Mathlib that the rotation subgroup itself does not need.

## Main definitions

* `TauCeti.dihedralRotationChar`: the character of the rotation subgroup sending `r i` to `ζ ^ i`,
  for `ζ` an `n`-th root of unity.

## Main results

* `TauCeti.dihedralRotationChar_injective`: the character attached to a *primitive* `n`-th root of
  unity is faithful.
-/

public section

namespace TauCeti

variable {n : ℕ} {M : Type*} [CommMonoid M] {ζ : M} [NeZero n]

/-- **The character of the rotation subgroup attached to an `n`-th root of unity** `ζ`: the
rotation `r i` is sent to `ζ ^ i`, the exponent being the canonical representative of `i` in
`ZMod n`. It is `MulEquiv.zmodCoordChar` for the cyclic coordinate
`TauCeti.dihedralRotationsMulEquiv`. -/
def dihedralRotationChar (hζ : ζ ^ n = 1) : dihedralRotations n →* M :=
  (dihedralRotationsMulEquiv n).zmodCoordChar hζ

@[simp]
theorem dihedralRotationChar_apply (hζ : ζ ^ n = 1) (x : dihedralRotations n) :
    dihedralRotationChar hζ x = ζ ^ (Multiplicative.toAdd (dihedralRotationsMulEquiv n x)).val :=
  (dihedralRotationsMulEquiv n).zmodCoordChar_apply hζ x

/-- The character sends the rotation `r i` to `ζ ^ i`. -/
theorem dihedralRotationChar_r (hζ : ζ ^ n = 1) (i : ZMod n) :
    dihedralRotationChar hζ ⟨DihedralGroup.r i, r_mem_dihedralRotations i⟩ = ζ ^ i.val := by
  rw [dihedralRotationChar_apply, dihedralRotationsMulEquiv_r, toAdd_ofAdd]

/-- **The character attached to a *primitive* `n`-th root of unity is faithful**: this is
`MulEquiv.zmodCoordChar_injective` for the rotation coordinate. -/
theorem dihedralRotationChar_injective (h : IsPrimitiveRoot ζ n) :
    Function.Injective (dihedralRotationChar h.pow_eq_one) :=
  (dihedralRotationsMulEquiv n).zmodCoordChar_injective h

end TauCeti
