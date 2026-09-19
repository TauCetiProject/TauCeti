/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter

/-!
# Characters of a cyclic group read off a `ZMod` coordinate

A group `H` presented as cyclic of order `m` by a coordinate `e : H ≃* Multiplicative (ZMod m)`
has its characters named by the `m`-th roots of unity: the character attached to `ζ` sends the
element with coordinate `i` to `ζ ^ i`. This file reads Mathlib's `AddChar.zmodChar` through such
a coordinate to get `TauCeti.zmodCoordChar`, and shows that a *primitive* root of unity gives a
faithful character.

The coordinate is data, not merely the existence of `IsCyclic H`: the character depends on which
generator `e` names, a different coordinate permuting the characters among themselves. Concrete
cyclic subgroups come with a preferred coordinate -- the rotation subgroup of a dihedral or a
generalized quaternion group, for instance -- and the characters used there are the
specializations of this one.

## Main definitions

* `TauCeti.zmodCoordChar`: the character sending the element with coordinate `i` to `ζ ^ i`, for
  `ζ` an `m`-th root of unity.

## Main results

* `TauCeti.zmodCoordChar_injective`: the character attached to a *primitive* `m`-th root of unity
  is faithful.
-/

public section

namespace TauCeti

variable {H M : Type*} [Group H] [CommMonoid M] {m : ℕ} [NeZero m] {ζ : M}

/-- **The character of a cyclic group attached to an `m`-th root of unity** `ζ`, read off a
coordinate `e : H ≃* Multiplicative (ZMod m)`: the element with coordinate `i` is sent to `ζ ^ i`,
the exponent being the canonical representative of `i` in `ZMod m`. It is Mathlib's
`AddChar.zmodChar` composed with `e`. -/
def zmodCoordChar (e : H ≃* Multiplicative (ZMod m)) (hζ : ζ ^ m = 1) : H →* M :=
  (AddChar.toMonoidHomEquiv (AddChar.zmodChar m hζ)).comp e.toMonoidHom

@[simp]
theorem zmodCoordChar_apply (e : H ≃* Multiplicative (ZMod m)) (hζ : ζ ^ m = 1) (x : H) :
    zmodCoordChar e hζ x = ζ ^ (Multiplicative.toAdd (e x)).val := by
  simp [zmodCoordChar, AddChar.zmodChar_apply]

/-- **The character attached to a *primitive* `m`-th root of unity is faithful**: the additive
character `AddChar.zmodChar` it is read off is then primitive, so it takes the value `1` only at
the identity. -/
theorem zmodCoordChar_injective (e : H ≃* Multiplicative (ZMod m)) (h : IsPrimitiveRoot ζ m) :
    Function.Injective (zmodCoordChar e h.pow_eq_one) := by
  refine (injective_iff_map_eq_one _).mpr fun x hx => ?_
  rw [zmodCoordChar_apply] at hx
  have hzero := ((AddChar.zmodChar_primitive_of_primitive_root m h).zmod_char_eq_one_iff m
    (Multiplicative.toAdd (e x))).mp (by rwa [AddChar.zmodChar_apply])
  exact e.map_eq_one_iff.mp (toAdd_eq_zero.mp hzero)

end TauCeti
