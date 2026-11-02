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
a coordinate to get `MulEquiv.zmodCoordChar`, and shows that a *primitive* root of unity gives a
faithful character.

The coordinate is data, not merely the existence of `IsCyclic H`: the character depends on which
generator `e` names, a different coordinate permuting the characters among themselves. Concrete
cyclic subgroups come with a preferred coordinate -- the rotation subgroup of a dihedral or a
generalized quaternion group, for instance -- and the characters used there are the
specializations of this one.

## Main definitions

* `MulEquiv.zmodCoordChar`: the character sending the element with coordinate `i` to `ζ ^ i`, for
  `ζ` an `m`-th root of unity.

## Main results

* `AddChar.pow_char_eq_one`: every additive character on a ring of characteristic `p`, such as
  `ZMod p`, takes values in the `p`-th roots of unity.
* `MulEquiv.zmodCoordChar_injective`: the character attached to a *primitive* `m`-th root of unity
  is faithful.
-/

public section

/-- An additive character on a ring of characteristic `p` takes values in the `p`-th roots of
unity; for instance every additive character on `ZMod p` does. -/
theorem AddChar.pow_char_eq_one {R M : Type*} [NonAssocSemiring R] (p : ℕ) [CharP R p]
    [Monoid M] (ψ : AddChar R M) (x : R) : ψ x ^ p = 1 := by
  simp [← AddChar.map_nsmul_eq_pow]

namespace MulEquiv

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

/-- **The character attached to a *primitive* `m`-th root of unity is faithful**: it takes the
value `1` only at the identity. -/
theorem zmodCoordChar_injective (e : H ≃* Multiplicative (ZMod m)) (h : IsPrimitiveRoot ζ m) :
    Function.Injective (zmodCoordChar e h.pow_eq_one) := by
  refine (injective_iff_map_eq_one _).mpr fun x hx => ?_
  simpa [h.pow_eq_one_iff_dvd, ← ZMod.natCast_eq_zero_iff] using hx

end MulEquiv
