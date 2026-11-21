/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import TauCeti.NumberTheory.LegendreSymbol.AddCharacter

/-!
# The standard pairing on `ℤ/n`, and the characters of a finite ring

Mathlib's `AddChar.zmodHom` indexes the circle-valued characters of `ZMod n` by `ZMod n` itself,
`a ↦ (b ↦ e(a b / n))` with `e(x) = exp(2 π i x)`. This file writes it multiplicatively, as a
pairing `TauCeti.zmodPairing n` on `Multiplicative (ZMod n)` that is a monoid homomorphism in each
variable, the form in which it can be composed with group homomorphisms into
`Multiplicative (ZMod n)`, such as discrete logarithms.

Over a finite commutative ring `R`, a primitive additive character `ψ` parametrizes all
characters with values in `ℂ` (or any `RCLike` field) in the same way: `a ↦ ψ.mulShift a` is an
isomorphism of `R` onto its character group. It is injective by Mathlib's
`AddChar.to_mulShift_inj_of_isPrimitive`, and bijective because there are at most `#R` characters
(`AddChar.card_addChar_le`). The primitive characters are exactly the shifts by units. Over a
finite field, where every nontrivial character is primitive, every additive character is thus a
shift of any fixed nontrivial one.

## Main definitions

* `TauCeti.zmodPairing n`: the pairing `(a, b) ↦ e(a b / n)` on `Multiplicative (ZMod n)`.
* `AddChar.IsPrimitive.mulShiftAddEquiv`: for a primitive character `ψ` of a finite ring `R`, the
  isomorphism `a ↦ ψ.mulShift a` of `R` onto its character group.

## Main results

* `TauCeti.zmodPairing_apply`: `zmodPairing n a b = ZMod.toCircle (a b)`.
* `TauCeti.zmodPairing_comm`: the pairing is symmetric.
* `TauCeti.zmodPairing_eq_one_iff`: the pairing is nondegenerate: `e(a / n) = 1` only for `a = 0`.
* `AddChar.IsPrimitive.bijective_mulShift`: the shifts of a primitive character of a finite ring
  are all the characters, each exactly once.
* `AddChar.IsPrimitive.existsUnique_mulShift_eq`: every character is the shift of a given
  primitive character by exactly one element.
* `AddChar.IsPrimitive.existsUnique_units_mulShift_eq`: every primitive character is the shift of
  a given primitive character by a unique unit.
-/

public section

open Multiplicative AddChar

namespace TauCeti

variable (n : ℕ) [NeZero n]

/-- **The standard pairing on `ℤ/n`**, `(a, b) ↦ e(a b / n)`: Mathlib's `AddChar.zmodHom` written
multiplicatively, as a monoid homomorphism in each variable. -/
noncomputable def zmodPairing :
    Multiplicative (ZMod n) →* Multiplicative (ZMod n) →* Circle :=
  toMonoidHomMulEquiv.toMonoidHom.comp (zmodHom (n := n)).toMonoidHom

/-- The standard pairing on `ℤ/n` evaluates to `e(a b / n)`, that is,
`zmodPairing n a b = ZMod.toCircle (a b)`. -/
theorem zmodPairing_apply (a b : Multiplicative (ZMod n)) :
    zmodPairing n a b = ZMod.toCircle (a.toAdd * b.toAdd) := by
  -- `AddChar.zmod n a` is defined as `b ↦ ZMod.toCircle (a * b)`. A tactic proof, unlike a term
  -- `rfl`, does not require the body of `zmodPairing` to be exposed.
  rfl

/-- The standard pairing on `ℤ/n` is symmetric. -/
theorem zmodPairing_comm (a b : Multiplicative (ZMod n)) :
    zmodPairing n a b = zmodPairing n b a := by
  rw [zmodPairing_apply, zmodPairing_apply, mul_comm]

/-- **The standard pairing on `ℤ/n` is nondegenerate**: pairing with the generator `1` is
trivial only at the identity. -/
@[simp]
theorem zmodPairing_eq_one_iff (a : Multiplicative (ZMod n)) :
    zmodPairing n a (ofAdd 1) = 1 ↔ a = 1 := by
  rw [zmodPairing_apply, toAdd_ofAdd, mul_one, ← map_zero_eq_one (ZMod.toCircle (N := n)),
    (ZMod.injective_toCircle (N := n)).eq_iff, toAdd_eq_zero]

end TauCeti

namespace AddChar

variable {R R' : Type*} [CommRing R] [Finite R] [RCLike R'] {ψ : AddChar R R'}

/-- The shifts of a primitive additive character of a finite ring are all its characters, each
exactly once: `a ↦ ψ.mulShift a` is a bijection. -/
theorem IsPrimitive.bijective_mulShift (hψ : ψ.IsPrimitive) : Function.Bijective ψ.mulShift := by
  have := Fintype.ofFinite R
  have hinj := to_mulShift_inj_of_isPrimitive hψ
  exact (Fintype.bijective_iff_injective_and_card _).2
    ⟨hinj, (Fintype.card_le_of_injective _ hinj).antisymm (card_addChar_le R R')⟩

/-- A primitive additive character `ψ` of a finite ring `R` identifies `R` with its group of
characters, through `a ↦ ψ.mulShift a`. -/
noncomputable def IsPrimitive.mulShiftAddEquiv (hψ : ψ.IsPrimitive) : R ≃+ AddChar R R' :=
  AddEquiv.ofBijective
    (AddMonoidHom.mk' ψ.mulShift fun a b ↦ by ext x; simp [add_mul, map_add_eq_mul])
    hψ.bijective_mulShift

/-- The isomorphism `IsPrimitive.mulShiftAddEquiv` sends `a` to the shift `ψ.mulShift a`. -/
@[simp]
theorem IsPrimitive.mulShiftAddEquiv_apply (hψ : ψ.IsPrimitive) (a : R) :
    hψ.mulShiftAddEquiv a = ψ.mulShift a := by
  rfl

/-- The inverse of `IsPrimitive.mulShiftAddEquiv` reads off the shift parameter. -/
@[simp]
theorem IsPrimitive.mulShiftAddEquiv_symm_mulShift (hψ : ψ.IsPrimitive) (a : R) :
    hψ.mulShiftAddEquiv.symm (ψ.mulShift a) = a := by
  rw [← hψ.mulShiftAddEquiv_apply, AddEquiv.symm_apply_apply]

/-- Shifting by the parameter that `IsPrimitive.mulShiftAddEquiv` reads off a character recovers
that character. -/
@[simp]
theorem IsPrimitive.mulShift_mulShiftAddEquiv_symm (hψ : ψ.IsPrimitive) (φ : AddChar R R') :
    ψ.mulShift (hψ.mulShiftAddEquiv.symm φ) = φ := by
  rw [← hψ.mulShiftAddEquiv_apply, AddEquiv.apply_symm_apply]

/-- Every additive character of a finite ring is the shift of a given primitive character by
exactly one element. -/
theorem IsPrimitive.existsUnique_mulShift_eq (hψ : ψ.IsPrimitive) (φ : AddChar R R') :
    ∃! a : R, ψ.mulShift a = φ :=
  hψ.bijective_mulShift.existsUnique φ

/-- Every primitive additive character of a finite ring is the shift of a given primitive
character by a unique unit. -/
theorem IsPrimitive.existsUnique_units_mulShift_eq (hψ : ψ.IsPrimitive) {φ : AddChar R R'}
    (hφ : φ.IsPrimitive) : ∃! u : Rˣ, ψ.mulShift u = φ := by
  obtain ⟨a, rfl⟩ := hψ.bijective_mulShift.2 φ
  have ha : IsUnit a := hψ.isPrimitive_mulShift_iff.1 hφ
  exact ⟨ha.unit, rfl, fun u hu ↦ Units.ext (hψ.bijective_mulShift.1 hu)⟩

end AddChar
