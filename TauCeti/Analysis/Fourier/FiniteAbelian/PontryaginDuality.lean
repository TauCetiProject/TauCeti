/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

/-!
# The standard pairing on `ℤ/n` and the shifts of a primitive character

Mathlib's `AddChar.zmodHom` indexes the circle-valued characters of `ZMod n` by `ZMod n` itself,
`a ↦ (b ↦ e(a b / n))` with `e(x) = exp(2 π i x)`. This file writes it multiplicatively, as a
pairing `TauCeti.zmodPairing n` on `Multiplicative (ZMod n)` that is a monoid homomorphism in each
variable, the form in which it can be composed with group homomorphisms into
`Multiplicative (ZMod n)`, such as discrete logarithms.

A primitive complex additive character `ψ` of a finite commutative ring `R` indexes all the
complex additive characters of `R` in the same way: the shifts `a ↦ ψ.mulShift a` are injective
(Mathlib's `AddChar.to_mulShift_inj_of_isPrimitive`), and `R` has exactly `#R` complex additive
characters (Mathlib's `AddChar.card_eq`), so the shifts are an isomorphism. For `R = ZMod n` and
`ψ = ZMod.stdAddChar` this agrees pointwise with Mathlib's `AddChar.zmodAddEquiv`;
over a finite field it says that every additive character is a shift of a fixed nontrivial one.

## Main definitions

* `TauCeti.zmodPairing n`: the pairing `(a, b) ↦ e(a b / n)` on `Multiplicative (ZMod n)`.
* `AddChar.IsPrimitive.mulShiftAddEquiv`: for a primitive complex additive character `ψ` of a
  finite commutative ring `R`, the isomorphism `a ↦ ψ.mulShift a` from `R` onto `AddChar R ℂ`.

## Main results

* `TauCeti.zmodPairing_apply`: `zmodPairing n a b = ZMod.toCircle (a b)`.
* `TauCeti.zmodPairing_comm`: the pairing is symmetric.
* `TauCeti.zmodPairing_eq_one_iff`: the pairing is nondegenerate: `e(a / n) = 1` only for `a = 0`.
* `AddChar.IsPrimitive.existsUnique_mulShift_eq`: every complex additive character of a finite
  commutative ring is the shift of a primitive one by exactly one element.
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

namespace AddChar.IsPrimitive

variable {R : Type*} [CommRing R] [Finite R] {ψ : AddChar R ℂ}

/-- For a primitive complex additive character `ψ` of a finite commutative ring `R`, the shifts
`a ↦ ψ.mulShift a` form an isomorphism from the additive group of `R` onto the group of complex
additive characters of `R`. -/
noncomputable def mulShiftAddEquiv (hψ : ψ.IsPrimitive) : R ≃+ AddChar R ℂ :=
  AddEquiv.ofBijective
    ({ toFun := ψ.mulShift
       map_zero' := mulShift_zero ψ
       map_add' := fun a b ↦ (mulShift_mul ψ a b).symm } : R →+ AddChar R ℂ) <| by
    have := Fintype.ofFinite R
    rw [Fintype.bijective_iff_injective_and_card, card_eq]
    exact ⟨to_mulShift_inj_of_isPrimitive hψ, rfl⟩

@[simp]
theorem mulShiftAddEquiv_apply (hψ : ψ.IsPrimitive) (a : R) :
    hψ.mulShiftAddEquiv a = ψ.mulShift a := by
  -- A tactic proof, unlike a term `rfl`, does not require the body of `mulShiftAddEquiv` to be
  -- exposed.
  rfl

/-- Every complex additive character of a finite commutative ring is the shift of a primitive
one by exactly one element. -/
theorem existsUnique_mulShift_eq (hψ : ψ.IsPrimitive) (φ : AddChar R ℂ) :
    ∃! a : R, ψ.mulShift a = φ := by
  simpa using hψ.mulShiftAddEquiv.bijective.existsUnique φ

end AddChar.IsPrimitive
