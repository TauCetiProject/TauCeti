/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

/-!
# The standard pairing on `ℤ/n`

Mathlib's `AddChar.zmodHom` indexes the circle-valued characters of `ZMod n` by `ZMod n` itself,
`a ↦ (b ↦ e(a b / n))` with `e(x) = exp(2 π i x)`. This file writes it multiplicatively, as a
pairing `TauCeti.zmodPairing n` on `Multiplicative (ZMod n)` that is a monoid homomorphism in each
variable, the form in which it can be composed with group homomorphisms into
`Multiplicative (ZMod n)`, such as discrete logarithms.

## Main definitions

* `TauCeti.zmodPairing n`: the pairing `(a, b) ↦ e(a b / n)` on `Multiplicative (ZMod n)`.

## Main results

* `TauCeti.zmodPairing_apply`: `zmodPairing n a b = ZMod.toCircle (a b)`.
* `TauCeti.zmodPairing_comm`: the pairing is symmetric.
* `TauCeti.zmodPairing_eq_one_iff`: the pairing is nondegenerate: `e(a / n) = 1` only for `a = 0`.
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
