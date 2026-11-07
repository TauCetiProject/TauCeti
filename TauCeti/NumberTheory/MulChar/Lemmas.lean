/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.MulChar.Lemmas

/-!
# The zero extension of an inverse unit character

`MulChar.ofUnitHom` extends a unit homomorphism `χ : Rˣ →* R'ˣ` by zero to a multiplicative
character. It carries the inverse of `χ` to the inverse character, and for values in an
`RCLike` field, where the values of `χ` on a finite unit group have norm one and so their
inverses are their conjugates, to the conjugate character.

## Main results

* `MulChar.ofUnitHom_inv`: `ofUnitHom χ⁻¹ = (ofUnitHom χ)⁻¹`.
* `MulChar.ofUnitHom_inv_eq_star`: for `RCLike` values, `ofUnitHom χ⁻¹ = star (ofUnitHom χ)`.
-/

public section

namespace MulChar

/-- The zero extension of the inverse of a unit homomorphism is the inverse character. -/
theorem ofUnitHom_inv {R R' : Type*} [CommMonoid R] [CommMonoidWithZero R'] (χ : Rˣ →* R'ˣ) :
    ofUnitHom χ⁻¹ = (ofUnitHom χ)⁻¹ :=
  map_inv mulEquivToUnitHom.symm χ

/-- For a unit homomorphism `χ` with values in an `RCLike` field `K` on a ring with finitely
many units, the zero extension of `χ⁻¹` is the conjugate of the zero extension of `χ`. -/
theorem ofUnitHom_inv_eq_star {R K : Type*} [CommRing R] [Finite Rˣ] [RCLike K]
    (χ : Rˣ →* Kˣ) : ofUnitHom χ⁻¹ = star (ofUnitHom χ) := by
  ext a
  simpa using RCLike.inv_eq_conj
    (((Units.coeHom K).comp χ).isOfFinOrder (isOfFinOrder_of_finite a)).norm_eq_one

end MulChar
