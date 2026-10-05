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
character. It carries the inverse of `χ` to the inverse character, and for complex values, where
the inverse of a character of finite order is its complex conjugate (`MulChar.star_eq_inv`), to
the conjugate character.

## Main results

* `MulChar.ofUnitHom_inv`: `ofUnitHom χ⁻¹ = (ofUnitHom χ)⁻¹`.
* `MulChar.ofUnitHom_inv_eq_star`: for complex values, `ofUnitHom χ⁻¹ = star (ofUnitHom χ)`.
-/

public section

namespace MulChar

/-- The zero extension of the inverse of a unit homomorphism is the inverse character. -/
theorem ofUnitHom_inv {R R' : Type*} [CommMonoid R] [CommMonoidWithZero R'] (χ : Rˣ →* R'ˣ) :
    ofUnitHom χ⁻¹ = (ofUnitHom χ)⁻¹ := by
  simpa [ofUnitHom_eq] using map_inv (mulEquivToUnitHom (R := R) (R' := R')).symm χ

/-- For a complex-valued unit homomorphism `χ` on a ring with finitely many units, the zero
extension of `χ⁻¹` is the complex conjugate of the zero extension of `χ`. -/
theorem ofUnitHom_inv_eq_star {R : Type*} [CommRing R] [Finite Rˣ] (χ : Rˣ →* ℂˣ) :
    ofUnitHom χ⁻¹ = star (ofUnitHom χ) := by
  rw [ofUnitHom_inv, star_eq_inv]

end MulChar
