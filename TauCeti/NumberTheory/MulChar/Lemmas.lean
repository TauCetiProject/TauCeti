/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.MulChar.Lemmas

/-!
# The zero extension of a unit character

`MulChar.ofUnitHom` extends a unit homomorphism `χ : Rˣ →* R'ˣ` by zero to a multiplicative
character. It carries the inverse of `χ` to the inverse character, and for values in an
`RCLike` field, where the values of `χ` on a finite unit group have norm one and so their
inverses are their conjugates, to the conjugate character. It also carries integer powers to
integer powers, and pulling homomorphisms back along a surjection onto their domain before
extending by zero is injective.

## Main results

* `MulChar.ofUnitHom_inv`: `ofUnitHom χ⁻¹ = (ofUnitHom χ)⁻¹`.
* `MulChar.ofUnitHom_inv_eq_star`: for `RCLike` values, `ofUnitHom χ⁻¹ = star (ofUnitHom χ)`.
* `MulChar.ofUnitHom_zpow`: `ofUnitHom (χ ^ n) = ofUnitHom χ ^ n`.
* `MulChar.ofUnitHom_comp_injective`: for a surjection `f : Rˣ →* G`, the map
  `χ ↦ ofUnitHom (χ.comp f)` is injective.
-/

public section

namespace MulChar

/-- The zero extension of the inverse of a unit homomorphism is the inverse character. -/
theorem ofUnitHom_inv {R R' : Type*} [CommMonoid R] [CommMonoidWithZero R'] (χ : Rˣ →* R'ˣ) :
    ofUnitHom χ⁻¹ = (ofUnitHom χ)⁻¹ := by
  simpa [ofUnitHom_eq] using map_inv (mulEquivToUnitHom (R := R) (R' := R')).symm χ

/-- The zero extension of an integer power of a unit homomorphism is that power of the zero
extension. -/
theorem ofUnitHom_zpow {R R' : Type*} [CommMonoid R] [CommMonoidWithZero R'] (χ : Rˣ →* R'ˣ)
    (n : ℤ) : ofUnitHom (χ ^ n) = ofUnitHom χ ^ n := by
  simpa [ofUnitHom_eq] using map_zpow (mulEquivToUnitHom (R := R) (R' := R')).symm χ n

/-- Pulling unit homomorphisms back along a surjection onto `G` and extending by zero gives
different characters for different homomorphisms on `G`. -/
theorem ofUnitHom_comp_injective {R R' G : Type*} [CommMonoid R] [CommMonoidWithZero R']
    [MulOneClass G] {f : Rˣ →* G} (hf : Function.Surjective f) :
    Function.Injective fun χ : G →* R'ˣ ↦ ofUnitHom (χ.comp f) := fun a b hab ↦
  (MonoidHom.cancel_right hf).mp <| equivToUnitHom.symm.injective <| by
    simpa only [ofUnitHom_eq] using hab

/-- For a unit homomorphism `χ` with values in an `RCLike` field `K` on a ring with finitely
many units, the zero extension of `χ⁻¹` is the conjugate of the zero extension of `χ`. -/
theorem ofUnitHom_inv_eq_star {R K : Type*} [CommRing R] [Finite Rˣ] [RCLike K]
    (χ : Rˣ →* Kˣ) : ofUnitHom χ⁻¹ = star (ofUnitHom χ) := by
  ext a
  simpa using RCLike.inv_eq_conj
    (((Units.coeHom K).comp χ).isOfFinOrder (isOfFinOrder_of_finite a)).norm_eq_one

end MulChar
