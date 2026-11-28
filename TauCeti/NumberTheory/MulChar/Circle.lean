/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Circle
public import Mathlib.NumberTheory.MulChar.Basic
import Mathlib.Analysis.Normed.Ring.Finite

/-!
# Circle-valued multiplicative characters

For a commutative monoid with finite unit group, complex multiplicative characters are
equivalent to circle-valued homomorphisms on units. The equivalence refines Mathlib's
`MulChar.mulEquivToUnitHom` using `IsOfFinOrder.norm_eq_one` for the character values.
-/

public noncomputable section

namespace MulChar

variable {R : Type*} [CommMonoid R] [Finite Rˣ]

/-- Restrict a complex multiplicative character to the finite unit group and take its values
in the circle. The inverse extends the character by zero off the units. -/
def mulEquivToCircle : MulChar R ℂ ≃* (Rˣ →* Circle) :=
  let restrict (χ : MulChar R ℂ) : Rˣ →* Circle :=
    { toFun := fun u ↦ ⟨χ u, mem_sphere_zero_iff_norm.2
        (((χ : R →* ℂ).comp (Units.coeHom R)).isOfFinOrder
          (isOfFinOrder_of_finite u)).norm_eq_one⟩
      map_one' := Circle.ext (map_one χ)
      map_mul' := fun u v ↦ Circle.ext (map_mul χ (u : R) (v : R)) }
  let extend (χ : Rˣ →* Circle) : MulChar R ℂ :=
    ofUnitHom (Circle.toUnits.comp χ)
  have hextend (χ : Rˣ →* Circle) (u : Rˣ) : extend χ u = (χ u : ℂ) :=
    ofUnitHom_coe (Circle.toUnits.comp χ) u
  { toFun := restrict
    invFun := extend
    left_inv := fun χ ↦ MulChar.ext fun u ↦ hextend (restrict χ) u
    right_inv := fun χ ↦ MonoidHom.ext fun u ↦ Circle.ext (hextend χ u)
    map_mul' := fun χ ψ ↦ MonoidHom.ext fun u ↦ Circle.ext (MulChar.mul_apply χ ψ u) }

/-- On a unit, the circle-valued character has the original complex value. -/
@[simp] theorem coe_mulEquivToCircle_apply (χ : MulChar R ℂ) (u : Rˣ) :
    (mulEquivToCircle χ u : ℂ) = χ u := (rfl)

/-- The extension by zero agrees with the original circle-valued homomorphism on units. -/
@[simp] theorem mulEquivToCircle_symm_apply_coe (χ : Rˣ →* Circle) (u : Rˣ) :
    mulEquivToCircle.symm χ u = (χ u : ℂ) := by
  rw [← coe_mulEquivToCircle_apply, MulEquiv.apply_symm_apply]

end MulChar
