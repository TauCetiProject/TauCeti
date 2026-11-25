/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.RayClass.Character.Weight

/-!
# Conjugation of ray class weights

Inversion of a ray class character conjugates its ideal weight, including at ideals where the
weight is zero. This gives the coefficient symmetry underlying the reflection of its Hecke
L-function across the real axis.
-/

public section

open scoped NumberField ComplexConjugate

namespace TauCeti.GlobalNumberFields.RayClassCharacter

variable {K : Type*} [Field K] [NumberField K] {𝔪 : Modulus K}

/-- The ideal weight of the inverse character is the conjugate ideal weight. -/
@[simp]
theorem toUnitaryIdealWeight_inv (χ : RayClassCharacter 𝔪) :
    χ⁻¹.toUnitaryIdealWeight = χ.toUnitaryIdealWeight.conj := by
  apply Subtype.ext
  ext I
  rw [UnitaryIdealWeight.val_conj, val_toUnitaryIdealWeight, val_toUnitaryIdealWeight,
    MultiplicativeIdealWeight.conj_apply]
  by_cases hI : I.IsPrimeTo 𝔪.support
  · have hg : χ.toUnitaryIdealWeight.val.IsGood I := by
      simpa only [val_toUnitaryIdealWeight, MultiplicativeIdealWeight.IsGood,
        badPrimes_toMultiplicativeIdealWeight] using hI
    have hn := χ.toUnitaryIdealWeight.norm_eq_one hg
    rw [val_toUnitaryIdealWeight, toMultiplicativeIdealWeight_apply_of_isPrimeTo χ hI,
      onIdeals_apply] at hn
    simp only [toMultiplicativeIdealWeight_apply_of_isPrimeTo _ hI, onIdeals_apply,
      MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
    exact Complex.inv_eq_conj hn
  · simp [toMultiplicativeIdealWeight_apply_of_not_isPrimeTo _ hI]

end TauCeti.GlobalNumberFields.RayClassCharacter
