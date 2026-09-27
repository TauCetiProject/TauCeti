/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.HeckeCharacter.FiniteOrder
public import TauCeti.NumberTheory.NumberField.Global.RayClass.Character.Weight

/-!
# Ideal weights of finite-order Hecke characters

A finite-order Hecke character factors through the ray class group of some modulus.  Once such a
modulus is fixed, injectivity of pullback from the ray class group makes the representing ray class
character unique.  Its zero extension on integral ideals is therefore a well-defined unitary ideal
weight.

The resulting weight depends on the chosen modulus at its bad primes.  If the modulus is enlarged,
the new weight is the restriction of the old one away from the finite primes in the larger modulus.
Thus the values on ideals prime to the larger modulus are independent of the chosen ray-class
presentation, while the conventional zero values record the chosen Euler factors.

## Main declarations

* `TauCeti.GlobalNumberFields.HeckeCharacter.rayClassCharacterAt` is the unique ray class
  character representing a Hecke character at a specified modulus.
* `TauCeti.GlobalNumberFields.HeckeCharacter.toUnitaryIdealWeightAt` is its unitary ideal weight.
* `TauCeti.GlobalNumberFields.HeckeCharacter.toUnitaryIdealWeightAt_of_dvd` describes change of
  modulus as restriction away from the primes of the larger modulus.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §6.
-/

public section
noncomputable section

open IsDedekindDomain NumberField
open scoped NumberField

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

namespace HeckeCharacter

variable {𝔪 𝔫 : Modulus K}

/-- The unique ray class character of `𝔪` whose pullback is `χ`, given that `χ` comes from
`RayClassGroup 𝔪`. -/
noncomputable def rayClassCharacterAt (χ : HeckeCharacter K) (𝔪 : Modulus K)
    (hχ : χ ∈ (ofRayClassCharacter 𝔪).range) : RayClassCharacter 𝔪 :=
  hχ.choose

/-- Pulling the representing ray class character back to the idele class group recovers the
original Hecke character. -/
@[simp]
theorem ofRayClassCharacter_rayClassCharacterAt (χ : HeckeCharacter K) (𝔪 : Modulus K)
    (hχ : χ ∈ (ofRayClassCharacter 𝔪).range) :
    ofRayClassCharacter 𝔪 (rayClassCharacterAt χ 𝔪 hχ) = χ :=
  hχ.choose_spec

/-- The representing ray class character is characterized by its pullback to the idele class
group. -/
theorem rayClassCharacterAt_eq_iff {χ : HeckeCharacter K}
    (hχ : χ ∈ (ofRayClassCharacter 𝔪).range) {η : RayClassCharacter 𝔪} :
    rayClassCharacterAt χ 𝔪 hχ = η ↔ ofRayClassCharacter 𝔪 η = χ := by
  constructor
  · rintro rfl
    exact ofRayClassCharacter_rayClassCharacterAt χ 𝔪 hχ
  · intro hη
    exact (ofRayClassCharacter_injective 𝔪) <|
      (ofRayClassCharacter_rayClassCharacterAt χ 𝔪 hχ).trans hη.symm

/-- Extracting the representative of a Hecke character already presented by a ray class character
returns that character. -/
@[simp]
theorem rayClassCharacterAt_ofRayClassCharacter (η : RayClassCharacter 𝔪) :
    rayClassCharacterAt (ofRayClassCharacter 𝔪 η) 𝔪 ⟨η, rfl⟩ = η :=
  (rayClassCharacterAt_eq_iff ⟨η, rfl⟩).mpr rfl

/-- On increasing the modulus, the representative of a Hecke character is obtained by inducing
its representative at the smaller modulus. -/
theorem rayClassCharacterAt_of_dvd (h : 𝔪 ∣ 𝔫) (χ : HeckeCharacter K)
    (hχ : χ ∈ (ofRayClassCharacter 𝔪).range) :
    rayClassCharacterAt χ 𝔫 (range_ofRayClassCharacter_le h hχ) =
      RayClassCharacter.induced h (rayClassCharacterAt χ 𝔪 hχ) := by
  rw [rayClassCharacterAt_eq_iff, ofRayClassCharacter_induced,
    ofRayClassCharacter_rayClassCharacterAt]

/-- At a fixed modulus, the representative of a product is the product of the representatives. -/
theorem rayClassCharacterAt_mul {χ ψ : HeckeCharacter K}
    (hχ : χ ∈ (ofRayClassCharacter 𝔪).range)
    (hψ : ψ ∈ (ofRayClassCharacter 𝔪).range) :
    rayClassCharacterAt (χ * ψ) 𝔪 (mul_mem hχ hψ) =
      rayClassCharacterAt χ 𝔪 hχ * rayClassCharacterAt ψ 𝔪 hψ := by
  rw [rayClassCharacterAt_eq_iff, map_mul,
    ofRayClassCharacter_rayClassCharacterAt, ofRayClassCharacter_rayClassCharacterAt]

/-- The unitary ideal weight of a Hecke character at a ray modulus through which it factors.

The bad primes are the finite primes dividing `𝔪`; at every ideal prime to `𝔪`, this is the value
of the unique ray class character representing `χ`. -/
noncomputable def toUnitaryIdealWeightAt (χ : HeckeCharacter K) (𝔪 : Modulus K)
    (hχ : χ ∈ (ofRayClassCharacter 𝔪).range) : TauCeti.UnitaryIdealWeight K :=
  (rayClassCharacterAt χ 𝔪 hχ).toUnitaryIdealWeight

/-- The underlying multiplicative ideal weight is the zero extension of the representing ray
class character. -/
@[simp]
theorem val_toUnitaryIdealWeightAt (χ : HeckeCharacter K) (𝔪 : Modulus K)
    (hχ : χ ∈ (ofRayClassCharacter 𝔪).range) :
    (toUnitaryIdealWeightAt χ 𝔪 hχ).1 =
      (rayClassCharacterAt χ 𝔪 hχ).toMultiplicativeIdealWeight := by
  simp [toUnitaryIdealWeightAt]

/-- For a Hecke character explicitly pulled back from `η`, the associated weight is the unitary
zero extension of `η`. -/
@[simp]
theorem toUnitaryIdealWeightAt_ofRayClassCharacter (η : RayClassCharacter 𝔪) :
    toUnitaryIdealWeightAt (ofRayClassCharacter 𝔪 η) 𝔪 ⟨η, rfl⟩ =
      η.toUnitaryIdealWeight := by
  simp [toUnitaryIdealWeightAt]

/-- At a fixed ray modulus, pointwise multiplication of Hecke characters becomes pointwise
multiplication of their unitary ideal weights. -/
theorem toUnitaryIdealWeightAt_mul {χ ψ : HeckeCharacter K}
    (hχ : χ ∈ (ofRayClassCharacter 𝔪).range)
    (hψ : ψ ∈ (ofRayClassCharacter 𝔪).range) :
    toUnitaryIdealWeightAt (χ * ψ) 𝔪 (mul_mem hχ hψ) =
      toUnitaryIdealWeightAt χ 𝔪 hχ * toUnitaryIdealWeightAt ψ 𝔪 hψ := by
  simp [toUnitaryIdealWeightAt, rayClassCharacterAt_mul hχ hψ,
    RayClassCharacter.toUnitaryIdealWeight_mul]

/-- **Change of ray modulus for ideal weights.** If `𝔪 ∣ 𝔫`, the weight obtained from the
representation at `𝔫` is the weight at `𝔪`, restricted away from the finite primes of `𝔫`.
Consequently both weights agree on every ideal prime to `𝔫`. -/
theorem toUnitaryIdealWeightAt_of_dvd (h : 𝔪 ∣ 𝔫) (χ : HeckeCharacter K)
    (hχ : χ ∈ (ofRayClassCharacter 𝔪).range) :
    toUnitaryIdealWeightAt χ 𝔫 (range_ofRayClassCharacter_le h hχ) =
      (toUnitaryIdealWeightAt χ 𝔪 hχ).restrict 𝔫.support 𝔫.support.finite_toSet := by
  apply Subtype.ext
  ext I
  by_cases hI : Ideal.IsPrimeTo I 𝔫.support
  · have hI𝔪 : Ideal.IsPrimeTo I 𝔪.support := hI.mono (Modulus.support_mono h)
    rw [TauCeti.UnitaryIdealWeight.val_restrict,
      TauCeti.MultiplicativeIdealWeight.restrict_apply]
    simp only [hI, ite_true]
    rw [val_toUnitaryIdealWeightAt, val_toUnitaryIdealWeightAt,
      RayClassCharacter.toMultiplicativeIdealWeight_apply_of_isPrimeTo _ hI,
      RayClassCharacter.toMultiplicativeIdealWeight_apply_of_isPrimeTo _ hI𝔪,
      rayClassCharacterAt_of_dvd (𝔪 := 𝔪) (𝔫 := 𝔫) h χ hχ,
      RayClassCharacter.onIdeals_induced]
    congr 2
    exact Subtype.ext (coe_integralIdealsPrimeToInclusion h _)
  · rw [TauCeti.UnitaryIdealWeight.val_restrict,
      TauCeti.MultiplicativeIdealWeight.restrict_apply]
    simp only [hI, ite_false]
    rw [val_toUnitaryIdealWeightAt,
      RayClassCharacter.toMultiplicativeIdealWeight_apply_of_not_isPrimeTo _ hI]

end HeckeCharacter

end TauCeti.GlobalNumberFields
