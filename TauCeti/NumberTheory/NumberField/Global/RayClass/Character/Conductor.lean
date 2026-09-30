/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.HeckeCharacter.Conductor
public import TauCeti.NumberTheory.NumberField.Global.RayClass.Character.Primitive

/-!
# The conductor of a ray class character

For a ray class character `η` of `𝔪`, the conductor of its Hecke character
(`HeckeCharacter.conductor`) is the least modulus from which `η` is induced.  It divides `𝔪`, it
does not change when `η` is induced to a larger modulus, and `η` is primitive exactly when its
conductor is `𝔪`.  Every ray class character is induced from a primitive character of its
conductor, `RayClassCharacter.primitiveCharacter`, and every finite-order Hecke character is the
pullback of a primitive ray class character of its conductor.  Primitive characters are the
normalization in which ray class L-functions are studied.

## Main definitions

* `TauCeti.GlobalNumberFields.RayClassCharacter.conductor`: the least modulus from which a ray
  class character is induced.
* `TauCeti.GlobalNumberFields.RayClassCharacter.primitiveCharacter`: the primitive character of
  the conductor inducing a ray class character.

## Main results

* `TauCeti.GlobalNumberFields.RayClassCharacter.conductor_dvd_iff`: a ray class character is
  induced from a divisor `𝔫` of its modulus exactly when its conductor divides `𝔫`.
* `TauCeti.GlobalNumberFields.RayClassCharacter.conductor_induced`: inducing a character to a
  larger modulus does not change its conductor.
* `TauCeti.GlobalNumberFields.RayClassCharacter.isPrimitive_iff_conductor_eq`: a ray class
  character is primitive exactly when its conductor is its modulus.
* `TauCeti.GlobalNumberFields.RayClassCharacter.induced_primitiveCharacter` and
  `TauCeti.GlobalNumberFields.RayClassCharacter.isPrimitive_primitiveCharacter`: every ray class
  character is induced from a primitive character of its conductor.
* `TauCeti.GlobalNumberFields.RayClassCharacter.conductor_inv`,
  `TauCeti.GlobalNumberFields.RayClassCharacter.conductor_zpow_dvd`, and
  `TauCeti.GlobalNumberFields.RayClassCharacter.conductor_mul_dvd_lcm`: the conductor and the group
  operations.
* `TauCeti.GlobalNumberFields.HeckeCharacter.isPrimitive_rayClassCharacterAt_conductor`: a
  finite-order Hecke character is the pullback of a primitive ray class character of its
  conductor, namely its representative there.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §1 and Chapter VII, §6.
* The API follows Mathlib's conductor of Dirichlet characters,
  `Mathlib.NumberTheory.DirichletCharacter.Basic` (`DirichletCharacter.conductor`,
  `DirichletCharacter.primitiveCharacter`, `DirichletCharacter.conductor_changeLevel`).
-/

public section
noncomputable section

open IsDedekindDomain NumberField
open scoped NumberField

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

namespace RayClassCharacter

variable {𝔪 𝔫 : Modulus K}

/-- **The conductor of a ray class character**: the conductor of its Hecke character, that is, the
least modulus from which the character is induced (`RayClassCharacter.conductor_dvd_iff`). -/
def conductor (η : RayClassCharacter 𝔪) : Modulus K :=
  (HeckeCharacter.ofRayClassCharacter 𝔪 η).conductor
    (HeckeCharacter.isFiniteOrder_ofRayClassCharacter η)

/-- The conductor of the Hecke character of a ray class character is the conductor of the ray
class character. -/
@[simp]
theorem _root_.TauCeti.GlobalNumberFields.HeckeCharacter.conductor_ofRayClassCharacter
    (η : RayClassCharacter 𝔪)
    (hη : (HeckeCharacter.ofRayClassCharacter 𝔪 η).IsFiniteOrder) :
    (HeckeCharacter.ofRayClassCharacter 𝔪 η).conductor hη = η.conductor :=
  (rfl)

/-- **The conductor is the least modulus from which a ray class character is induced**: a ray
class character of `𝔪` is induced from a divisor `𝔫` of `𝔪` exactly when its conductor divides
`𝔫`. -/
theorem conductor_dvd_iff (h : 𝔫 ∣ 𝔪) {η : RayClassCharacter 𝔪} :
    η.conductor ∣ 𝔫 ↔ ∃ ψ : RayClassCharacter 𝔫, ψ.induced h = η := by
  rw [exists_induced_eq_iff_mem_range, conductor, HeckeCharacter.conductor_dvd_iff]

/-- The conductor of a ray class character divides its modulus. -/
theorem conductor_dvd (η : RayClassCharacter 𝔪) : η.conductor ∣ 𝔪 :=
  (conductor_dvd_iff (Modulus.dvd_refl 𝔪)).mpr ⟨η, induced_refl η⟩

/-- **The primitive character inducing a ray class character**: the character of the conductor
from which the ray class character is induced (`RayClassCharacter.induced_primitiveCharacter`).
It is primitive (`RayClassCharacter.isPrimitive_primitiveCharacter`). -/
def primitiveCharacter (η : RayClassCharacter 𝔪) : RayClassCharacter η.conductor :=
  ((conductor_dvd_iff η.conductor_dvd).mp (Modulus.dvd_refl _)).choose

/-- A ray class character is induced from its primitive character. -/
@[simp]
theorem induced_primitiveCharacter (η : RayClassCharacter 𝔪) :
    η.primitiveCharacter.induced η.conductor_dvd = η :=
  ((conductor_dvd_iff η.conductor_dvd).mp (Modulus.dvd_refl _)).choose_spec

/-- **Inducing a ray class character to a larger modulus does not change its conductor.** -/
@[simp]
theorem conductor_induced (h : 𝔪 ∣ 𝔫) (η : RayClassCharacter 𝔪) :
    (η.induced h).conductor = η.conductor := by
  simp only [conductor, HeckeCharacter.ofRayClassCharacter_induced]

/-- **A ray class character is primitive exactly when its conductor is its modulus.** -/
theorem isPrimitive_iff_conductor_eq (η : RayClassCharacter 𝔪) :
    η.IsPrimitive ↔ η.conductor = 𝔪 := by
  refine ⟨fun hη ↦ (isPrimitive_iff η).mp hη _ η.conductor_dvd _ η.induced_primitiveCharacter,
    fun hη ↦ (isPrimitive_iff η).mpr fun 𝔫 h ψ hψ ↦ ?_⟩
  have hdvd : η.conductor ∣ 𝔫 := (conductor_dvd_iff h).mpr ⟨ψ, hψ⟩
  rw [hη] at hdvd
  exact Modulus.dvd_antisymm h hdvd

/-- **The primitive character of a ray class character is primitive.** -/
theorem isPrimitive_primitiveCharacter (η : RayClassCharacter 𝔪) :
    η.primitiveCharacter.IsPrimitive := by
  rw [isPrimitive_iff_conductor_eq, ← conductor_induced η.conductor_dvd,
    induced_primitiveCharacter]

/-- The trivial character of any modulus has the trivial conductor. -/
@[simp]
theorem conductor_one : (1 : RayClassCharacter 𝔪).conductor = Modulus.one K := by
  simp only [conductor, map_one, HeckeCharacter.conductor_one]

/-- A ray class character has the trivial conductor exactly when it is induced from a character
of the trivial modulus, that is, of the ideal class group. -/
theorem conductor_eq_one_iff {η : RayClassCharacter 𝔪} :
    η.conductor = Modulus.one K ↔
      ∃ ψ : RayClassCharacter (Modulus.one K), ψ.induced (Modulus.one_dvd 𝔪) = η := by
  rw [← conductor_dvd_iff (Modulus.one_dvd 𝔪)]
  exact ⟨fun h ↦ h ▸ Modulus.dvd_refl _, Modulus.eq_one_of_dvd_one⟩

/-- **Inverting a ray class character does not change its conductor.** -/
@[simp]
theorem conductor_inv (η : RayClassCharacter 𝔪) : η⁻¹.conductor = η.conductor := by
  have key (ψ : RayClassCharacter 𝔪) : ψ⁻¹.conductor ∣ ψ.conductor := by
    -- `map_inv` needs its arguments: the inverse of `RayClassCharacter 𝔪` is `MonoidHom.instInv`,
    -- which the unapplied lemma's `Group.toInv` does not match syntactically.
    rw [conductor, HeckeCharacter.conductor_dvd_iff,
      map_inv (HeckeCharacter.ofRayClassCharacter 𝔪) ψ]
    exact inv_mem (HeckeCharacter.mem_range_ofRayClassCharacter_conductor _)
  exact Modulus.dvd_antisymm (key η) (inv_inv η ▸ key η⁻¹)

/-- The conductor of a power of a ray class character divides its conductor. -/
theorem conductor_pow_dvd (η : RayClassCharacter 𝔪) (n : ℕ) :
    (η ^ n).conductor ∣ η.conductor := by
  rw [conductor, HeckeCharacter.conductor_dvd_iff,
    map_pow (HeckeCharacter.ofRayClassCharacter 𝔪) η n]
  exact pow_mem (HeckeCharacter.mem_range_ofRayClassCharacter_conductor _) n

/-- The conductor of an integer power of a ray class character divides its conductor. -/
theorem conductor_zpow_dvd (η : RayClassCharacter 𝔪) (n : ℤ) :
    (η ^ n).conductor ∣ η.conductor := by
  rw [conductor, HeckeCharacter.conductor_dvd_iff,
    map_zpow (HeckeCharacter.ofRayClassCharacter 𝔪) η n]
  exact zpow_mem (HeckeCharacter.mem_range_ofRayClassCharacter_conductor _) n

/-- The conductor of a product of ray class characters divides the least common multiple of their
conductors. -/
theorem conductor_mul_dvd_lcm (η ψ : RayClassCharacter 𝔪) :
    (η * ψ).conductor ∣ η.conductor.lcm ψ.conductor := by
  rw [conductor, HeckeCharacter.conductor_dvd_iff, map_mul]
  exact mul_mem
    (HeckeCharacter.range_ofRayClassCharacter_le (Modulus.dvd_lcm_left _ _)
      (HeckeCharacter.mem_range_ofRayClassCharacter_conductor _))
    (HeckeCharacter.range_ofRayClassCharacter_le (Modulus.dvd_lcm_right _ _)
      (HeckeCharacter.mem_range_ofRayClassCharacter_conductor _))

end RayClassCharacter

namespace HeckeCharacter

/-- **The representative of a finite-order Hecke character at its conductor is primitive.**
Since its pullback is the character itself (`ofRayClassCharacter_rayClassCharacterAt`), a
finite-order Hecke character is the pullback of a primitive ray class character of its
conductor. -/
theorem isPrimitive_rayClassCharacterAt_conductor {χ : HeckeCharacter K} (hχ : χ.IsFiniteOrder) :
    (χ.rayClassCharacterAt (χ.conductor hχ)
      (mem_range_ofRayClassCharacter_conductor hχ)).IsPrimitive := by
  rw [RayClassCharacter.isPrimitive_iff_conductor_eq, ← conductor_ofRayClassCharacter _
    (by rw [ofRayClassCharacter_rayClassCharacterAt]; exact hχ)]
  simp only [ofRayClassCharacter_rayClassCharacterAt]

end HeckeCharacter

end TauCeti.GlobalNumberFields
