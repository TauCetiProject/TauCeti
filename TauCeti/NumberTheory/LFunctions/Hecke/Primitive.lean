/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.RayClass.Character.Conductor

/-!
# Primitive ray class characters

A ray class character can be presented at every multiple of its conductor, so a conductor stored
next to a presentation modulus would let one character carry several incompatible conductors,
and with them several gamma factors, root numbers and local factors. A
`TauCeti.LFunctions.PrimitiveRayClassCharacter` instead bundles a modulus, a character of that
modulus and the proof that the character is primitive. Its modulus is then the conductor of the
character (`PrimitiveRayClassCharacter.conductor_character`), and a primitive character is
determined by any of its presentations (`PrimitiveRayClassCharacter.eq_of_induced_eq`). This is
the carrier on which completed Hecke L-functions, Gauss sums and root numbers are defined, while
the presented L-series keep taking a ray class character of a chosen modulus.

`PrimitiveRayClassCharacter.of χ` is the primitive character underlying a ray class character `χ`
of any modulus, built from the supplier's `RayClassCharacter.conductor` and
`RayClassCharacter.primitiveCharacter`. It does not depend on the presentation
(`PrimitiveRayClassCharacter.of_induced`) and it is the identity on primitive characters
(`PrimitiveRayClassCharacter.of_character`). Inversion keeps the conductor
(`PrimitiveRayClassCharacter.conductor_inv`), which is the reflection in the functional equation.

## Main definitions

* `TauCeti.LFunctions.PrimitiveRayClassCharacter`: a primitive ray class character together with
  its conductor.
* `TauCeti.LFunctions.PrimitiveRayClassCharacter.of`: the primitive character underlying a ray
  class character.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §6.
-/

public section
noncomputable section

namespace TauCeti.LFunctions

open GlobalNumberFields

/-- **A ray class character presented at its own conductor**: a modulus `conductor`, a ray class
character of that modulus, and the proof that this character is primitive. Its modulus is the
conductor of the character (`PrimitiveRayClassCharacter.conductor_character`). -/
structure PrimitiveRayClassCharacter (K : Type*) [Field K] [NumberField K] where
  /-- The conductor, at which the character is presented. -/
  conductor : Modulus K
  /-- The character, a ray class character of the conductor. -/
  character : RayClassCharacter conductor
  /-- The character is primitive. -/
  isPrimitive : character.IsPrimitive

namespace PrimitiveRayClassCharacter

variable {K : Type*} [Field K] [NumberField K] {𝔪 𝔫 : Modulus K}

/-- The modulus of a primitive character is the conductor of its character. -/
theorem conductor_character (ψ : PrimitiveRayClassCharacter K) :
    ψ.character.conductor = ψ.conductor :=
  (RayClassCharacter.isPrimitive_iff_conductor_eq _).mp ψ.isPrimitive

/-- **A primitive character is determined by any of its presentations.** Two primitive characters
inducing the same character of a common multiple of their conductors are equal. -/
theorem eq_of_induced_eq {ψ₁ ψ₂ : PrimitiveRayClassCharacter K} {𝔐 : Modulus K}
    (h₁ : ψ₁.conductor ∣ 𝔐) (h₂ : ψ₂.conductor ∣ 𝔐)
    (h : ψ₁.character.induced h₁ = ψ₂.character.induced h₂) : ψ₁ = ψ₂ := by
  obtain ⟨𝔫₁, χ₁, hχ₁⟩ := ψ₁
  obtain ⟨𝔫₂, χ₂, hχ₂⟩ := ψ₂
  have h𝔫 : 𝔫₁ = 𝔫₂ := by
    rw [← (RayClassCharacter.isPrimitive_iff_conductor_eq χ₁).mp hχ₁,
      ← (RayClassCharacter.isPrimitive_iff_conductor_eq χ₂).mp hχ₂]
    exact RayClassCharacter.conductor_eq_of_induced_eq h₁ h₂ h
  subst h𝔫
  obtain rfl := RayClassCharacter.induced_injective h₁ h
  rfl

/-- Two primitive characters are equal exactly when they induce the same character of a common
multiple of their conductors. -/
theorem induced_character_inj {ψ₁ ψ₂ : PrimitiveRayClassCharacter K} {𝔐 : Modulus K}
    (h₁ : ψ₁.conductor ∣ 𝔐) (h₂ : ψ₂.conductor ∣ 𝔐) :
    ψ₁.character.induced h₁ = ψ₂.character.induced h₂ ↔ ψ₁ = ψ₂ := by
  refine ⟨eq_of_induced_eq h₁ h₂, ?_⟩
  rintro rfl
  rfl

/-! ### The primitive character of a presentation -/

/-- **The primitive character underlying a ray class character**: the supplier's
`RayClassCharacter.primitiveCharacter`, presented at the conductor `RayClassCharacter.conductor`.
The character is induced from it (`PrimitiveRayClassCharacter.induced_character_of`). -/
def of (χ : RayClassCharacter 𝔪) : PrimitiveRayClassCharacter K :=
  ⟨χ.conductor, χ.primitiveCharacter, χ.isPrimitive_primitiveCharacter⟩

/-- The conductor of `of χ` is the conductor of `χ`. -/
@[simp]
theorem conductor_of (χ : RayClassCharacter 𝔪) : (of χ).conductor = χ.conductor :=
  (rfl)

/-- The conductor of `of χ` divides the modulus of `χ`. -/
theorem conductor_of_dvd (χ : RayClassCharacter 𝔪) : (of χ).conductor ∣ 𝔪 :=
  χ.conductor_dvd

/-- **A ray class character is induced from its primitive character.** -/
@[simp]
theorem induced_character_of (χ : RayClassCharacter 𝔪) (h : (of χ).conductor ∣ 𝔪) :
    (of χ).character.induced h = χ :=
  χ.induced_primitiveCharacter

/-- The primitive character of a primitive character is itself. -/
@[simp]
theorem of_character (ψ : PrimitiveRayClassCharacter K) : of ψ.character = ψ :=
  eq_of_induced_eq (conductor_of_dvd ψ.character) (Modulus.dvd_refl ψ.conductor)
    (by rw [induced_character_of, RayClassCharacter.induced_refl])

/-- **The primitive character does not depend on the presentation.** -/
@[simp]
theorem of_induced (h : 𝔪 ∣ 𝔫) (χ : RayClassCharacter 𝔪) : of (χ.induced h) = of χ :=
  eq_of_induced_eq (conductor_of_dvd _) (Modulus.dvd_trans (conductor_of_dvd χ) h) (by
    rw [induced_character_of, ← RayClassCharacter.induced_trans (conductor_of_dvd χ) h,
      induced_character_of])

/-- The primitive character of the trivial character is the trivial character of the trivial
modulus. -/
@[simp]
theorem of_one :
    of (1 : RayClassCharacter 𝔪) =
      ⟨Modulus.one K, 1, (RayClassCharacter.isPrimitive_one_iff).mpr rfl⟩ :=
  eq_of_induced_eq (conductor_of_dvd 1) (Modulus.one_dvd 𝔪) (by
    rw [induced_character_of, map_one])

/-! ### Inversion -/

/-- The inverse of a primitive character is primitive at the same conductor, by the supplier's
`RayClassCharacter.conductor_inv`. The functional equation reflects a character against it. -/
instance : Inv (PrimitiveRayClassCharacter K) where
  inv ψ := ⟨ψ.conductor, ψ.character⁻¹, (RayClassCharacter.isPrimitive_iff_conductor_eq _).mpr
    ((RayClassCharacter.conductor_inv _).trans ψ.conductor_character)⟩

/-- Inversion keeps the conductor. -/
@[simp]
theorem conductor_inv (ψ : PrimitiveRayClassCharacter K) : ψ⁻¹.conductor = ψ.conductor :=
  (rfl)

/-- The character of the inverse is the inverse character. -/
@[simp]
theorem character_inv (ψ : PrimitiveRayClassCharacter K) : ψ⁻¹.character = ψ.character⁻¹ :=
  (rfl)

/-- Every presentation of the inverse is the inverse of the corresponding presentation. -/
theorem induced_character_inv (ψ : PrimitiveRayClassCharacter K) {𝔐 : Modulus K}
    (h : ψ⁻¹.conductor ∣ 𝔐) : ψ⁻¹.character.induced h = (ψ.character.induced h)⁻¹ :=
  map_inv (RayClassCharacter.induced h) ψ.character

instance : InvolutiveInv (PrimitiveRayClassCharacter K) where
  inv_inv ψ := eq_of_induced_eq (Modulus.dvd_refl _) (Modulus.dvd_refl _) (by
    rw [RayClassCharacter.induced_refl, RayClassCharacter.induced_refl]
    exact inv_inv ψ.character)

/-- Taking the primitive character commutes with inversion. -/
@[simp]
theorem of_inv (χ : RayClassCharacter 𝔪) : of χ⁻¹ = (of χ)⁻¹ :=
  eq_of_induced_eq (conductor_of_dvd _) (conductor_of_dvd χ) (by
    rw [induced_character_of, induced_character_inv, induced_character_of])

end PrimitiveRayClassCharacter

end TauCeti.LFunctions
