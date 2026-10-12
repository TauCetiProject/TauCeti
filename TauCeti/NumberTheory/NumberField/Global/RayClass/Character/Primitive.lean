/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.RayClass.Character.Basic

/-!
# Primitive ray class characters

A ray class character is primitive when it is not induced from any strictly smaller modulus.
This formulation uses the transition maps of ray class groups and includes the real places in the
conductor condition. In particular, the trivial character of a nontrivial modulus is imprimitive:
it comes from the trivial modulus.

This is the finite-character distinction needed when assigning a least modulus to a Hecke
character and when comparing ray class characters with Dirichlet characters.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §1.
-/

public section
noncomputable section

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

namespace RayClassCharacter

variable {𝔪 𝔫 : Modulus K}

/-- A ray class character is primitive if it is not induced from a strictly smaller modulus. -/
def IsPrimitive (χ : RayClassCharacter 𝔪) : Prop :=
  ∀ (𝔫 : Modulus K) (h : 𝔫 ∣ 𝔪) (ψ : RayClassCharacter 𝔫),
    ψ.induced h = χ → 𝔫 = 𝔪

/-- A character is primitive exactly when every modulus inducing it is its own modulus. -/
theorem isPrimitive_iff (χ : RayClassCharacter 𝔪) :
    χ.IsPrimitive ↔ ∀ (𝔫 : Modulus K) (h : 𝔫 ∣ 𝔪) (ψ : RayClassCharacter 𝔫),
      ψ.induced h = χ → 𝔫 = 𝔪 := Iff.rfl

/-- An imprimitive character is induced from a strictly smaller modulus. -/
theorem not_isPrimitive_iff (χ : RayClassCharacter 𝔪) :
    ¬χ.IsPrimitive ↔ ∃ (𝔫 : Modulus K) (h : 𝔫 ∣ 𝔪) (ψ : RayClassCharacter 𝔫),
      𝔫 ≠ 𝔪 ∧ ψ.induced h = χ := by
  simp only [IsPrimitive, not_forall]
  constructor
  · rintro ⟨𝔫, h, ψ, hinduced, hne⟩
    exact ⟨𝔫, h, ψ, hne, hinduced⟩
  · rintro ⟨𝔫, h, ψ, hne, hinduced⟩
    exact ⟨𝔫, h, ψ, hinduced, hne⟩

/-- A character induced from a strictly smaller modulus is imprimitive. -/
theorem not_isPrimitive_induced (h : 𝔫 ∣ 𝔪) (hne : 𝔫 ≠ 𝔪)
    (ψ : RayClassCharacter 𝔫) : ¬(ψ.induced h).IsPrimitive := by
  intro hp
  exact hne (hp 𝔫 h ψ rfl)

/-- Every character of the trivial modulus is primitive. -/
@[simp]
theorem isPrimitive_of_modulus_one (χ : RayClassCharacter (Modulus.one K)) :
    χ.IsPrimitive := by
  intro 𝔫 h _ _
  exact Modulus.eq_one_of_dvd_one h

/-- The trivial character is primitive exactly at the trivial modulus. -/
@[simp]
theorem isPrimitive_one_iff {𝔪 : Modulus K} :
    (1 : RayClassCharacter 𝔪).IsPrimitive ↔ 𝔪 = Modulus.one K := by
  constructor
  · intro hp
    exact (hp (Modulus.one K) (Modulus.one_dvd 𝔪) 1 (map_one _)).symm
  · rintro rfl
    exact isPrimitive_of_modulus_one 1

end RayClassCharacter

end TauCeti.GlobalNumberFields
