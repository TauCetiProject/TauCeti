/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DirichletCharacter.Conductor
public import TauCeti.NumberTheory.LFunctions.Hecke.Primitive.Basic
public import TauCeti.NumberTheory.NumberField.Global.RayClass.Character.Dirichlet
import TauCeti.NumberTheory.DirichletCharacter.Basic
import TauCeti.NumberTheory.DirichletCharacter.Primitive

/-!
# Primitive ray class characters of `ℚ` and their Dirichlet characters

Every bundled primitive ray class character `ψ : TauCeti.LFunctions.PrimitiveRayClassCharacter ℚ`
determines a primitive complex Dirichlet character `ψ.toDirichletCharacter` of level
`Ideal.absNorm ψ.conductor.finitePart`. For the canonical equivalence
`PrimitiveDirichletCharacter ≃ PrimitiveRayClassCharacter ℚ`, see
`TauCeti.PrimitiveDirichletCharacter.toPrimitiveRayClassCharacter` in
`TauCeti.NumberTheory.DirichletCharacter.Primitive.RayClass`.

## Main definitions

* `TauCeti.LFunctions.PrimitiveRayClassCharacter.toDirichletCharacter`: the primitive Dirichlet
  character attached to a bundled primitive ray class character of `ℚ`.

## Main results

* `TauCeti.LFunctions.PrimitiveRayClassCharacter.isPrimitive_toDirichletCharacter`:
  `ψ.toDirichletCharacter` is primitive.
* `TauCeti.LFunctions.PrimitiveRayClassCharacter.changeLevel_toDirichletCharacter_of`:
  lifting `(of η).toDirichletCharacter` recovers `η.toDirichletCharacter`.
* `TauCeti.LFunctions.PrimitiveRayClassCharacter.conductor_eq_ratFiniteModulus_of_even` and
  `TauCeti.LFunctions.PrimitiveRayClassCharacter.conductor_eq_ratModulus_of_not_even`: the
  conductor of `ψ` in terms of the parity of `ψ.toDirichletCharacter`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §1 and Chapter VII, §6.
-/

public section
noncomputable section

open DirichletCharacter NumberField
open scoped NumberField

namespace TauCeti.LFunctions.PrimitiveRayClassCharacter

open GlobalNumberFields

/-- **The primitive Dirichlet character attached to a bundled primitive ray class character of
`ℚ`**, of level `Ideal.absNorm ψ.conductor.finitePart`. -/
abbrev toDirichletCharacter (ψ : PrimitiveRayClassCharacter ℚ) :
    DirichletCharacter ℂ (Ideal.absNorm ψ.conductor.finitePart) :=
  ψ.character.toDirichletCharacter

theorem toDirichletCharacter_def (ψ : PrimitiveRayClassCharacter ℚ) :
    ψ.toDirichletCharacter = ψ.character.toDirichletCharacter := (rfl)

/-- The Dirichlet character of a primitive ray class character of `ℚ` is primitive. -/
theorem isPrimitive_toDirichletCharacter (ψ : PrimitiveRayClassCharacter ℚ) :
    ψ.toDirichletCharacter.IsPrimitive := by
  rw [DirichletCharacter.isPrimitive_def, toDirichletCharacter_def,
    RayClassCharacter.conductor_toDirichletCharacter, ψ.conductor_character]

theorem toDirichletCharacter_eq_one_iff (ψ : PrimitiveRayClassCharacter ℚ) :
    ψ.toDirichletCharacter = 1 ↔ ψ = 1 :=
  (RayClassCharacter.toDirichletCharacter_eq_one_iff ψ.character).trans (character_eq_one_iff ψ)

/-- Lifting `(of η).toDirichletCharacter` to the norm of `𝔪.finitePart` recovers
`η.toDirichletCharacter`. -/
theorem changeLevel_toDirichletCharacter_of {𝔪 : Modulus ℚ} (η : RayClassCharacter 𝔪) :
    changeLevel (map_dvd Ideal.absNorm (Modulus.dvd_iff.mp (conductor_of_dvd η)).1)
      (of η).toDirichletCharacter = η.toDirichletCharacter :=
  (RayClassCharacter.toDirichletCharacter_induced (conductor_of_dvd η)
    (of η).character).symm.trans (congrArg _ (induced_character_of η))

@[simp]
theorem toDirichletCharacter_of_intCast {𝔪 : Modulus ℚ} (η : RayClassCharacter 𝔪) (m : ℤ) :
    (of η).toDirichletCharacter m = η.toDirichletCharacter.primitiveCharacter m :=
  (of η).isPrimitive_toDirichletCharacter.apply_intCast_eq_primitiveCharacter_of_changeLevel_eq
    (map_dvd Ideal.absNorm (Modulus.dvd_iff.mp (conductor_of_dvd η)).1)
    (changeLevel_toDirichletCharacter_of η) m

@[simp]
theorem toDirichletCharacter_of_natCast {𝔪 : Modulus ℚ} (η : RayClassCharacter 𝔪) (m : ℕ) :
    (of η).toDirichletCharacter m = η.toDirichletCharacter.primitiveCharacter m := by
  simpa only [Int.cast_natCast] using toDirichletCharacter_of_intCast η (m : ℤ)

@[simp]
theorem toDirichletCharacter_inv (ψ : PrimitiveRayClassCharacter ℚ) :
    ψ⁻¹.toDirichletCharacter = ψ.toDirichletCharacter⁻¹ :=
  map_inv RayClassCharacter.toDirichletCharacter ψ.character

/-- When `ψ.toDirichletCharacter` is even, the conductor of `ψ` is the finite modulus `(f)`
without the real place. -/
theorem conductor_eq_ratFiniteModulus_of_even (ψ : PrimitiveRayClassCharacter ℚ)
    (h : ψ.toDirichletCharacter.Even) :
    ψ.conductor = ratFiniteModulus ψ.toDirichletCharacter.conductor (conductor_ne_zero _) :=
  ψ.conductor_character.symm.trans (ψ.character.conductor_eq_ratFiniteModulus_of_even h)

/-- When `ψ.toDirichletCharacter` is odd, the conductor of `ψ` is the modulus `(f)·∞` including
the real place. -/
theorem conductor_eq_ratModulus_of_not_even (ψ : PrimitiveRayClassCharacter ℚ)
    (h : ¬ ψ.toDirichletCharacter.Even) :
    ψ.conductor = ratModulus ψ.toDirichletCharacter.conductor (conductor_ne_zero _) :=
  ψ.conductor_character.symm.trans (ψ.character.conductor_eq_ratModulus_of_not_even h)

end TauCeti.LFunctions.PrimitiveRayClassCharacter
