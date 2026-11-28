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

For a bundled primitive ray class character `ψ : TauCeti.LFunctions.PrimitiveRayClassCharacter ℚ`,
`ψ.character.toDirichletCharacter` is a primitive complex Dirichlet character of level
`Ideal.absNorm ψ.conductor.finitePart`. For the canonical equivalence
`PrimitiveDirichletCharacter ≃ PrimitiveRayClassCharacter ℚ`, see
`TauCeti.PrimitiveDirichletCharacter.toPrimitiveRayClassCharacter` in
`TauCeti.NumberTheory.DirichletCharacter.Primitive.RayClass`.

## Main results

* `TauCeti.LFunctions.PrimitiveRayClassCharacter.isPrimitive_toDirichletCharacter`:
  `ψ.character.toDirichletCharacter` is primitive.
* `TauCeti.LFunctions.PrimitiveRayClassCharacter.changeLevel_toDirichletCharacter_of`:
  lifting `(of η).character.toDirichletCharacter` recovers `η.toDirichletCharacter`.
* `TauCeti.LFunctions.PrimitiveRayClassCharacter.toDirichletCharacter_of_intCast` and
  `TauCeti.LFunctions.PrimitiveRayClassCharacter.toDirichletCharacter_of_natCast`: values of
  `(of η).character.toDirichletCharacter` on integers and natural numbers recover
  `η.toDirichletCharacter.primitiveCharacter`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §1 and Chapter VII, §6.
-/

public section
noncomputable section

open DirichletCharacter NumberField
open scoped NumberField

namespace TauCeti.LFunctions.PrimitiveRayClassCharacter

open GlobalNumberFields

/-- The Dirichlet character of a primitive ray class character of `ℚ` is primitive. -/
theorem isPrimitive_toDirichletCharacter (ψ : PrimitiveRayClassCharacter ℚ) :
    ψ.character.toDirichletCharacter.IsPrimitive := by
  rw [DirichletCharacter.isPrimitive_def,
    RayClassCharacter.conductor_toDirichletCharacter, ψ.conductor_character]

/-- Lifting `(of η).character.toDirichletCharacter` to the norm of `𝔪.finitePart` recovers
`η.toDirichletCharacter`. -/
theorem changeLevel_toDirichletCharacter_of {𝔪 : Modulus ℚ} (η : RayClassCharacter 𝔪) :
    changeLevel (map_dvd Ideal.absNorm (Modulus.dvd_iff.mp (conductor_of_dvd η)).1)
      (of η).character.toDirichletCharacter = η.toDirichletCharacter :=
  (RayClassCharacter.toDirichletCharacter_induced (conductor_of_dvd η)
    (of η).character).symm.trans (congrArg _ (induced_character_of η))

/-- At any integer `m : ℤ`, the Dirichlet character of `of η` equals
`η.toDirichletCharacter.primitiveCharacter m`. -/
@[simp]
theorem toDirichletCharacter_of_intCast {𝔪 : Modulus ℚ} (η : RayClassCharacter 𝔪) (m : ℤ) :
    (of η).character.toDirichletCharacter m = η.toDirichletCharacter.primitiveCharacter m :=
  (of η).isPrimitive_toDirichletCharacter.apply_intCast_eq_primitiveCharacter_of_changeLevel_eq
    (map_dvd Ideal.absNorm (Modulus.dvd_iff.mp (conductor_of_dvd η)).1)
    (changeLevel_toDirichletCharacter_of η) m

/-- At any natural number `m : ℕ`, the Dirichlet character of `of η` equals
`η.toDirichletCharacter.primitiveCharacter m`. -/
@[simp]
theorem toDirichletCharacter_of_natCast {𝔪 : Modulus ℚ} (η : RayClassCharacter 𝔪) (m : ℕ) :
    (of η).character.toDirichletCharacter m = η.toDirichletCharacter.primitiveCharacter m := by
  simpa only [Int.cast_natCast] using toDirichletCharacter_of_intCast η (m : ℤ)

end TauCeti.LFunctions.PrimitiveRayClassCharacter
