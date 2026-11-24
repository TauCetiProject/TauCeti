/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DirichletCharacter.Primitive

/-!
# Primitive Dirichlet characters bundled with their conductor

One Dirichlet character can be presented at every multiple of its conductor. The structure
`TauCeti.PrimitiveDirichletCharacter` bundles a primitive complex Dirichlet character with its
level, which is then its conductor, so that a bundle cannot carry a second level: the principal
character modulo `6` and the character modulo `1` have the same bundle `1`. It is the Dirichlet
counterpart of `TauCeti.LFunctions.PrimitiveRayClassCharacter`, built on Mathlib's
`DirichletCharacter` so that the L-function of a bundle `ψ` is Mathlib's
`ψ.character.LFunction`.

## Main definitions

* `TauCeti.PrimitiveDirichletCharacter`: a level in `ℕ+`, a character of that level and a proof
  that it is primitive.
* `TauCeti.PrimitiveDirichletCharacter.of`: the bundle of a character `χ` of nonzero level, with
  level `χ.conductor` and character `χ.primitiveCharacter`.
* The bundle `1`, of level `1`, and the inverse `ψ⁻¹`, at the same level.

## Main results

* `TauCeti.PrimitiveDirichletCharacter.changeLevel_character_inj`,
  `TauCeti.PrimitiveDirichletCharacter.eq_iff_changeLevel_mul`: two bundles are equal exactly when
  their characters agree after lifting to a common level, for instance the product of the levels.
* `TauCeti.PrimitiveDirichletCharacter.of_eq_iff`: `of χ = ψ` exactly when `χ` is the lift of
  `ψ.character`.
* `TauCeti.PrimitiveDirichletCharacter.of_character`,
  `TauCeti.PrimitiveDirichletCharacter.of_changeLevel`,
  `TauCeti.PrimitiveDirichletCharacter.of_one`, `TauCeti.PrimitiveDirichletCharacter.of_inv`: the
  bundle of the character of a bundle, of a lift, of a principal character and of an inverse.
-/

public section

open DirichletCharacter

namespace TauCeti

/-- **A primitive Dirichlet character bundled with its conductor.** One Dirichlet character can be
presented at every multiple of its conductor; on this carrier the level is the conductor of the
character, so it cannot record a second level. -/
structure PrimitiveDirichletCharacter where
  /-- The level, which is the conductor of the character. -/
  level : ℕ+
  /-- The character, presented at its conductor. -/
  character : DirichletCharacter ℂ level
  /-- The character is primitive. -/
  isPrimitive : character.IsPrimitive

namespace PrimitiveDirichletCharacter

variable {N M L : ℕ}

/-- The level of a bundle is the conductor of its character. -/
@[simp]
theorem conductor_character (ψ : PrimitiveDirichletCharacter) :
    ψ.character.conductor = ψ.level :=
  ψ.isPrimitive

/-- Two bundles whose characters have the same lift to a common nonzero level are equal. -/
theorem eq_of_changeLevel_eq [NeZero L] {ψ ψ' : PrimitiveDirichletCharacter}
    (h : (ψ.level : ℕ) ∣ L) (h' : (ψ'.level : ℕ) ∣ L)
    (hψ : changeLevel h ψ.character = changeLevel h' ψ'.character) : ψ = ψ' := by
  obtain ⟨n, χ, hχ⟩ := ψ
  obtain ⟨n', χ', hχ'⟩ := ψ'
  obtain ⟨hn, hχeq⟩ := (hχ.changeLevel_eq_changeLevel_iff hχ' h h').1 hψ
  obtain rfl : n = n' := PNat.eq hn
  obtain rfl : χ = χ' := hχeq
  rfl

/-- Two bundles are equal exactly when their characters have the same lift to a common nonzero
level. -/
theorem changeLevel_character_inj [NeZero L] {ψ ψ' : PrimitiveDirichletCharacter}
    (h : (ψ.level : ℕ) ∣ L) (h' : (ψ'.level : ℕ) ∣ L) :
    changeLevel h ψ.character = changeLevel h' ψ'.character ↔ ψ = ψ' := by
  refine ⟨eq_of_changeLevel_eq h h', ?_⟩
  rintro rfl
  rfl

/-- Two bundles are equal exactly when their characters agree after lifting both to the product
of the levels. -/
theorem eq_iff_changeLevel_mul {ψ ψ' : PrimitiveDirichletCharacter} :
    ψ = ψ' ↔ changeLevel (dvd_mul_right (ψ.level : ℕ) ψ'.level) ψ.character =
      changeLevel (dvd_mul_left (ψ'.level : ℕ) ψ.level) ψ'.character :=
  (changeLevel_character_inj _ _).symm

/-- The bundle of a Dirichlet character of nonzero level: its primitive character, at its
conductor. -/
noncomputable def of [NeZero N] (χ : DirichletCharacter ℂ N) : PrimitiveDirichletCharacter :=
  ⟨⟨χ.conductor, Nat.pos_of_ne_zero χ.conductor_ne_zero⟩, χ.primitiveCharacter,
    χ.primitiveCharacter_isPrimitive⟩

/-- The level of the bundle of `χ` is the conductor of `χ`. -/
@[simp]
theorem level_of [NeZero N] (χ : DirichletCharacter ℂ N) : ((of χ).level : ℕ) = χ.conductor :=
  (rfl)

/-- The level of the bundle of a character divides the level at which the character is
presented. -/
theorem level_of_dvd [NeZero N] (χ : DirichletCharacter ℂ N) : ((of χ).level : ℕ) ∣ N :=
  χ.conductor_dvd_level

/-- A Dirichlet character is the lift of the character of its bundle. -/
@[simp]
theorem changeLevel_character_of [NeZero N] (χ : DirichletCharacter ℂ N) :
    changeLevel (level_of_dvd χ) (of χ).character = χ :=
  χ.changeLevel_primitiveCharacter

/-- The bundle of `χ` is `ψ` exactly when `χ` is the lift of the character of `ψ`. -/
theorem of_eq_iff [NeZero N] {χ : DirichletCharacter ℂ N} {ψ : PrimitiveDirichletCharacter} :
    of χ = ψ ↔ ∃ h : (ψ.level : ℕ) ∣ N, changeLevel h ψ.character = χ := by
  refine ⟨?_, fun ⟨h, hψ⟩ => eq_of_changeLevel_eq (level_of_dvd χ) h ?_⟩
  · rintro rfl
    exact ⟨level_of_dvd χ, changeLevel_character_of χ⟩
  · rw [changeLevel_character_of, hψ]

/-- The bundle of the character of a bundle is that bundle. -/
@[simp]
theorem of_character (ψ : PrimitiveDirichletCharacter) : of ψ.character = ψ :=
  of_eq_iff.2 ⟨dvd_rfl, changeLevel_self _⟩

/-- **The bundle does not depend on the presentation**: a character and its lift to a multiple of
its level have the same bundle. -/
@[simp]
theorem of_changeLevel [NeZero N] (h : M ∣ N) (χ : DirichletCharacter ℂ M) :
    of (changeLevel h χ) =
      haveI : NeZero M := ⟨ne_zero_of_dvd_ne_zero (NeZero.ne N) h⟩
      of χ := by
  have : NeZero M := ⟨ne_zero_of_dvd_ne_zero (NeZero.ne N) h⟩
  exact of_eq_iff.2 ⟨(level_of_dvd χ).trans h, by
    rw [changeLevel_trans _ (level_of_dvd χ) h, changeLevel_character_of]⟩

/-- The trivial bundle: the character modulo `1`. -/
noncomputable instance : One PrimitiveDirichletCharacter :=
  ⟨⟨1, 1, isPrimitive_one_level_one⟩⟩

/-- The trivial bundle has level `1`. -/
@[simp]
theorem level_one : (1 : PrimitiveDirichletCharacter).level = 1 :=
  (rfl)

/-- The character of the trivial bundle is the character modulo `1`. -/
@[simp]
theorem character_one : (1 : PrimitiveDirichletCharacter).character = 1 :=
  (rfl)

/-- The principal character of every nonzero level has the trivial bundle. -/
@[simp]
theorem of_one [NeZero N] : of (1 : DirichletCharacter ℂ N) = 1 :=
  of_eq_iff.2 ⟨one_dvd N, changeLevel_one _⟩

/-- The inverse of a bundle: the inverse character, primitive at the same level. -/
noncomputable instance : Inv PrimitiveDirichletCharacter :=
  ⟨fun ψ => ⟨ψ.level, ψ.character⁻¹, ψ.isPrimitive.inv⟩⟩

/-- The inverse of a bundle has the same level. -/
@[simp]
theorem level_inv (ψ : PrimitiveDirichletCharacter) : ψ⁻¹.level = ψ.level :=
  (rfl)

/-- The character of the inverse of a bundle is the inverse of its character. -/
@[simp]
theorem character_inv (ψ : PrimitiveDirichletCharacter) : ψ⁻¹.character = ψ.character⁻¹ :=
  (rfl)

/-- The bundle of the inverse of a character is the inverse of its bundle. -/
@[simp]
theorem of_inv [NeZero N] (χ : DirichletCharacter ℂ N) : of χ⁻¹ = (of χ)⁻¹ :=
  of_eq_iff.2 ⟨level_of_dvd χ, by rw [character_inv, map_inv, changeLevel_character_of]⟩

/-- Inversion of bundles is an involution. -/
noncomputable instance : InvolutiveInv PrimitiveDirichletCharacter where
  inv_inv ψ := by rw [← of_character ψ, ← of_inv, ← of_inv, inv_inv]

/-- The trivial bundle is its own inverse. -/
@[simp]
theorem inv_one : (1 : PrimitiveDirichletCharacter)⁻¹ = 1 := by
  rw [← of_one (N := 1), ← of_inv, _root_.inv_one]

end PrimitiveDirichletCharacter

end TauCeti
