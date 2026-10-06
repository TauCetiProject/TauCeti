/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.HeckeCharacter.Basic
public import TauCeti.NumberTheory.NumberField.Global.Ideles.Ray.OpenSubgroup

import TauCeti.Topology.Algebra.ContinuousMonoidHom.Basic

/-!
# Finite-order Hecke characters

A finite-order Hecke character is locally constant: its kernel is an open subgroup of the idele
class group.  Every open subgroup of the idele class group contains a ray subgroup
(`exists_raySubgroup_le_of_isOpen`), and a Hecke character trivial on `raySubgroup 𝔪` is the
pullback of a ray class character of `𝔪` (`HeckeCharacter.mem_range_ofRayClassCharacter_iff`).
Together with the finiteness of the ray class groups this proves that, for a Hecke character, the
following are equivalent: it has finite order, its kernel is open, and it is the pullback of a ray
class character of some modulus.  The finite-order Hecke characters are therefore exactly the
characters of the ray class groups, which is why the ray class L-functions exhaust the Hecke
L-functions of finite-order characters.

## Main results

* `HeckeCharacter.isOpen_ker_of_isFiniteOrder`: a finite-order Hecke character has open kernel.
* `HeckeCharacter.exists_ofRayClassCharacter_eq_of_isOpen_ker`: a Hecke character with open kernel
  is the pullback of a ray class character.
* `HeckeCharacter.isFiniteOrder_iff_exists_rayClassCharacter`: a Hecke character has finite order
  exactly when it is the pullback of a ray class character of some modulus.
* `HeckeCharacter.isFiniteOrder_iff_isOpen_ker`: a Hecke character has finite order exactly when
  its kernel is open.
* `HeckeCharacter.rayClassCharacterAt`: the unique ray class character representing a Hecke
  character at a specified modulus.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §1 and Chapter VII, §6.
-/

public section
noncomputable section

open IsDedekindDomain NumberField Set
open scoped NumberField

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

namespace HeckeCharacter

variable {𝔪 𝔫 : Modulus K}

/-- A finite-order Hecke character has open kernel, and is therefore locally constant. -/
theorem isOpen_ker_of_isFiniteOrder {χ : HeckeCharacter K} (hχ : χ.IsFiniteOrder) :
    IsOpen ((χ : IdeleClassGroup (𝓞 K) K →* ℂˣ).ker : Set (IdeleClassGroup (𝓞 K) K)) := by
  simpa only [MonoidHom.coe_ker, ContinuousMonoidHom.coe_toMonoidHom, MonoidHom.coe_ofClass] using
    (ContinuousMonoidHom.isOpen_ker_of_isOfFinOrder hχ)

/-- **A Hecke character pulled back from a ray class character has open kernel.** -/
theorem isOpen_ker_ofRayClassCharacter {𝔪 : Modulus K} (η : RayClassCharacter 𝔪) :
    IsOpen (((ofRayClassCharacter 𝔪 η : HeckeCharacter K) :
      IdeleClassGroup (𝓞 K) K →* ℂˣ).ker : Set (IdeleClassGroup (𝓞 K) K)) :=
  isOpen_ker_of_isFiniteOrder (isFiniteOrder_ofRayClassCharacter η)

/-- **A Hecke character with open kernel is the pullback of a ray class character** of some
modulus `𝔪`.  Together with `isOpen_ker_ofRayClassCharacter` this identifies the Hecke characters
with open kernel with the ray class characters of all moduli. -/
theorem exists_ofRayClassCharacter_eq_of_isOpen_ker {χ : HeckeCharacter K}
    (hχ : IsOpen ((χ : IdeleClassGroup (𝓞 K) K →* ℂˣ).ker : Set (IdeleClassGroup (𝓞 K) K))) :
    ∃ (𝔪 : Modulus K) (η : RayClassCharacter 𝔪), ofRayClassCharacter 𝔪 η = χ := by
  obtain ⟨𝔪, h𝔪⟩ := exists_raySubgroup_le_of_isOpen _ hχ
  exact ⟨𝔪, MonoidHom.mem_range.mp (mem_range_ofRayClassCharacter_iff.mpr h𝔪)⟩

/-- **Finite-order Hecke characters are exactly the ray class characters**: a Hecke character has
finite order exactly when it is the pullback of a ray class character of some modulus. -/
theorem isFiniteOrder_iff_exists_rayClassCharacter (χ : HeckeCharacter K) :
    χ.IsFiniteOrder ↔
      ∃ (𝔪 : Modulus K) (η : RayClassCharacter 𝔪), ofRayClassCharacter 𝔪 η = χ := by
  refine ⟨fun h ↦ exists_ofRayClassCharacter_eq_of_isOpen_ker (isOpen_ker_of_isFiniteOrder h), ?_⟩
  rintro ⟨𝔪, η, rfl⟩
  exact isFiniteOrder_ofRayClassCharacter η

/-- **A Hecke character has finite order exactly when its kernel is open.** -/
theorem isFiniteOrder_iff_isOpen_ker (χ : HeckeCharacter K) :
    χ.IsFiniteOrder ↔
      IsOpen ((χ : IdeleClassGroup (𝓞 K) K →* ℂˣ).ker : Set (IdeleClassGroup (𝓞 K) K)) := by
  refine ⟨isOpen_ker_of_isFiniteOrder, fun h ↦ ?_⟩
  obtain ⟨𝔪, η, rfl⟩ := exists_ofRayClassCharacter_eq_of_isOpen_ker h
  exact isFiniteOrder_ofRayClassCharacter η

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

end HeckeCharacter

end TauCeti.GlobalNumberFields
