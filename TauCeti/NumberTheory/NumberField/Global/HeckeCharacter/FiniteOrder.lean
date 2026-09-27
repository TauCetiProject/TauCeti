/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.HeckeCharacter.Basic
public import TauCeti.NumberTheory.NumberField.Global.Ideles.Ray.OpenSubgroup

import TauCeti.Topology.Algebra.ContinuousMonoidHom

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

end HeckeCharacter

end TauCeti.GlobalNumberFields
