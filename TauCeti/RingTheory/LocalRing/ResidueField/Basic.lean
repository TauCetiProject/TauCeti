/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import TauCeti.RingTheory.LocalRing.RingHom

/-!
# Coercions of scalar-tower algebra maps on residue fields

Mathlib defines `IsLocalRing.ResidueField.mapAlgHom` and `IsLocalRing.ResidueField.mapAlgHom'` by
upgrading `IsLocalRing.ResidueField.map` to algebra homomorphisms over the base ring and its
residue field, respectively. Along a scalar tower `R → A → B` with `algebraMap A B` local,
`IsScalarTower.toAlgHom R A B` is local (`TauCeti.IsScalarTower.isLocalHom_toAlgHom`), and this
file records `@[simp]` lemmas identifying the underlying functions of the induced residue-field
algebra maps with `IsLocalRing.ResidueField.map (algebraMap A B)`.

## Main results

* `TauCeti.IsLocalRing.ResidueField.coe_mapAlgHom_toAlgHom`: forgetting the `R`-algebra structure
  on `IsLocalRing.ResidueField.mapAlgHom (IsScalarTower.toAlgHom R A B)` gives
  `IsLocalRing.ResidueField.map (algebraMap A B)`.
* `TauCeti.IsLocalRing.ResidueField.coe_mapAlgHom'_toAlgHom`: forgetting the `ResidueField R`-
  algebra structure on `IsLocalRing.ResidueField.mapAlgHom' (IsScalarTower.toAlgHom R A B)` gives
  `IsLocalRing.ResidueField.map (algebraMap A B)`.
-/

public section

open IsLocalRing

namespace TauCeti.IsLocalRing.ResidueField

/-- In a scalar tower `R → A → B`,
`IsLocalRing.ResidueField.mapAlgHom (IsScalarTower.toAlgHom R A B)` has underlying function
`IsLocalRing.ResidueField.map (algebraMap A B)`. -/
@[simp]
theorem coe_mapAlgHom_toAlgHom {R A B : Type*} [CommRing R] [CommRing A] [IsLocalRing A]
    [CommRing B] [IsLocalRing B] [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [IsLocalHom (algebraMap A B)] :
    ⇑(ResidueField.mapAlgHom (IsScalarTower.toAlgHom R A B)) =
      ⇑(ResidueField.map (algebraMap A B)) := by
  ext x
  obtain ⟨a, rfl⟩ := residue_surjective x
  rw [ResidueField.mapAlgHom_residue, IsScalarTower.toAlgHom_apply, ResidueField.map_residue]

/-- In a scalar tower `R → A → B`,
`IsLocalRing.ResidueField.mapAlgHom' (IsScalarTower.toAlgHom R A B)` has underlying function
`IsLocalRing.ResidueField.map (algebraMap A B)`. -/
@[simp]
theorem coe_mapAlgHom'_toAlgHom {R A B : Type*} [CommRing R] [IsLocalRing R]
    [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [IsLocalHom (algebraMap R A)] [IsLocalHom (algebraMap R B)] [IsLocalHom (algebraMap A B)] :
    ⇑(ResidueField.mapAlgHom' (IsScalarTower.toAlgHom R A B)) =
      ⇑(ResidueField.map (algebraMap A B)) := by
  ext x
  obtain ⟨a, rfl⟩ := residue_surjective x
  rw [ResidueField.mapAlgHom'_residue, IsScalarTower.toAlgHom_apply, ResidueField.map_residue]

end TauCeti.IsLocalRing.ResidueField
