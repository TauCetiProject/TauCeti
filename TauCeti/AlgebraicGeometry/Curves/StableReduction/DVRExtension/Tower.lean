/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Category.Basic
public import TauCeti.AlgebraicGeometry.Curves.StableReduction.DVRExtension.Basic

/-!
# Maps and towers of chosen finite DVR extensions

The chosen place in a finite extension of a DVR is part of the data: a field embedding alone does
not say how the corresponding local rings are related. This file therefore packages a compatible
field embedding and local-ring map, with the square between them as an explicit law. These maps
form the category of chosen extensions. It also records the finite separable field towers that
occur between such extensions; these maps are the compatible pieces used by later
common-refinement arguments.

The existence of a common refinement for two arbitrary chosen extensions is not asserted here.
Constructing it requires the compositum together with a compatible choice of a place.

## References

This module implements the finite and separable tower and compatible-embedding target in Layer 0
of the StableReduction roadmap:
https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/StableReduction/README.md
-/

public section

universe u

namespace TauCeti

open CategoryTheory

namespace FiniteDVRExtension

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- A map of chosen finite DVR extensions.

`field` embeds the extension fields over `K`, while `localMap` embeds the selected local rings
over `R`. The commutative-square law says that the field embedding restricts to the local-ring map.
The local map is local, so the chosen closed point is respected rather than merely mapping one
subring into another.
-/
structure Hom (E F : FiniteDVRExtension R K) where
  /-- The embedding of the extension fields over `K`. -/
  field : E.extensionField →ₐ[K] F.extensionField
  /-- The map of chosen local rings over `R`. -/
  localMap : E.localRing →ₐ[R] F.localRing
  /-- The field and local-ring maps commute with the fraction maps. -/
  field_local : ∀ x,
    field (algebraMap E.localRing E.extensionField x) =
      algebraMap F.localRing F.extensionField (localMap x)
  /-- The map preserves the chosen maximal ideals. -/
  isLocalHom_localMap : IsLocalHom localMap.toRingHom

attribute [instance] Hom.isLocalHom_localMap
attribute [simp] Hom.field_local

namespace Hom

/-- Two maps are equal when their field and local-ring components agree. -/
@[ext (iff := false)]
lemma ext {E F : FiniteDVRExtension R K} {f g : Hom E F}
    (hfield : f.field = g.field) (hlocal : f.localMap = g.localMap) : f = g := by
  cases f
  cases g
  cases hfield
  cases hlocal
  congr

end Hom

/-- Chosen extensions and their compatible maps form a category over a fixed `R` and `K`. -/
instance finiteDVRExtensionCategory : Category (FiniteDVRExtension R K) where
  Hom := Hom
  id E :=
    { field := AlgHom.id K E.extensionField
      localMap := AlgHom.id R E.localRing
      field_local := fun x ↦ by simp
      isLocalHom_localMap := by
        have h : (AlgHom.id R E.localRing).toRingHom = RingHom.id E.localRing := by
          ext x
          simp
        rw [h]
        exact isLocalHom_id _ }
  comp f g :=
    { field := g.field.comp f.field
      localMap := g.localMap.comp f.localMap
      field_local := fun x ↦ by
        simp only [AlgHom.comp_apply]
        rw [f.field_local x, g.field_local (f.localMap x)]
      isLocalHom_localMap := by
        let _ : IsLocalHom g.localMap.toRingHom := g.isLocalHom_localMap
        let _ : IsLocalHom f.localMap.toRingHom := f.isLocalHom_localMap
        have h : (g.localMap.comp f.localMap).toRingHom =
            g.localMap.toRingHom.comp f.localMap.toRingHom := by
          ext x
          rfl
        rw [h]
        exact RingHom.isLocalHom_comp _ _ }
  id_comp := by
    intro E F f
    apply Hom.ext
    · ext x
      rfl
    · ext x
      rfl
  comp_id := by
    intro E F f
    apply Hom.ext
    · ext x
      rfl
    · ext x
      rfl
  assoc := by
    intro E F G H f g h
    apply Hom.ext
    · ext x
      rfl
    · ext x
      rfl

namespace Hom

@[simp] lemma id_field (E : FiniteDVRExtension R K) :
    (𝟙 E : E ⟶ E).field = AlgHom.id K E.extensionField := by
  simp [CategoryStruct.id]

@[simp] lemma id_localMap (E : FiniteDVRExtension R K) :
    (𝟙 E : E ⟶ E).localMap = AlgHom.id R E.localRing := by
  simp [CategoryStruct.id]

@[simp] lemma comp_field {E F G : FiniteDVRExtension R K} (f : E ⟶ F) (g : F ⟶ G) :
    (f ≫ g).field = g.field.comp f.field := by
  rfl

@[simp] lemma comp_localMap {E F G : FiniteDVRExtension R K} (f : E ⟶ F) (g : F ⟶ G) :
    (f ≫ g).localMap = g.localMap.comp f.localMap := by
  rfl

end Hom

/-- The algebra structure induced by the compatible field embedding. -/
@[instance_reducible]
def Hom.fieldAlgebra {E F : FiniteDVRExtension R K} (T : Hom E F) :
    Algebra E.extensionField F.extensionField :=
  T.field.toRingHom.toAlgebra

/-- The scalar tower induced by the compatible field embedding. -/
instance Hom.fieldTower {E F : FiniteDVRExtension R K} (T : Hom E F) :
    letI : Algebra E.extensionField F.extensionField := T.fieldAlgebra
    IsScalarTower K E.extensionField F.extensionField := by
  let algebra : Algebra E.extensionField F.extensionField := T.fieldAlgebra
  exact @IsScalarTower.of_algebraMap_eq K E.extensionField F.extensionField _ _ _
    inferInstance algebra inferInstance (by
      intro x
      simp [RingHom.algebraMap_toAlgebra, AlgHom.commutes])

/-- Finiteness of the upper field over the lower field follows from its finiteness over `K`. -/
instance Hom.fieldFinite {E F : FiniteDVRExtension R K} (T : Hom E F) :
    letI : Algebra E.extensionField F.extensionField := T.fieldAlgebra
    FiniteDimensional E.extensionField F.extensionField := by
  let algebra : Algebra E.extensionField F.extensionField := T.fieldAlgebra
  let tower : @IsScalarTower K E.extensionField F.extensionField
      (@Algebra.toSMul K E.extensionField _ _ inferInstance)
      (@Algebra.toSMul E.extensionField F.extensionField _ _ algebra)
      (@Algebra.toSMul K F.extensionField _ _ inferInstance) := T.fieldTower
  exact @Module.Finite.of_restrictScalars_finite K E.extensionField F.extensionField
    _ _ _ (@Algebra.toModule K F.extensionField _ _ inferInstance)
      (@Algebra.toModule E.extensionField F.extensionField _ _ algebra)
      (@Algebra.toSMul K E.extensionField _ _ inferInstance) tower inferInstance

/-- Separability of the upper field over the lower field follows from its separability over `K`. -/
instance Hom.fieldSeparable {E F : FiniteDVRExtension R K} (T : Hom E F) :
    letI : Algebra E.extensionField F.extensionField := T.fieldAlgebra
    Algebra.IsSeparable E.extensionField F.extensionField := by
  let algebra : Algebra E.extensionField F.extensionField := T.fieldAlgebra
  let tower : @IsScalarTower K E.extensionField F.extensionField
      (@Algebra.toSMul K E.extensionField _ _ inferInstance)
      (@Algebra.toSMul E.extensionField F.extensionField _ _ algebra)
      (@Algebra.toSMul K F.extensionField _ _ inferInstance) := T.fieldTower
  exact @Algebra.isSeparable_tower_top_of_isSeparable K E.extensionField _ F.extensionField
    _ _ inferInstance inferInstance algebra tower inferInstance

end FiniteDVRExtension

end TauCeti
