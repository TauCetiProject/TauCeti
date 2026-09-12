/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.SeparableDegree
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

The existence of a common refinement for two arbitrary chosen extensions is deliberately not
asserted here. Constructing it requires the compositum together with a compatible choice of a
place, which is the next arithmetic step in the roadmap.
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
  local_isLocal : IsLocalHom localMap.toRingHom

attribute [instance] Hom.local_isLocal

namespace Hom

@[ext (iff := false)]
lemma ext {E F : FiniteDVRExtension R K} {f g : Hom E F}
    (hfield : f.field = g.field) (hlocal : f.localMap = g.localMap) : f = g := by
  cases f
  cases g
  cases hfield
  cases hlocal
  congr

/-- The identity map of a chosen finite DVR extension. -/
def id (E : FiniteDVRExtension R K) : Hom E E where
  field := AlgHom.id K E.extensionField
  localMap := AlgHom.id R E.localRing
  field_local x := by simp
  local_isLocal := by
    have h : (AlgHom.id R E.localRing).toRingHom = RingHom.id E.localRing := by
      ext x
      simp
    rw [h]
    exact isLocalHom_id _

/-- Composition of maps of chosen finite DVR extensions. -/
def comp {E F G : FiniteDVRExtension R K} (f : Hom E F) (g : Hom F G) : Hom E G where
  field := g.field.comp f.field
  localMap := g.localMap.comp f.localMap
  field_local x := by
    simp only [AlgHom.comp_apply]
    rw [f.field_local x, g.field_local (f.localMap x)]
  local_isLocal := by
    let _ : IsLocalHom g.localMap.toRingHom := g.local_isLocal
    let _ : IsLocalHom f.localMap.toRingHom := f.local_isLocal
    have h : (g.localMap.comp f.localMap).toRingHom =
        g.localMap.toRingHom.comp f.localMap.toRingHom := by
      ext x
      rfl
    rw [h]
    exact RingHom.isLocalHom_comp _ _

lemma id_comp {E F : FiniteDVRExtension R K} (f : Hom E F) : comp (id E) f = f := by
  apply ext
  · ext x
    simp [id, comp]
  · ext x
    simp [id, comp]

lemma comp_id {E F : FiniteDVRExtension R K} (f : Hom E F) : comp f (id F) = f := by
  apply ext
  · ext x
    simp [id, comp]
  · ext x
    simp [id, comp]

lemma assoc {E F G H : FiniteDVRExtension R K} (f : Hom E F) (g : Hom F G) (h : Hom G H) :
    comp (comp f g) h = comp f (comp g h) := by
  apply ext
  · ext x
    simp [comp]
  · ext x
    simp [comp]

end Hom

/-- Chosen extensions and their compatible maps form a category over a fixed `R` and `K`. -/
instance : Category (FiniteDVRExtension R K) where
  Hom := Hom
  id := Hom.id
  comp f g := Hom.comp f g
  id_comp := Hom.id_comp
  comp_id := Hom.comp_id
  assoc := Hom.assoc

/-- A finite separable field tower between two chosen DVR extensions, together with its compatible
map of chosen places. -/
structure Tower (E F : FiniteDVRExtension R K) where
  /-- The compatible map between the chosen extensions. -/
  hom : Hom E F
  /-- The algebra structure of the upper extension field over the lower one. -/
  [fieldAlgebra : Algebra E.extensionField F.extensionField]
  /-- The field algebra map is the field component of `hom`. -/
  field_algebra : algebraMap E.extensionField F.extensionField = hom.field.toRingHom
  /-- The scalar actions of `K` through `E` and directly on `F` agree. -/
  [fieldTower : IsScalarTower K E.extensionField F.extensionField]
  /-- The upper field is finite-dimensional over the lower one. -/
  [fieldFinite : FiniteDimensional E.extensionField F.extensionField]
  /-- The upper field is separable over the lower one. -/
  [fieldSeparable : Algebra.IsSeparable E.extensionField F.extensionField]

namespace Tower

variable {E F : FiniteDVRExtension R K}

variable {G : FiniteDVRExtension R K}

/-- Compose finite separable towers, including their compatible maps of chosen places. -/
def comp (T : Tower E F) (U : Tower F G) : Tower E G := by
  letI : Algebra E.extensionField F.extensionField := T.fieldAlgebra
  letI : Algebra F.extensionField G.extensionField := U.fieldAlgebra
  letI : IsScalarTower K E.extensionField F.extensionField := T.fieldTower
  letI : IsScalarTower K F.extensionField G.extensionField := U.fieldTower
  letI : Algebra E.extensionField G.extensionField :=
    (U.hom.field.toRingHom.comp T.hom.field.toRingHom).toAlgebra
  letI : IsScalarTower E.extensionField F.extensionField G.extensionField :=
    IsScalarTower.of_algebraMap_eq fun x => by
      rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply, ← U.field_algebra,
        ← T.field_algebra]
  letI : IsScalarTower K E.extensionField G.extensionField :=
    IsScalarTower.of_algebraMap_eq fun x => by
      calc
        algebraMap K G.extensionField x =
            algebraMap F.extensionField G.extensionField (algebraMap K F.extensionField x) :=
          IsScalarTower.algebraMap_apply K F.extensionField G.extensionField x
        _ = U.hom.field (algebraMap K F.extensionField x) := by
          rw [U.field_algebra]
          rfl
        _ = U.hom.field (T.hom.field (algebraMap K E.extensionField x)) := by
          rw [T.hom.field.commutes]
        _ = algebraMap E.extensionField G.extensionField (algebraMap K E.extensionField x) := by
          rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply]
          rfl
  letI : FiniteDimensional E.extensionField F.extensionField := T.fieldFinite
  letI : FiniteDimensional F.extensionField G.extensionField := U.fieldFinite
  letI : Algebra.IsSeparable E.extensionField F.extensionField := T.fieldSeparable
  letI : Algebra.IsSeparable F.extensionField G.extensionField := U.fieldSeparable
  letI : FiniteDimensional E.extensionField G.extensionField :=
    FiniteDimensional.trans E.extensionField F.extensionField G.extensionField
  letI : Algebra.IsSeparable E.extensionField G.extensionField :=
    Algebra.IsSeparable.trans E.extensionField F.extensionField G.extensionField
  refine ⟨Hom.comp T.hom U.hom, ?_⟩
  rfl

end Tower

end FiniteDVRExtension

end TauCeti
