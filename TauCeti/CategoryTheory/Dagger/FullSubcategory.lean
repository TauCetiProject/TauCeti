/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Dagger.Functor
public import TauCeti.CategoryTheory.Linear.FullSubcategory

/-!
# Induced and full subcategories of dagger categories

Pulling back a dagger category along an object map `F : D → C` gives a dagger structure on
`CategoryTheory.InducedCategory C F`, and in particular on `P.FullSubcategory` for any
`P : CategoryTheory.ObjectProperty C`. Additive and conjugate-linear compatibilities transfer
along the inclusion functors `inducedFunctor F` and `P.ι`, which preserve daggers.
-/

public section

open CategoryTheory TauCeti

universe w v u u'

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [DaggerCategory C]

section InducedCategory

variable {D : Type u'} (F : D → C)

instance InducedCategory.instDaggerCategory : DaggerCategory (InducedCategory C F) where
  dagger f := InducedCategory.homMk (dagger f.hom)
  dagger_id _ := by ext; simp
  dagger_comp _ _ := by ext; simp
  dagger_dagger _ := by ext; simp

variable {F}

/-- The underlying arrow of a dagger in `InducedCategory C F` is the dagger of the underlying
arrow. -/
@[simp, grind =] theorem InducedCategory.dagger_hom {X Y : InducedCategory C F} (f : X ⟶ Y) :
    (dagger f).hom = dagger f.hom := (rfl)

/-- Wrapping a dagger arrow in `InducedCategory C F` commutes with `dagger`. -/
@[simp, grind =] theorem InducedCategory.homMk_dagger {X Y : InducedCategory C F}
    (f : F X ⟶ F Y) : InducedCategory.homMk (dagger f) = dagger (InducedCategory.homMk f) := (rfl)

/-- Unitarity in `InducedCategory C F` agrees with unitarity in `C`. -/
@[simp] theorem InducedCategory.isUnitary_iff {X Y : InducedCategory C F} (f : X ⟶ Y) :
    IsUnitary f ↔ IsUnitary f.hom := by
  simp [TauCeti.isUnitary_iff, InducedCategory.hom_ext_iff]

instance InducedCategory.instDaggerPreadditive [Preadditive C] [DaggerPreadditive C] :
    DaggerPreadditive (InducedCategory C F) where
  dagger_add f g := InducedCategory.hom_ext (dagger_add f.hom g.hom)

instance InducedCategory.instDaggerLinear {R : Type w} [Semiring R] [Star R] [Preadditive C]
    [Linear R C] [DaggerLinear R C] :
    DaggerLinear R (InducedCategory C F) where
  dagger_smul r f := InducedCategory.hom_ext (dagger_smul r f.hom)

instance instPreservesDaggerInducedFunctor : (inducedFunctor F).PreservesDagger where
  map_dagger _ := (rfl)

end InducedCategory

namespace ObjectProperty

variable {P : ObjectProperty C}

instance instDaggerCategoryFullSubcategory (P : ObjectProperty C) :
    DaggerCategory P.FullSubcategory :=
  InducedCategory.instDaggerCategory ObjectProperty.FullSubcategory.obj

/-- The underlying arrow of a dagger in `P.FullSubcategory` is the dagger of the underlying
arrow. -/
@[simp, grind =] theorem dagger_hom {X Y : P.FullSubcategory} (f : X ⟶ Y) :
    (dagger f).hom = dagger f.hom := (rfl)

/-- Constructing a morphism in `P.FullSubcategory` commutes with `dagger`. -/
@[simp, grind =] theorem homMk_dagger {X Y : P.FullSubcategory} (f : X.obj ⟶ Y.obj) :
    P.homMk (dagger f) = dagger (P.homMk f) := (rfl)

/-- Unitarity in `P.FullSubcategory` agrees with unitarity in `C`. -/
@[simp] theorem isUnitary_iff {X Y : P.FullSubcategory} (f : X ⟶ Y) :
    IsUnitary f ↔ IsUnitary f.hom := by
  simp [TauCeti.isUnitary_iff, ObjectProperty.hom_ext_iff]

instance instDaggerPreadditiveFullSubcategory (P : ObjectProperty C) [Preadditive C]
    [DaggerPreadditive C] : DaggerPreadditive P.FullSubcategory where
  dagger_add _ _ := by ext; simp

instance instDaggerLinearFullSubcategory (P : ObjectProperty C) {R : Type w} [Semiring R]
    [Star R] [Preadditive C] [Linear R C] [DaggerLinear R C] :
    DaggerLinear R P.FullSubcategory where
  dagger_smul _ _ := by ext; simp

instance instPreservesDaggerι (P : ObjectProperty C) : P.ι.PreservesDagger where
  map_dagger _ := (rfl)

end ObjectProperty

end CategoryTheory
