/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Bicategory.LocallyInduced.Basic
public import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic

/-!
# Adjunctions in locally induced bicategories

Chosen composite comparisons transfer specified adjunctions between generating arrows and
their images in the ambient bicategory. The transfer preserves the full unit and counit data,
with the comparisons inserted at their boundaries. It is inverse to Mathlib's action of the
inclusion pseudofunctor on adjunctions.

## References

* A. D. Fairbanks and M. Shulman, *Doubly weak double categories*, Applied Categorical
  Structures **34** (2026), article 26; Proposition 2.7.
-/

public section

universe w v u u' v'

namespace TauCeti.BicategoryInductionData

open CategoryTheory
open scoped Bicategory

variable {B : Type u} [Bicategory.{w, v} B] {O : Type u'} {H : Quiver.{v'} O}
  (I : BicategoryInductionData B O H) {a b : I.Obj} {f : a ⟶ b} {g : b ⟶ a}

/-- Lift an adjunction between the images of two generators to the induced bicategory. -/
def liftAdjunction (adj : I.map f ⊣ I.map g) : f ⊣ g where
  unit := InducedCategory.homMk ((I.mapUnit a.obj).hom ≫ adj.unit ≫ (I.mapMul f g).inv)
  counit := InducedCategory.homMk ((I.mapMul g f).hom ≫ adj.counit ≫ (I.mapUnit b.obj).inv)
  left_triangle := by
    apply InducedCategory.hom_ext
    dsimp [Bicategory.leftZigzag, bicategoricalComp, Bicategory.whiskerLeft,
      Bicategory.whiskerRight, Bicategory.associator, Bicategory.leftUnitor,
      Bicategory.rightUnitor]
    dsimp only [CategoryStruct.comp, CategoryStruct.id, InducedCategory.homMk]
    simp [InducedCategory.isoMk, InducedCategory.homMk, CategoryStruct.id]
    simpa [Bicategory.leftZigzag, Bicategory.rightZigzag, bicategoricalComp] using congrArg
      (fun θ ↦ (I.mapMul (I.unit a.obj) f).hom ≫ (I.mapUnit a.obj).hom ▷ I.map f ≫ θ ≫
        I.map f ◁ (I.mapUnit b.obj).inv ≫ (I.mapMul f (I.unit b.obj)).inv) adj.left_triangle
  right_triangle := by
    apply InducedCategory.hom_ext
    dsimp [Bicategory.rightZigzag, bicategoricalComp, Bicategory.whiskerLeft,
      Bicategory.whiskerRight, Bicategory.associator, Bicategory.leftUnitor,
      Bicategory.rightUnitor]
    dsimp only [CategoryStruct.comp, CategoryStruct.id, InducedCategory.homMk]
    simp [InducedCategory.isoMk, InducedCategory.homMk, CategoryStruct.id]
    simpa [Bicategory.leftZigzag, Bicategory.rightZigzag, bicategoricalComp] using congrArg
      (fun θ ↦ (I.mapMul g (I.unit a.obj)).hom ≫ I.map g ◁ (I.mapUnit a.obj).hom ≫ θ ≫
        (I.mapUnit b.obj).inv ▷ I.map g ≫ (I.mapMul (I.unit b.obj) g).inv) adj.right_triangle

/-- The lifted unit inserts the chosen identity comparison and reverses the composite
comparison. -/
@[simp]
theorem liftAdjunction_unit_hom (adj : I.map f ⊣ I.map g) :
    (I.liftAdjunction adj).unit.hom =
      (I.mapUnit a.obj).hom ≫ adj.unit ≫ (I.mapMul f g).inv :=
  (rfl)

/-- The lifted counit inserts the composite comparison and reverses the identity comparison. -/
@[simp]
theorem liftAdjunction_counit_hom (adj : I.map f ⊣ I.map g) :
    (I.liftAdjunction adj).counit.hom =
      (I.mapMul g f).hom ≫ adj.counit ≫ (I.mapUnit b.obj).inv :=
  (rfl)

/-- Mapping a lifted adjunction recovers its specified ambient unit and counit. -/
@[simp]
theorem mapAdjunction_liftAdjunction (adj : I.map f ⊣ I.map g) :
    I.inclusion.mapAdjunction (I.liftAdjunction adj) = adj := by
  ext
  -- Normalize the ambient hom-category at the inclusion's object map; otherwise simp sees
  -- the unreduced object wrapper in its category instance.
  · change (I.mapUnit a.obj).inv ≫
        ((I.mapUnit a.obj).hom ≫ adj.unit ≫ (I.mapMul f g).inv) ≫
          (I.mapMul f g).hom = adj.unit
    simp [Category.assoc]
  · change (I.mapMul g f).inv ≫
        ((I.mapMul g f).hom ≫ adj.counit ≫ (I.mapUnit b.obj).inv) ≫
          (I.mapUnit b.obj).hom = adj.counit
    simp [Category.assoc]

/-- Lifting the image of an adjunction recovers the full specified adjunction. -/
@[simp]
theorem liftAdjunction_mapAdjunction (adj : f ⊣ g) :
    I.liftAdjunction (I.inclusion.mapAdjunction adj) = adj := by
  ext <;> apply InducedCategory.hom_ext <;>
    dsimp [Pseudofunctor.mapAdjunction, inclusion, liftAdjunction, CategoryStruct.comp,
      CategoryStruct.id] <;> simp [Category.assoc]

/-- Specified adjunctions between generators are equivalent to specified adjunctions between
their images in the ambient bicategory. The forward map is Mathlib's action of the inclusion
pseudofunctor, and the inverse conjugates the unit and counit by the chosen comparisons. -/
def adjunctionEquiv : (f ⊣ g) ≃ (I.map f ⊣ I.map g) where
  toFun := I.inclusion.mapAdjunction
  invFun := I.liftAdjunction
  left_inv := I.liftAdjunction_mapAdjunction
  right_inv := I.mapAdjunction_liftAdjunction

@[simp]
theorem adjunctionEquiv_apply (adj : f ⊣ g) :
    I.adjunctionEquiv adj = I.inclusion.mapAdjunction adj :=
  (rfl)

@[simp]
theorem adjunctionEquiv_symm_apply (adj : I.map f ⊣ I.map g) :
    I.adjunctionEquiv.symm adj = I.liftAdjunction adj :=
  (rfl)

end TauCeti.BicategoryInductionData
