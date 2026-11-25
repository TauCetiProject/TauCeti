/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Over categories of full subcategories

For a property `P` of objects of `C` and an object `X` of the full subcategory of `P`, the
category of objects of the full subcategory over `X` is equivalent to the full subcategory of
`Over X.obj` on the objects whose source satisfies `P`. The comparison keeps the underlying
objects and morphisms of `C`.
-/

public section

namespace CategoryTheory.ObjectProperty

variable {C : Type*} [Category* C] (P : ObjectProperty C) (X : P.FullSubcategory)

/-- The over category of an object `X` of the full subcategory of `P` is equivalent to the full
subcategory of `Over X.obj` on the objects whose source satisfies `P`. -/
-- The functor and inverse are exposed so that the underlying objects and morphisms of `C` are
-- definitionally unchanged.
@[expose, simps! functor_obj_obj functor_map_hom inverse_obj_left_obj inverse_obj_hom_hom
  inverse_map_left_hom]
def overFullSubcategoryEquiv :
    Over X ≌ (P.inverseImage (Over.forget X.obj)).FullSubcategory :=
  Equivalence.mk
    ((P.inverseImage (Over.forget X.obj)).lift (Over.post P.ι) fun Y ↦ Y.left.property)
    { obj Z := Over.mk (Y := (⟨Z.obj.left, Z.property⟩ : P.FullSubcategory)) (P.homMk Z.obj.hom)
      map f := Over.homMk (P.homMk f.hom.left) (by ext; exact Over.w f.hom) }
    (NatIso.ofComponents (fun _ ↦ Over.isoMk (Iso.refl _) (Category.id_comp _))
      (fun _ ↦ by ext; exact (Category.comp_id _).trans (Category.id_comp _).symm))
    (NatIso.ofComponents (fun _ ↦ isoMk _ (Over.isoMk (Iso.refl _) (Category.id_comp _)))
      (fun _ ↦ by ext; exact (Category.comp_id _).trans (Category.id_comp _).symm))

end CategoryTheory.ObjectProperty
