/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Bicategory.CatEnriched

/-!
# Invertible `2`-cells of `Cat`-enriched ordinary categories

In the strict bicategory `CatEnrichedOrdinary C` of a `Cat`-enriched ordinary category `C`, the
`2`-cells `f ⟶ g` are by definition the morphisms `homEquiv f ⟶ homEquiv g` of the hom-category.
Accordingly, the invertible `2`-cells `f ≅ g` are the isomorphisms `homEquiv f ≅ homEquiv g`
(`CategoryTheory.CatEnrichedOrdinary.isoEquiv`). This identifies, for instance, the invertible
natural transformations of the bicategory of quasicategories with the isomorphisms of the homotopy
categories of their functor quasicategories.

## Main declarations

* `CategoryTheory.CatEnrichedOrdinary.isoEquiv`: invertible `2`-cells `f ≅ g` are isomorphisms
  `homEquiv f ≅ homEquiv g`.
-/

public section

universe v u u' v'

namespace CategoryTheory.CatEnrichedOrdinary

variable {C : Type u} [Category.{v} C] [EnrichedOrdinaryCategory Cat.{v', u'} C]

/-- The invertible `2`-cells `f ≅ g` of `CatEnrichedOrdinary C` are the isomorphisms
`homEquiv f ≅ homEquiv g` of the hom-category. -/
def isoEquiv {X Y : CatEnrichedOrdinary C} {f g : X ⟶ Y} :
    (f ≅ g) ≃ (homEquiv f ≅ homEquiv g) where
  toFun α :=
    { hom := α.hom.base
      inv := α.inv.base
      hom_inv_id := congrArg Hom.base α.hom_inv_id
      inv_hom_id := congrArg Hom.base α.inv_hom_id }
  invFun β :=
    { hom := .mk β.hom
      inv := .mk β.inv
      hom_inv_id := Hom.ext _ _ β.hom_inv_id
      inv_hom_id := Hom.ext _ _ β.inv_hom_id }
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
lemma isoEquiv_apply_hom {X Y : CatEnrichedOrdinary C} {f g : X ⟶ Y} (α : f ≅ g) :
    (isoEquiv α).hom = α.hom.base := (rfl)

@[simp]
lemma isoEquiv_apply_inv {X Y : CatEnrichedOrdinary C} {f g : X ⟶ Y} (α : f ≅ g) :
    (isoEquiv α).inv = α.inv.base := (rfl)

@[simp]
lemma isoEquiv_symm_apply_hom {X Y : CatEnrichedOrdinary C} {f g : X ⟶ Y}
    (β : homEquiv f ≅ homEquiv g) : (isoEquiv.symm β).hom = .mk β.hom := (rfl)

@[simp]
lemma isoEquiv_symm_apply_inv {X Y : CatEnrichedOrdinary C} {f g : X ⟶ Y}
    (β : homEquiv f ≅ homEquiv g) : (isoEquiv.symm β).inv = .mk β.inv := (rfl)

end CategoryTheory.CatEnrichedOrdinary
