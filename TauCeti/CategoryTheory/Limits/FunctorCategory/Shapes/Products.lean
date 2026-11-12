/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Products

/-!
# Naturality of the evaluation of products of functors

Mathlib's `CategoryTheory.Limits.piObjIso F d` identifies the value at `d` of a product of
functors `F j : D ⥤ C` with the product of their values at `d`. This file records that the
isomorphism is natural in `d`: under it, the value of the product on a morphism `g : d ⟶ d'` is the
product of the morphisms `(F j).map g` (`CategoryTheory.Limits.piObjIso_hom_naturality`). For
presheaves this says that the restriction maps of a product are the products of the restriction
maps.
-/

public section

universe w

namespace CategoryTheory.Limits

/-- Under `piObjIso`, the value of a product of functors on a morphism is the product of their
values on it. -/
@[reassoc]
theorem piObjIso_hom_naturality {C D : Type*} [Category* C] [Category* D] {J : Type w}
    [HasLimitsOfShape (Discrete J) C] (F : J → D ⥤ C) {d d' : D} (g : d ⟶ d') :
    (∏ᶜ F).map g ≫ (piObjIso F d').hom =
      (piObjIso F d).hom ≫ Limits.Pi.map fun j ↦ (F j).map g := by
  ext j
  simp [piObjIso_hom_comp_π]

end CategoryTheory.Limits
