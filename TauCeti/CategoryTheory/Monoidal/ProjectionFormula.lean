/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Category

/-!
# Naturality of a projection formula

A natural projection isomorphism `L (G X ⊗ Y) ≅ X ⊗ L Y` has an inverse natural in both
variables. The tensor-form equation below is used when lifting the projection formula to
homological complexes, in particular to check compatibility with the tensor differential.
-/

public section

open CategoryTheory MonoidalCategory

namespace CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D]
  [MonoidalCategory C] [MonoidalCategory D]
  (L : D ⥤ C) (G : C ⥤ D)
  (e : G.prod (𝟭 D) ⋙ tensor D ⋙ L ≅ (𝟭 C).prod L ⋙ tensor C)

/-- The inverse of a natural projection isomorphism is natural in both tensor factors. -/
@[reassoc]
lemma projectionFormula_inv_naturality {X X' : C} {Y Y' : D}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    (f ⊗ₘ L.map g) ≫ (e.app (X', Y')).inv =
      (e.app (X, Y)).inv ≫ L.map (G.map f ⊗ₘ g) := by
  simpa only [comp_obj, prod_obj, id_obj, comp_map, prod_map, id_map, tensor_map,
    Iso.app_inv] using e.inv.naturality (X := (X, Y)) (Y := (X', Y')) (f, g)

end CategoryTheory.Functor
