/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-!
# Translation by a point of a group object

Let `G` be a group object in a cartesian monoidal category `C`. A global point `x : 𝟙_ C ⟶ G`
acts on `G` by left translation `y ↦ x * y`. In terms of points with values in an object `Y`, the
translation sends `f : Y ⟶ G` to the product of the constant point `toUnit Y ≫ x` and `f`. It is
an automorphism of `G`, with inverse the translation by `x⁻¹`, and a homomorphism of group
objects `i : H ⟶ G` intertwines translation by `x` on `H` with translation by `x ≫ i` on `G`.

For a group scheme `G` over `S`, these are the translations of `G` by its `S`-points, which move
closed subschemes of `G` around; a closed subgroup scheme is stable under translation by its own
points.

## Main definitions

* `TauCeti.leftTranslation x`: left translation by `x`, as an isomorphism `G ≅ G`.

## Main results

* `TauCeti.comp_leftTranslation_hom`: translation by `x` sends a point `f` to `x * f`.
* `TauCeti.leftTranslation_hom_comp`: a homomorphism `i` intertwines translation by `x` with
  translation by `x ≫ i`.
-/

public section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj

namespace TauCeti

universe u v

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] {G : C} [GrpObj G]

/-- Translating by `x` and then by `y` is translating by `y * x`. -/
private theorem translate_comp_translate (x y : 𝟙_ C ⟶ G) :
    ((toUnit G ≫ x) * 𝟙 G) ≫ ((toUnit G ≫ y) * 𝟙 G) = (toUnit G ≫ (y * x)) * 𝟙 G := by
  rw [MonObj.comp_mul, comp_toUnit_assoc, Category.comp_id, ← _root_.mul_assoc,
    ← MonObj.comp_mul]

/-- **Left translation** `y ↦ x * y` on a group object `G` by a global point `x : 𝟙_ C ⟶ G`, as an
automorphism of `G`. Its inverse is the translation by `x⁻¹`. -/
noncomputable def leftTranslation (x : 𝟙_ C ⟶ G) : G ≅ G where
  hom := (toUnit G ≫ x) * 𝟙 G
  inv := (toUnit G ≫ x⁻¹) * 𝟙 G
  hom_inv_id := by simp [translate_comp_translate]
  inv_hom_id := by simp [translate_comp_translate]

/-- Translation by `x` is the product of the constant point `x` and the identity of `G`. -/
theorem leftTranslation_hom (x : 𝟙_ C ⟶ G) : (leftTranslation x).hom = (toUnit G ≫ x) * 𝟙 G :=
  (rfl)

/-- The inverse of translation by `x` is translation by `x⁻¹`. -/
@[simp]
theorem leftTranslation_inv (x : 𝟙_ C ⟶ G) : (leftTranslation x).inv = (leftTranslation x⁻¹).hom :=
  (rfl)

/-- Translation by `x` sends a point `f : Y ⟶ G` to `x * f`. -/
@[reassoc (attr := simp)]
theorem comp_leftTranslation_hom {Y : C} (f : Y ⟶ G) (x : 𝟙_ C ⟶ G) :
    f ≫ (leftTranslation x).hom = (toUnit Y ≫ x) * f := by
  rw [leftTranslation_hom, MonObj.comp_mul, comp_toUnit_assoc, Category.comp_id]

/-- A homomorphism of group objects `i : H ⟶ G` intertwines translation by a point `x` of `H` with
translation by its image `x ≫ i`. -/
theorem leftTranslation_hom_comp {H : C} [GrpObj H] (i : H ⟶ G) [IsMonHom i] (x : 𝟙_ C ⟶ H) :
    (leftTranslation x).hom ≫ i = i ≫ (leftTranslation (x ≫ i)).hom := by
  rw [leftTranslation_hom, MonObj.mul_comp, Category.assoc, Category.id_comp,
    comp_leftTranslation_hom]

end TauCeti
