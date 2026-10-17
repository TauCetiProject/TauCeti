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

More generally, a point `φ : Y ⟶ G` with values in an object `Y` acts on `G ⊗ Y`, the base change
of `G` to `Y`, by `(g, y) ↦ (φ y * g, y)`. For a group scheme `G` over `S` and a scheme `Y` over
`S`, this is left translation of `G ×_S Y` over `Y` by the `Y`-point of `G ×_S Y` given by `φ`; it
moves points of `G` that are not defined over the base, such as the tautological point `Y = G`,
`φ = 𝟙 G`.

## Main definitions

* `TauCeti.leftTranslation x`: left translation by `x`, as an isomorphism `G ≅ G`.
* `TauCeti.leftTranslationProd φ`: left translation by a point `φ : Y ⟶ G`, as an isomorphism
  `G ⊗ Y ≅ G ⊗ Y`.

## Main results

* `TauCeti.comp_leftTranslation_hom`: translation by `x` sends a point `f` to `x * f`.
* `TauCeti.leftTranslation_hom_comp`: a homomorphism `i` intertwines translation by `x` with
  translation by `x ≫ i`.
* `TauCeti.lift_comp_leftTranslationProd_hom`: translation by `φ` sends a point `(a, b)` of
  `G ⊗ Y` to `((b ≫ φ) * a, b)`.
* `TauCeti.leftTranslationProd_hom_comp_whiskerRight`: a homomorphism `i` intertwines translation
  by `φ` with translation by `φ ≫ i`.
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

/-! ### Translation by a point with values in an object -/

section Prod

variable {Y : C}

/-- **Left translation by a point with values in `Y`.** For a point `φ : Y ⟶ G`, the automorphism
`(g, y) ↦ (φ y * g, y)` of `G ⊗ Y`, the base change of `G` to `Y`. Its inverse is the translation
by `φ⁻¹`. -/
noncomputable def leftTranslationProd (φ : Y ⟶ G) : G ⊗ Y ≅ G ⊗ Y where
  hom := lift ((snd G Y ≫ φ) * fst G Y) (snd G Y)
  inv := lift ((snd G Y ≫ φ⁻¹) * fst G Y) (snd G Y)
  hom_inv_id := by ext <;> simp [MonObj.comp_mul, GrpObj.comp_inv, ← _root_.mul_assoc]
  inv_hom_id := by ext <;> simp [MonObj.comp_mul, GrpObj.comp_inv, ← _root_.mul_assoc]

/-- Translation by `φ` is `(g, y) ↦ (φ y * g, y)`. -/
theorem leftTranslationProd_hom (φ : Y ⟶ G) :
    (leftTranslationProd φ).hom = lift ((snd G Y ≫ φ) * fst G Y) (snd G Y) :=
  (rfl)

/-- The inverse of translation by `φ` is translation by `φ⁻¹`. -/
@[simp]
theorem leftTranslationProd_inv (φ : Y ⟶ G) :
    (leftTranslationProd φ).inv = (leftTranslationProd φ⁻¹).hom :=
  (rfl)

/-- Translation by `φ` sends a point `(a, b)` of `G ⊗ Y` to `((b ≫ φ) * a, b)`. -/
@[reassoc (attr := simp)]
theorem lift_comp_leftTranslationProd_hom {Z : C} (a : Z ⟶ G) (b : Z ⟶ Y) (φ : Y ⟶ G) :
    lift a b ≫ (leftTranslationProd φ).hom = lift ((b ≫ φ) * a) b := by
  simp [leftTranslationProd_hom, MonObj.comp_mul]

/-- The first component of the translate of `(g, y)` by `φ` is `φ y * g`. -/
@[reassoc (attr := simp)]
theorem leftTranslationProd_hom_fst (φ : Y ⟶ G) :
    (leftTranslationProd φ).hom ≫ fst G Y = (snd G Y ≫ φ) * fst G Y := by
  simp [leftTranslationProd_hom]

/-- Translation by `φ` lies over `Y`. -/
@[reassoc (attr := simp)]
theorem leftTranslationProd_hom_snd (φ : Y ⟶ G) :
    (leftTranslationProd φ).hom ≫ snd G Y = snd G Y := by
  simp [leftTranslationProd_hom]

/-- A homomorphism of group objects `i : G ⟶ H` intertwines translation by a point `φ` of `G` with
translation by its image `φ ≫ i`. -/
@[reassoc]
theorem leftTranslationProd_hom_comp_whiskerRight {H : C} [GrpObj H] (i : G ⟶ H) [IsMonHom i]
    (φ : Y ⟶ G) :
    (leftTranslationProd φ).hom ≫ i ▷ Y = i ▷ Y ≫ (leftTranslationProd (φ ≫ i)).hom := by
  ext <;> simp [leftTranslationProd_hom, MonObj.mul_comp, MonObj.comp_mul]

end Prod

end TauCeti
