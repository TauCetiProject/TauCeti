/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import TauCeti.CategoryTheory.Monoidal.Cartesian.Basic

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

Finally, a morphism `c : X ⟶ G` to a monoid object gives the **universal shift**
`G ⊗ X ⟶ G ⊗ G`, `(y, x) ↦ (y, y * c x)`, over the first factor `G`. With `c = 1` it is the
diagonal shift `(y, x) ↦ (y, y)`. It commutes with a monoidal functor `F` through the product
comparison maps, with `F.obj G` carrying the image monoid structure.

## Main definitions

* `TauCeti.rightTranslation x`: right translation by a global point, as an isomorphism.
* `TauCeti.leftTranslation x`: left translation by `x`, as an isomorphism `G ≅ G`.
* `TauCeti.leftTranslationProd φ`: left translation by a point `φ : Y ⟶ G`, as an isomorphism
  `G ⊗ Y ≅ G ⊗ Y`.
* `TauCeti.GrpObj.universalShift c`: the morphism `(y, x) ↦ (y, y * c x)`.

## Main results

* `TauCeti.comp_leftTranslation_hom`: translation by `x` sends a point `f` to `x * f`.
* `TauCeti.leftTranslation_hom_comp`: a homomorphism `i` intertwines translation by `x` with
  translation by `x ≫ i`.
* `TauCeti.lift_comp_leftTranslationProd_hom`: translation by `φ` sends a point `(a, b)` of
  `G ⊗ Y` to `((b ≫ φ) * a, b)`.
* `TauCeti.leftTranslationProd_hom_comp_whiskerRight`: a homomorphism `i` intertwines translation
  by `φ` with translation by `φ ≫ i`.
* `TauCeti.GrpObj.lift_comp_universalShift`: the universal shift on points with values in an
  object.
* `TauCeti.GrpObj.map_universalShift_comp_prodComparison`: compatibility with monoidal functors.

## References

* X. Yuan, *Arithmetic bigness and a uniform Bogomolov-type result*, arXiv:2108.05625v4, §4.6.2,
  for the universal shift.
-/

public section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj

namespace TauCeti

universe u v

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] {G : C} [GrpObj G]

/-- **Left translation** `y ↦ x * y` on a group object `G` by a global point `x : 𝟙_ C ⟶ G`, as an
automorphism of `G`. Its inverse is the translation by `x⁻¹`. -/
noncomputable def leftTranslation (x : 𝟙_ C ⟶ G) : G ≅ G where
  hom := (toUnit G ≫ x) * 𝟙 G
  inv := (toUnit G ≫ x⁻¹) * 𝟙 G
  hom_inv_id := by simp [MonObj.comp_mul, GrpObj.comp_inv, ← _root_.mul_assoc]
  inv_hom_id := by simp [MonObj.comp_mul, GrpObj.comp_inv, ← _root_.mul_assoc]

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
  simp [leftTranslation_hom, MonObj.comp_mul]

/-- A homomorphism of group objects `i : H ⟶ G` intertwines translation by a point `x` of `H` with
translation by its image `x ≫ i`. -/
theorem leftTranslation_hom_comp {H : C} [GrpObj H] (i : H ⟶ G) [IsMonHom i] (x : 𝟙_ C ⟶ H) :
    (leftTranslation x).hom ≫ i = i ≫ (leftTranslation (x ≫ i)).hom := by
  simp [leftTranslation_hom, MonObj.mul_comp, MonObj.comp_mul]

/-- Right translation `y ↦ y * x` by a global group point, with inverse given by `x⁻¹`. -/
noncomputable def rightTranslation (x : 𝟙_ C ⟶ G) : G ≅ G where
  hom := 𝟙 G * (toUnit G ≫ x)
  inv := 𝟙 G * (toUnit G ≫ x⁻¹)
  hom_inv_id := by simp [MonObj.comp_mul, _root_.mul_assoc, GrpObj.comp_inv]
  inv_hom_id := by simp [MonObj.comp_mul, _root_.mul_assoc, GrpObj.comp_inv]

/-- The morphism underlying right translation is right multiplication by the constant point. -/
theorem rightTranslation_hom (x : 𝟙_ C ⟶ G) :
    (rightTranslation x).hom = 𝟙 G * (toUnit G ≫ x) := (rfl)

/-- The inverse of right translation is right translation by the inverse point. -/
@[simp]
theorem rightTranslation_inv (x : 𝟙_ C ⟶ G) :
    (rightTranslation x).inv = (rightTranslation x⁻¹).hom := (rfl)

/-- Right translation acts on every test-object point by right multiplication. -/
@[reassoc (attr := simp)]
theorem comp_rightTranslation_hom {Y : C} (f : Y ⟶ G) (x : 𝟙_ C ⟶ G) :
    f ≫ (rightTranslation x).hom = f * (toUnit Y ≫ x) := by
  simp [rightTranslation_hom, MonObj.comp_mul]

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

/-! ### The universal shift -/

namespace TauCeti.GrpObj

universe u u' v v'

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] {X G : C} [MonObj G]

/-- The **universal shift** of a morphism `c : X ⟶ G` to a monoid object: the morphism
`G ⊗ X ⟶ G ⊗ G` sending `(y, x)` to `(y, y * c x)` (`lift_comp_universalShift`). It is a morphism
over the first factor `G` (`universalShift_fst`). -/
noncomputable def universalShift (c : X ⟶ G) : G ⊗ X ⟶ G ⊗ G :=
  lift (fst G X) (fst G X * snd G X ≫ c)

/-- The universal shift keeps the first factor. -/
@[reassoc (attr := simp)]
theorem universalShift_fst (c : X ⟶ G) : universalShift c ≫ fst G G = fst G X := by
  simp [universalShift]

/-- The second coordinate of the universal shift is `y * c x`. -/
@[reassoc (attr := simp)]
theorem universalShift_snd (c : X ⟶ G) :
    universalShift c ≫ snd G G = fst G X * snd G X ≫ c := by
  simp [universalShift]

/-- The universal shift sends a pair of points `(y, x)` to `(y, y * c x)`. -/
@[reassoc (attr := simp)]
theorem lift_comp_universalShift {T : C} (y : T ⟶ G) (x : T ⟶ X) (c : X ⟶ G) :
    lift y x ≫ universalShift c = lift y (y * x ≫ c) := by
  ext <;> simp [MonObj.comp_mul]

/-- The universal shift of the trivial morphism is the diagonal shift `(y, x) ↦ (y, y)`. -/
@[simp]
theorem universalShift_one : universalShift (1 : X ⟶ G) = lift (fst G X) (fst G X) := by
  simp [universalShift]

open scoped CategoryTheory.Obj in
/-- A monoidal functor commutes with the universal shift through the product comparison maps,
where `F.obj G` carries the image monoid structure. -/
@[reassoc]
theorem map_universalShift_comp_prodComparison {D : Type u'} [Category.{v'} D]
    [CartesianMonoidalCategory D] (F : C ⥤ D) [F.Monoidal] (c : X ⟶ G) :
    F.map (universalShift c) ≫ prodComparison F G G =
      prodComparison F G X ≫ universalShift (F.map c) := by
  rw [universalShift, Functor.map_lift_comp_prodComparison]
  ext <;> simp [Functor.map_mul, MonObj.comp_mul]

end TauCeti.GrpObj
