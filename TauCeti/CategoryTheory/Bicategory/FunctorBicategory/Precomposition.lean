/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Bicategory.NaturalTransformation.Pseudo

/-!
# Precomposition on bicategories of pseudofunctors

Precomposition by `P : B ⥤ᵖ B'` acts on pseudofunctors, strong transformations and
modifications. The construction `P.precomposition C` packages these operations as a
pseudofunctor `(B' ⥤ᵖ C) ⥤ᵖ (B ⥤ᵖ C)`. Its unit and composition comparisons are the
identity-component modifications `P.whiskerLeftId` and `P.whiskerLeftComp`.

In particular, restriction of category-valued families along a functor of parameter
groupoids also restricts their morphisms and all comparison cells. This is needed to
transport coherent families, rather than just their values at objects.

The construction extends `Pseudofunctor.whiskerLeft` using Mathlib's bicategory of
pseudofunctors with strong transformations and modifications.

## References

* Niles Johnson and Donald Yau, *2-Dimensional Categories*, Oxford University Press
  (2021), for the bicategory of pseudofunctors and precomposition.
-/

public section

namespace CategoryTheory.Pseudofunctor

open Bicategory StrongTrans

universe w₁ w₂ w₃ v₁ v₂ v₃ u₁ u₂ u₃

variable {B : Type u₁} [Bicategory.{w₁, v₁} B]
  {B' : Type u₂} [Bicategory.{w₂, v₂} B']
  {C : Type u₃} [Bicategory.{w₃, v₃} C]
  (P : B ⥤ᵖ B')

/-- Restrict a modification along a pseudofunctor. -/
def whiskerLeft₂ {F G : B' ⥤ᵖ C} {η θ : F ⟶ G} (m : η ⟶ θ) :
    P.whiskerLeft η ⟶ P.whiskerLeft θ where
  as.app a := m.as.app (P.obj a)
  as.naturality f := m.as.naturality (P.map f)

@[simp]
lemma whiskerLeft₂_as_app {F G : B' ⥤ᵖ C} {η θ : F ⟶ G} (m : η ⟶ θ) (a : B) :
    (P.whiskerLeft₂ m).as.app a = m.as.app (P.obj a) :=
  (rfl)

@[simp]
lemma whiskerLeft₂_id {F G : B' ⥤ᵖ C} (η : F ⟶ G) :
    P.whiskerLeft₂ (𝟙 η) = 𝟙 (P.whiskerLeft η) := by
  ext a
  rfl

@[simp]
lemma whiskerLeft₂_comp {F G : B' ⥤ᵖ C} {η θ ι : F ⟶ G} (m : η ⟶ θ) (n : θ ⟶ ι) :
    P.whiskerLeft₂ (m ≫ n) = P.whiskerLeft₂ m ≫ P.whiskerLeft₂ n := by
  ext a
  rfl

/-- Precomposition by a pseudofunctor, including its action on strong transformations
and modifications and its unit and composition coherence. -/
-- Exposed so the dependent formulas for maps and comparison cells are well-typed.
@[expose] def precomposition (C : Type u₃) [Bicategory.{w₃, v₃} C] :
    (B' ⥤ᵖ C) ⥤ᵖ (B ⥤ᵖ C) where
  obj F := P.comp F
  map η := P.whiskerLeft η
  map₂ m := P.whiskerLeft₂ m
  map₂_id := P.whiskerLeft₂_id
  map₂_comp m n := P.whiskerLeft₂_comp m n
  mapId F := P.whiskerLeftId F
  mapComp η θ := P.whiskerLeftComp η θ
  -- State component identities in C, so the simplifier need not identify the
  -- hom categories of composite pseudofunctors at reducible transparency.
  map₂_whisker_left η m n α := by
    ext a
    simp only [whiskerLeft₂_as_app, homCategory_comp_as_app, whiskerLeft_as_app,
      whiskerLeftComp_hom_as_app, whiskerLeftComp_inv_as_app]
    have h {X Y : C} {f g : X ⟶ Y} (β : f ⟶ g) : β = 𝟙 _ ≫ β ≫ 𝟙 _ := by simp
    exact h _
  map₂_whisker_right m η := by
    ext a
    simp only [whiskerLeft₂_as_app, homCategory_comp_as_app, whiskerRight_as_app,
      whiskerLeftComp_hom_as_app, whiskerLeftComp_inv_as_app]
    have h {X Y : C} {f g : X ⟶ Y} (β : f ⟶ g) : β = 𝟙 _ ≫ β ≫ 𝟙 _ := by simp
    exact h _
  map₂_associator η θ ι := by
    ext a
    simp only [whiskerLeft₂_as_app, homCategory_comp_as_app, whiskerLeft_as_app,
      whiskerRight_as_app, whiskerLeftComp_hom_as_app, whiskerLeftComp_inv_as_app,
      associator_hom_as_app]
    have h {W X Y Z : C} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) :
        (α_ f g h).hom = 𝟙 _ ≫ 𝟙 (f ≫ g) ▷ h ≫ (α_ f g h).hom ≫
          f ◁ 𝟙 (g ≫ h) ≫ 𝟙 _ := by simp
    exact h _ _ _
  map₂_left_unitor η := by
    ext a
    simp only [whiskerLeft₂_as_app, homCategory_comp_as_app, whiskerRight_as_app,
      whiskerLeftComp_hom_as_app, whiskerLeftId_hom_as_app, leftUnitor_hom_as_app]
    have h {X Y : C} (f : X ⟶ Y) :
        (λ_ f).hom = 𝟙 _ ≫ 𝟙 (𝟙 X) ▷ f ≫ (λ_ f).hom := by simp
    exact h _
  map₂_right_unitor η := by
    ext a
    simp only [whiskerLeft₂_as_app, homCategory_comp_as_app, whiskerLeft_as_app,
      whiskerLeftComp_hom_as_app, whiskerLeftId_hom_as_app, rightUnitor_hom_as_app]
    have h {X Y : C} (f : X ⟶ Y) :
        (ρ_ f).hom = 𝟙 _ ≫ f ◁ 𝟙 (𝟙 Y) ≫ (ρ_ f).hom := by simp
    exact h _

@[simp]
lemma precomposition_obj (F : B' ⥤ᵖ C) :
    (P.precomposition C).obj F = P.comp F :=
  (rfl)

@[simp]
lemma precomposition_map {F G : B' ⥤ᵖ C} (η : F ⟶ G) :
    (P.precomposition C).map η = P.whiskerLeft η :=
  (rfl)

@[simp]
lemma precomposition_map₂ {F G : B' ⥤ᵖ C} {η θ : F ⟶ G} (m : η ⟶ θ) :
    (P.precomposition C).map₂ m = P.whiskerLeft₂ m :=
  (rfl)

@[simp]
lemma precomposition_mapId (F : B' ⥤ᵖ C) :
    (P.precomposition C).mapId F = P.whiskerLeftId F :=
  (rfl)

@[simp]
lemma precomposition_mapComp {F G H : B' ⥤ᵖ C} (η : F ⟶ G) (θ : G ⟶ H) :
    (P.precomposition C).mapComp η θ = P.whiskerLeftComp η θ :=
  (rfl)

end CategoryTheory.Pseudofunctor
