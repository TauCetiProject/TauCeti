/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Pseudo

/-!
# Evaluation of pseudofunctors

Evaluation at an object of a bicategory acts on pseudofunctors, strong transformations,
and modifications. It is itself a pseudofunctor, with identity unit and composition
comparisons. Evaluation at a varying object is pseudofunctorial as well: a `1`-morphism
induces a strong transformation between evaluations, whose naturality cell is the inverse
of the naturality cell of the strong transformation being evaluated.

These constructions let comparisons of category-valued families be evaluated on fibers
without discarding their naturality or their modification data.

## References

* Niles Johnson and Donald Yau, *2-Dimensional Categories*, Oxford University Press
  (2021), Chapter 4, for strong transformations and modifications.

The construction uses Mathlib's bicategory of pseudofunctors and its pointwise
associators and unitors, defined by Calle Sönne.
-/

public section

universe w₁ w₂ v₁ v₂ u₁ u₂

namespace TauCeti.CategoryTheory.Pseudofunctor

open _root_.CategoryTheory _root_.CategoryTheory.Pseudofunctor
open Bicategory StrongTrans

variable {B : Type u₁} [Bicategory.{w₁, v₁} B]
  {C : Type u₂} [Bicategory.{w₂, v₂} C]

/-- Evaluation at an object, on pseudofunctors, strong transformations and modifications.
Its unit and composition comparisons are identities. -/
-- Expose the object assignment so evaluated transformations have their original endpoints.
@[expose] def eval (C : Type u₂) [Bicategory.{w₂, v₂} C] (a : B) :
    (B ⥤ᵖ C) ⥤ᵖ C where
  obj F := F.obj a
  map η := η.app a
  map₂ m := m.as.app a
  mapId _ := Iso.refl _
  mapComp _ _ := Iso.refl _
  -- The component of an identity transformation is definitionally an identity;
  -- state the unitor laws at a general 1-morphism to avoid unfolding it in `simp`.
  map₂_left_unitor η := by
    have h {X Y : C} (f : X ⟶ Y) :
        (λ_ f).hom = 𝟙 _ ≫ 𝟙 (𝟙 X) ▷ f ≫ (λ_ f).hom := by simp
    exact h _
  map₂_right_unitor η := by
    have h {X Y : C} (f : X ⟶ Y) :
        (ρ_ f).hom = 𝟙 _ ≫ f ◁ 𝟙 (𝟙 Y) ≫ (ρ_ f).hom := by simp
    exact h _

@[simp] lemma eval_obj (a : B) (F : B ⥤ᵖ C) : (eval C a).obj F = F.obj a := (rfl)

@[simp] lemma eval_map (a : B) {F G : B ⥤ᵖ C} (η : F ⟶ G) :
    (eval C a).map η = η.app a := (rfl)

@[simp] lemma eval_map₂ (a : B) {F G : B ⥤ᵖ C} {η θ : F ⟶ G} (m : η ⟶ θ) :
    (eval C a).map₂ m = m.as.app a := (rfl)

@[simp] lemma eval_mapId (a : B) (F : B ⥤ᵖ C) :
    (eval C a).mapId F = Iso.refl _ := (rfl)

@[simp] lemma eval_mapComp (a : B) {F G H : B ⥤ᵖ C} (η : F ⟶ G) (θ : G ⟶ H) :
    (eval C a).mapComp η θ = Iso.refl _ := (rfl)

/-- A `1`-morphism induces a strong transformation between evaluation pseudofunctors.
Its component at `F` is `F.map f`; its naturality is the inverse of the naturality of the
strong transformation being evaluated. -/
-- Expose the components so the naturality cell has its original endpoints.
@[expose] def evaluationMap {a b : B} (f : a ⟶ b) : eval C a ⟶ eval C b where
  app F := F.map f
  naturality η := (η.naturality f).symm
  naturality_naturality m := by
    -- State the inverse square before identifying the endpoints of `eval`.
    have h {F G : B ⥤ᵖ C} {η θ : F ⟶ G} (m : η ⟶ θ) :
        m.as.app a ▷ G.map f ≫ (θ.naturality f).inv =
          (η.naturality f).inv ≫ F.map f ◁ m.as.app b := by
      rw [← cancel_epi (η.naturality f).hom]
      simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
      rw [← m.as.naturality f]
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    exact h m
  -- Compute the identity comparisons of evaluation before using the pointwise
  -- formulas for identities and composites of strong transformations.
  naturality_id F := by
    have h {X Y : C} (g : X ⟶ Y) :
        ((λ_ g).hom ≫ (ρ_ g).inv) ≫ g ◁ 𝟙 (𝟙 Y) =
          𝟙 (𝟙 X) ▷ g ≫ (λ_ g).hom ≫ (ρ_ g).inv := by simp
    exact h _
  naturality_comp η θ := by
    have h {F G H : B ⥤ᵖ C} (η : F ⟶ G) (θ : G ⟶ H) :
        ((η ≫ θ).naturality f).inv ≫ F.map f ◁ 𝟙 ((η ≫ θ).app b) =
          𝟙 ((η ≫ θ).app a) ▷ H.map f ≫
            (α_ _ _ _).hom ≫ η.app a ◁ (θ.naturality f).inv ≫
              (α_ _ _ _).inv ≫ (η.naturality f).inv ▷ θ.app b ≫ (α_ _ _ _).hom := by
      simp only [Bicategory.whiskerLeft_id, Bicategory.id_whiskerRight,
        Category.id_comp]
      exact (Category.comp_id ((η ≫ θ).naturality f).inv).trans
        (categoryStruct_comp_naturality_inv η θ f)
    exact h η θ

@[simp] lemma evaluationMap_app {a b : B} (f : a ⟶ b) (F : B ⥤ᵖ C) :
    (evaluationMap (C := C) f).app F = F.map f := (rfl)

@[simp] lemma evaluationMap_naturality {a b : B} (f : a ⟶ b)
    {F G : B ⥤ᵖ C} (η : F ⟶ G) :
    (evaluationMap (C := C) f).naturality η = (η.naturality f).symm := (rfl)

/-- A `2`-morphism induces a modification between the corresponding evaluation maps. -/
def evaluationMap₂ {a b : B} {f g : a ⟶ b} (α : f ⟶ g) :
    evaluationMap (C := C) f ⟶ evaluationMap g where
  as.app F := F.map₂ α
  as.naturality η := by
    have h {F G : B ⥤ᵖ C} (η : F ⟶ G) :
        η.app a ◁ G.map₂ α ≫ (η.naturality g).inv =
          (η.naturality f).inv ≫ F.map₂ α ▷ η.app b := by
      rw [← cancel_epi (η.naturality f).hom]
      simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
      rw [← η.naturality_naturality α]
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    exact h η

@[simp] lemma evaluationMap₂_as_app {a b : B} {f g : a ⟶ b} (α : f ⟶ g)
    (F : B ⥤ᵖ C) : (evaluationMap₂ (C := C) α).as.app F = F.map₂ α := (rfl)

/-- Evaluation of the identity `1`-morphism is the identity transformation, by the unit
comparisons of the evaluated pseudofunctors. -/
def evaluationMapId (a : B) : evaluationMap (C := C) (𝟙 a) ≅ 𝟙 (eval C a) :=
  isoMk (fun F => F.mapId a) fun η => by
    have h {F G : B ⥤ᵖ C} (η : F ⟶ G) :
        η.app a ◁ (G.mapId a).hom ≫ ((ρ_ (η.app a)).hom ≫ (λ_ (η.app a)).inv) =
          (η.naturality (𝟙 a)).inv ≫ (F.mapId a).hom ▷ η.app a := by
      rw [naturality_id_inv]
      simp
    exact h η

@[simp] lemma evaluationMapId_hom_as_app (a : B) (F : B ⥤ᵖ C) :
    (evaluationMapId (C := C) a).hom.as.app F = (F.mapId a).hom := (rfl)

@[simp] lemma evaluationMapId_inv_as_app (a : B) (F : B ⥤ᵖ C) :
    (evaluationMapId (C := C) a).inv.as.app F = (F.mapId a).inv := (rfl)

/-- Evaluation of a composite is the composite of the evaluations, by the composition
comparisons of the evaluated pseudofunctors. -/
def evaluationMapComp {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
    evaluationMap (C := C) (f ≫ g) ≅ evaluationMap f ≫ evaluationMap g :=
  isoMk (fun F => F.mapComp f g) fun η => by
    have h {F G : B ⥤ᵖ C} (η : F ⟶ G) :
        η.app a ◁ (G.mapComp f g).hom ≫
            ((α_ _ _ _).inv ≫ (η.naturality f).inv ▷ G.map g ≫ (α_ _ _ _).hom ≫
              F.map f ◁ (η.naturality g).inv ≫ (α_ _ _ _).inv) =
          (η.naturality (f ≫ g)).inv ≫ (F.mapComp f g).hom ▷ η.app c := by
      rw [naturality_comp_inv]
      simp
    exact h η

@[simp] lemma evaluationMapComp_hom_as_app {a b c : B} (f : a ⟶ b) (g : b ⟶ c)
    (F : B ⥤ᵖ C) :
    (evaluationMapComp (C := C) f g).hom.as.app F = (F.mapComp f g).hom := (rfl)

@[simp] lemma evaluationMapComp_inv_as_app {a b c : B} (f : a ⟶ b) (g : b ⟶ c)
    (F : B ⥤ᵖ C) :
    (evaluationMapComp (C := C) f g).inv.as.app F = (F.mapComp f g).inv := (rfl)

/-- Evaluation is pseudofunctorial in the object being evaluated at. Its naturality cells
are the inverse naturality cells of strong transformations; its unit and composition
modifications are the original pseudofunctors' unit and composition comparisons. -/
-- Expose the object assignment so its maps have evaluation pseudofunctors as endpoints.
@[expose] def evaluation (B : Type u₁) [Bicategory.{w₁, v₁} B]
    (C : Type u₂) [Bicategory.{w₂, v₂} C] : B ⥤ᵖ ((B ⥤ᵖ C) ⥤ᵖ C) where
  obj a := eval C a
  map f := evaluationMap f
  map₂ α := evaluationMap₂ α
  map₂_id f := by ext F; exact F.map₂_id f
  map₂_comp α β := by ext F; exact F.map₂_comp α β
  mapId a := evaluationMapId a
  mapComp f g := evaluationMapComp f g
  map₂_whisker_left f _ _ α := by ext F; exact F.map₂_whisker_left f α
  map₂_whisker_right α g := by ext F; exact F.map₂_whisker_right α g
  map₂_associator f g h := by ext F; exact F.map₂_associator f g h
  map₂_left_unitor f := by ext F; exact F.map₂_left_unitor f
  map₂_right_unitor f := by ext F; exact F.map₂_right_unitor f

@[simp] lemma evaluation_obj (a : B) : (evaluation B C).obj a = eval C a := (rfl)

@[simp] lemma evaluation_map {a b : B} (f : a ⟶ b) :
    (evaluation B C).map f = evaluationMap f := (rfl)

@[simp] lemma evaluation_map₂ {a b : B} {f g : a ⟶ b} (α : f ⟶ g) :
    (evaluation B C).map₂ α = evaluationMap₂ α := (rfl)

@[simp] lemma evaluation_mapId (a : B) :
    (evaluation B C).mapId a = evaluationMapId a := (rfl)

@[simp] lemma evaluation_mapComp {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
    (evaluation B C).mapComp f g = evaluationMapComp f g := (rfl)

end TauCeti.CategoryTheory.Pseudofunctor
