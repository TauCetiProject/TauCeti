/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Pseudo

/-!
# Whiskering strong transformations by a pseudofunctor

For a pseudofunctor `P : B ⥤ᵖ B'` and a strong transformation `η : F ⟶ G` between pseudofunctors
`F G : B' ⥤ᵖ C`, the strong transformation `P.whiskerLeft η : P.comp F ⟶ P.comp G` has
components `η.app (P.obj a)` and naturality isomorphisms `η.naturality (P.map f)`. This is the
bicategorical analogue of `Functor.whiskerLeft`. Restricting a strong transformation along an
inclusion of bicategories, for instance to a fiber of a product of locally discrete
bicategories, is an instance of this construction.

Whiskering preserves identities and composites up to the invertible modifications
`Pseudofunctor.whiskerLeftId` and `Pseudofunctor.whiskerLeftComp`, whose components are
identities. The file also records `Pseudofunctor.StrongTrans.isoApp`, the component
`η.app a ≅ θ.app a` of an invertible modification `η ≅ θ`, analogous to `Iso.app` for natural
isomorphisms.
-/

public section

namespace CategoryTheory.Pseudofunctor

open Bicategory StrongTrans

universe w₁ w₂ w₃ v₁ v₂ v₃ u₁ u₂ u₃

variable {B : Type u₁} [Bicategory.{w₁, v₁} B] {B' : Type u₂} [Bicategory.{w₂, v₂} B']
  {C : Type u₃} [Bicategory.{w₃, v₃} C]

/-- The whiskering `P.whiskerLeft η : P.comp F ⟶ P.comp G` of a strong transformation
`η : F ⟶ G` by a pseudofunctor `P`. Its component at `a` is `η.app (P.obj a)` and its
naturality isomorphism at `f` is `η.naturality (P.map f)`. -/
-- The body is exposed so that the components and naturality isomorphisms of the whiskering are
-- definitionally those of `η`; otherwise `whiskerLeft_naturality` cannot even be stated.
@[expose, simps]
def whiskerLeft (P : B ⥤ᵖ B') {F G : B' ⥤ᵖ C} (η : F ⟶ G) : P.comp F ⟶ P.comp G where
  app a := η.app (P.obj a)
  naturality f := η.naturality (P.map f)
  naturality_naturality θ := η.naturality_naturality (P.map₂ θ)
  -- The coherence conditions are stated for `F` and `G` at the images under `P`, where they follow
  -- from those of `η`; the goals agree with these statements up to unfolding `Pseudofunctor.comp`.
  naturality_id a := by
    have h : (η.naturality (P.map (𝟙 a))).hom ≫
        η.app (P.obj a) ◁ (G.map₂ (P.mapId a).hom ≫ (G.mapId (P.obj a)).hom) =
          (F.map₂ (P.mapId a).hom ≫ (F.mapId (P.obj a)).hom) ▷ η.app (P.obj a) ≫
            (λ_ (η.app (P.obj a))).hom ≫ (ρ_ (η.app (P.obj a))).inv := by
      rw [whiskerLeft_comp, comp_whiskerRight, ← η.naturality_naturality_assoc, η.naturality_id,
        Category.assoc]
    exact h
  naturality_comp f g := by
    have h : (η.naturality (P.map (f ≫ g))).hom ≫ η.app (P.obj _) ◁
        (G.map₂ (P.mapComp f g).hom ≫ (G.mapComp (P.map f) (P.map g)).hom) =
          (F.map₂ (P.mapComp f g).hom ≫ (F.mapComp (P.map f) (P.map g)).hom) ▷ η.app (P.obj _) ≫
            (α_ _ _ _).hom ≫ F.map (P.map f) ◁ (η.naturality (P.map g)).hom ≫
              (α_ _ _ _).inv ≫ (η.naturality (P.map f)).hom ▷ G.map (P.map g) ≫
                (α_ _ _ _).hom := by
      rw [whiskerLeft_comp, comp_whiskerRight, ← η.naturality_naturality_assoc, η.naturality_comp,
        Category.assoc]
    exact h

/-- The component `η.app a ≅ θ.app a` at `a` of an invertible modification `e : η ≅ θ`. -/
def StrongTrans.isoApp {F G : B ⥤ᵖ C} {η θ : F ⟶ G} (e : η ≅ θ) (a : B) : η.app a ≅ θ.app a where
  hom := e.hom.as.app a
  inv := e.inv.as.app a
  hom_inv_id := congrArg (fun m => m.as.app a) e.hom_inv_id
  inv_hom_id := congrArg (fun m => m.as.app a) e.inv_hom_id

@[simp]
lemma StrongTrans.isoApp_hom {F G : B ⥤ᵖ C} {η θ : F ⟶ G} (e : η ≅ θ) (a : B) :
    (isoApp e a).hom = e.hom.as.app a :=
  (rfl)

@[simp]
lemma StrongTrans.isoApp_inv {F G : B ⥤ᵖ C} {η θ : F ⟶ G} (e : η ≅ θ) (a : B) :
    (isoApp e a).inv = e.inv.as.app a :=
  (rfl)

variable (P : B ⥤ᵖ B')

/-- Whiskering the identity strong transformation gives the identity, up to the invertible
modification with identity components. -/
def whiskerLeftId (F : B' ⥤ᵖ C) : P.whiskerLeft (𝟙 F) ≅ 𝟙 (P.comp F) :=
  -- The naturality condition is stated for `F` at the images under `P`; the goal agrees with it
  -- up to unfolding `Pseudofunctor.comp` and `whiskerLeft`.
  isoMk (fun a => Iso.refl _) (fun {a b} f => by
    have h : F.map (P.map f) ◁ 𝟙 (𝟙 (F.obj (P.obj b))) ≫
        ((ρ_ (F.map (P.map f))).hom ≫ (λ_ (F.map (P.map f))).inv) =
          ((ρ_ (F.map (P.map f))).hom ≫ (λ_ (F.map (P.map f))).inv) ≫
            𝟙 (𝟙 (F.obj (P.obj a))) ▷ F.map (P.map f) := by
      simp
    exact h)

@[simp]
lemma whiskerLeftId_hom_as_app (F : B' ⥤ᵖ C) (a : B) :
    (P.whiskerLeftId F).hom.as.app a = 𝟙 _ :=
  (rfl)

@[simp]
lemma whiskerLeftId_inv_as_app (F : B' ⥤ᵖ C) (a : B) :
    (P.whiskerLeftId F).inv.as.app a = 𝟙 _ :=
  (rfl)

/-- Whiskering a composite of strong transformations gives the composite of the whiskerings, up to
the invertible modification with identity components. -/
def whiskerLeftComp {F G H : B' ⥤ᵖ C} (η : F ⟶ G) (θ : G ⟶ H) :
    P.whiskerLeft (η ≫ θ) ≅ P.whiskerLeft η ≫ P.whiskerLeft θ :=
  -- The naturality condition is stated for `η ≫ θ` at the images under `P`; the goal agrees with
  -- it up to unfolding `Pseudofunctor.comp` and `whiskerLeft`.
  isoMk (fun a => Iso.refl _) (fun {a b} f => by
    have h : F.map (P.map f) ◁ 𝟙 (η.app (P.obj b) ≫ θ.app (P.obj b)) ≫
        ((η ≫ θ).naturality (P.map f)).hom =
          ((η ≫ θ).naturality (P.map f)).hom ≫
            𝟙 (η.app (P.obj a) ≫ θ.app (P.obj a)) ▷ H.map (P.map f) := by
      rw [Bicategory.whiskerLeft_id, Bicategory.id_whiskerRight]
      exact (Category.id_comp _).trans (Category.comp_id _).symm
    exact h)

@[simp]
lemma whiskerLeftComp_hom_as_app {F G H : B' ⥤ᵖ C} (η : F ⟶ G) (θ : G ⟶ H) (a : B) :
    (P.whiskerLeftComp η θ).hom.as.app a = 𝟙 _ :=
  (rfl)

@[simp]
lemma whiskerLeftComp_inv_as_app {F G H : B' ⥤ᵖ C} (η : F ⟶ G) (θ : G ⟶ H) (a : B) :
    (P.whiskerLeftComp η θ).inv.as.app a = 𝟙 _ :=
  (rfl)

end CategoryTheory.Pseudofunctor
