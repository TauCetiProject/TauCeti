/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Pseudo
public import Mathlib.CategoryTheory.Bicategory.Strict.Pseudofunctor

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

The last section restates the unit and composition conditions of a strong transformation for the
comparisons `F.mapId'` and `F.mapComp'` at `1`-morphisms that are only propositionally identities
or composites (`StrongTrans.naturality_id'_inv`, `StrongTrans.naturality_comp'_hom`,
`StrongTrans.naturality_comp'_inv`). Over a strict bicategory, it deduces that a strong
transformation is compatible with the isomorphisms `F t ≫ F r ≅ F l ≫ F b` of a commutative
square (`StrongTrans.naturality_isoMapOfCommSq`).
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

/-! ### Naturality at identities and composites up to equality -/

namespace StrongTrans

variable {F G : B ⥤ᵖ C}

/-- The unit condition of a strong transformation, for a `1`-morphism `f` equal to an identity:
the inverse naturality isomorphism at `f` is determined by the comparisons `F.mapId' f` and
`G.mapId' f`. This generalizes `StrongTrans.naturality_id_inv`. -/
lemma naturality_id'_inv (η : F ⟶ G) {a : B} (f : a ⟶ a) (hf : f = 𝟙 a) :
    (η.naturality f).inv = η.app a ◁ (G.mapId' f hf).hom ≫ (ρ_ (η.app a)).hom ≫
      (λ_ (η.app a)).inv ≫ (F.mapId' f hf).inv ▷ η.app a := by
  subst hf
  simp [mapId'_eq_mapId, naturality_id_inv]

/-- The composition condition of a strong transformation, for a `1`-morphism `fg` equal to a
composite `f ≫ g`, stated with the comparisons `F.mapComp' f g fg` and `G.mapComp' f g fg`. This
generalizes `StrongTrans.naturality_comp_hom`. -/
lemma naturality_comp'_hom (η : F ⟶ G) {a b c : B} (f : a ⟶ b) (g : b ⟶ c) (fg : a ⟶ c)
    (h : f ≫ g = fg) :
    (η.naturality fg).hom =
      (F.mapComp' f g fg h).hom ▷ η.app c ≫ (α_ _ _ _).hom ≫ F.map f ◁ (η.naturality g).hom ≫
        (α_ _ _ _).inv ≫ (η.naturality f).hom ▷ G.map g ≫ (α_ _ _ _).hom ≫
          η.app a ◁ (G.mapComp' f g fg h).inv := by
  subst h
  simp [mapComp'_eq_mapComp, naturality_comp_hom]

/-- The inverse form of `StrongTrans.naturality_comp'_hom`, generalizing
`StrongTrans.naturality_comp_inv`. -/
lemma naturality_comp'_inv (η : F ⟶ G) {a b c : B} (f : a ⟶ b) (g : b ⟶ c) (fg : a ⟶ c)
    (h : f ≫ g = fg) :
    (η.naturality fg).inv =
      η.app a ◁ (G.mapComp' f g fg h).hom ≫ (α_ _ _ _).inv ≫ (η.naturality f).inv ▷ G.map g ≫
        (α_ _ _ _).hom ≫ F.map f ◁ (η.naturality g).inv ≫ (α_ _ _ _).inv ≫
          (F.mapComp' f g fg h).inv ▷ η.app c := by
  subst h
  simp [mapComp'_eq_mapComp, naturality_comp_inv]

/-- A strong transformation `η` is compatible with the isomorphisms
`F t ≫ F r ≅ F l ≫ F b` of a commutative square `t ≫ r = l ≫ b` in a strict bicategory: the
naturality isomorphisms of `η` along the two sides of the square, composed with the square
isomorphisms of `F` and of `G`, agree. The two sides are arranged as the naturality isomorphisms
of the composites of `η` with strong transformations whose naturality isomorphisms are the square
isomorphisms, as in `CategoryTheory.Pseudofunctor.mapNatTrans`. -/
lemma naturality_isoMapOfCommSq [Strict B] (η : F ⟶ G) {X₁ X₂ Y₁ Y₂ : B} {t : X₁ ⟶ Y₁}
    {l : X₁ ⟶ X₂} {r : Y₁ ⟶ Y₂} {b : X₂ ⟶ Y₂} (sq : CommSq t l r b) :
    F.map t ◁ (η.naturality r).hom ≫ (α_ _ _ _).inv ≫ (η.naturality t).hom ▷ G.map r ≫
      (α_ _ _ _).hom ≫ η.app X₁ ◁ (G.isoMapOfCommSq sq).hom ≫ (α_ _ _ _).inv =
    ((α_ _ _ _).inv ≫ (F.isoMapOfCommSq sq).hom ▷ η.app Y₂ ≫ (α_ _ _ _).hom ≫
      F.map l ◁ (η.naturality b).hom ≫ (α_ _ _ _).inv) ≫ (η.naturality l).hom ▷ G.map b := by
  -- Both sides are the naturality isomorphism of `η` at `t ≫ r = l ≫ b`, factored in two ways.
  have key {Z : B} (f : X₁ ⟶ Z) (g : Z ⟶ Y₂) (h : f ≫ g = t ≫ r) :
      (α_ _ _ _).hom ≫ F.map f ◁ (η.naturality g).hom ≫ (α_ _ _ _).inv ≫
        (η.naturality f).hom ▷ G.map g ≫ (α_ _ _ _).hom =
      (F.mapComp' f g (t ≫ r) h).inv ▷ η.app Y₂ ≫ (η.naturality (t ≫ r)).hom ≫
        η.app X₁ ◁ (G.mapComp' f g (t ≫ r) h).hom := by
    simp [η.naturality_comp'_hom f g (t ≫ r) h]
  have h₁ := key t r rfl
  rw [← Iso.eq_inv_comp] at h₁
  rw [← cancel_mono (α_ _ _ _).hom, isoMapOfCommSq_eq _ sq (t ≫ r) rfl,
    isoMapOfCommSq_eq _ sq (t ≫ r) rfl]
  simp only [Iso.trans_hom, Iso.symm_hom, comp_whiskerRight, whiskerLeft_comp, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]
  rw [key l b sq.w.symm, reassoc_of% h₁]
  simp

end StrongTrans

end CategoryTheory.Pseudofunctor
