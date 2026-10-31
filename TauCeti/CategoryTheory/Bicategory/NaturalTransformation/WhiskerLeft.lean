/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Pseudo

/-!
# Precomposing strong transformations with a pseudofunctor

Let `P : A ⥤ᵖ B` be a pseudofunctor and `η : F ⟶ G` a strong transformation between
pseudofunctors `F G : B ⥤ᵖ C`. Then `Pseudofunctor.whiskerLeft P η : P.comp F ⟶ P.comp G` is the
strong transformation with components `η.app (P.obj a)` and naturality isomorphisms
`η.naturality (P.map f)`. A modification `Γ : η ⟶ θ` likewise restricts to a modification
`whiskerLeftMap P Γ : whiskerLeft P η ⟶ whiskerLeft P θ`.

Precomposition is strict: it preserves identities and composites of strong transformations on
the nose, and it sends the whiskerings, associators and unitors of the bicategory of
pseudofunctors `B ⥤ᵖ C` to those of `A ⥤ᵖ C`. This is the analogue for pseudofunctors of
`CategoryTheory.Functor.whiskerLeft`. A typical use is restricting a strong transformation
between pseudofunctors out of a product to one factor, by precomposing with a section.

## Main declarations

* `CategoryTheory.Pseudofunctor.whiskerLeft`: the strong transformation `P.comp F ⟶ P.comp G`;
* `CategoryTheory.Pseudofunctor.whiskerLeftMap`: its action on modifications;
* `CategoryTheory.Pseudofunctor.whiskerLeft_id`, `whiskerLeft_comp`, `whiskerLeftMap_id`,
  `whiskerLeftMap_comp`: strict functoriality;
* `CategoryTheory.Pseudofunctor.whiskerLeftMap_whiskerLeft`, `whiskerLeftMap_whiskerRight`,
  `whiskerLeftMap_associator_hom`, `whiskerLeftMap_leftUnitor_hom`,
  `whiskerLeftMap_rightUnitor_hom`: compatibility with the bicategory structure of
  pseudofunctors.

## References

* Niles Johnson and Donald Yau, *2-Dimensional Categories*, Oxford University Press (2021),
  Chapter 4: pseudofunctors, strong transformations and modifications.
-/

public section

universe w₁ v₁ u₁ w₂ v₂ u₂ w₃ v₃ u₃

namespace CategoryTheory.Pseudofunctor

open Bicategory
open scoped Pseudofunctor.StrongTrans

/-! `whiskerLeft` and `whiskerLeftMap` are exposed: the statements of the strict functoriality
lemmas below, and the types of restricted modifications downstream, only typecheck by unfolding
them. -/

variable {A : Type u₁} [Bicategory.{w₁, v₁} A] {B : Type u₂} [Bicategory.{w₂, v₂} B]
  {C : Type u₃} [Bicategory.{w₃, v₃} C] (P : A ⥤ᵖ B) {F G H I : B ⥤ᵖ C}

/-- The precomposite `P.comp F ⟶ P.comp G` of a strong transformation `η : F ⟶ G` with a
pseudofunctor `P`. Its component at `a` is `η.app (P.obj a)` and its naturality isomorphism at
`f` is `η.naturality (P.map f)`. -/
@[expose] def whiskerLeft (η : F ⟶ G) : P.comp F ⟶ P.comp G where
  app a := η.app (P.obj a)
  naturality f := η.naturality (P.map f)
  naturality_naturality θ := η.naturality_naturality (P.map₂ θ)
  naturality_id a := by
    -- The unit comparison of `P.comp F` is `F.map₂ (P.mapId a).hom ≫ (F.mapId _).hom`, and
    -- `(P.comp F).map` is `F.map ∘ P.map`. Rewriting does not see through `Pseudofunctor.comp`,
    -- so `change` states the goal in this unfolded form for the rewrites below.
    change (η.naturality (P.map (𝟙 a))).hom ≫
        η.app (P.obj a) ◁ (G.map₂ (P.mapId a).hom ≫ (G.mapId (P.obj a)).hom) =
      (F.map₂ (P.mapId a).hom ≫ (F.mapId (P.obj a)).hom) ▷ η.app (P.obj a) ≫
        (λ_ (η.app (P.obj a))).hom ≫ (ρ_ (η.app (P.obj a))).inv
    -- Move `F.map₂` across the naturality isomorphism, then use oplax unity of `η`.
    rw [Bicategory.whiskerLeft_comp, ← η.naturality_naturality_assoc, η.naturality_id,
      comp_whiskerRight, Category.assoc]
  naturality_comp {a b c} f g := by
    -- As for the unit, unfold the composition comparison of `P.comp F`.
    change (η.naturality (P.map (f ≫ g))).hom ≫ η.app (P.obj a) ◁
        (G.map₂ (P.mapComp f g).hom ≫ (G.mapComp (P.map f) (P.map g)).hom) =
      (F.map₂ (P.mapComp f g).hom ≫ (F.mapComp (P.map f) (P.map g)).hom) ▷ η.app (P.obj c) ≫
        (α_ _ _ _).hom ≫ F.map (P.map f) ◁ (η.naturality (P.map g)).hom ≫ (α_ _ _ _).inv ≫
        (η.naturality (P.map f)).hom ▷ G.map (P.map g) ≫ (α_ _ _ _).hom
    -- Move `F.map₂` across the naturality isomorphism, then use oplax functoriality of `η`.
    rw [Bicategory.whiskerLeft_comp, ← η.naturality_naturality_assoc, η.naturality_comp,
      comp_whiskerRight, Category.assoc]

@[simp]
lemma whiskerLeft_app (η : F ⟶ G) (a : A) : (whiskerLeft P η).app a = η.app (P.obj a) :=
  rfl

@[simp]
lemma whiskerLeft_naturality {a b : A} (η : F ⟶ G) (f : a ⟶ b) :
    (whiskerLeft P η).naturality f = η.naturality (P.map f) :=
  rfl

/-- Precomposition preserves identity strong transformations. -/
@[simp]
lemma whiskerLeft_id : whiskerLeft P (𝟙 F) = 𝟙 (P.comp F) :=
  rfl

/-- Precomposition preserves composites of strong transformations. -/
@[simp]
lemma whiskerLeft_comp (η : F ⟶ G) (θ : G ⟶ H) :
    whiskerLeft P (η ≫ θ) = whiskerLeft P η ≫ whiskerLeft P θ :=
  rfl

/-- The precomposite `whiskerLeft P η ⟶ whiskerLeft P θ` of a modification `Γ : η ⟶ θ` with a
pseudofunctor `P`. Its component at `a` is `Γ.as.app (P.obj a)`. -/
@[expose] def whiskerLeftMap {η θ : F ⟶ G} (Γ : η ⟶ θ) : whiskerLeft P η ⟶ whiskerLeft P θ :=
  .of
    { app a := Γ.as.app (P.obj a)
      naturality f := Γ.as.naturality (P.map f) }

@[simp]
lemma whiskerLeftMap_as_app {η θ : F ⟶ G} (Γ : η ⟶ θ) (a : A) :
    (whiskerLeftMap P Γ).as.app a = Γ.as.app (P.obj a) :=
  rfl

@[simp]
lemma whiskerLeftMap_id (η : F ⟶ G) : whiskerLeftMap P (𝟙 η) = 𝟙 (whiskerLeft P η) :=
  rfl

@[simp]
lemma whiskerLeftMap_comp {η θ ι : F ⟶ G} (Γ : η ⟶ θ) (Δ : θ ⟶ ι) :
    whiskerLeftMap P (Γ ≫ Δ) = whiskerLeftMap P Γ ≫ whiskerLeftMap P Δ :=
  rfl

/-- Precomposition commutes with left whiskering of a modification by a strong
transformation. -/
@[simp]
lemma whiskerLeftMap_whiskerLeft (η : F ⟶ G) {θ ι : G ⟶ H} (Γ : θ ⟶ ι) :
    whiskerLeftMap P (η ◁ Γ) = whiskerLeft P η ◁ whiskerLeftMap P Γ :=
  rfl

/-- Precomposition commutes with right whiskering of a modification by a strong
transformation. -/
@[simp]
lemma whiskerLeftMap_whiskerRight {η θ : F ⟶ G} (Γ : η ⟶ θ) (ι : G ⟶ H) :
    whiskerLeftMap P (Γ ▷ ι) = whiskerLeftMap P Γ ▷ whiskerLeft P ι :=
  rfl

/-- Precomposition sends the associator of strong transformations to the associator. -/
@[simp]
lemma whiskerLeftMap_associator_hom (η : F ⟶ G) (θ : G ⟶ H) (ι : H ⟶ I) :
    whiskerLeftMap P (α_ η θ ι).hom =
      (α_ (whiskerLeft P η) (whiskerLeft P θ) (whiskerLeft P ι)).hom :=
  rfl

/-- Precomposition sends the left unitor of strong transformations to the left unitor. -/
@[simp]
lemma whiskerLeftMap_leftUnitor_hom (η : F ⟶ G) :
    whiskerLeftMap P (λ_ η).hom = (λ_ (whiskerLeft P η)).hom :=
  rfl

/-- Precomposition sends the right unitor of strong transformations to the right unitor. -/
@[simp]
lemma whiskerLeftMap_rightUnitor_hom (η : F ⟶ G) :
    whiskerLeftMap P (ρ_ η).hom = (ρ_ (whiskerLeft P η)).hom :=
  rfl

end CategoryTheory.Pseudofunctor
