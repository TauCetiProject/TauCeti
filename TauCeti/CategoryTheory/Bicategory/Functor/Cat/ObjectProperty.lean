/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Bicategory.Functor.Cat.ObjectProperty
public import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Pseudo
public import Mathlib.CategoryTheory.Bicategory.LocallyDiscrete

/-!
# Inverse images and lifts for pseudofunctor object properties

A strong transformation of `Cat`-valued pseudofunctors pulls back object properties fibrewise.
This construction respects identity transformations and composition, independently of any
Grothendieck topology or descent condition. It uses Mathlib's `ObjectProperty.inverseImage`
on each component functor. A transformation whose components land in a full sub-pseudofunctor
lifts through its inclusion. Postcomposition with the inclusion is fully faithful on modifications.
-/

public section

open CategoryTheory Bicategory Opposite

namespace CategoryTheory.Pseudofunctor.ObjectProperty

universe v v' u u'

variable {C : Type u} [Category.{v} C] {F G : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}}

/-- The inverse image of an object property along a strong transformation, computed in each
fibre category. -/
def inverseImage (Q : G.ObjectProperty) (η : StrongTrans F G) : F.ObjectProperty where
  prop U := (Q.prop U).inverseImage (η.app U).toFunctor

@[simp]
lemma inverseImage_prop (Q : G.ObjectProperty) (η : StrongTrans F G)
    (U : LocallyDiscrete Cᵒᵖ) (M : F.obj U) :
    (Q.inverseImage η).prop U M ↔ Q.prop U ((η.app U).toFunctor.obj M) :=
  Iff.rfl

@[simp]
lemma inverseImage_id (P : F.ObjectProperty) : P.inverseImage (StrongTrans.id F) = P :=
  (rfl)

@[simp]
lemma inverseImage_comp {H : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}}
    (Q : H.ObjectProperty) (η : StrongTrans F G) (θ : StrongTrans G H) :
    Q.inverseImage (StrongTrans.vcomp η θ) = (Q.inverseImage θ).inverseImage η :=
  (rfl)

section

open scoped Pseudofunctor.StrongTrans

universe w

variable {B : Type u} [Bicategory.{w, v} B] {F G : B ⥤ᵖ Cat.{v', u'}}
variable (P : G.ObjectProperty) [P.IsClosedUnderMapObj]

/-- Lift a strong transformation whose component functors land in the full subcategories. -/
def lift (η : F ⟶ G) (h : ∀ X M, P.prop X ((η.app X).toFunctor.obj M)) :
    F ⟶ P.fullsubcategory where
  app X := ((P.prop X).lift (η.app X).toFunctor (h X)).toCatHom
  naturality {X Y} f := Cat.Hom.isoMk <|
    ((P.prop Y).fullyFaithfulι.whiskeringRight _).preimageIso (Cat.Hom.toNatIso (η.naturality f))
  naturality_naturality α := by
    ext M
    apply (P.prop _).hom_ext
    exact congrArg (fun t ↦ t.toNatTrans.app M) (η.naturality_naturality α)
  naturality_id X := by
    ext M
    apply (P.prop _).hom_ext
    exact congrArg (fun t ↦ t.toNatTrans.app M) (η.naturality_id X)
  naturality_comp f g := by
    ext M
    apply (P.prop _).hom_ext
    exact congrArg (fun t ↦ t.toNatTrans.app M) (η.naturality_comp f g)

@[simp]
lemma lift_app (η : F ⟶ G) (h : ∀ X M, P.prop X ((η.app X).toFunctor.obj M)) (X : B) :
    (P.lift η h).app X = ((P.prop X).lift (η.app X).toFunctor (h X)).toCatHom :=
  (rfl)

/-- Including the lift recovers the original strong transformation up to invertible modification. -/
def liftCompιIso (η : F ⟶ G) (h : ∀ X M, P.prop X ((η.app X).toFunctor.obj M)) :
    P.lift η h ≫ P.ι ≅ η :=
  StrongTrans.isoMk (fun _ ↦ Iso.refl _) (fun f ↦ by
    ext M
    -- The included lift agrees with η fibrewise by definition. Write the components explicitly
    -- so that the associators and the naturality of the inclusion reduce to identities.
    change 𝟙 _ ≫ (η.naturality f).hom.toNatTrans.app M =
      (𝟙 _ ≫ (η.naturality f).hom.toNatTrans.app M ≫ 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _) ≫
        (G.map f).toFunctor.map (𝟙 _)
    simp)

/-- Every modification between composites with the inclusion lifts uniquely. -/
def fullyFaithfulPostcompι (F : B ⥤ᵖ Cat.{v', u'}) : (postcomp F P.ι).FullyFaithful where
  preimage {η θ} m := ⟨{
    app X := Cat.Hom₂.ofNatTrans <|
      ((P.prop X).fullyFaithfulι.whiskeringRight _).preimage (m.as.app X).toNatTrans
    naturality {X Y} f := by
      ext M
      apply (P.prop Y).hom_ext
      have eqn := congrArg (fun t ↦ t.toNatTrans.app M) (m.as.naturality f)
      -- Evaluate in the ambient category: the lifted endpoints agree there by definition,
      -- and the associators and the naturality of the inclusion all have identity components.
      change (m.as.app Y).toNatTrans.app ((F.map f).toFunctor.obj M) ≫
          (𝟙 _ ≫ ((θ.naturality f).hom.toNatTrans.app M).hom ≫ 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _) =
        (𝟙 _ ≫ ((η.naturality f).hom.toNatTrans.app M).hom ≫ 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _) ≫
          (G.map f).toFunctor.map ((m.as.app X).toNatTrans.app M) at eqn
      simp only [Category.comp_id, Category.id_comp] at eqn
      erw [Category.comp_id] at eqn
      exact eqn
  }⟩
  map_preimage m := by ext; rfl
  preimage_map m := by ext; rfl

end

end CategoryTheory.Pseudofunctor.ObjectProperty
