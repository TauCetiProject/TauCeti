/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Pseudo
public import Mathlib.CategoryTheory.Monoidal.Action.LinearFunctor
public import TauCeti.CategoryTheory.Monoidal.Action.Pseudofunctor

/-!
# Equivariant functors as strong transformations

Let a monoid `M` act on categories `C` and `D`, that is, let `Discrete M` act on the left on
both. A functor `F : C ⥤ D` is equivariant when it is left-linear for these actions in the sense
of Mathlib's `Functor.LeftLinear`: it carries isomorphisms `F (g ⊙ₗ X) ≅ g ⊙ₗ F X` compatible
with the unitors and associators of the two actions. Equivalently, it carries natural
isomorphisms `actionLeft C g ⋙ F ≅ F ⋙ actionLeft D g` satisfying the unit and product
diagrams; this is `Functor.commActionLeftIso`, defined for an arbitrary monoidal category acting.

The actions correspond to the pseudofunctors `pseudofunctor M C` and `pseudofunctor M D` out of
`LocallyDiscrete (SingleObj M)`, and this file shows that equivariant functors are exactly the
strong transformations between these pseudofunctors.

* `MonoidalLeftAction.strongTrans M F` is the strong transformation with component `F` whose
  naturality isomorphism at `g` comes from `F.commActionLeftIso ⟨g⟩`: its components are the oplax
  lineators `δₗ F ⟨g⟩ X : F (g ⊙ₗ X) ⟶ g ⊙ₗ F X`. The unit and composition axioms of a strong
  transformation are the unitality and associativity of these lineators.
* Conversely `MonoidalLeftAction.functorOfStrongTrans η` is the component of a strong
  transformation `η` at the unique object, and it is left-linear with lineators the components
  of the naturality isomorphisms of `η`.
* `MonoidalLeftAction.strongTransEquiv` packages the two constructions as an equivalence between
  functors equipped with a left-linear structure and strong transformations. Both round trips
  hold definitionally, so the comparison keeps the lineators, and not only the functor.

The order conventions are those of `MonoidalLeftAction.pseudofunctor`: the composite `g ≫ h` in
`SingleObj M` is the product `h * g`, which acts by `actionLeft C g ⋙ actionLeft C h`.
-/

public section

universe w v u

namespace CategoryTheory

open Bicategory MonoidalCategory MonoidalLeftAction Functor.LaxLeftLinear
  Functor.OplaxLeftLinear

namespace Functor

variable {C : Type*} [Category* C] [MonoidalCategory C] {D D' : Type*} [Category* D]
  [Category* D'] [MonoidalLeftAction C D] [MonoidalLeftAction C D'] (F : D ⥤ D')
  [F.LeftLinear C]

/-- A left-linear functor commutes with the action functors: the natural isomorphism
`actionLeft D c ⋙ F ≅ F ⋙ actionLeft D' c` whose components are the oplax lineators
`δₗ F c X : F (c ⊙ₗ X) ⟶ c ⊙ₗ F X`, with inverse the lax lineators `μₗ F c X`. -/
def commActionLeftIso (c : C) : actionLeft D c ⋙ F ≅ F ⋙ actionLeft D' c :=
  NatIso.ofComponents (fun X ↦ (LeftLinear.μₗIso F c X).symm)
    (fun f ↦ δₗ_naturality_right F c f)

@[simp]
lemma commActionLeftIso_hom_app (c : C) (X : D) :
    ((F.commActionLeftIso c).hom.app X : F.obj (c ⊙ₗ X) ⟶ c ⊙ₗ F.obj X) = δₗ F c X :=
  (rfl)

@[simp]
lemma commActionLeftIso_inv_app (c : C) (X : D) :
    ((F.commActionLeftIso c).inv.app X : c ⊙ₗ F.obj X ⟶ F.obj (c ⊙ₗ X)) = μₗ F c X :=
  (rfl)

end Functor

namespace MonoidalCategory.MonoidalLeftAction

variable {M : Type u} [Monoid M] {C D : Type w} [Category.{v} C] [Category.{v} D]
  [MonoidalLeftAction (Discrete M) C] [MonoidalLeftAction (Discrete M) D]

section strongTrans

variable (M) (F : C ⥤ D) [F.LeftLinear (Discrete M)]

/-- A functor that is left-linear for actions of a monoid `M` on `C` and on `D` is a strong
transformation `pseudofunctor M C ⟶ pseudofunctor M D`. Its component at the unique object is
`F`, and its naturality isomorphism at `g` is the `2`-isomorphism of `Cat` given by
`F.commActionLeftIso ⟨g⟩ : actionLeft C ⟨g⟩ ⋙ F ≅ F ⋙ actionLeft D ⟨g⟩`. -/
@[expose] def strongTrans : Pseudofunctor.StrongTrans (pseudofunctor M C) (pseudofunctor M D) where
  app _ := F.toCatHom
  naturality g := Cat.Hom.isoMk (F.commActionLeftIso (⟨g.as⟩ : Discrete M))
  -- In the three coherence conditions the component `F.toCatHom` has type `Cat.of C ⟶ Cat.of D`
  -- while `(pseudofunctor M C).obj a` is only definitionally `Cat.of C`, so the component
  -- lemmas of `Cat` do not apply. The conditions are instead stated componentwise in `C` and
  -- `D` and closed by definitional unfolding of the components.
  naturality_naturality η := by
    obtain rfl := LocallyDiscrete.eq_of_hom η
    rw [Subsingleton.elim η (𝟙 _)]
    simp only [PrelaxFunctor.map₂_id]
    have h (c : Discrete M) (X : C) : F.map (𝟙 _) ≫ δₗ F c X = δₗ F c X ≫ 𝟙 _ := by simp
    ext X
    exact h _ X
  naturality_id _ := by
    have h (X : C) : δₗ F (𝟙_ (Discrete M)) X ≫ (λₗ (F.obj X)).hom =
        F.map (λₗ X).hom ≫ 𝟙 _ ≫ 𝟙 _ := by
      simp
    ext X
    exact h X
  naturality_comp f g := by
    have h (X : C) : δₗ F (⟨g.as * f.as⟩ : Discrete M) X ≫
          ((pseudofunctor M D).mapComp f g).hom.toNatTrans.app (F.obj X) =
        F.map (((pseudofunctor M C).mapComp f g).hom.toNatTrans.app X) ≫ 𝟙 _ ≫
          δₗ F (⟨g.as⟩ : Discrete M) ((⟨f.as⟩ : Discrete M) ⊙ₗ X) ≫ 𝟙 _ ≫
          (⟨g.as⟩ : Discrete M) ⊴ₗ δₗ F (⟨f.as⟩ : Discrete M) X ≫ 𝟙 _ := by
      simp only [pseudofunctor_mapComp_hom_toNatTrans_app, Category.id_comp, Category.comp_id]
      exact δₗ_associativity F _ _ X
    ext X
    exact h X

@[simp]
lemma strongTrans_app (a : LocallyDiscrete (SingleObj M)) :
    (strongTrans M F).app a = F.toCatHom :=
  (rfl)

@[simp]
lemma strongTrans_naturality_hom_toNatTrans_app {a b : LocallyDiscrete (SingleObj M)}
    (g : a ⟶ b) (X : C) :
    (((strongTrans M F).naturality g).hom.toNatTrans.app X :
      F.obj ((⟨g.as⟩ : Discrete M) ⊙ₗ X) ⟶ (⟨g.as⟩ : Discrete M) ⊙ₗ F.obj X) =
      δₗ F (⟨g.as⟩ : Discrete M) X :=
  (rfl)

@[simp]
lemma strongTrans_naturality_inv_toNatTrans_app {a b : LocallyDiscrete (SingleObj M)}
    (g : a ⟶ b) (X : C) :
    (((strongTrans M F).naturality g).inv.toNatTrans.app X :
      (⟨g.as⟩ : Discrete M) ⊙ₗ F.obj X ⟶ F.obj ((⟨g.as⟩ : Discrete M) ⊙ₗ X)) =
      μₗ F (⟨g.as⟩ : Discrete M) X :=
  (rfl)

end strongTrans

section functorOfStrongTrans

variable (η : Pseudofunctor.StrongTrans (pseudofunctor M C) (pseudofunctor M D))

/-- The functor `C ⥤ D` underlying a strong transformation
`η : pseudofunctor M C ⟶ pseudofunctor M D`: its component at the unique object. -/
@[expose] def functorOfStrongTrans : C ⥤ D :=
  (η.app ⟨SingleObj.star M⟩).toFunctor

/-- The functor underlying a strong transformation `η : pseudofunctor M C ⟶ pseudofunctor M D`
is left-linear: its oplax lineator `δₗ _ c X` is the component at `X` of the naturality
isomorphism of `η` at `c`, and its lax lineator is the inverse. The unitality and associativity
of the lineators are the unit and composition axioms of `η`. -/
instance leftLinearFunctorOfStrongTrans : (functorOfStrongTrans η).LeftLinear (Discrete M) where
  μₗ c X := (η.naturality c).inv.toNatTrans.app X
  δₗ c X := (η.naturality c).hom.toNatTrans.app X
  μₗ_naturality_left f X := by
    obtain rfl := Discrete.ext (Discrete.eq_of_hom f)
    simp only [Subsingleton.elim f (𝟙 _), id_actionHomLeft, Functor.map_id]
    exact (Category.id_comp _).trans (Category.comp_id _).symm
  μₗ_naturality_right c _ _ f := (η.naturality c).inv.toNatTrans.naturality f
  -- The component lemmas of `Cat` apply to objects of `(pseudofunctor M C).obj _`, which is only
  -- definitionally `C`. The coherence conditions are therefore computed for such objects `Y`,
  -- then specialized to `X : C`, where the associator and unitor of the action appear.
  μₗ_associativity c c' X := by
    have key (Y : ↑((pseudofunctor M C).obj ⟨SingleObj.star M⟩)) :=
      congrArg (·.toNatTrans.app Y) (η.naturality_comp_inv (a := ⟨SingleObj.star M⟩)
        (b := ⟨SingleObj.star M⟩) (c := ⟨SingleObj.star M⟩) c' c)
    simp only [Cat.Hom.toNatTrans_comp, NatTrans.comp_app, Cat.whiskerLeft_app,
      Cat.whiskerRight_app, Cat.associator_hom_app, Cat.associator_inv_app, eqToHom_refl,
      Category.id_comp] at key
    have key' (Y : ↑((pseudofunctor M C).obj ⟨SingleObj.star M⟩)) :
        (η.naturality (a := ⟨SingleObj.star M⟩) (b := ⟨SingleObj.star M⟩)
            (c' ≫ c)).inv.toNatTrans.app Y ≫
          (η.app ⟨SingleObj.star M⟩).toFunctor.map (((pseudofunctor M C).mapComp
            (a := ⟨SingleObj.star M⟩) (b := ⟨SingleObj.star M⟩) (c := ⟨SingleObj.star M⟩)
            c' c).hom.toNatTrans.app Y) =
        ((pseudofunctor M D).mapComp (a := ⟨SingleObj.star M⟩) (b := ⟨SingleObj.star M⟩)
            (c := ⟨SingleObj.star M⟩) c' c).hom.toNatTrans.app
            ((η.app ⟨SingleObj.star M⟩).toFunctor.obj Y) ≫
          ((pseudofunctor M D).map c).toFunctor.map ((η.naturality c').inv.toNatTrans.app Y) ≫
          (η.naturality c).inv.toNatTrans.app (((pseudofunctor M C).map c').toFunctor.obj Y) := by
      rw [key Y]
      simp only [Category.assoc, ← Functor.map_comp, Cat.Hom.inv_hom_id_toNatTrans_app,
        Functor.map_id, Cat.Hom.comp_toFunctor, Functor.comp_obj, Category.comp_id]
    have h : (η.naturality (a := ⟨SingleObj.star M⟩) (b := ⟨SingleObj.star M⟩)
          (c' ≫ c)).inv.toNatTrans.app X ≫
        (functorOfStrongTrans η).map ((actionLeftTensorIso C c c').hom.app X) =
        (actionLeftTensorIso D c c').hom.app ((functorOfStrongTrans η).obj X) ≫
          (actionLeft D c).map ((η.naturality c').inv.toNatTrans.app X) ≫
          (η.naturality c).inv.toNatTrans.app (c' ⊙ₗ X : C) :=
      key' X
    rw [actionLeftTensorIso_hom_app, actionLeftTensorIso_hom_app] at h
    exact h
  μₗ_unitality X := by
    have key (Y : ↑((pseudofunctor M C).obj ⟨SingleObj.star M⟩)) :=
      congrArg (·.toNatTrans.app Y)
        (Pseudofunctor.StrongTrans.naturality_id_inv η ⟨SingleObj.star M⟩)
    simp only [Cat.Hom.toNatTrans_comp, NatTrans.comp_app, Cat.whiskerLeft_app,
      Cat.whiskerRight_app, Cat.leftUnitor_inv_app, Cat.rightUnitor_hom_app, eqToHom_refl,
      Category.id_comp] at key
    have key' (Y : ↑((pseudofunctor M C).obj ⟨SingleObj.star M⟩)) :
        ((pseudofunctor M D).mapId ⟨SingleObj.star M⟩).hom.toNatTrans.app
            ((η.app ⟨SingleObj.star M⟩).toFunctor.obj Y) =
          (η.naturality (𝟙 ⟨SingleObj.star M⟩)).inv.toNatTrans.app Y ≫
          (η.app ⟨SingleObj.star M⟩).toFunctor.map
            (((pseudofunctor M C).mapId ⟨SingleObj.star M⟩).hom.toNatTrans.app Y) := by
      rw [key Y]
      simp only [Category.assoc, ← Functor.map_comp, Cat.Hom.inv_hom_id_toNatTrans_app,
        Functor.map_id, Cat.Hom.id_toFunctor, Functor.id_obj]
      exact (Category.comp_id _).symm
    exact key' X
  δₗ_naturality_left f X := by
    obtain rfl := Discrete.ext (Discrete.eq_of_hom f)
    simp only [Subsingleton.elim f (𝟙 _), id_actionHomLeft, Functor.map_id]
    exact (Category.id_comp _).trans (Category.comp_id _).symm
  δₗ_naturality_right c _ _ f := (η.naturality c).hom.toNatTrans.naturality f
  δₗ_associativity c c' X := by
    have key (Y : ↑((pseudofunctor M C).obj ⟨SingleObj.star M⟩)) :=
      congrArg (·.toNatTrans.app Y) (η.naturality_comp (a := ⟨SingleObj.star M⟩)
        (b := ⟨SingleObj.star M⟩) (c := ⟨SingleObj.star M⟩) c' c)
    simp only [Cat.Hom.toNatTrans_comp, NatTrans.comp_app, Cat.whiskerLeft_app,
      Cat.whiskerRight_app, Cat.associator_hom_app, Cat.associator_inv_app, eqToHom_refl,
      Category.id_comp, Category.comp_id] at key
    have h : (η.naturality (a := ⟨SingleObj.star M⟩) (b := ⟨SingleObj.star M⟩)
          (c' ≫ c)).hom.toNatTrans.app X ≫
        (actionLeftTensorIso D c c').hom.app ((functorOfStrongTrans η).obj X) =
        (functorOfStrongTrans η).map ((actionLeftTensorIso C c c').hom.app X) ≫
          (η.naturality c).hom.toNatTrans.app (c' ⊙ₗ X : C) ≫
          (actionLeft D c).map ((η.naturality c').hom.toNatTrans.app X) :=
      key X
    rw [actionLeftTensorIso_hom_app, actionLeftTensorIso_hom_app] at h
    exact h
  δₗ_unitality_inv X := by
    have key (Y : ↑((pseudofunctor M C).obj ⟨SingleObj.star M⟩)) :=
      congrArg (·.toNatTrans.app Y) (η.naturality_id ⟨SingleObj.star M⟩)
    simp only [Cat.Hom.toNatTrans_comp, NatTrans.comp_app, Cat.whiskerLeft_app,
      Cat.whiskerRight_app, Cat.leftUnitor_hom_app, Cat.rightUnitor_inv_app, eqToHom_refl,
      Category.comp_id] at key
    have key' (Y : ↑((pseudofunctor M C).obj ⟨SingleObj.star M⟩)) :
        ((pseudofunctor M D).mapId ⟨SingleObj.star M⟩).inv.toNatTrans.app
            ((η.app ⟨SingleObj.star M⟩).toFunctor.obj Y) =
          (η.app ⟨SingleObj.star M⟩).toFunctor.map
            (((pseudofunctor M C).mapId ⟨SingleObj.star M⟩).inv.toNatTrans.app Y) ≫
          (η.naturality (𝟙 ⟨SingleObj.star M⟩)).hom.toNatTrans.app Y := by
      rw [← cancel_mono (((pseudofunctor M D).mapId ⟨SingleObj.star M⟩).hom.toNatTrans.app _),
        Category.assoc, key Y]
      simp only [Cat.Hom.inv_hom_id_toNatTrans_app, ← Functor.map_comp, Functor.map_id,
        Cat.Hom.id_toFunctor, Functor.id_obj]
    exact key' X
  μₗ_comp_δₗ c X := Cat.Hom.inv_hom_id_toNatTrans_app (η.naturality c) X
  δₗ_comp_μₗ c X := Cat.Hom.hom_inv_id_toNatTrans_app (η.naturality c) X

lemma functorOfStrongTrans_δₗ (c : Discrete M) (X : C) :
    δₗ (functorOfStrongTrans η) c X =
      (η.naturality c).hom.toNatTrans.app X :=
  (rfl)

lemma functorOfStrongTrans_μₗ (c : Discrete M) (X : C) :
    μₗ (functorOfStrongTrans η) c X =
      (η.naturality c).inv.toNatTrans.app X :=
  (rfl)

end functorOfStrongTrans

@[simp]
lemma functorOfStrongTrans_strongTrans (F : C ⥤ D) [F.LeftLinear (Discrete M)] :
    functorOfStrongTrans (strongTrans M F) = F :=
  (rfl)

lemma leftLinearFunctorOfStrongTrans_strongTrans (F : C ⥤ D) [inst : F.LeftLinear (Discrete M)] :
    leftLinearFunctorOfStrongTrans (strongTrans M F) = inst :=
  (rfl)

@[simp]
lemma strongTrans_functorOfStrongTrans
    (η : Pseudofunctor.StrongTrans (pseudofunctor M C) (pseudofunctor M D)) :
    strongTrans M (functorOfStrongTrans η) = η :=
  (rfl)

variable (M C D) in
/-- Equivariant functors are the strong transformations between the pseudofunctors attached to
the actions: functors `C ⥤ D` equipped with a left-linear structure for the actions of
`Discrete M` correspond to strong transformations `pseudofunctor M C ⟶ pseudofunctor M D`. The
correspondence keeps the lineators: the naturality isomorphisms of `strongTrans M F` have
components the lineators of `F`. -/
def strongTransEquiv : (Σ F : C ⥤ D, F.LeftLinear (Discrete M)) ≃
    Pseudofunctor.StrongTrans (pseudofunctor M C) (pseudofunctor M D) where
  toFun F := letI := F.2; strongTrans M F.1
  invFun η := ⟨functorOfStrongTrans η, leftLinearFunctorOfStrongTrans η⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
lemma strongTransEquiv_apply (F : Σ F : C ⥤ D, F.LeftLinear (Discrete M)) :
    strongTransEquiv M C D F = letI := F.2; strongTrans M F.1 :=
  (rfl)

@[simp]
lemma strongTransEquiv_symm_apply
    (η : Pseudofunctor.StrongTrans (pseudofunctor M C) (pseudofunctor M D)) :
    (strongTransEquiv M C D).symm η = ⟨functorOfStrongTrans η, leftLinearFunctorOfStrongTrans η⟩ :=
  (rfl)

end MonoidalCategory.MonoidalLeftAction

end CategoryTheory
