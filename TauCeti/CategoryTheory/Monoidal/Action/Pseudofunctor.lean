/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.SingleObj
public import TauCeti.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import TauCeti.CategoryTheory.Monoidal.Action.Basic

/-!
# Monoid actions on categories as pseudofunctors

A monoid `M` acts on a category `C` in the categorical sense when we are given a left action
`MonoidalLeftAction (Discrete M) C` of the discrete monoidal category on `M`. Equivalently, such
an action is a pseudofunctor `LocallyDiscrete (SingleObj M) ⥤ᵖ Cat` out of the one-object
bicategory of `M` whose value at the unique object is `C`. This file constructs both directions
of this comparison and shows that they are mutually inverse. It is the case of a discrete
monoidal category of the comparison between actions and pseudofunctors listed as a TODO in
`Mathlib.CategoryTheory.Monoidal.Action.Basic`.

Composition order: in `SingleObj M` the composite `g ≫ h` is the product `h * g`, while a left
action satisfies `T (h * g) ≅ T g ⋙ T h`. Thus the pseudofunctor sends `g` to the action
functor `actionLeft C ⟨g⟩`, its unit comparison is `λₗ`, and its composition comparison at
`g ≫ h` has components `αₗ ⟨h⟩ ⟨g⟩ X : (h * g) ⊙ₗ X ≅ h ⊙ₗ g ⊙ₗ X`. The coherence of the
pseudofunctor is exactly the associativity and unit axioms of the action, and conversely.

## Main declarations

* `CategoryTheory.MonoidalCategory.MonoidalLeftAction.pseudofunctor`: the pseudofunctor
  `LocallyDiscrete (SingleObj M) ⥤ᵖ Cat` attached to an action of `Discrete M` on `C`;
* `CategoryTheory.Pseudofunctor.monoidalLeftAction`: conversely, the action of `Discrete M` on
  the value of a pseudofunctor `LocallyDiscrete (SingleObj M) ⥤ᵖ Cat` at the unique object,
  whose associator and unitor are given by the composition and unit comparisons of the
  pseudofunctor;
* `CategoryTheory.MonoidalCategory.MonoidalLeftAction.monoidalLeftAction_pseudofunctor`:
  the action recovered from `pseudofunctor M C` is the original action, including its
  associator and unitor;
* `CategoryTheory.Pseudofunctor.pseudofunctor_monoidalLeftAction`: conversely, the pseudofunctor
  recovered from `F.monoidalLeftAction` is `F`, including its unit and composition comparisons;
* `CategoryTheory.MonoidalCategory.MonoidalLeftAction.pseudofunctorEquiv`: the resulting
  bijection between categories equipped with a left action of `Discrete M` and pseudofunctors
  `LocallyDiscrete (SingleObj M) ⥤ᵖ Cat`.
-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Bicategory MonoidalCategory MonoidalLeftAction

namespace MonoidalCategory.MonoidalLeftAction

section SingleObj

variable (M : Type u) [Monoid M] (C : Type w) [Category.{v} C] [MonoidalLeftAction (Discrete M) C]

/-- The pseudofunctor `LocallyDiscrete (SingleObj M) ⥤ᵖ Cat` attached to a left action of
`Discrete M` on `C`. It sends the unique object to `C` and `g` to `actionLeft C ⟨g⟩`; its unit
comparison is `λₗ` and its composition comparison at `g ≫ h` (that is, at `h * g`) has
components `αₗ ⟨h⟩ ⟨g⟩`. -/
@[simps! obj]
def pseudofunctor : LocallyDiscrete (SingleObj M) ⥤ᵖ Cat.{v, w} :=
  LocallyDiscrete.mkPseudofunctor (fun _ ↦ Cat.of C)
    (fun g ↦ (actionLeft C (Discrete.mk g)).toCatHom)
    (fun _ ↦ Cat.Hom.isoMk (actionUnitNatIso (Discrete M) C))
    (fun g h ↦ Cat.Hom.isoMk (actionLeftTensorIso C (Discrete.mk h) (Discrete.mk g)))
    (fun f g h ↦ by
      ext X
      have := (associator_actionHom (⟨h⟩ : Discrete M) ⟨g⟩ ⟨f⟩ (D := C) X =≫
        (actionAssocIso (D := C) (⟨h⟩ : Discrete M) ⟨g⟩ _).inv) =≫
          (actionAssocIso (D := C) ((⟨h⟩ : Discrete M) ⊗ ⟨g⟩) ⟨f⟩ X).inv
      simp only [actionHomLeft_eq_eqToHom, Category.assoc, Iso.hom_inv_id,
        eqToHom_comp_iff, Category.comp_id] at this
      -- After computing the components of the `2`-cells of `Cat`, the goal is `this` with the
      -- tensor products of `Discrete M` written as composites in `SingleObj M`.
      simp only [Cat.of_α, Functor.toCatHom_toFunctor, Cat.Hom.isoMk_hom, Cat.Hom.isoMk_inv,
        Cat.Hom.toNatTrans_comp, Cat.Hom.comp_toFunctor, NatTrans.toCatHom₂_toNatTrans,
        Cat.whiskerRight_toNatTrans, Cat.associator_hom_toNatTrans, Cat.whiskerLeft_toNatTrans,
        NatTrans.comp_app, Functor.comp_obj, actionLeftTensorIso_hom_app, Functor.whiskerRight_app,
        Functor.associator_hom_app, Functor.whiskerLeft_app, actionLeftTensorIso_inv_app,
        Category.id_comp, Cat.Hom₂.eqToHom_toNatTrans, eqToHom_app]
      exact this)
    (fun f ↦ by
      ext X
      simp only [Cat.of_α, Functor.toCatHom_toFunctor, Cat.Hom.isoMk_hom,
        Cat.Hom.toNatTrans_comp, Cat.Hom.comp_toFunctor, NatTrans.toCatHom₂_toNatTrans,
        Cat.Hom.id_toFunctor, Cat.whiskerRight_toNatTrans, Cat.leftUnitor_hom_toNatTrans,
        NatTrans.comp_app, Functor.comp_obj, actionLeftTensorIso_hom_app, Functor.id_obj,
        Functor.whiskerRight_app, actionUnitNatIso_hom_app, Functor.leftUnitor_hom_app,
        Category.comp_id, Cat.Hom₂.eqToHom_toNatTrans, eqToHom_app]
      -- The goal is the right unitor axiom, with `𝟙_ (Discrete M)` written as `⟨𝟙 b₀⟩`.
      exact (rightUnitor_actionHom (⟨f⟩ : Discrete M) (D := C) X).symm.trans
        (actionHomLeft_eq_eqToHom _ _))
    (fun f ↦ by
      ext X
      simp only [Cat.of_α, Functor.toCatHom_toFunctor, Cat.Hom.isoMk_hom,
        Cat.Hom.toNatTrans_comp, Cat.Hom.comp_toFunctor, NatTrans.toCatHom₂_toNatTrans,
        Cat.Hom.id_toFunctor, Cat.whiskerLeft_toNatTrans, Cat.rightUnitor_hom_toNatTrans,
        NatTrans.comp_app, Functor.comp_obj, actionLeftTensorIso_hom_app, Functor.id_obj,
        Functor.whiskerLeft_app, actionUnitNatIso_hom_app, Functor.rightUnitor_hom_app,
        Cat.Hom₂.eqToHom_toNatTrans, eqToHom_app]
      -- The right unitor of `Cat` contributes an identity whose source is only definitionally
      -- the target of the left unitor of the action, so `simp` cannot remove it.
      refine (congrArg (_ ≫ ·) (Category.comp_id _)).trans ?_
      exact (leftUnitor_actionHom (⟨f⟩ : Discrete M) (D := C) X).symm.trans
        (actionHomLeft_eq_eqToHom _ _))

variable {M C}

@[simp]
lemma pseudofunctor_map_toFunctor {a b : LocallyDiscrete (SingleObj M)} (g : a ⟶ b) :
    ((pseudofunctor M C).map g).toFunctor = actionLeft C (⟨g.as⟩ : Discrete M) :=
  rfl

@[simp]
lemma pseudofunctor_mapId_hom_toNatTrans_app (a : LocallyDiscrete (SingleObj M)) (X : C) :
    ((pseudofunctor M C).mapId a).hom.toNatTrans.app X = (λₗ X).hom :=
  rfl

@[simp]
lemma pseudofunctor_mapId_inv_toNatTrans_app (a : LocallyDiscrete (SingleObj M)) (X : C) :
    ((pseudofunctor M C).mapId a).inv.toNatTrans.app X = (λₗ X).inv :=
  rfl

@[simp]
lemma pseudofunctor_mapComp_hom_toNatTrans_app {a b c : LocallyDiscrete (SingleObj M)}
    (g : a ⟶ b) (h : b ⟶ c) (X : C) :
    ((pseudofunctor M C).mapComp g h).hom.toNatTrans.app X =
      (αₗ (⟨h.as⟩ : Discrete M) ⟨g.as⟩ X).hom :=
  actionLeftTensorIso_hom_app C _ _ X

@[simp]
lemma pseudofunctor_mapComp_inv_toNatTrans_app {a b c : LocallyDiscrete (SingleObj M)}
    (g : a ⟶ b) (h : b ⟶ c) (X : C) :
    ((pseudofunctor M C).mapComp g h).inv.toNatTrans.app X =
      (αₗ (⟨h.as⟩ : Discrete M) ⟨g.as⟩ X).inv :=
  actionLeftTensorIso_inv_app C _ _ X

end SingleObj

end MonoidalCategory.MonoidalLeftAction

namespace Pseudofunctor

variable {M : Type u} [Monoid M] (F : LocallyDiscrete (SingleObj M) ⥤ᵖ Cat.{v, w})

/-- The left action of `Discrete M` on the value of a pseudofunctor
`F : LocallyDiscrete (SingleObj M) ⥤ᵖ Cat` at the unique object. The action functor of `c` is
`F.map c`, the associator `αₗ c c'` has components those of `F.mapComp c' c`, and the unitor
`λₗ` has components those of `F.mapId`. -/
@[simps!, instance_reducible]
def monoidalLeftAction : MonoidalLeftAction (Discrete M) (F.obj ⟨SingleObj.star M⟩) where
  actionObj c X := (F.map (X := ⟨.star M⟩) (Y := ⟨.star M⟩) c).toFunctor.obj X
  actionHomLeft f _ := eqToHom (by rw [Discrete.ext (Discrete.eq_of_hom f)])
  actionHomRight c _ _ f := (F.map (X := ⟨.star M⟩) (Y := ⟨.star M⟩) c).toFunctor.map f
  actionAssocIso c c' X :=
    (Cat.Hom.toNatIso (F.mapComp (a := ⟨.star M⟩) (b := ⟨.star M⟩) (c := ⟨.star M⟩) c' c)).app X
  actionUnitIso X := (Cat.Hom.toNatIso (F.mapId ⟨SingleObj.star M⟩)).app X
  actionHom_comp f₁ f₂ _ _ := by
    obtain rfl := Discrete.ext (Discrete.eq_of_hom f₁)
    obtain rfl := Discrete.ext (Discrete.eq_of_hom f₂)
    simp
  actionAssocIso_hom_naturality f g _ := by
    obtain rfl := Discrete.ext (Discrete.eq_of_hom f)
    obtain rfl := Discrete.ext (Discrete.eq_of_hom g)
    simp
  whiskerLeft_actionHomLeft _ _ _ f _ := by
    obtain rfl := Discrete.ext (Discrete.eq_of_hom f)
    simp
    -- `c ⊗ c'` and the composite `c' ≫ c` in `LocallyDiscrete (SingleObj M)` are both
    -- `⟨c.as * c'.as⟩`, but only up to unfolding the two instances.
    rfl
  whiskerRight_actionHomLeft _ f _ := by
    obtain rfl := Discrete.ext (Discrete.eq_of_hom f)
    simp
    -- As above, `c ⊗ c'` and `c' ≫ c` agree only up to unfolding instances.
    rfl
  associator_actionHom c₁ c₂ c₃ X := by
    have := F.mapComp_assoc_left_hom_app (b := ⟨.star M⟩) (c := ⟨.star M⟩) (d := ⟨.star M⟩)
      c₃ c₂ c₁ X
    rw [PrelaxFunctor.map₂_eq_eqToHom, Cat.eqToHom_app, ← eqToHom_comp_iff] at this
    -- `this` is the goal, with `c₂ ⊗ c₃` written as the composite `c₃ ≫ c₂`.
    exact this
  leftUnitor_actionHom c X := by
    have := F.mapComp_id_right_hom_app (a := ⟨.star M⟩) (b := ⟨.star M⟩) c X =≫
      (F.mapId ⟨.star M⟩).hom.toNatTrans.app ((F.map c).toFunctor.obj X)
    simp only [Category.assoc, Cat.Hom.inv_hom_id_toNatTrans_app, PrelaxFunctor.map₂_eq_eqToHom,
      Cat.eqToHom_app] at this
    -- `this` is the goal up to a trailing identity and with `𝟙_ (Discrete M)` written as the
    -- identity `1`-morphism; the two agree only up to unfolding instances.
    exact (Category.comp_id _).symm.trans this.symm
  rightUnitor_actionHom c X := by
    have := F.mapComp_id_left_hom_app (a := ⟨.star M⟩) (b := ⟨.star M⟩) c X =≫
      (F.map c).toFunctor.map ((F.mapId ⟨.star M⟩).hom.toNatTrans.app X)
    simp only [Category.assoc, ← Functor.map_comp, Cat.Hom.inv_hom_id_toNatTrans_app,
      Functor.map_id, PrelaxFunctor.map₂_eq_eqToHom, Cat.eqToHom_app] at this
    -- As for the left unitor.
    exact (Category.comp_id _).symm.trans this.symm

end Pseudofunctor

namespace MonoidalCategory.MonoidalLeftAction

variable (M : Type u) [Monoid M] (C : Type w) [Category.{v} C]

/-- The action of `Discrete M` recovered from the pseudofunctor `pseudofunctor M C` is the
original action: the comparison transports the action functors, the associator and the unitor
unchanged. -/
theorem monoidalLeftAction_pseudofunctor [inst : MonoidalLeftAction (Discrete M) C] :
    (pseudofunctor M C).monoidalLeftAction = inst := by
  have hLeft {c c' : Discrete M} (f : c ⟶ c') (X : C) := actionHomLeft_eq_eqToHom f X
  have hHom {c c' : Discrete M} {X Y : C} (f : c ⟶ c') (g : X ⟶ Y) := actionHom_def f g
  have hAssoc (c c' : Discrete M) (X : C) :=
    pseudofunctor_mapComp_hom_toNatTrans_app (M := M) (C := C)
      (a := ⟨SingleObj.star M⟩) (b := ⟨SingleObj.star M⟩) (c := ⟨SingleObj.star M⟩) c' c X
  cases inst with | @mk struct _ =>
  cases struct
  unfold Pseudofunctor.monoidalLeftAction
  congr
  · funext _ _ f X
    exact (hLeft f X).symm
  · funext _ _ _ _ f g
    exact ((hHom f g).trans (congrArg (· ≫ _) (hLeft f _))).symm
  · funext c c' X
    apply Iso.ext
    exact hAssoc c c' X

end MonoidalCategory.MonoidalLeftAction

namespace Pseudofunctor

variable {M : Type u} [Monoid M]

/-- The pseudofunctor recovered from the action `F.monoidalLeftAction` is `F` itself: the
comparison transports the action functors, the unit comparison and the composition comparison
unchanged. -/
theorem pseudofunctor_monoidalLeftAction (F : LocallyDiscrete (SingleObj M) ⥤ᵖ Cat.{v, w}) :
    letI := F.monoidalLeftAction
    MonoidalLeftAction.pseudofunctor M (F.obj ⟨SingleObj.star M⟩) = F := by
  rcases F with ⟨⟨⟨⟨obj, map⟩, map₂⟩, map₂_id, map₂_comp⟩, mapId, mapComp, _, _, _, _, _⟩
  unfold MonoidalLeftAction.pseudofunctor LocallyDiscrete.mkPseudofunctor
    pseudofunctorOfIsLocallyDiscrete
  -- The values on objects and `1`-morphisms and the unit comparisons agree definitionally; the
  -- remaining goals are the `2`-morphisms, the composition comparisons and the coherence proofs.
  congr
  · funext a b f g φ
    exact (PrelaxFunctor.map₂_eq_eqToHom ⟨⟨⟨obj, map⟩, map₂⟩, map₂_id, map₂_comp⟩ φ).symm
  · funext a b c f g
    ext X
    -- After destructuring `F`, the action `monoidalLeftAction _` is not an instance in scope.
    exact @actionLeftTensorIso_hom_app _ _ _ _ _ (monoidalLeftAction _) _ _ X
  all_goals exact proof_irrel_heq _ _

end Pseudofunctor

namespace MonoidalCategory.MonoidalLeftAction

variable (M : Type u) [Monoid M]

/-- Left actions of `Discrete M` on categories correspond bijectively to pseudofunctors
`LocallyDiscrete (SingleObj M) ⥤ᵖ Cat`: an action on `C` is sent to `pseudofunctor M C`, and a
pseudofunctor `F` to the action `F.monoidalLeftAction` on its value at the unique object. -/
@[simps]
def pseudofunctorEquiv :
    (Σ C : Cat.{v, w}, MonoidalLeftAction (Discrete M) C) ≃
      (LocallyDiscrete (SingleObj M) ⥤ᵖ Cat.{v, w}) where
  toFun C := letI := C.2; pseudofunctor M C.1
  invFun F := ⟨F.obj ⟨SingleObj.star M⟩, F.monoidalLeftAction⟩
  left_inv C := Sigma.ext rfl (heq_of_eq (letI := C.2; monoidalLeftAction_pseudofunctor M C.1))
  right_inv := Pseudofunctor.pseudofunctor_monoidalLeftAction

end MonoidalCategory.MonoidalLeftAction

end CategoryTheory
