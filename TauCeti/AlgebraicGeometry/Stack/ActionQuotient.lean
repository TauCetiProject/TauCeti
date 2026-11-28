/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import TauCeti.AlgebraicGeometry.Stack.Stackification
public import TauCeti.CategoryTheory.Sites.Descent.ActionGroupoid
public import TauCeti.CategoryTheory.Sites.Descent.LocallyEssSurj
public import TauCeti.CategoryTheory.Sites.Descent.Stackification.StrongTrans
public import TauCeti.CategoryTheory.Sites.Descent.Yoneda

/-!
# The fppf quotient stack of a group scheme action

`actionQuotient G X` is the fppf stackification of Mathlib-style internal action data
`ModObj G X` on schemes over a base. It uses `ModObj.actionCategory` for the action
prestack and `TauCeti.Stack.stackification` to adjoin descent objects.

The canonical atlas `actionQuotient.atlas` is fppf locally essentially surjective. Between points
coming from maps to `X`, the arrows are the group-valued sections carrying one map to the other
(`actionQuotient.homEquiv`).

## References

* [Stacks Project, Definition 78.20.1 (044Q)](https://stacks.math.columbia.edu/tag/044Q)
-/

public noncomputable section

open CategoryTheory Opposite Bicategory Pseudofunctor.StrongTrans
open scoped MonObj
open _root_.AlgebraicGeometry (Scheme)

namespace CategoryTheory.Over

universe u

open TauCeti.Stack TauCeti.Stack.Stackification

variable {S : Scheme.{u}} (G X : CategoryTheory.Over S) [GrpObj G] [ModObj G X]

/-- The quotient stack `[X/G]` on the big fppf site of `S`, obtained by stackifying
the action groupoid of the action of `G` on `X`. -/
abbrev actionQuotient :=
  stackification.{u} (Scheme.fppfTopology.over S) (ModObj.actionCategory G X)

namespace actionQuotient

/-- Every fibre of the action quotient is a groupoid. -/
instance (T : LocallyDiscrete (Over S)ᵒᵖ) : IsGroupoid ((actionQuotient G X).obj T) := by
  rw [stackification_obj]
  exact Obj.isGroupoid (hF := fun U ↦ ModObj.isGroupoid_actionCategory_obj G X (op U))

variable {G X} {T V : Over S}

/-- A map to `X` gives an object of `[X/G]` over its domain. -/
abbrev point (x : T ⟶ X) : (actionQuotient G X).obj (.mk (op T)) :=
  (Obj.toObjFunctor.{u} (Scheme.fppfTopology.over S) (ModObj.actionCategory G X) T).obj
    (ActionCategory.objEquiv (T ⟶ G) (T ⟶ X) x)

/-- The arrows between the images of two maps to `X` in `[X/G]` are the group-valued
sections taking the source map to the target map. -/
def homEquiv (x y : T ⟶ X) : (point (G := G) x ⟶ point (G := G) y) ≃ {g : T ⟶ G // g • x = y} :=
  (Obj.fullyFaithfulToObjFunctor.{u} (Scheme.fppfTopology.over S)
      (ModObj.actionCategory G X) T).homEquiv.symm.trans
    { toFun := fun a ↦ ⟨a.hom, a.map_val⟩
      invFun := fun g ↦ Functor.Elements.homMk g.val g.property
      left_inv := fun _ ↦ Functor.Elements.hom_ext rfl
      right_inv := fun _ ↦ Subtype.ext rfl }

/-- The arrow with label `g` is the image of the corresponding action groupoid arrow. -/
theorem homEquiv_symm_apply (x y : T ⟶ X) (g : {g : T ⟶ G // g • x = y}) :
    (homEquiv x y).symm g =
      (Obj.toObjFunctor.{u} (Scheme.fppfTopology.over S) (ModObj.actionCategory G X) T).map
        (Functor.Elements.homMk
          (x := ActionCategory.objEquiv (T ⟶ G) (T ⟶ X) x)
          (y := ActionCategory.objEquiv (T ⟶ G) (T ⟶ X) y) g.val g.property) :=
  (rfl)

/-- The label of an embedded action arrow is its original group-valued section. -/
@[simp]
theorem homEquiv_apply_map (x y : T ⟶ X)
    (a : ActionCategory.objEquiv (T ⟶ G) (T ⟶ X) x ⟶
      ActionCategory.objEquiv (T ⟶ G) (T ⟶ X) y) :
    (homEquiv x y ((Obj.toObjFunctor.{u} (Scheme.fppfTopology.over S)
      (ModObj.actionCategory G X) T).map a)).val = a.hom :=
  congrArg Subtype.val ((homEquiv x y).eq_symm_apply.mp (homEquiv_symm_apply
    x y ⟨a.hom, a.map_val⟩).symm)

/-- Applying the identity-cover embedding to the restricted action object gives the
atlas point of the restricted map. -/
theorem pointPullbackObj_eq (x : T ⟶ X) (f : V ⟶ T) :
    (Obj.toObjFunctor.{u} (Scheme.fppfTopology.over S) (ModObj.actionCategory G X) V).obj
        (((ModObj.actionCategory G X).map f.op.toLoc).toFunctor.obj
          (ActionCategory.objEquiv (T ⟶ G) (T ⟶ X) x)) = point (G := G) (f ≫ x) := by
  apply congrArg (Obj.toObjFunctor.{u} (Scheme.fppfTopology.over S) _ V).obj
  apply ActionCategory.back_injective
  exact (ModObj.actionCategory_map_obj_back G X f _).trans <|
    (congrArg (f ≫ ·) ((ActionCategory.objEquiv (T ⟶ G) (T ⟶ X)).symm_apply_apply x)).trans
      ((ActionCategory.objEquiv (V ⟶ G) (V ⟶ X)).symm_apply_apply (f ≫ x)).symm

/-- Restricting an atlas point is isomorphic to the atlas point of the restricted map. -/
def pointPullbackIso (x : T ⟶ X) (f : V ⟶ T) :
    ((actionQuotient G X).map f.op.toLoc).toFunctor.obj (point (G := G) x) ≅
      point (G := G) (f ≫ x) :=
  (toStackificationNatIso.{u} (Scheme.fppfTopology.over S) (ModObj.actionCategory G X) f).symm.app
      (ActionCategory.objEquiv (T ⟶ G) (T ⟶ X) x) ≪≫
    eqToIso (pointPullbackObj_eq x f)

/-- The restriction comparison is the inverse naturality map of the stackification embedding,
followed by the identification of the restricted point. -/
@[simp]
theorem pointPullbackIso_hom (x : T ⟶ X) (f : V ⟶ T) :
    (pointPullbackIso (G := G) x f).hom =
      (toStackificationNatIso.{u} (Scheme.fppfTopology.over S)
        (ModObj.actionCategory G X) f).inv.app (ActionCategory.objEquiv (T ⟶ G) (T ⟶ X) x) ≫
        eqToHom (pointPullbackObj_eq x f) :=
  (rfl)

/-- The canonical map from the representable pseudofunctor of `X` to `[X/G]`,
corresponding under 2-Yoneda to the atlas point of `𝟙 X`. -/
def atlas : Pseudofunctor.ofPresheaf.{u + 1} (yoneda.obj X) ⟶ actionQuotient G X :=
  Pseudofunctor.yonedaPullbackObj.{u + 1} (actionQuotient G X) X (point (G := G) (𝟙 X))

/-- The atlas is the 2-Yoneda map attached to the identity point. -/
theorem atlas_eq :
    atlas (G := G) (X := X) =
      Pseudofunctor.yonedaPullbackObj.{u + 1} (actionQuotient G X) X (point (G := G) (𝟙 X)) :=
  (rfl)

/-- The atlas evaluates at `x : T ⟶ X` by pulling back the identity point along `x`. -/
@[simp]
theorem atlas_app_obj (x : T ⟶ X) :
    ((atlas (G := G) (X := X)).app (.mk (op T))).toFunctor.obj
        ((Pseudofunctor.ofPresheaf.objEquiv.{u + 1} (P := yoneda.obj X) (op T)).symm x) =
      ((actionQuotient G X).map x.op.toLoc).toFunctor.obj (point (G := G) (𝟙 X)) := by
  rw [atlas_eq, Pseudofunctor.yonedaPullbackObj_app,
    Pseudofunctor.yonedaPullbackApp_toFunctor_obj, Equiv.apply_symm_apply]

/-- The atlas of the action quotient is fppf locally essentially surjective. -/
instance isLocallyEssSurj_atlas :
    IsLocallyEssSurj (atlas (G := G) (X := X)) (Scheme.fppfTopology.over S) where
  exists_covering_lift {U} A := by
    obtain ⟨R, hR, h⟩ := stackification_locally_essSurj _ _ A
    refine ⟨R, hR, fun V f hf ↦ ?_⟩
    obtain ⟨M, ⟨e⟩⟩ := h f hf
    let points := ActionCategory.objEquiv (V ⟶ G) (V ⟶ X)
    let x := points.symm M
    have hx : point (G := G) x =
        (Obj.toObjFunctor.{u} (Scheme.fppfTopology.over S) (ModObj.actionCategory G X) V).obj M :=
      congrArg (Obj.toObjFunctor.{u} (Scheme.fppfTopology.over S) _ V).obj
        (points.apply_symm_apply M)
    exact ⟨(Pseudofunctor.ofPresheaf.objEquiv.{u + 1} (P := yoneda.obj X) (op V)).symm x,
      ⟨eqToIso (atlas_app_obj x) ≪≫ pointPullbackIso (𝟙 X) x ≪≫
        eqToIso (congrArg (point (G := G)) (Category.comp_id x)) ≪≫ eqToIso hx ≪≫ e.symm⟩⟩

end actionQuotient

end CategoryTheory.Over
