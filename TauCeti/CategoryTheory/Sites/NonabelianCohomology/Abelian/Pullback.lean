/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.Pullback
public import TauCeti.CategoryTheory.Sites.NonabelianCohomology.Abelian.Basic

/-!
# Abelian sheaves as sheaves of groups under pullback

Viewing an abelian sheaf as a sheaf of groups (`CategoryTheory.abelianSheafToGrpSheaf`) commutes
with pushforward along a continuous functor `u : C ⥤ D`
(`CategoryTheory.abelianSheafToGrpSheafPushforwardIso`). When the pushforward of abelian sheaves
has a left adjoint `u^*`, the unit `F ⟶ u_* u^* F` therefore gives a morphism from the sheaf of
groups underlying `F` to the pushforward of the sheaf of groups underlying `u^* F`, natural in
`F`. Pulling back torsors along it compares torsor classes of `F` and of `u^* F`.

## Main declarations

* `CategoryTheory.Functor.abelianSheafToGrpSheafUnit u J K`: the unit `F ⟶ u_* u^* F` on the
  underlying sheaves of groups, as a natural transformation, with
  `CategoryTheory.Functor.abelianSheafToGrpSheafUnit_app_hom_app` computing it on sections.
-/

public noncomputable section

open CategoryTheory Opposite

universe w v v' u u'

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {D : Type u'} [Category.{v'} D] (K : GrothendieckTopology D)

namespace Functor

variable (u : C ⥤ D) [u.IsContinuous J K]
  [(u.sheafPushforwardContinuous AddCommGrpCat.{w} J K).IsRightAdjoint]

/-- The unit `F ⟶ u_* u^* F` of the adjunction `u^* ⊣ u_*` on abelian sheaves, as a natural
transformation from the sheaf of groups underlying `F` to the pushforward of the sheaf of groups
underlying `u^* F`: the image of the unit under `abelianSheafToGrpSheaf J`, followed by
`abelianSheafToGrpSheafPushforwardIso`. Use `abelianSheafToGrpSheafUnit_app_hom_app` to compute
it. -/
def abelianSheafToGrpSheafUnit :
    abelianSheafToGrpSheaf J ⟶ u.sheafPullback AddCommGrpCat.{w} J K ⋙
      abelianSheafToGrpSheaf K ⋙ u.sheafPushforwardContinuous GrpCat.{w} J K :=
  whiskerRight (u.sheafAdjunctionContinuous AddCommGrpCat.{w} J K).unit
      (abelianSheafToGrpSheaf J) ≫
    whiskerLeft (u.sheafPullback AddCommGrpCat.{w} J K)
      (abelianSheafToGrpSheafPushforwardIso J K u).hom

/-- The unit `F ⟶ u_* u^* F` on the underlying sheaves of groups applies the unit to sections.
(Not `@[simp]`: `simp` rewrites the type of the section through `Functor.comp_obj`.) -/
lemma abelianSheafToGrpSheafUnit_app_hom_app (F : Sheaf J AddCommGrpCat.{w}) (U : Cᵒᵖ)
    (a : Multiplicative (F.obj.obj U)) :
    ((u.abelianSheafToGrpSheafUnit J K).app F).hom.app U (abelianSheafToGrpSheafObjEquiv F U a) =
      abelianSheafToGrpSheafObjEquiv _ (u.op.obj U) (.ofAdd
        (((u.sheafAdjunctionContinuous AddCommGrpCat.{w} J K).unit.app F).hom.app U a.toAdd)) := by
  rw [abelianSheafToGrpSheafUnit, NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
    ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, ConcreteCategory.comp_apply]
  -- The unit has source `(𝟭 _).obj F`, which is `F` only up to unfolding, so the section lemma
  -- for `abelianSheafToGrpSheaf` is applied by `congrArg` rather than by rewriting.
  exact (congrArg _ (abelianSheafToGrpSheaf_map_hom_app_abelianSheafToGrpSheafObjEquiv
    ((u.sheafAdjunctionContinuous AddCommGrpCat.{w} J K).unit.app F) U a)).trans
    (abelianSheafToGrpSheafPushforwardIso_hom_app_hom_app J K u _ U _)

end Functor

end CategoryTheory
