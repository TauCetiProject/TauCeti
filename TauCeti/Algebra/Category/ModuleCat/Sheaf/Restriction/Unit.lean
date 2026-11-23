/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Over
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Pullback.Unit
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Restriction.OpenSubspace

/-!
# Open-subspace restriction of the unit sheaf of modules

Using the open-subspace restriction `TopologicalSpace.Opens.sheafOfModulesRestrict` and its
identification with pullback along `Opens.sheafInclusionHom`, restriction to an open subspace `U`
preserves the unit sheaf of modules (`TopologicalSpace.Opens.sheafOfModulesRestrictUnitIso`),
compatibly with Mathlib's slice equivalence unit comparison `U.sheafOfModulesEquivOverUnit R` and
`SheafOfModules.overFunctorUnitIso`
(`TopologicalSpace.Opens.sheafOfModulesEquivOverUnit_inv_comp_sheafOfModulesRestrictUnitIso_hom`).

## Main declarations

* `TopologicalSpace.Opens.sheafOfModulesRestrictUnitIso` (with forward formula
  `sheafOfModulesRestrictUnitIso_hom`): open-subspace restriction preserves the unit sheaf of
  modules;
* `TopologicalSpace.Opens.sheafOfModulesEquivOverUnit_inv_comp_sheafOfModulesRestrictUnitIso_hom`:
  compatibility of `sheafOfModulesRestrictUnitIso` with the slice equivalence unit comparison.

## References

* [The Stacks Project, Tag 008F](https://stacks.math.columbia.edu/tag/008F)
-/

public section

open CategoryTheory TopologicalSpace

universe u

noncomputable section

namespace TopologicalSpace.Opens

section UnitRestriction

variable {X : TopCat.{u}} (U : Opens X) (R : X.Sheaf RingCat.{u})

/-- Open-subspace restriction preserves the unit sheaf of modules. -/
def sheafOfModulesRestrictUnitIso :
    (U.sheafOfModulesRestrict.{u} R).obj (SheafOfModules.unit R) ≅
      SheafOfModules.unit ((U.isOpenEmbedding.sheafPullback RingCat.{u}).obj R) :=
  (U.sheafOfModulesRestrictIsoPullback.{u} R).app (SheafOfModules.unit R) ≪≫
    SheafOfModules.pullbackObjUnitIso (U.sheafInclusionHom RingCat.{u} R)

/-- The forward morphism of `sheafOfModulesRestrictUnitIso` is `sheafOfModulesRestrictIsoPullback`
followed by `pullbackObjUnitToUnit`. -/
theorem sheafOfModulesRestrictUnitIso_hom :
    (U.sheafOfModulesRestrictUnitIso R).hom =
      (U.sheafOfModulesRestrictIsoPullback.{u} R).hom.app (SheafOfModules.unit R) ≫
        SheafOfModules.pullbackObjUnitToUnit (U.sheafInclusionHom RingCat.{u} R) := by
  unfold sheafOfModulesRestrictUnitIso
  rw [Iso.trans_hom, Iso.app_hom, SheafOfModules.pullbackObjUnitIso_hom]

/-- Comparing the unit sheaf on the slice site over `U` with the unit sheaf on the open subspace
`U` via `sheafOfModulesEquivOverUnit` and `overFunctorCompSheafOfModulesEquivOver` is left
inverse to `sheafOfModulesRestrictUnitIso`. -/
@[reassoc]
theorem sheafOfModulesEquivOverUnit_inv_comp_sheafOfModulesRestrictUnitIso_hom :
    (U.sheafOfModulesEquivOverUnit R).inv ≫
        (U.sheafOfModulesEquivOver R).functor.map (SheafOfModules.overFunctorUnitIso R U).hom ≫
        (U.overFunctorCompSheafOfModulesEquivOver R).hom.app (SheafOfModules.unit R) ≫
        (U.sheafOfModulesRestrictUnitIso R).hom = 𝟙 _ := by
  have h1 : (U.sheafOfModulesRestrictAdj.{u} R).homEquiv _ _
      ((U.sheafOfModulesRestrictIsoPullback.{u} R).hom.app (SheafOfModules.unit R) ≫
        SheafOfModules.pullbackObjUnitToUnit (U.sheafInclusionHom RingCat.{u} R)) =
      SheafOfModules.unitToPushforwardObjUnit (U.sheafInclusionHom RingCat.{u} R) := by
    refine (Adjunction.homEquiv_naturality_right _ _ _).trans ?_
    rw [U.sheafOfModulesRestrictAdj_homEquiv_sheafOfModulesRestrictIsoPullback_hom_app,
      ← Adjunction.homEquiv_unit,
      SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit]
  have h2 := congrArg (fun k ↦ ((U.sheafOfModulesRestrictAdj.{u} R).homEquiv _ _).symm k) h1
  rw [Equiv.symm_apply_apply] at h2
  have h0 :
      ((U.sheafOfModulesEquivOverUnit R).inv ≫
          (U.sheafOfModulesEquivOver R).functor.map (SheafOfModules.overFunctorUnitIso R U).hom ≫
          (U.overFunctorCompSheafOfModulesEquivOver R).hom.app (SheafOfModules.unit R)) ≫
        (U.sheafOfModulesRestrictIsoPullback.{u} R).hom.app (SheafOfModules.unit R) ≫
        SheafOfModules.pullbackObjUnitToUnit (U.sheafInclusionHom RingCat.{u} R) = 𝟙 _ := by
    refine (congrArg
      (((U.sheafOfModulesEquivOverUnit R).inv ≫
          (U.sheafOfModulesEquivOver R).functor.map (SheafOfModules.overFunctorUnitIso R U).hom ≫
          (U.overFunctorCompSheafOfModulesEquivOver R).hom.app (SheafOfModules.unit R)) ≫ ·)
      h2).trans ?_
    rw [Adjunction.homEquiv_symm_apply]
    ext W
    let W' : (Opens ((Opens.toTopCat X).obj U))ᵒᵖ := W
    let y := ((U.overFunctorCompSheafOfModulesEquivOver R).hom.app
        (SheafOfModules.unit R)).val.app W'
      (1 : R.obj.obj (Opposite.op (U.isOpenEmbedding.functor.obj W'.unop)))
    have hy :
        (eqToHom (Opens.sheafOfModulesRestrict_obj_val_presheaf_obj U R
            (SheafOfModules.unit R) W') :
            ((U.sheafOfModulesRestrict.{u} R).obj (SheafOfModules.unit R)).val.presheaf.obj W' ⟶
              (SheafOfModules.unit R).val.presheaf.obj
                (Opposite.op (U.isOpenEmbedding.functor.obj W'.unop)))
          y = (1 : R.obj.obj (Opposite.op (U.isOpenEmbedding.functor.obj W'.unop))) :=
      U.overFunctorCompSheafOfModulesEquivOver_hom_app_val_app R (SheafOfModules.unit R) W' _
    have hstep1 :
        (((U.sheafOfModulesEquivOverUnit R).inv ≫
            (U.sheafOfModulesEquivOver R).functor.map
              (SheafOfModules.overFunctorUnitIso R U).hom ≫
            (U.overFunctorCompSheafOfModulesEquivOver R).hom.app
              (SheafOfModules.unit R)).val.app W)
          (1 : (U.sheafRestrict.obj R).obj.obj W) = y :=
      congrArg (((U.overFunctorCompSheafOfModulesEquivOver R).hom.app
        (SheafOfModules.unit R)).val.app W')
        (SheafOfModules.overFunctorUnitIso_hom_val_app R U _ _)
    have hmap :
        (((U.sheafOfModulesRestrict.{u} R).map
            (SheafOfModules.unitToPushforwardObjUnit
              (U.sheafInclusionHom RingCat.{u} R))).val.app W') y =
          (eqToHom (Opens.sheafOfModulesRestrict_obj_val_presheaf_obj U R
              ((SheafOfModules.pushforward.{u} (U.sheafInclusionHom RingCat.{u} R)).obj
                (SheafOfModules.unit ((U.isOpenEmbedding.sheafPullback RingCat.{u}).obj R)))
              W').symm :
            (SheafOfModules.unit
                ((U.isOpenEmbedding.sheafPullback RingCat.{u}).obj R)).val.presheaf.obj
                (Opposite.op
                  ((Opens.map U.inclusion').obj (U.isOpenEmbedding.functor.obj W'.unop))) ⟶
              ((U.sheafOfModulesRestrict.{u} R).obj
                ((SheafOfModules.pushforward.{u} (U.sheafInclusionHom RingCat.{u} R)).obj
                  (SheafOfModules.unit
                    ((U.isOpenEmbedding.sheafPullback RingCat.{u}).obj R)))).val.presheaf.obj W')
            (((SheafOfModules.unitToPushforwardObjUnit
                (U.sheafInclusionHom RingCat.{u} R)).val.app
              (Opposite.op (U.isOpenEmbedding.functor.obj W'.unop)))
              (1 : R.obj.obj (Opposite.op (U.isOpenEmbedding.functor.obj W'.unop)))) := by
      have hmv := Opens.sheafOfModulesRestrict_map_val_app U R
        (SheafOfModules.unitToPushforwardObjUnit (U.sheafInclusionHom RingCat.{u} R)) W'
      have hm1 := congrArg (fun k ↦ ((forget₂ _ AddCommGrpCat).map k) y) hmv
      have ha := congrArg (fun k ↦ k y)
        (CategoryTheory.Functor.map_comp (forget₂ (ModuleCat _) AddCommGrpCat)
          (eqToHom (Opens.sheafOfModulesRestrict_obj_val_obj U R (SheafOfModules.unit R) W'))
          ((SheafOfModules.unitToPushforwardObjUnit
              (U.sheafInclusionHom RingCat.{u} R)).val.app
              (Opposite.op (U.isOpenEmbedding.functor.obj W'.unop)) ≫
            eqToHom (Opens.sheafOfModulesRestrict_obj_val_obj U R
              ((SheafOfModules.pushforward.{u} (U.sheafInclusionHom RingCat.{u} R)).obj
                (SheafOfModules.unit ((U.isOpenEmbedding.sheafPullback RingCat.{u}).obj R)))
              W').symm))
      have hsplit := ha.trans (congrArg
        (fun k ↦ k (((forget₂ _ AddCommGrpCat).map
          (eqToHom (Opens.sheafOfModulesRestrict_obj_val_obj U R (SheafOfModules.unit R) W'))) y))
        (CategoryTheory.Functor.map_comp (forget₂ (ModuleCat _) AddCommGrpCat)
          ((SheafOfModules.unitToPushforwardObjUnit
            (U.sheafInclusionHom RingCat.{u} R)).val.app
            (Opposite.op (U.isOpenEmbedding.functor.obj W'.unop)))
          (eqToHom (Opens.sheafOfModulesRestrict_obj_val_obj U R
            ((SheafOfModules.pushforward.{u} (U.sheafInclusionHom RingCat.{u} R)).obj
              (SheafOfModules.unit ((U.isOpenEmbedding.sheafPullback RingCat.{u}).obj R)))
            W').symm)))
      have h1 :
          ((forget₂ (ModuleCat _) AddCommGrpCat).map
            (eqToHom (Opens.sheafOfModulesRestrict_obj_val_obj U R
              (SheafOfModules.unit R) W'))) =
          eqToHom (Opens.sheafOfModulesRestrict_obj_val_presheaf_obj U R
            (SheafOfModules.unit R) W') :=
        eqToHom_map _ _
      have h2 :
          ((forget₂ (ModuleCat _) AddCommGrpCat).map
            (eqToHom (Opens.sheafOfModulesRestrict_obj_val_obj U R
              ((SheafOfModules.pushforward.{u} (U.sheafInclusionHom RingCat.{u} R)).obj
                (SheafOfModules.unit ((U.isOpenEmbedding.sheafPullback RingCat.{u}).obj R)))
              W').symm)) =
          eqToHom (Opens.sheafOfModulesRestrict_obj_val_presheaf_obj U R
              ((SheafOfModules.pushforward.{u} (U.sheafInclusionHom RingCat.{u} R)).obj
                (SheafOfModules.unit ((U.isOpenEmbedding.sheafPullback RingCat.{u}).obj R)))
              W').symm :=
        eqToHom_map _ _
      let f := (forget₂ (ModuleCat _) AddCommGrpCat).map
        ((SheafOfModules.unitToPushforwardObjUnit (U.sheafInclusionHom RingCat.{u} R)).val.app
          (Opposite.op (U.isOpenEmbedding.functor.obj W'.unop)))
      let g2 := (forget₂ (ModuleCat _) AddCommGrpCat).map
        (eqToHom (Opens.sheafOfModulesRestrict_obj_val_obj U R
          ((SheafOfModules.pushforward.{u} (U.sheafInclusionHom RingCat.{u} R)).obj
            (SheafOfModules.unit ((U.isOpenEmbedding.sheafPullback RingCat.{u}).obj R)))
          W').symm)
      let q1 : ((U.sheafOfModulesRestrict.{u} R).obj (SheafOfModules.unit R)).val.presheaf.obj W' ⟶
          (SheafOfModules.unit R).val.presheaf.obj
            (Opposite.op (U.isOpenEmbedding.functor.obj W'.unop)) :=
        eqToHom (Opens.sheafOfModulesRestrict_obj_val_presheaf_obj U R
          (SheafOfModules.unit R) W')
      have h12 := (congrArg (fun k ↦ (f ≫ g2) (k y)) h1).trans
        (congrArg (fun k ↦ (f ≫ k) (q1 y)) h2)
      have hrhs :
          (f ≫ eqToHom (Opens.sheafOfModulesRestrict_obj_val_presheaf_obj U R
              ((SheafOfModules.pushforward.{u} (U.sheafInclusionHom RingCat.{u} R)).obj
                (SheafOfModules.unit ((U.isOpenEmbedding.sheafPullback RingCat.{u}).obj R)))
              W').symm)
            (q1 y) =
          _ :=
        congrArg (fun z ↦ (eqToHom (Opens.sheafOfModulesRestrict_obj_val_presheaf_obj U R
            ((SheafOfModules.pushforward.{u} (U.sheafInclusionHom RingCat.{u} R)).obj
              (SheafOfModules.unit ((U.isOpenEmbedding.sheafPullback RingCat.{u}).obj R)))
            W').symm :
          (SheafOfModules.unit
              ((U.isOpenEmbedding.sheafPullback RingCat.{u}).obj R)).val.presheaf.obj
              (Opposite.op ((Opens.map U.inclusion').obj
                (U.isOpenEmbedding.functor.obj W'.unop))) ⟶
            ((U.sheafOfModulesRestrict.{u} R).obj
              ((SheafOfModules.pushforward.{u} (U.sheafInclusionHom RingCat.{u} R)).obj
                (SheafOfModules.unit
                  ((U.isOpenEmbedding.sheafPullback RingCat.{u}).obj R)))).val.presheaf.obj
              W')
          (((SheafOfModules.unitToPushforwardObjUnit
              (U.sheafInclusionHom RingCat.{u} R)).val.app
            (Opposite.op (U.isOpenEmbedding.functor.obj W'.unop))) z)) hy
      exact hm1.trans (hsplit.trans (h12.trans hrhs))
    have hcounit := Opens.sheafOfModulesRestrictAdj_counit_app_val_app U R
      (SheafOfModules.unit ((U.isOpenEmbedding.sheafPullback RingCat.{u}).obj R)) W'
      (((SheafOfModules.unitToPushforwardObjUnit (U.sheafInclusionHom RingCat.{u} R)).val.app
        (Opposite.op (U.isOpenEmbedding.functor.obj W'.unop)))
        (1 : R.obj.obj (Opposite.op (U.isOpenEmbedding.functor.obj W'.unop))))
    refine (congrArg (((U.sheafOfModulesRestrictAdj.{u} R).counit.app _).val.app W')
      ((congrArg (((U.sheafOfModulesRestrict.{u} R).map _).val.app W') hstep1).trans
        hmap)).trans ?_
    refine hcounit.trans ?_
    have hunit :
        ((SheafOfModules.unitToPushforwardObjUnit (U.sheafInclusionHom RingCat.{u} R)).val.app
            (Opposite.op (U.isOpenEmbedding.functor.obj W'.unop)))
          (1 : R.obj.obj (Opposite.op (U.isOpenEmbedding.functor.obj W'.unop))) =
        (1 : ((U.isOpenEmbedding.sheafPullback RingCat.{u}).obj R).obj.obj
          (Opposite.op
            ((Opens.map U.inclusion').obj (U.isOpenEmbedding.functor.obj W'.unop)))) := by
      rw [SheafOfModules.unitToPushforwardObjUnit_val_app_apply, map_one]
      rfl
    refine (congrArg (fun z ↦ (((U.isOpenEmbedding.sheafPullback RingCat.{u}).obj R).obj.map
        (U.isOpenEmbedding.isOpenMap.adjunction.unit.app W'.unop).op) z) hunit).trans ?_
    rw [map_one]
    rfl
  unfold sheafOfModulesRestrictUnitIso
  rw [Iso.trans_hom, Iso.app_hom, SheafOfModules.pullbackObjUnitIso_hom]
  exact (congrArg (_ ≫ ·) (Category.assoc _ _ _).symm).trans
    ((Category.assoc _ _ _).symm.trans h0)

end UnitRestriction

end TopologicalSpace.Opens

end
