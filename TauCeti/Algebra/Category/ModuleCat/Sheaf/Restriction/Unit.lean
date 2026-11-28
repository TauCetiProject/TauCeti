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
  `sheafOfModulesRestrictUnitIso_hom`, adjunction transpose
  `sheafOfModulesRestrictAdj_homEquiv_sheafOfModulesRestrictUnitIso_hom`, and sectionwise
  characterization `sheafOfModulesRestrictUnitIso_hom_val_app`): open-subspace restriction
  preserves the unit sheaf of modules;
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

/-- Under `sheafOfModulesRestrictAdj`, transposing `(U.sheafOfModulesRestrictUnitIso R).hom`
produces `unitToPushforwardObjUnit (U.sheafInclusionHom RingCat R)`. -/
theorem sheafOfModulesRestrictAdj_homEquiv_sheafOfModulesRestrictUnitIso_hom :
    (U.sheafOfModulesRestrictAdj.{u} R).homEquiv _ _ (U.sheafOfModulesRestrictUnitIso R).hom =
      SheafOfModules.unitToPushforwardObjUnit (U.sheafInclusionHom RingCat.{u} R) := by
  rw [sheafOfModulesRestrictUnitIso_hom, Adjunction.homEquiv_naturality_right,
    U.sheafOfModulesRestrictAdj_homEquiv_sheafOfModulesRestrictIsoPullback_hom_app,
    ← Adjunction.homEquiv_unit,
    SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit]

/-- On sections over `W`, `(U.sheafOfModulesRestrictUnitIso R).hom` acts as the identity on the
underlying ring sections over `U.isOpenEmbedding.functor.obj W.unop`. -/
theorem sheafOfModulesRestrictUnitIso_hom_val_app
    (W : (Opens ((Opens.toTopCat X).obj U))ᵒᵖ)
    (x : ((U.sheafOfModulesRestrict.{u} R).obj (SheafOfModules.unit R)).val.obj W) :
    ((U.sheafOfModulesRestrictUnitIso R).hom.val.app W) x =
      (eqToHom (sheafOfModulesRestrict_obj_val_presheaf_obj U R (SheafOfModules.unit R) W) :
          ((U.sheafOfModulesRestrict.{u} R).obj (SheafOfModules.unit R)).val.presheaf.obj W ⟶
            (SheafOfModules.unit R).val.presheaf.obj
              (Opposite.op (U.isOpenEmbedding.functor.obj W.unop))) x := by
  have hhom : (U.sheafOfModulesRestrictUnitIso R).hom =
      (U.sheafOfModulesRestrict.{u} R).map
        (SheafOfModules.unitToPushforwardObjUnit (U.sheafInclusionHom RingCat.{u} R)) ≫
      (U.sheafOfModulesRestrictAdj.{u} R).counit.app _ := by
    rw [← Equiv.symm_apply_apply ((U.sheafOfModulesRestrictAdj.{u} R).homEquiv _ _)
      (U.sheafOfModulesRestrictUnitIso R).hom,
      U.sheafOfModulesRestrictAdj_homEquiv_sheafOfModulesRestrictUnitIso_hom R,
      Adjunction.homEquiv_symm_apply]
  rw [hhom, SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply,
    Opens.sheafOfModulesRestrict_map_val_app_apply]
  refine (Opens.sheafOfModulesRestrictAdj_counit_app_val_app U R
    (SheafOfModules.unit ((U.isOpenEmbedding.sheafPullback RingCat.{u}).obj R)) W _).trans ?_
  refine (congrArg
    (((U.isOpenEmbedding.sheafPullback RingCat.{u}).obj R).obj.map
      (U.isOpenEmbedding.isOpenMap.adjunction.unit.app W.unop).op)
    (SheafOfModules.unitToPushforwardObjUnit_val_app_apply
      (U.sheafInclusionHom RingCat.{u} R) _)).trans ?_
  dsimp only
  rw [U.sheafInclusionHom_hom_app, Topology.IsOpenEmbedding.sheafPullback_obj_obj_map]
  -- `sheafPullback_obj_obj_map` keeps `(sheafPullback.obj R).obj.obj` as the implicit domain
  -- in `ConcreteCategory.hom`, which matches `R.obj.obj` under `refine` (`comp_apply`).
  refine (ConcreteCategory.comp_apply (R.obj.map _) (R.obj.map _) _).symm.trans ?_
  rw [← R.obj.map_comp, ← op_comp]
  refine (congrArg (fun k ↦ R.obj.map k.op _)
    (U.isOpenEmbedding.isOpenMap.adjunction.left_triangle_components W.unop)).trans ?_
  rw [op_id, R.obj.map_id]
  refine (ConcreteCategory.id_apply _).trans ?_
  -- The remaining transport is cancelling `eqToHom` on the section carrier along the open equality
  -- `Opens.map U.inclusion' (U.isOpenEmbedding.functor W) = W`.
  rfl

/-- Sectionwise action of `(U.sheafOfModulesEquivOverUnit R).inv` followed by the image of
`(SheafOfModules.overFunctorUnitIso R U).hom` under `(U.sheafOfModulesEquivOver R).functor`. -/
private lemma sheafOfModulesEquivOverUnit_inv_comp_map_overFunctorUnitIso_val_app_apply
    (W : (Opens U)ᵒᵖ) (x : (U.sheafRestrict.obj R).obj.obj W) :
    (((U.sheafOfModulesEquivOverUnit R).inv ≫
        (U.sheafOfModulesEquivOver R).functor.map
          (SheafOfModules.overFunctorUnitIso R U).hom).val.app W) x =
      (x : R.obj.obj (Opposite.op (U.isOpenEmbedding.functor.obj W.unop))) := by
  rw [SheafOfModules.comp_val, PresheafOfModules.comp_app]
  refine (ModuleCat.comp_apply _ _ _).trans ?_
  unfold sheafOfModulesEquivOver sheafOfModulesEquivOverUnit
  exact SheafOfModules.overFunctorUnitIso_hom_val_app R U _ _

/-- Comparing the unit sheaf on the slice site over `U` with the unit sheaf on the open subspace
`U` via `sheafOfModulesEquivOverUnit` and `overFunctorCompSheafOfModulesEquivOver` gives a right
inverse of `(U.sheafOfModulesRestrictUnitIso R).hom`. -/
@[reassoc]
theorem sheafOfModulesEquivOverUnit_inv_comp_sheafOfModulesRestrictUnitIso_hom :
    (U.sheafOfModulesEquivOverUnit R).inv ≫
        (U.sheafOfModulesEquivOver R).functor.map (SheafOfModules.overFunctorUnitIso R U).hom ≫
        (U.overFunctorCompSheafOfModulesEquivOver R).hom.app (SheafOfModules.unit R) ≫
        (U.sheafOfModulesRestrictUnitIso R).hom = 𝟙 _ := by
  ext W
  let W' : (Opens ((Opens.toTopCat X).obj U))ᵒᵖ := W
  have h1 := sheafOfModulesEquivOverUnit_inv_comp_map_overFunctorUnitIso_val_app_apply U R W 1
  refine (congrArg ((U.sheafOfModulesRestrictUnitIso R).hom.val.app W')
    (congrArg (((U.overFunctorCompSheafOfModulesEquivOver R).hom.app
      (SheafOfModules.unit R)).val.app W') h1)).trans ?_
  refine (U.sheafOfModulesRestrictUnitIso_hom_val_app R W' _).trans ?_
  exact U.overFunctorCompSheafOfModulesEquivOver_hom_app_val_app R (SheafOfModules.unit R) W' _

end UnitRestriction

end TopologicalSpace.Opens

end
