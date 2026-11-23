/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Restriction.Unit

/-!
# Restriction and slice-site pullback of sheaves of modules on ringed spaces

For a continuous map `f : X ⟶ Y` and a morphism of sheaves of rings `φ : S ⟶ f_* R`, restricting a
sheaf of rings to opens `V ⊆ Y` and `U ⊆ f⁻¹(V)` produces the restricted ring-sheaf morphism
`TopologicalSpace.Opens.sheafHomResLE φ V U e` along
`TopologicalSpace.Opens.resLE f V U e : (Opens.toTopCat X).obj U ⟶ (Opens.toTopCat Y).obj V`.
Module pullback commutes with open-subspace restriction (`SheafOfModules.restrictPullbackIso`),
yielding the slice-site pullback functor `SheafOfModules.pullbackOver φ V` together with its unit
and slice-restriction natural comparisons `SheafOfModules.pullbackOverUnitIso` and
`SheafOfModules.overFunctorCompPullbackOverIso` (and their compatibility with the unit module
sheaf, `SheafOfModules.pullbackOverUnitIso_hom_comp_overFunctorCompPullbackOverIso_hom_app`).

## Main declarations

* `SheafOfModules.restrictPullbackIso` and `SheafOfModules.restrictPullbackIso_hom_app`:
  compatibility of module pullback with open-subspace restriction, and its component formula;
* `SheafOfModules.pullbackOver`: the induced pullback functor between slice sites;
* `SheafOfModules.pullbackOverUnitIso`: unit preservation for `pullbackOver`;
* `SheafOfModules.overFunctorCompPullbackOverIso` and
  `SheafOfModules.pullbackOverUnitIso_hom_comp_overFunctorCompPullbackOverIso_hom_app`: natural
  isomorphism identifying slice restriction followed by `pullbackOver` with `pullback` followed by
  slice restriction, and its compatibility with the unit comparisons.

## References

* [The Stacks Project, Tag 0097](https://stacks.math.columbia.edu/tag/0097)
-/

public section

open CategoryTheory TopologicalSpace

universe v u

noncomputable section

namespace SheafOfModules

section RingedSpacePullback

variable {X Y : TopCat.{u}} {f : X ⟶ Y}
  {S : Y.Sheaf RingCat.{u}} {R : X.Sheaf RingCat.{u}}
  (φ : S ⟶ ((Opens.map f).sheafPushforwardContinuous RingCat.{u}
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).obj R)

/-- Pushforward of module sheaves along `Opens.sheafHomResLE φ V U e` is a right adjoint. -/
instance isRightAdjoint_pushforward_sheafHomResLE (V : Opens Y) (U : Opens X)
    (e : U ≤ (Opens.map f).obj V) :
    (pushforward.{u} (Opens.sheafHomResLE φ V U e)).IsRightAdjoint :=
  isRightAdjoint_pushforward (Opens.sheafHomResLE φ V U e)

/-- Module pullback along a ringed-space morphism `(f, φ)` commutes with restriction to open
subspaces `V ⊆ Y` and `U ⊆ f⁻¹(V)`. -/
def restrictPullbackIso [(pushforward.{v} φ).IsRightAdjoint]
    (V : Opens Y) (U : Opens X) (e : U ≤ (Opens.map f).obj V)
    [(pushforward.{v} (Opens.sheafHomResLE φ V U e)).IsRightAdjoint] :
    pullback.{v} φ ⋙ U.sheafOfModulesRestrict.{v} R ≅
      V.sheafOfModulesRestrict.{v} S ⋙ pullback.{v} (Opens.sheafHomResLE φ V U e) :=
  haveI : (Opens.map f ⋙ Opens.map U.inclusion').IsContinuous
      (Opens.grothendieckTopology Y)
      (Opens.grothendieckTopology ((Opens.toTopCat X).obj U)) :=
    Functor.isContinuous_comp _ _ _ (Opens.grothendieckTopology X) _
  haveI : (Opens.map V.inclusion' ⋙ Opens.map (Opens.resLE f V U e)).IsContinuous
      (Opens.grothendieckTopology Y)
      (Opens.grothendieckTopology ((Opens.toTopCat X).obj U)) :=
    Functor.isContinuous_comp _ _ _
      (Opens.grothendieckTopology ((Opens.toTopCat Y).obj V)) _
  Functor.isoWhiskerLeft (pullback.{v} φ) (U.sheafOfModulesRestrictIsoPullback.{v} R) ≪≫
    pullbackComp.{v} φ (U.sheafInclusionHom RingCat.{u} R) ≪≫
    (pullbackCongr₂.{v} _ (Opens.mapCompResLEIso f V U e)
      (Opens.sheafInclusionHom_comp_map_sheafHomResLE φ V U e)).symm ≪≫
    (pullbackComp.{v} (V.sheafInclusionHom RingCat.{u} S)
      (Opens.sheafHomResLE φ V U e)).symm ≪≫
    Functor.isoWhiskerRight (V.sheafOfModulesRestrictIsoPullback.{v} S).symm
      (pullback.{v} (Opens.sheafHomResLE φ V U e))

/-- The components of `restrictPullbackIso`: both restrictions are identified with pullbacks along
the open inclusions, and `Opens.map f ⋙ Opens.map U.inclusion'` is naturally isomorphic to
`Opens.map V.inclusion' ⋙ Opens.map (Opens.resLE f V U e)`. -/
theorem restrictPullbackIso_hom_app [(pushforward.{v} φ).IsRightAdjoint]
    (V : Opens Y) (U : Opens X) (e : U ≤ (Opens.map f).obj V)
    [(pushforward.{v} (Opens.sheafHomResLE φ V U e)).IsRightAdjoint]
    (M : SheafOfModules.{v} S) :
    (restrictPullbackIso.{v} φ V U e).hom.app M =
      (haveI : (Opens.map f ⋙ Opens.map U.inclusion').IsContinuous
          (Opens.grothendieckTopology Y)
          (Opens.grothendieckTopology ((Opens.toTopCat X).obj U)) :=
        Functor.isContinuous_comp _ _ _ (Opens.grothendieckTopology X) _
      haveI : (Opens.map V.inclusion' ⋙ Opens.map (Opens.resLE f V U e)).IsContinuous
          (Opens.grothendieckTopology Y)
          (Opens.grothendieckTopology ((Opens.toTopCat X).obj U)) :=
        Functor.isContinuous_comp _ _ _
          (Opens.grothendieckTopology ((Opens.toTopCat Y).obj V)) _
      (U.sheafOfModulesRestrictIsoPullback.{v} R).hom.app ((pullback.{v} φ).obj M) ≫
        (pullbackComp.{v} φ (U.sheafInclusionHom RingCat.{u} R)).hom.app M ≫
        (pullbackCongr₂.{v} _ (Opens.mapCompResLEIso f V U e)
          (Opens.sheafInclusionHom_comp_map_sheafHomResLE φ V U e)).inv.app M ≫
        (pullbackComp.{v} (V.sheafInclusionHom RingCat.{u} S)
          (Opens.sheafHomResLE φ V U e)).inv.app M ≫
        (pullback.{v} (Opens.sheafHomResLE φ V U e)).map
          ((V.sheafOfModulesRestrictIsoPullback.{v} S).inv.app M)) :=
  (rfl)

/-- Pullback along `(f, φ)` read between slice sites over `V : Opens Y` and
`(Opens.map f).obj V : Opens X`, obtained by conjugating pullback along
`Opens.sheafHomResLE φ V ((Opens.map f).obj V) le_rfl` by Mathlib's `sheafOfModulesEquivOver`. -/
def pullbackOver (V : Opens Y) :
    SheafOfModules.{u} (S.over V) ⥤ SheafOfModules.{u} (R.over ((Opens.map f).obj V)) :=
  let eV : SheafOfModules.{u} (S.over V) ≌
      SheafOfModules.{u} ((V.isOpenEmbedding.sheafPullback RingCat.{u}).obj S) :=
    V.sheafOfModulesEquivOver S
  let eU : SheafOfModules.{u} (R.over ((Opens.map f).obj V)) ≌
      SheafOfModules.{u}
        ((((Opens.map f).obj V).isOpenEmbedding.sheafPullback RingCat.{u}).obj R) :=
    ((Opens.map f).obj V).sheafOfModulesEquivOver R
  eV.functor ⋙ pullback.{u} (Opens.sheafHomResLE φ V ((Opens.map f).obj V) le_rfl) ⋙ eU.inverse

/-- Slice-site pullback `pullbackOver φ V` is a left adjoint. -/
instance isLeftAdjoint_pullbackOver (V : Opens Y) : (pullbackOver φ V).IsLeftAdjoint :=
  let eV : SheafOfModules.{u} (S.over V) ≌
      SheafOfModules.{u} ((V.isOpenEmbedding.sheafPullback RingCat.{u}).obj S) :=
    V.sheafOfModulesEquivOver S
  let eU : SheafOfModules.{u} (R.over ((Opens.map f).obj V)) ≌
      SheafOfModules.{u}
        ((((Opens.map f).obj V).isOpenEmbedding.sheafPullback RingCat.{u}).obj R) :=
    ((Opens.map f).obj V).sheafOfModulesEquivOver R
  inferInstanceAs
    (eV.functor ⋙ pullback.{u} (Opens.sheafHomResLE φ V ((Opens.map f).obj V) le_rfl) ⋙
      eU.inverse).IsLeftAdjoint

/-- Slice-site pullback `pullbackOver φ V` preserves the unit sheaf of modules. -/
def pullbackOverUnitIso (V : Opens Y) :
    unit (R.over ((Opens.map f).obj V)) ≅ (pullbackOver φ V).obj (unit (S.over V)) :=
  let eU : SheafOfModules.{u} (R.over ((Opens.map f).obj V)) ≌
      SheafOfModules.{u}
        ((((Opens.map f).obj V).isOpenEmbedding.sheafPullback RingCat.{u}).obj R) :=
    ((Opens.map f).obj V).sheafOfModulesEquivOver R
  (((Opens.map f).obj V).sheafOfModulesEquivOverInverseUnit R).symm ≪≫
    eU.inverse.mapIso
      ((pullbackObjUnitIso (Opens.sheafHomResLE φ V ((Opens.map f).obj V) le_rfl)).symm ≪≫
        (pullback.{u} (Opens.sheafHomResLE φ V ((Opens.map f).obj V) le_rfl)).mapIso
          (V.sheafOfModulesEquivOverUnit S).symm)

/-- Slice-site pullback `pullbackOver φ V` is naturally isomorphic to restricting to `V` before
pulling back along `(f, φ)` and restricting to `(Opens.map f).obj V`. -/
def overFunctorCompPullbackOverIso [(pushforward.{u} φ).IsRightAdjoint] (V : Opens Y) :
    overFunctor.{u} S V ⋙ pullbackOver φ V ≅
      pullback.{u} φ ⋙ overFunctor.{u} R ((Opens.map f).obj V) :=
  let eU : SheafOfModules.{u} (R.over ((Opens.map f).obj V)) ≌
      SheafOfModules.{u}
        ((((Opens.map f).obj V).isOpenEmbedding.sheafPullback RingCat.{u}).obj R) :=
    ((Opens.map f).obj V).sheafOfModulesEquivOver R
  let φV := Opens.sheafHomResLE φ V ((Opens.map f).obj V) le_rfl
  let P := pullback.{u} φV
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (V.overFunctorCompSheafOfModulesEquivOver S) P ≪≫
        (restrictPullbackIso φ V ((Opens.map f).obj V) le_rfl).symm)
      eU.inverse ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (pullback.{u} φ)
      (Functor.isoWhiskerRight
        (((Opens.map f).obj V).overFunctorCompSheafOfModulesEquivOver R).symm eU.inverse ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ eU.unitIso.symm ≪≫
        Functor.rightUnitor _)

end RingedSpacePullback

private lemma restrictPullbackIso_inv_app_unit_square
    {X Y : TopCat.{u}} {f : X ⟶ Y}
    {S : Y.Sheaf RingCat.{u}} {R : X.Sheaf RingCat.{u}}
    (φ : S ⟶ ((Opens.map f).sheafPushforwardContinuous RingCat.{u}
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).obj R)
    [(pushforward.{u} φ).IsRightAdjoint] (V : Opens Y) (U : Opens X)
    (e : U ≤ (Opens.map f).obj V) :
    (pullback.{u} (Opens.sheafHomResLE φ V U e)).map
        ((V.sheafOfModulesEquivOverUnit S).inv ≫
          (V.sheafOfModulesEquivOver S).functor.map (overFunctorUnitIso S V).hom ≫
          (V.overFunctorCompSheafOfModulesEquivOver S).hom.app (unit S)) ≫
      (restrictPullbackIso φ V U e).inv.app (unit S) ≫
      (U.sheafOfModulesRestrict.{u} R).map (pullbackObjUnitToUnit φ) =
    pullbackObjUnitToUnit (Opens.sheafHomResLE φ V U e) ≫
      ((U.sheafOfModulesEquivOverUnit R).inv ≫
        (U.sheafOfModulesEquivOver R).functor.map (overFunctorUnitIso R U).hom ≫
        (U.overFunctorCompSheafOfModulesEquivOver R).hom.app (unit R)) := by
  have hunitComp {Z : TopCat.{u}} (W : Opens Z) (M : Z.Sheaf RingCat.{u}) :
      ((W.sheafOfModulesEquivOverUnit M).inv ≫
          (W.sheafOfModulesEquivOver M).functor.map (overFunctorUnitIso M W).hom ≫
          (W.overFunctorCompSheafOfModulesEquivOver M).hom.app (unit M)) ≫
        (W.sheafOfModulesRestrictIsoPullback.{u} M).hom.app (unit M) ≫
        pullbackObjUnitToUnit (W.sheafInclusionHom RingCat.{u} M) = 𝟙 _ :=
    (congrArg (_ ≫ ·) (Opens.sheafOfModulesRestrictUnitIso_hom W M).symm).trans
      ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (Category.assoc _ _ _)).trans
        (Opens.sheafOfModulesEquivOverUnit_inv_comp_sheafOfModulesRestrictUnitIso_hom W M)))
  have hm : Mono ((U.sheafOfModulesRestrictIsoPullback.{u} R).hom.app (unit R) ≫
      pullbackObjUnitToUnit (U.sheafInclusionHom RingCat.{u} R)) :=
    mono_comp _ _
  refine (cancel_mono ((U.sheafOfModulesRestrictIsoPullback.{u} R).hom.app (unit R) ≫
    pullbackObjUnitToUnit (U.sheafInclusionHom RingCat.{u} R))).mp ?_
  have hRHS :
      (pullbackObjUnitToUnit (Opens.sheafHomResLE φ V U e) ≫
          ((U.sheafOfModulesEquivOverUnit R).inv ≫
            (U.sheafOfModulesEquivOver R).functor.map (overFunctorUnitIso R U).hom ≫
            (U.overFunctorCompSheafOfModulesEquivOver R).hom.app (unit R))) ≫
        ((U.sheafOfModulesRestrictIsoPullback.{u} R).hom.app (unit R) ≫
          pullbackObjUnitToUnit (U.sheafInclusionHom RingCat.{u} R)) =
      pullbackObjUnitToUnit (Opens.sheafHomResLE φ V U e) :=
    (Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) (hunitComp U R)).trans (Category.comp_id _))
  refine .trans ?_ hRHS.symm
  have hnat : (U.sheafOfModulesRestrict.{u} R).map (pullbackObjUnitToUnit φ) ≫
      (U.sheafOfModulesRestrictIsoPullback.{u} R).hom.app (unit R) =
      (U.sheafOfModulesRestrictIsoPullback.{u} R).hom.app ((pullback.{u} φ).obj (unit S)) ≫
      (pullback.{u} (U.sheafInclusionHom RingCat.{u} R)).map (pullbackObjUnitToUnit φ) :=
    (U.sheafOfModulesRestrictIsoPullback.{u} R).hom.naturality (pullbackObjUnitToUnit φ)
  have hkey :
      (restrictPullbackIso φ V U e).inv.app (unit S) ≫
        (U.sheafOfModulesRestrictIsoPullback.{u} R).hom.app ((pullback.{u} φ).obj (unit S)) ≫
        (pullback.{u} (U.sheafInclusionHom RingCat.{u} R)).map (pullbackObjUnitToUnit φ) ≫
        pullbackObjUnitToUnit (U.sheafInclusionHom RingCat.{u} R) =
      (pullback.{u} (Opens.sheafHomResLE φ V U e)).map
          ((V.sheafOfModulesRestrictIsoPullback.{u} S).hom.app (unit S) ≫
            pullbackObjUnitToUnit (V.sheafInclusionHom RingCat.{u} S)) ≫
        pullbackObjUnitToUnit (Opens.sheafHomResLE φ V U e) := by
    refine (Iso.inv_comp_eq ((restrictPullbackIso φ V U e).app (unit S))).mpr ?_
    have : (Opens.map f ⋙ Opens.map U.inclusion').IsContinuous
        (Opens.grothendieckTopology Y)
        (Opens.grothendieckTopology ((Opens.toTopCat X).obj U)) :=
      Functor.isContinuous_comp _ _ _ (Opens.grothendieckTopology X) _
    have : (Opens.map V.inclusion' ⋙ Opens.map (Opens.resLE f V U e)).IsContinuous
        (Opens.grothendieckTopology Y)
        (Opens.grothendieckTopology ((Opens.toTopCat X).obj U)) :=
      Functor.isContinuous_comp _ _ _
        (Opens.grothendieckTopology ((Opens.toTopCat Y).obj V)) _
    have hcompV := pullbackObjUnitToUnit_comp (V.sheafInclusionHom RingCat.{u} S)
      (Opens.sheafHomResLE φ V U e)
    have hcompU := pullbackObjUnitToUnit_comp φ (U.sheafInclusionHom RingCat.{u} R)
    have hcongr := (Iso.inv_comp_eq
      ((pullbackCongr₂.{u} _ (Opens.mapCompResLEIso f V U e)
        (Opens.sheafInclusionHom_comp_map_sheafHomResLE φ V U e)).app (unit S))).mpr
      (pullbackCongr₂_hom_app_pullbackObjUnitToUnit _ (Opens.mapCompResLEIso f V U e)
        (Opens.sheafInclusionHom_comp_map_sheafHomResLE φ V U e)).symm
    symm
    change (restrictPullbackIso φ V U e).hom.app (unit S) ≫
        (pullback.{u} (Opens.sheafHomResLE φ V U e)).map
          ((V.sheafOfModulesRestrictIsoPullback.{u} S).hom.app (unit S) ≫
            pullbackObjUnitToUnit (V.sheafInclusionHom RingCat.{u} S)) ≫
        pullbackObjUnitToUnit (Opens.sheafHomResLE φ V U e) = _
    rw [restrictPullbackIso_hom_app]
    simp only [Category.assoc, CategoryTheory.Functor.map_comp]
    have hidV :
        (pullback.{u} (Opens.sheafHomResLE φ V U e)).map
            ((V.sheafOfModulesRestrictIsoPullback.{u} S).inv.app (unit S)) ≫
          (pullback.{u} (Opens.sheafHomResLE φ V U e)).map
            ((V.sheafOfModulesRestrictIsoPullback.{u} S).hom.app (unit S)) = 𝟙 _ :=
      (CategoryTheory.Functor.map_comp _ _ _).symm.trans
        ((congrArg _ (Iso.inv_hom_id_app
          (V.sheafOfModulesRestrictIsoPullback.{u} S) (unit S))).trans
          (CategoryTheory.Functor.map_id _ _))
    have hstepV :
        (pullback.{u} (Opens.sheafHomResLE φ V U e)).map
            ((V.sheafOfModulesRestrictIsoPullback.{u} S).inv.app (unit S)) ≫
          (pullback.{u} (Opens.sheafHomResLE φ V U e)).map
            ((V.sheafOfModulesRestrictIsoPullback.{u} S).hom.app (unit S)) ≫
          (pullback.{u} (Opens.sheafHomResLE φ V U e)).map
            (pullbackObjUnitToUnit (V.sheafInclusionHom RingCat.{u} S)) ≫
          pullbackObjUnitToUnit (Opens.sheafHomResLE φ V U e) =
        (pullback.{u} (Opens.sheafHomResLE φ V U e)).map
            (pullbackObjUnitToUnit (V.sheafInclusionHom RingCat.{u} S)) ≫
          pullbackObjUnitToUnit (Opens.sheafHomResLE φ V U e) :=
      (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hidV).trans (Category.id_comp _))
    have hstepU :
        (pullbackComp.{u} φ (U.sheafInclusionHom RingCat.{u} R)).hom.app (unit S) ≫
          (pullbackComp.{u} φ (U.sheafInclusionHom RingCat.{u} R)).inv.app (unit S) ≫
          (pullback.{u} (U.sheafInclusionHom RingCat.{u} R)).map (pullbackObjUnitToUnit φ) ≫
          pullbackObjUnitToUnit (U.sheafInclusionHom RingCat.{u} R) =
        (pullback.{u} (U.sheafInclusionHom RingCat.{u} R)).map (pullbackObjUnitToUnit φ) ≫
          pullbackObjUnitToUnit (U.sheafInclusionHom RingCat.{u} R) :=
      (Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ _)
          (Iso.hom_inv_id_app (pullbackComp.{u} φ (U.sheafInclusionHom RingCat.{u} R))
            (unit S))).trans (Category.id_comp _))
    refine congrArg (_ ≫ ·) ?_
    refine (congrArg (_ ≫ ·) (congrArg (_ ≫ ·) (congrArg (_ ≫ ·) hstepV))).trans ?_
    refine (congrArg (_ ≫ ·) (congrArg (_ ≫ ·) hcompV)).trans ?_
    refine (congrArg (_ ≫ ·) hcongr).trans ?_
    exact (congrArg (_ ≫ ·) hcompU.symm).trans hstepU
  have hL1 :
      ((pullback.{u} (Opens.sheafHomResLE φ V U e)).map
          ((V.sheafOfModulesEquivOverUnit S).inv ≫
            (V.sheafOfModulesEquivOver S).functor.map (overFunctorUnitIso S V).hom ≫
            (V.overFunctorCompSheafOfModulesEquivOver S).hom.app (unit S)) ≫
        (restrictPullbackIso φ V U e).inv.app (unit S) ≫
        (U.sheafOfModulesRestrict.{u} R).map (pullbackObjUnitToUnit φ)) ≫
        ((U.sheafOfModulesRestrictIsoPullback.{u} R).hom.app (unit R) ≫
          pullbackObjUnitToUnit (U.sheafInclusionHom RingCat.{u} R)) =
      (pullback.{u} (Opens.sheafHomResLE φ V U e)).map
          ((V.sheafOfModulesEquivOverUnit S).inv ≫
            (V.sheafOfModulesEquivOver S).functor.map (overFunctorUnitIso S V).hom ≫
            (V.overFunctorCompSheafOfModulesEquivOver S).hom.app (unit S)) ≫
        (restrictPullbackIso φ V U e).inv.app (unit S) ≫
        (U.sheafOfModulesRestrictIsoPullback.{u} R).hom.app ((pullback.{u} φ).obj (unit S)) ≫
        (pullback.{u} (U.sheafInclusionHom RingCat.{u} R)).map (pullbackObjUnitToUnit φ) ≫
        pullbackObjUnitToUnit (U.sheafInclusionHom RingCat.{u} R) := by
    refine (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ?_)
    refine (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ?_)
    refine (Category.assoc _ _ _).symm.trans ?_
    exact (congrArg (· ≫ _) hnat).trans (Category.assoc _ _ _)
  refine hL1.trans ?_
  refine (congrArg ((pullback.{u} (Opens.sheafHomResLE φ V U e)).map _ ≫ ·) hkey).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) ?_).trans (Category.id_comp _)
  refine (CategoryTheory.Functor.map_comp _ _ _).symm.trans ?_
  exact (congrArg _ (hunitComp V S)).trans (CategoryTheory.Functor.map_id _ _)

private lemma pullbackOverUnitIso_inner
    {X Y : TopCat.{u}} {f : X ⟶ Y}
    {S : Y.Sheaf RingCat.{u}} {R : X.Sheaf RingCat.{u}}
    (φ : S ⟶ ((Opens.map f).sheafPushforwardContinuous RingCat.{u}
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).obj R)
    [(pushforward.{u} φ).IsRightAdjoint] (V : Opens Y) (U : Opens X)
    (hU : U = (Opens.map f).obj V) :
    (U.sheafOfModulesEquivOverUnit R).hom ≫
      (pullbackObjUnitIso (Opens.sheafHomResLE φ V U hU.le)).inv ≫
      (pullback.{u} (Opens.sheafHomResLE φ V U hU.le)).map
        ((V.sheafOfModulesEquivOverUnit S).inv ≫
          (V.sheafOfModulesEquivOver S).functor.map (overFunctorUnitIso S V).hom ≫
          (V.overFunctorCompSheafOfModulesEquivOver S).hom.app (unit S)) ≫
      (restrictPullbackIso φ V U hU.le).inv.app (unit S) ≫
      (U.overFunctorCompSheafOfModulesEquivOver R).inv.app ((pullback.{u} φ).obj (unit S)) ≫
      (U.sheafOfModulesEquivOver R).functor.map
        ((overFunctor.{u} R U).map (pullbackObjUnitToUnit φ)) ≫
      (U.sheafOfModulesEquivOver R).functor.map (overFunctorUnitIso R U).inv = 𝟙 _ := by
  have hnatU :
      (U.overFunctorCompSheafOfModulesEquivOver R).inv.app ((pullback.{u} φ).obj (unit S)) ≫
        (U.sheafOfModulesEquivOver R).functor.map
          ((overFunctor.{u} R U).map (pullbackObjUnitToUnit φ)) =
      (U.sheafOfModulesRestrict.{u} R).map (pullbackObjUnitToUnit φ) ≫
        (U.overFunctorCompSheafOfModulesEquivOver R).inv.app (unit R) :=
    ((U.overFunctorCompSheafOfModulesEquivOver R).inv.naturality (pullbackObjUnitToUnit φ)).symm
  have step1 := congrArg
    (fun k ↦ (U.sheafOfModulesEquivOverUnit R).hom ≫
      (pullbackObjUnitIso (Opens.sheafHomResLE φ V U hU.le)).inv ≫
      (pullback.{u} (Opens.sheafHomResLE φ V U hU.le)).map
        ((V.sheafOfModulesEquivOverUnit S).inv ≫
          (V.sheafOfModulesEquivOver S).functor.map (overFunctorUnitIso S V).hom ≫
          (V.overFunctorCompSheafOfModulesEquivOver S).hom.app (unit S)) ≫
      (restrictPullbackIso φ V U hU.le).inv.app (unit S) ≫
      k ≫ (U.sheafOfModulesEquivOver R).functor.map (overFunctorUnitIso R U).inv) hnatU
  have step2 := congrArg
    (fun k ↦ (U.sheafOfModulesEquivOverUnit R).hom ≫
      (pullbackObjUnitIso (Opens.sheafHomResLE φ V U hU.le)).inv ≫
      k ≫ (U.overFunctorCompSheafOfModulesEquivOver R).inv.app (unit R) ≫
      (U.sheafOfModulesEquivOver R).functor.map (overFunctorUnitIso R U).inv)
    (restrictPullbackIso_inv_app_unit_square φ V U hU.le)
  have step3 :
      (U.sheafOfModulesEquivOverUnit R).hom ≫
        (pullbackObjUnitIso (Opens.sheafHomResLE φ V U hU.le)).inv ≫
        (pullbackObjUnitToUnit (Opens.sheafHomResLE φ V U hU.le) ≫
          ((U.sheafOfModulesEquivOverUnit R).inv ≫
            (U.sheafOfModulesEquivOver R).functor.map (overFunctorUnitIso R U).hom ≫
            (U.overFunctorCompSheafOfModulesEquivOver R).hom.app (unit R))) ≫
        (U.overFunctorCompSheafOfModulesEquivOver R).inv.app (unit R) ≫
        (U.sheafOfModulesEquivOver R).functor.map (overFunctorUnitIso R U).inv = 𝟙 _ := by
    have h4a :
        (pullbackObjUnitIso (Opens.sheafHomResLE φ V U hU.le)).inv ≫
          pullbackObjUnitToUnit (Opens.sheafHomResLE φ V U hU.le) = 𝟙 _ :=
      (congrArg (_ ≫ ·) (pullbackObjUnitIso_hom _).symm).trans
        (Iso.inv_hom_id (pullbackObjUnitIso (Opens.sheafHomResLE φ V U hU.le)))
    let a := (U.sheafOfModulesEquivOverUnit R).hom
    let b := (pullbackObjUnitIso (Opens.sheafHomResLE φ V U hU.le)).inv
    let c := pullbackObjUnitToUnit (Opens.sheafHomResLE φ V U hU.le)
    let m := (U.sheafOfModulesEquivOver R).functor.map (overFunctorUnitIso R U).hom
    let h := (U.overFunctorCompSheafOfModulesEquivOver R).hom.app (unit R)
    let i := (U.overFunctorCompSheafOfModulesEquivOver R).inv.app (unit R)
    let n := (U.sheafOfModulesEquivOver R).functor.map (overFunctorUnitIso R U).inv
    let d := (U.sheafOfModulesEquivOverUnit R).inv ≫ m ≫ h
    let k := i ≫ n
    have h4b : b ≫ (c ≫ d) ≫ k = d ≫ k :=
      (congrArg (b ≫ ·) (Category.assoc c d k)).trans
        ((Category.assoc b c (d ≫ k)).symm.trans
          ((congrArg (· ≫ (d ≫ k)) h4a).trans (Category.id_comp (d ≫ k))))
    have h4c : a ≫ d ≫ k = (m ≫ h) ≫ k :=
      (congrArg (a ≫ ·) (Category.assoc (U.sheafOfModulesEquivOverUnit R).inv (m ≫ h) k)).trans
        ((Category.assoc a (U.sheafOfModulesEquivOverUnit R).inv ((m ≫ h) ≫ k)).symm.trans
          ((congrArg (· ≫ ((m ≫ h) ≫ k)) (Iso.hom_inv_id (U.sheafOfModulesEquivOverUnit R))).trans
            (Category.id_comp ((m ≫ h) ≫ k))))
    have h4d : (m ≫ h) ≫ i ≫ n = m ≫ n :=
      (Category.assoc m h (i ≫ n)).trans
        (congrArg (m ≫ ·) ((Category.assoc h i n).symm.trans
          ((congrArg (· ≫ n) (Iso.hom_inv_id_app (U.overFunctorCompSheafOfModulesEquivOver R)
            (unit R))).trans (Category.id_comp n))))
    have h4e : m ≫ n = 𝟙 _ :=
      (CategoryTheory.Functor.map_comp _ _ _).symm.trans
        ((congrArg _ (Iso.hom_inv_id (overFunctorUnitIso R U))).trans
          (CategoryTheory.Functor.map_id _ _))
    exact (congrArg (a ≫ ·) h4b).trans (h4c.trans (h4d.trans h4e))
  refine step1.trans ?_
  refine (congrArg (_ ≫ ·) (congrArg (_ ≫ ·) ?_)).trans (step2.trans step3)
  refine (congrArg (_ ≫ ·) ?_).trans (Category.assoc _ _ _).symm
  exact (congrArg (_ ≫ ·) (Category.assoc _ _ _)).trans (Category.assoc _ _ _).symm

section UnitCompatibility

variable {X Y : TopCat.{u}} {f : X ⟶ Y}
  {S : Y.Sheaf RingCat.{u}} {R : X.Sheaf RingCat.{u}}
  (φ : S ⟶ ((Opens.map f).sheafPushforwardContinuous RingCat.{u}
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).obj R)

/-- The unit preservation isomorphism `pullbackOverUnitIso φ V` is compatible with
`overFunctorCompPullbackOverIso φ V` and the global pullback unit comparison
`pullbackObjUnitToUnit φ`. -/
@[reassoc]
theorem pullbackOverUnitIso_hom_comp_overFunctorCompPullbackOverIso_hom_app
    [(pushforward.{u} φ).IsRightAdjoint] (V : Opens Y) :
    (pullbackOverUnitIso φ V).hom ≫
        (pullbackOver φ V).map (overFunctorUnitIso S V).hom ≫
        (overFunctorCompPullbackOverIso φ V).hom.app (unit S) ≫
        (overFunctor.{u} R ((Opens.map f).obj V)).map (pullbackObjUnitToUnit φ) =
      (overFunctorUnitIso R ((Opens.map f).obj V)).hom := by
  have hLHS :
      (pullbackOverUnitIso φ V).hom ≫
        (pullbackOver φ V).map (overFunctorUnitIso S V).hom ≫
        (overFunctorCompPullbackOverIso φ V).hom.app (unit S) ≫
        (overFunctor.{u} R ((Opens.map f).obj V)).map (pullbackObjUnitToUnit φ) =
      ((((Opens.map f).obj V).sheafOfModulesEquivOver R).unitIso.hom.app
          (unit (R.over ((Opens.map f).obj V)))) ≫
        (((Opens.map f).obj V).sheafOfModulesEquivOver R).inverse.map
          ((((Opens.map f).obj V).sheafOfModulesEquivOverUnit R).hom ≫
            (pullbackObjUnitIso (Opens.sheafHomResLE φ V ((Opens.map f).obj V) le_rfl)).inv ≫
            (pullback.{u} (Opens.sheafHomResLE φ V ((Opens.map f).obj V) le_rfl)).map
              ((V.sheafOfModulesEquivOverUnit S).inv ≫
                (V.sheafOfModulesEquivOver S).functor.map (overFunctorUnitIso S V).hom ≫
                (V.overFunctorCompSheafOfModulesEquivOver S).hom.app (unit S)) ≫
            (restrictPullbackIso φ V ((Opens.map f).obj V) le_rfl).inv.app (unit S) ≫
            (((Opens.map f).obj V).overFunctorCompSheafOfModulesEquivOver R).inv.app
              ((pullback.{u} φ).obj (unit S)) ≫
            (((Opens.map f).obj V).sheafOfModulesEquivOver R).functor.map
              ((overFunctor.{u} R ((Opens.map f).obj V)).map (pullbackObjUnitToUnit φ)) ≫
            (((Opens.map f).obj V).sheafOfModulesEquivOver R).functor.map
              (overFunctorUnitIso R ((Opens.map f).obj V)).inv) ≫
        ((((Opens.map f).obj V).sheafOfModulesEquivOver R).unitIso.inv.app
          (unit (R.over ((Opens.map f).obj V)))) ≫
        (overFunctorUnitIso R ((Opens.map f).obj V)).hom := by
    have hunitNat :
        (((Opens.map f).obj V).sheafOfModulesEquivOver R).unitIso.inv.app
            ((overFunctor.{u} R ((Opens.map f).obj V)).obj ((pullback.{u} φ).obj (unit S))) ≫
          (overFunctor.{u} R ((Opens.map f).obj V)).map (pullbackObjUnitToUnit φ) ≫
          (overFunctorUnitIso R ((Opens.map f).obj V)).inv =
        (((Opens.map f).obj V).sheafOfModulesEquivOver R).inverse.map
            ((((Opens.map f).obj V).sheafOfModulesEquivOver R).functor.map
              ((overFunctor.{u} R ((Opens.map f).obj V)).map (pullbackObjUnitToUnit φ)) ≫
            (((Opens.map f).obj V).sheafOfModulesEquivOver R).functor.map
              (overFunctorUnitIso R ((Opens.map f).obj V)).inv) ≫
          ((((Opens.map f).obj V).sheafOfModulesEquivOver R).unitIso.inv.app
            (unit (R.over ((Opens.map f).obj V)))) := by
      have h1 := (((Opens.map f).obj V).sheafOfModulesEquivOver R).unitIso.inv.naturality
        ((overFunctor.{u} R ((Opens.map f).obj V)).map (pullbackObjUnitToUnit φ))
      have h2 := (((Opens.map f).obj V).sheafOfModulesEquivOver R).unitIso.inv.naturality
        (overFunctorUnitIso R ((Opens.map f).obj V)).inv
      refine (Category.assoc _ _ _).symm.trans ?_
      refine (congrArg (· ≫ _) h1.symm).trans ?_
      refine (Category.assoc _ _ _).trans ?_
      refine (congrArg (_ ≫ ·) h2.symm).trans ?_
      refine (Category.assoc _ _ _).symm.trans ?_
      exact congrArg (· ≫ _) (CategoryTheory.Functor.map_comp _ _ _).symm
    have hPBO :
        (pullbackOverUnitIso φ V).hom =
        ((((Opens.map f).obj V).sheafOfModulesEquivOver R).unitIso.hom.app
            (unit (R.over ((Opens.map f).obj V)))) ≫
          (((Opens.map f).obj V).sheafOfModulesEquivOver R).inverse.map
            ((((Opens.map f).obj V).sheafOfModulesEquivOverUnit R).hom ≫
              (pullbackObjUnitIso (Opens.sheafHomResLE φ V ((Opens.map f).obj V) le_rfl)).inv ≫
              (pullback.{u} (Opens.sheafHomResLE φ V ((Opens.map f).obj V) le_rfl)).map
                (V.sheafOfModulesEquivOverUnit S).inv) := by
      refine (Iso.trans_hom _ _).trans ?_
      refine (congrArg₂ (· ≫ ·) (Iso.trans_inv _ _) (Functor.mapIso_hom _ _)).trans ?_
      refine (congrArg₂ (· ≫ ·)
        (congrArg (_ ≫ ·) (Functor.mapIso_inv _ _))
        (congrArg ((((Opens.map f).obj V).sheafOfModulesEquivOver R).inverse.map ·)
          (Iso.trans_hom _ _))).trans ?_
      refine (Category.assoc _ _ _).trans ?_
      refine congrArg (_ ≫ ·) ?_
      refine (CategoryTheory.Functor.map_comp _ _ _).symm.trans ?_
      refine congrArg ((((Opens.map f).obj V).sheafOfModulesEquivOver R).inverse.map ·) ?_
      exact congrArg (_ ≫ ·) (congrArg (_ ≫ ·) (Functor.mapIso_hom _ _))
    have hOC :
        (overFunctorCompPullbackOverIso φ V).hom.app (unit S) =
        (((Opens.map f).obj V).sheafOfModulesEquivOver R).inverse.map
            ((pullback.{u} (Opens.sheafHomResLE φ V ((Opens.map f).obj V) le_rfl)).map
                ((V.overFunctorCompSheafOfModulesEquivOver S).hom.app (unit S)) ≫
              (restrictPullbackIso φ V ((Opens.map f).obj V) le_rfl).inv.app (unit S) ≫
              (((Opens.map f).obj V).overFunctorCompSheafOfModulesEquivOver R).inv.app
                ((pullback.{u} φ).obj (unit S))) ≫
          (((Opens.map f).obj V).sheafOfModulesEquivOver R).unitIso.inv.app
            ((overFunctor.{u} R ((Opens.map f).obj V)).obj ((pullback.{u} φ).obj (unit S))) := by
      refine (Category.id_comp _).trans ?_
      refine (congrArg₂ (· ≫ ·)
        (congrArg ((((Opens.map f).obj V).sheafOfModulesEquivOver R).inverse.map ·)
          (Category.id_comp _))
        ((Category.id_comp _).trans (congrArg (_ ≫ ·)
          ((Category.id_comp _).trans (congrArg (_ ≫ ·) (Category.comp_id _)))))).trans ?_
      refine (Category.assoc _ _ _).symm.trans ?_
      refine congrArg (· ≫ _) ?_
      refine (CategoryTheory.Functor.map_comp _ _ _).symm.trans ?_
      exact congrArg ((((Opens.map f).obj V).sheafOfModulesEquivOver R).inverse.map ·)
        (Category.assoc _ _ _)
    have hmap :
        (pullbackOver φ V).map (overFunctorUnitIso S V).hom =
        (((Opens.map f).obj V).sheafOfModulesEquivOver R).inverse.map
          ((pullback.{u} (Opens.sheafHomResLE φ V ((Opens.map f).obj V) le_rfl)).map
            ((V.sheafOfModulesEquivOver S).functor.map (overFunctorUnitIso S V).hom)) :=
      rfl
    have h12 :
        (pullbackOverUnitIso φ V).hom ≫ (pullbackOver φ V).map (overFunctorUnitIso S V).hom =
        ((((Opens.map f).obj V).sheafOfModulesEquivOver R).unitIso.hom.app
            (unit (R.over ((Opens.map f).obj V)))) ≫
          (((Opens.map f).obj V).sheafOfModulesEquivOver R).inverse.map
            ((((Opens.map f).obj V).sheafOfModulesEquivOverUnit R).hom ≫
              (pullbackObjUnitIso (Opens.sheafHomResLE φ V ((Opens.map f).obj V) le_rfl)).inv ≫
              (pullback.{u} (Opens.sheafHomResLE φ V ((Opens.map f).obj V) le_rfl)).map
                ((V.sheafOfModulesEquivOverUnit S).inv ≫
                  (V.sheafOfModulesEquivOver S).functor.map (overFunctorUnitIso S V).hom)) := by
      refine (congrArg (· ≫ _) hPBO).trans ?_
      refine (congrArg (_ ≫ ·) hmap).trans ?_
      refine (Category.assoc _ _ _).trans ?_
      refine congrArg (_ ≫ ·) ?_
      refine (CategoryTheory.Functor.map_comp _ _ _).symm.trans ?_
      refine congrArg ((((Opens.map f).obj V).sheafOfModulesEquivOver R).inverse.map ·) ?_
      refine (Category.assoc _ _ _).trans ?_
      refine congrArg (_ ≫ ·) ?_
      refine (Category.assoc _ _ _).trans ?_
      refine congrArg (_ ≫ ·) ?_
      exact (CategoryTheory.Functor.map_comp _ _ _).symm
    have h34 :
        (overFunctorCompPullbackOverIso φ V).hom.app (unit S) ≫
          ((overFunctor.{u} R ((Opens.map f).obj V)).map (pullbackObjUnitToUnit φ) ≫
            (overFunctorUnitIso R ((Opens.map f).obj V)).inv) =
        (((Opens.map f).obj V).sheafOfModulesEquivOver R).inverse.map
            ((pullback.{u} (Opens.sheafHomResLE φ V ((Opens.map f).obj V) le_rfl)).map
                ((V.overFunctorCompSheafOfModulesEquivOver S).hom.app (unit S)) ≫
              (restrictPullbackIso φ V ((Opens.map f).obj V) le_rfl).inv.app (unit S) ≫
              (((Opens.map f).obj V).overFunctorCompSheafOfModulesEquivOver R).inv.app
                ((pullback.{u} φ).obj (unit S)) ≫
              (((Opens.map f).obj V).sheafOfModulesEquivOver R).functor.map
                ((overFunctor.{u} R ((Opens.map f).obj V)).map (pullbackObjUnitToUnit φ)) ≫
              (((Opens.map f).obj V).sheafOfModulesEquivOver R).functor.map
                (overFunctorUnitIso R ((Opens.map f).obj V)).inv) ≫
          ((((Opens.map f).obj V).sheafOfModulesEquivOver R).unitIso.inv.app
            (unit (R.over ((Opens.map f).obj V)))) := by
      refine (congrArg (· ≫ _) hOC).trans ?_
      refine (Category.assoc _ _ _).trans ?_
      refine (congrArg (_ ≫ ·) hunitNat).trans ?_
      refine (Category.assoc _ _ _).symm.trans ?_
      refine congrArg (· ≫ _) ?_
      refine (CategoryTheory.Functor.map_comp _ _ _).symm.trans ?_
      refine congrArg ((((Opens.map f).obj V).sheafOfModulesEquivOver R).inverse.map ·) ?_
      refine (Category.assoc _ _ _).trans ?_
      refine congrArg (_ ≫ ·) ?_
      refine (Category.assoc _ _ _).trans ?_
      refine congrArg (_ ≫ ·) ?_
      exact (Category.assoc _ _ _).symm
    calc (pullbackOverUnitIso φ V).hom ≫
          (pullbackOver φ V).map (overFunctorUnitIso S V).hom ≫
          (overFunctorCompPullbackOverIso φ V).hom.app (unit S) ≫
          (overFunctor.{u} R ((Opens.map f).obj V)).map (pullbackObjUnitToUnit φ)
        = (pullbackOverUnitIso φ V).hom ≫
            (pullbackOver φ V).map (overFunctorUnitIso S V).hom ≫
            ((overFunctorCompPullbackOverIso φ V).hom.app (unit S) ≫
              ((overFunctor.{u} R ((Opens.map f).obj V)).map (pullbackObjUnitToUnit φ) ≫
                (overFunctorUnitIso R ((Opens.map f).obj V)).inv)) ≫
            (overFunctorUnitIso R ((Opens.map f).obj V)).hom := by
          simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      _ = _ := by
          refine (congrArg (_ ≫ ·) (congrArg (_ ≫ ·) (congrArg (· ≫ _) h34))).trans ?_
          refine (Category.assoc _ _ _).symm.trans ?_
          refine (Category.assoc _ _ _).symm.trans ?_
          refine (congrArg (· ≫ (overFunctorUnitIso R ((Opens.map f).obj V)).hom) ?_).trans
            ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Category.assoc _ _ _)))
          refine (congrArg (· ≫ _) h12).trans ?_
          refine (Category.assoc _ _ _).trans ?_
          refine congrArg (_ ≫ ·) ?_
          refine (Category.assoc _ _ _).symm.trans ?_
          refine congrArg (· ≫ _) ?_
          refine (CategoryTheory.Functor.map_comp _ _ _).symm.trans ?_
          refine congrArg ((((Opens.map f).obj V).sheafOfModulesEquivOver R).inverse.map ·) ?_
          refine (Category.assoc _ _ _).trans ?_
          refine congrArg (_ ≫ ·) ?_
          refine (Category.assoc _ _ _).trans ?_
          refine congrArg (_ ≫ ·) ?_
          refine (Category.assoc _ _ _).symm.trans ?_
          refine congrArg (· ≫ _) ?_
          exact (CategoryTheory.Functor.map_comp _ _ _).symm
  rw [hLHS, pullbackOverUnitIso_inner φ V ((Opens.map f).obj V) rfl,
    CategoryTheory.Functor.map_id]
  dsimp
  rw [Category.id_comp, Iso.hom_inv_id_app_assoc]

end UnitCompatibility

end SheafOfModules

end
