/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Pullback.Basic
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Pushforward.Basic
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Restriction.OpenSubspace
public import TauCeti.Topology.Sheaves.Functors

/-!
# Restriction and slice-site pullback of sheaves of modules on ringed spaces

For a continuous map `f : X ⟶ Y` and a morphism of sheaves of rings `φ : S ⟶ f_* R`, restricting a
sheaf of rings to opens `V ⊆ Y` and `U ⊆ f⁻¹(V)` produces the restricted ring-sheaf morphism
`TopologicalSpace.Opens.sheafHomResLE φ V U e` along
`TopologicalSpace.Opens.resLE f V U e : (Opens.toTopCat X).obj U ⟶ (Opens.toTopCat Y).obj V`.
Module pullback commutes with open-subspace restriction (`SheafOfModules.restrictPullbackIso`),
yielding the slice-site pullback functor `SheafOfModules.pullbackOver φ V` together with its unit
and slice-restriction natural comparisons `SheafOfModules.pullbackOverUnitIso` and
`SheafOfModules.overFunctorCompPullbackOverIso`.

## Main declarations

* `SheafOfModules.restrictPullbackIso`: compatibility of module pullback with open-subspace
  restriction;
* `SheafOfModules.pullbackOver`: the induced pullback functor between slice sites;
* `SheafOfModules.pullbackOverUnitIso`: unit preservation for `pullbackOver`;
* `SheafOfModules.overFunctorCompPullbackOverIso`: natural isomorphism identifying slice
  restriction followed by `pullbackOver` with `pullback` followed by slice restriction.

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

end SheafOfModules

end
