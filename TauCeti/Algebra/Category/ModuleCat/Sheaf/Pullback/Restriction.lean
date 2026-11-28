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
yielding the slice-site pullback functor `SheafOfModules.pullbackOver φ V`, its adjunction
`SheafOfModules.pullbackOverAdj φ V` to the restricted pushforward, and its unit and
slice-restriction natural comparisons `SheafOfModules.pullbackOverUnitIso` and
`SheafOfModules.overFunctorCompPullbackOverIso` (together with unit compatibilities
`SheafOfModules.restrictPullbackIso_hom_app_pullbackObjUnitToUnit` and
`SheafOfModules.pullbackOverUnitIso_hom_comp_overFunctorCompPullbackOverIso_hom_app`).

## Adjunction prerequisites

* `SheafOfModules.restrictPullbackIso.{v}` and `SheafOfModules.restrictPullbackIso_hom_app` work for
  an arbitrary module universe `v`, and therefore take both `[(pushforward.{v} φ).IsRightAdjoint]`
  and `[(pushforward.{v} (Opens.sheafHomResLE φ V U e)).IsRightAdjoint]`. At `v = u`, the
  restricted pushforward instance is supplied automatically by
  `isRightAdjoint_pushforward_sheafHomResLE` (via `SheafOfModules.isRightAdjoint_pushforward`),
  while callers can install the global instance locally with
  `letI := SheafOfModules.isRightAdjoint_pushforward φ`.
* `SheafOfModules.pullbackOver`, `SheafOfModules.pullbackOverAdj`, and
  `SheafOfModules.pullbackOverUnitIso` operate in universe `u` and obtain the restricted
  pushforward adjunction automatically via `isRightAdjoint_pushforward_sheafHomResLE`, so they need
  no extra `[IsRightAdjoint]` argument.
* `SheafOfModules.overFunctorCompPullbackOverIso`,
  `SheafOfModules.restrictPullbackIso_hom_app_pullbackObjUnitToUnit`, and
  `SheafOfModules.pullbackOverUnitIso_hom_comp_overFunctorCompPullbackOverIso_hom_app` operate in
  universe `u` and therefore only require `[(pushforward.{u} φ).IsRightAdjoint]`.

## Main declarations

* `SheafOfModules.restrictPullbackIso`, `SheafOfModules.restrictPullbackIso_hom_app`, and
  `SheafOfModules.restrictPullbackIso_hom_app_pullbackObjUnitToUnit`: compatibility of module
  pullback with open-subspace restriction, its component formula, and its unit compatibility;
* `SheafOfModules.pullbackOver` (with `pullbackOver_obj`, `pullbackOver_map`) and
  `SheafOfModules.pullbackOverAdj`: the induced pullback functor between slice sites and its
  adjunction to the restricted pushforward transported along `sheafOfModulesEquivOver`;
* `SheafOfModules.pullbackOverUnitIso` (with `pullbackOverUnitIso_hom`): unit preservation for
  `pullbackOver`;
* `SheafOfModules.overFunctorCompPullbackOverIso` (with `overFunctorCompPullbackOverIso_hom_app`)
  and `SheafOfModules.pullbackOverUnitIso_hom_comp_overFunctorCompPullbackOverIso_hom_app`: natural
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
subspaces `V ⊆ Y` and `U ⊆ f⁻¹(V)` at any module universe `v`, given pushforward adjunctions for
both `φ` and `Opens.sheafHomResLE φ V U e` (at `v = u`, the latter is supplied automatically by
`isRightAdjoint_pushforward_sheafHomResLE`, and the former is available via
`SheafOfModules.isRightAdjoint_pushforward φ`). -/
def restrictPullbackIso [(pushforward.{v} φ).IsRightAdjoint]
    (V : Opens Y) (U : Opens X) (e : U ≤ (Opens.map f).obj V)
    [(pushforward.{v} (Opens.sheafHomResLE φ V U e)).IsRightAdjoint] :
    pullback.{v} φ ⋙ U.sheafOfModulesRestrict.{v} R ≅
      V.sheafOfModulesRestrict.{v} S ⋙ pullback.{v} (Opens.sheafHomResLE φ V U e) :=
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
      (U.sheafOfModulesRestrictIsoPullback.{v} R).hom.app ((pullback.{v} φ).obj M) ≫
        (pullbackComp.{v} φ (U.sheafInclusionHom RingCat.{u} R)).hom.app M ≫
        (pullbackCongr₂.{v} _ (Opens.mapCompResLEIso f V U e)
          (Opens.sheafInclusionHom_comp_map_sheafHomResLE φ V U e)).inv.app M ≫
        (pullbackComp.{v} (V.sheafInclusionHom RingCat.{u} S)
          (Opens.sheafHomResLE φ V U e)).inv.app M ≫
        (pullback.{v} (Opens.sheafHomResLE φ V U e)).map
          ((V.sheafOfModulesRestrictIsoPullback.{v} S).inv.app M) :=
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

/-- Action of `pullbackOver φ V` on an object `M : SheafOfModules (S.over V)`. -/
theorem pullbackOver_obj (V : Opens Y) (M : SheafOfModules.{u} (S.over V)) :
    (pullbackOver φ V).obj M =
      (((Opens.map f).obj V).sheafOfModulesEquivOver R).inverse.obj
        ((pullback.{u} (Opens.sheafHomResLE φ V ((Opens.map f).obj V) le_rfl)).obj
          ((V.sheafOfModulesEquivOver S).functor.obj M)) := by
  unfold pullbackOver
  rfl

/-- Action of `pullbackOver φ V` on a morphism of module sheaves over `V`. -/
theorem pullbackOver_map (V : Opens Y) {M N : SheafOfModules.{u} (S.over V)} (g : M ⟶ N) :
    (pullbackOver φ V).map g =
      eqToHom (pullbackOver_obj φ V M) ≫
        (((Opens.map f).obj V).sheafOfModulesEquivOver R).inverse.map
          ((pullback.{u} (Opens.sheafHomResLE φ V ((Opens.map f).obj V) le_rfl)).map
            ((V.sheafOfModulesEquivOver S).functor.map g)) ≫
        eqToHom (pullbackOver_obj φ V N).symm := by
  unfold pullbackOver
  exact (Category.id_comp _).symm.trans (Category.comp_id _).symm

/-- Slice-site pullback `pullbackOver φ V` is left adjoint to the restricted pushforward along
`Opens.sheafHomResLE φ V ((Opens.map f).obj V) le_rfl`, transported through the two slice
equivalences `sheafOfModulesEquivOver`. -/
def pullbackOverAdj (V : Opens Y) :
    pullbackOver φ V ⊣
      (((Opens.map f).obj V).sheafOfModulesEquivOver R).functor ⋙
        (pushforward.{u} (Opens.sheafHomResLE φ V ((Opens.map f).obj V) le_rfl) :
          SheafOfModules.{u}
              ((((Opens.map f).obj V).isOpenEmbedding.sheafPullback RingCat.{u}).obj R) ⥤
            SheafOfModules.{u} ((V.isOpenEmbedding.sheafPullback RingCat.{u}).obj S)) ⋙
        (V.sheafOfModulesEquivOver S).inverse :=
  (V.sheafOfModulesEquivOver S).toAdjunction.comp
    ((pullbackPushforwardAdjunction.{u}
      (Opens.sheafHomResLE φ V ((Opens.map f).obj V) le_rfl)).comp
      (((Opens.map f).obj V).sheafOfModulesEquivOver R).symm.toAdjunction)

/-- Slice-site pullback `pullbackOver φ V` is a left adjoint. -/
instance isLeftAdjoint_pullbackOver (V : Opens Y) : (pullbackOver φ V).IsLeftAdjoint :=
  (pullbackOverAdj φ V).isLeftAdjoint

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

/-- Forward morphism formula for `pullbackOverUnitIso φ V`. -/
theorem pullbackOverUnitIso_hom (V : Opens Y) :
    (pullbackOverUnitIso φ V).hom =
      ((((Opens.map f).obj V).sheafOfModulesEquivOver R).unitIso.hom.app
          (unit (R.over ((Opens.map f).obj V)))) ≫
        (((Opens.map f).obj V).sheafOfModulesEquivOver R).inverse.map
          ((((Opens.map f).obj V).sheafOfModulesEquivOverUnit R).hom ≫
            (pullbackObjUnitIso (Opens.sheafHomResLE φ V ((Opens.map f).obj V) le_rfl)).inv ≫
            (pullback.{u} (Opens.sheafHomResLE φ V ((Opens.map f).obj V) le_rfl)).map
              (V.sheafOfModulesEquivOverUnit S).inv) ≫
        eqToHom (pullbackOver_obj φ V (unit (S.over V))).symm := by
  unfold pullbackOverUnitIso pullbackOver Opens.sheafOfModulesEquivOverInverseUnit
  dsimp [Opens.sheafRestrict, Topology.IsOpenEmbedding.sheafPullback]
  simp only [Category.assoc]
  rfl

/-- Restricting to the slice over `V` and then applying `pullbackOver φ V` is naturally isomorphic
to global pullback along `(f, φ)` followed by restriction to the slice over `f⁻¹(V)`
(`(Opens.map f).obj V`). -/
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

/-- Component formula for `(overFunctorCompPullbackOverIso φ V).hom.app M`. -/
theorem overFunctorCompPullbackOverIso_hom_app [(pushforward.{u} φ).IsRightAdjoint]
    (V : Opens Y) (M : SheafOfModules.{u} S) :
    (overFunctorCompPullbackOverIso φ V).hom.app M =
      eqToHom (pullbackOver_obj φ V ((overFunctor.{u} S V).obj M)) ≫
        (((Opens.map f).obj V).sheafOfModulesEquivOver R).inverse.map
          ((pullback.{u} (Opens.sheafHomResLE φ V ((Opens.map f).obj V) le_rfl)).map
              ((V.overFunctorCompSheafOfModulesEquivOver S).hom.app M) ≫
            (restrictPullbackIso φ V ((Opens.map f).obj V) le_rfl).inv.app M ≫
            (((Opens.map f).obj V).overFunctorCompSheafOfModulesEquivOver R).inv.app
              ((pullback.{u} φ).obj M)) ≫
        (((Opens.map f).obj V).sheafOfModulesEquivOver R).unitIso.inv.app
          ((overFunctor.{u} R ((Opens.map f).obj V)).obj ((pullback.{u} φ).obj M)) := by
  unfold overFunctorCompPullbackOverIso pullbackOver
  dsimp [Opens.sheafRestrict, Topology.IsOpenEmbedding.sheafPullback]
  simp only [Category.comp_id]
  rfl

/-- Compatibility of `(restrictPullbackIso φ V U e).hom.app (unit S)` with
`sheafOfModulesRestrictUnitIso` and `pullbackObjUnitToUnit`. -/
@[reassoc]
theorem restrictPullbackIso_hom_app_pullbackObjUnitToUnit
    [(pushforward.{u} φ).IsRightAdjoint] (V : Opens Y) (U : Opens X)
    (e : U ≤ (Opens.map f).obj V) :
    (restrictPullbackIso φ V U e).hom.app (unit S) ≫
        (pullback.{u} (Opens.sheafHomResLE φ V U e)).map
          (V.sheafOfModulesRestrictUnitIso S).hom ≫
        pullbackObjUnitToUnit (Opens.sheafHomResLE φ V U e) =
      (U.sheafOfModulesRestrict.{u} R).map (pullbackObjUnitToUnit φ) ≫
        (U.sheafOfModulesRestrictUnitIso R).hom := by
  have hcongr := (Iso.inv_comp_eq
    ((pullbackCongr₂.{u} _ (Opens.mapCompResLEIso f V U e)
      (Opens.sheafInclusionHom_comp_map_sheafHomResLE φ V U e)).app (unit S))).mpr
    (pullbackCongr₂_hom_app_pullbackObjUnitToUnit _ (Opens.mapCompResLEIso f V U e)
      (Opens.sheafInclusionHom_comp_map_sheafHomResLE φ V U e)).symm
  rw [Iso.app_inv] at hcongr
  rw [restrictPullbackIso_hom_app, Opens.sheafOfModulesRestrictUnitIso_hom,
    Opens.sheafOfModulesRestrictUnitIso_hom]
  simp only [Category.assoc, CategoryTheory.Functor.map_comp]
  rw [← CategoryTheory.Functor.map_comp_assoc, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp,
    pullbackObjUnitToUnit_comp, hcongr, ← pullbackObjUnitToUnit_comp,
    Iso.hom_inv_id_app_assoc, ← (U.sheafOfModulesRestrictIsoPullback.{u} R).hom.naturality_assoc]

end RingedSpacePullback

/-- Inverse unit compatibility for `(restrictPullbackIso φ V U e).inv.app (unit S)`, derived from
`restrictPullbackIso_hom_app_pullbackObjUnitToUnit` in the `IsOpenEmbedding.sheafPullback`
coefficient-sheaf presentation. -/
@[reassoc]
private lemma restrictPullbackIso_inv_app_pullbackObjUnitToUnit
    {X Y : TopCat.{u}} {f : X ⟶ Y}
    {S : Y.Sheaf RingCat.{u}} {R : X.Sheaf RingCat.{u}}
    (φ : S ⟶ ((Opens.map f).sheafPushforwardContinuous RingCat.{u}
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).obj R)
    [(pushforward.{u} φ).IsRightAdjoint] (V : Opens Y) (U : Opens X)
    (e : U ≤ (Opens.map f).obj V) :
    (pullback.{u} (Opens.sheafHomResLE φ V U e)).map
        (V.sheafOfModulesRestrictUnitIso S).inv ≫
      (restrictPullbackIso φ V U e).inv.app (unit S) ≫
      (U.sheafOfModulesRestrict.{u} R).map (pullbackObjUnitToUnit φ) =
    pullbackObjUnitToUnit (Opens.sheafHomResLE φ V U e) ≫
      (U.sheafOfModulesRestrictUnitIso R).inv := by
  refine (cancel_mono (U.sheafOfModulesRestrictUnitIso R).hom).mp ?_
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
    ← restrictPullbackIso_hom_app_pullbackObjUnitToUnit φ V U e,
    ← CategoryTheory.Functor.map_comp_assoc, Iso.inv_hom_id_app_assoc,
    Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]

/-- Boundary comparison translating the slice-equivalence unit composite on `W` (using
`W.sheafRestrict.obj M`) into `(W.sheafOfModulesRestrictUnitIso M).inv` (using
`(W.isOpenEmbedding.sheafPullback RingCat).obj M`). -/
private lemma sheafOfModulesEquivOverUnit_inv_comp_overFunctor_eq_restrictUnitIso_inv
    {Z : TopCat.{u}} (W : Opens Z) (M : Z.Sheaf RingCat.{u}) :
    (W.sheafOfModulesEquivOverUnit M).inv ≫
        (W.sheafOfModulesEquivOver M).functor.map (overFunctorUnitIso M W).hom ≫
        (W.overFunctorCompSheafOfModulesEquivOver M).hom.app (unit M) =
      (W.sheafOfModulesRestrictUnitIso M).inv := by
  -- `sheafOfModulesEquivOverUnit` targets `W.sheafRestrict.obj M`, whereas
  -- `sheafOfModulesRestrictUnitIso` uses `(W.isOpenEmbedding.sheafPullback RingCat).obj M`.
  refine (cancel_mono (W.sheafOfModulesRestrictUnitIso M).hom).mp ?_
  erw [Category.assoc, Category.assoc,
    Opens.sheafOfModulesEquivOverUnit_inv_comp_sheafOfModulesRestrictUnitIso_hom,
    Iso.inv_hom_id]
  rfl

/-- Boundary comparison cancelling `(W.sheafOfModulesRestrictUnitIso M).inv` against the
slice-equivalence and `overFunctor` unit comparisons on `W`. -/
private lemma sheafOfModulesEquivOverUnit_hom_comp_restrictUnitIso_inv_comp_overFunctor
    {Z : TopCat.{u}} (W : Opens Z) (M : Z.Sheaf RingCat.{u}) :
    (W.sheafOfModulesEquivOverUnit M).hom ≫
      (W.sheafOfModulesRestrictUnitIso M).inv ≫
      (W.overFunctorCompSheafOfModulesEquivOver M).inv.app (unit M) ≫
      (W.sheafOfModulesEquivOver M).functor.map (overFunctorUnitIso M W).inv = 𝟙 _ := by
  have h1 :
      (W.sheafOfModulesEquivOverUnit M).hom ≫
          (W.sheafOfModulesRestrictUnitIso M).inv =
        (W.sheafOfModulesEquivOver M).functor.map (overFunctorUnitIso M W).hom ≫
          (W.overFunctorCompSheafOfModulesEquivOver M).hom.app (unit M) := by
    erw [← sheafOfModulesEquivOverUnit_inv_comp_overFunctor_eq_restrictUnitIso_inv W M,
      Iso.hom_inv_id_assoc]
  erw [reassoc_of% h1, Category.assoc, Iso.hom_inv_id_app_assoc, ← CategoryTheory.Functor.map_comp,
    Iso.hom_inv_id, CategoryTheory.Functor.map_id]
  rfl

/-- Boundary comparison inside `(pullback (Opens.sheafHomResLE φ V U e)).map` cancelling
`V.sheafOfModulesEquivOverUnit` and `overFunctorUnitIso` into `V.sheafOfModulesRestrictUnitIso`. -/
@[reassoc]
private lemma pullbackOverUnitIso_V_boundary
    {X Y : TopCat.{u}} {f : X ⟶ Y}
    {S : Y.Sheaf RingCat.{u}} {R : X.Sheaf RingCat.{u}}
    (φ : S ⟶ ((Opens.map f).sheafPushforwardContinuous RingCat.{u}
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).obj R)
    (V : Opens Y) (U : Opens X)
    (e : U ≤ (Opens.map f).obj V) :
    (pullback.{u} (Opens.sheafHomResLE φ V U e)).map (V.sheafOfModulesEquivOverUnit S).inv ≫
      (pullback.{u} (Opens.sheafHomResLE φ V U e)).map
        ((V.sheafOfModulesEquivOver S).functor.map (overFunctorUnitIso S V).hom) ≫
      (pullback.{u} (Opens.sheafHomResLE φ V U e)).map
        ((V.overFunctorCompSheafOfModulesEquivOver S).hom.app (unit S)) =
    (pullback.{u} (Opens.sheafHomResLE φ V U e)).map
      (V.sheafOfModulesRestrictUnitIso S).inv := by
  erw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
    sheafOfModulesEquivOverUnit_inv_comp_overFunctor_eq_restrictUnitIso_inv V S]
  rfl

/-- Cancellation inside `eU.inverse.map` for the unit compatibility of `pullbackOver`, stated in
right-associated form using `sheafOfModulesRestrictUnitIso`. -/
private lemma pullbackOverUnitIso_inner
    {X Y : TopCat.{u}} {f : X ⟶ Y}
    {S : Y.Sheaf RingCat.{u}} {R : X.Sheaf RingCat.{u}}
    (φ : S ⟶ ((Opens.map f).sheafPushforwardContinuous RingCat.{u}
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).obj R)
    [(pushforward.{u} φ).IsRightAdjoint] (V : Opens Y) (U : Opens X)
    (e : U ≤ (Opens.map f).obj V) :
    (U.sheafOfModulesEquivOverUnit R).hom ≫
      (pullbackObjUnitIso (Opens.sheafHomResLE φ V U e)).inv ≫
      (pullback.{u} (Opens.sheafHomResLE φ V U e)).map (V.sheafOfModulesRestrictUnitIso S).inv ≫
      (restrictPullbackIso φ V U e).inv.app (unit S) ≫
      (U.overFunctorCompSheafOfModulesEquivOver R).inv.app ((pullback.{u} φ).obj (unit S)) ≫
      (U.sheafOfModulesEquivOver R).functor.map
        ((overFunctor.{u} R U).map (pullbackObjUnitToUnit φ)) ≫
      (U.sheafOfModulesEquivOver R).functor.map (overFunctorUnitIso R U).inv = 𝟙 _ := by
  have hnat := ((U.overFunctorCompSheafOfModulesEquivOver R).inv.naturality
    (pullbackObjUnitToUnit φ)).symm
  dsimp only [Functor.comp_map] at hnat
  have hinv_hom : (pullbackObjUnitIso (Opens.sheafHomResLE φ V U e)).inv ≫
      pullbackObjUnitToUnit (Opens.sheafHomResLE φ V U e) = 𝟙 _ := by
    rw [← pullbackObjUnitIso_hom, Iso.inv_hom_id]
  erw [reassoc_of% hnat, restrictPullbackIso_inv_app_pullbackObjUnitToUnit_assoc φ V U e,
    reassoc_of% hinv_hom]
  exact sheafOfModulesEquivOverUnit_hom_comp_restrictUnitIso_inv_comp_overFunctor U R

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
  let U := (Opens.map f).obj V
  refine (cancel_mono (overFunctorUnitIso R U).inv).mp ?_
  dsimp only [U]
  rw [pullbackOverUnitIso_hom, pullbackOver_map, overFunctorCompPullbackOverIso_hom_app,
    Iso.hom_inv_id]
  have hnat := ((((Opens.map f).obj V).sheafOfModulesEquivOver R).unitIso.inv.naturality
    ((overFunctor.{u} R ((Opens.map f).obj V)).map (pullbackObjUnitToUnit φ) ≫
      (overFunctorUnitIso R ((Opens.map f).obj V)).inv)).symm
  dsimp only [Functor.id_map, Functor.comp_map] at hnat
  have heq1 :
      eqToHom (pullbackOver_obj φ V (unit (S.over V))).symm ≫
        eqToHom (pullbackOver_obj φ V (unit (S.over V))) = 𝟙 _ := by simp
  have heq2 :
      eqToHom (pullbackOver_obj φ V ((overFunctor.{u} S V).obj (unit S))).symm ≫
        eqToHom (pullbackOver_obj φ V ((overFunctor.{u} S V).obj (unit S))) = 𝟙 _ := by simp
  have hmerge : ∀ {a b c d e : _} (f₁ : a ⟶ b) (f₂ : b ⟶ c) (f₃ : c ⟶ d) (f₄ : d ⟶ e),
      (((Opens.map f).obj V).sheafOfModulesEquivOver R).inverse.map f₁ ≫
        (((Opens.map f).obj V).sheafOfModulesEquivOver R).inverse.map f₂ ≫
        (((Opens.map f).obj V).sheafOfModulesEquivOver R).inverse.map f₃ ≫
        (((Opens.map f).obj V).sheafOfModulesEquivOver R).inverse.map f₄ =
      (((Opens.map f).obj V).sheafOfModulesEquivOver R).inverse.map
        (f₁ ≫ f₂ ≫ f₃ ≫ f₄) :=
    fun _ _ _ _ ↦ by simp only [CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]
  erw [reassoc_of% heq1, reassoc_of% heq2, hnat, reassoc_of% (hmerge _ _ _ _)]
  refine (congrArg (fun k ↦
      (((Opens.map f).obj V).sheafOfModulesEquivOver R).unitIso.hom.app _ ≫
      (((Opens.map f).obj V).sheafOfModulesEquivOver R).inverse.map k ≫
      (((Opens.map f).obj V).sheafOfModulesEquivOver R).unitIso.inv.app _)
    (?_ : _ = 𝟙 _)).trans ?_
  · erw [Category.assoc, Category.assoc, Category.assoc, Category.assoc,
      pullbackOverUnitIso_V_boundary_assoc φ V ((Opens.map f).obj V) le_rfl,
      CategoryTheory.Functor.map_comp]
    exact pullbackOverUnitIso_inner φ V ((Opens.map f).obj V) le_rfl
  · erw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id_app]
    rfl

end UnitCompatibility

end SheafOfModules

end
