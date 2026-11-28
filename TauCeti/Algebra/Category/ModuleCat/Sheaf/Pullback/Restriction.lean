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
* `SheafOfModules.pullbackOver` (with `pullbackOver_map`): the induced pullback functor between
  slice sites;
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
subspaces `V ⊆ Y` and `U ⊆ f⁻¹(V)`. -/
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
@[expose]
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

/-- Action of `pullbackOver φ V` on a morphism of module sheaves over `V`. -/
theorem pullbackOver_map (V : Opens Y) {M N : SheafOfModules.{u} (S.over V)} (g : M ⟶ N) :
    (pullbackOver φ V).map g =
      (((Opens.map f).obj V).sheafOfModulesEquivOver R).inverse.map
        ((pullback.{u} (Opens.sheafHomResLE φ V ((Opens.map f).obj V) le_rfl)).map
          ((V.sheafOfModulesEquivOver S).functor.map g)) := by
  unfold pullbackOver
  rfl

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

/-- Forward morphism formula for `pullbackOverUnitIso φ V`. -/
theorem pullbackOverUnitIso_hom (V : Opens Y) :
    (pullbackOverUnitIso φ V).hom =
      ((((Opens.map f).obj V).sheafOfModulesEquivOver R).unitIso.hom.app
          (unit (R.over ((Opens.map f).obj V)))) ≫
        (((Opens.map f).obj V).sheafOfModulesEquivOver R).inverse.map
          ((((Opens.map f).obj V).sheafOfModulesEquivOverUnit R).hom ≫
            (pullbackObjUnitIso (Opens.sheafHomResLE φ V ((Opens.map f).obj V) le_rfl)).inv ≫
            (pullback.{u} (Opens.sheafHomResLE φ V ((Opens.map f).obj V) le_rfl)).map
              (V.sheafOfModulesEquivOverUnit S).inv) := by
  unfold pullbackOverUnitIso pullbackOver Opens.sheafOfModulesEquivOverInverseUnit
  dsimp [Opens.sheafRestrict, Topology.IsOpenEmbedding.sheafPullback]
  simp only [Category.assoc]
  rfl

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

/-- Component formula for `(overFunctorCompPullbackOverIso φ V).hom.app M`. -/
theorem overFunctorCompPullbackOverIso_hom_app [(pushforward.{u} φ).IsRightAdjoint]
    (V : Opens Y) (M : SheafOfModules.{u} S) :
    (overFunctorCompPullbackOverIso φ V).hom.app M =
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

end RingedSpacePullback

/-- Compatibility of `(restrictPullbackIso φ V U e).inv.app (unit S)` with `pullbackObjUnitToUnit`
and `sheafOfModulesRestrictIsoPullback`. -/
@[reassoc]
private lemma restrictPullbackIso_inv_app_pullbackObjUnitToUnit
    {X Y : TopCat.{u}} {f : X ⟶ Y}
    {S : Y.Sheaf RingCat.{u}} {R : X.Sheaf RingCat.{u}}
    (φ : S ⟶ ((Opens.map f).sheafPushforwardContinuous RingCat.{u}
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).obj R)
    [(pushforward.{u} φ).IsRightAdjoint] (V : Opens Y) (U : Opens X)
    (e : U ≤ (Opens.map f).obj V) :
    (restrictPullbackIso φ V U e).inv.app (unit S) ≫
        (U.sheafOfModulesRestrictIsoPullback.{u} R).hom.app ((pullback.{u} φ).obj (unit S)) ≫
        (pullback.{u} (U.sheafInclusionHom RingCat.{u} R)).map (pullbackObjUnitToUnit φ) ≫
        pullbackObjUnitToUnit (U.sheafInclusionHom RingCat.{u} R) =
      (pullback.{u} (Opens.sheafHomResLE φ V U e)).map
          ((V.sheafOfModulesRestrictIsoPullback.{u} S).hom.app (unit S) ≫
            pullbackObjUnitToUnit (V.sheafInclusionHom RingCat.{u} S)) ≫
        pullbackObjUnitToUnit (Opens.sheafHomResLE φ V U e) := by
  refine (Iso.inv_comp_eq ((restrictPullbackIso φ V U e).app (unit S))).mpr ?_
  symm
  -- Rewrite `((restrictPullbackIso _).app _).hom` to `.hom.app _` via `Iso.app_hom` so
  -- `restrictPullbackIso_hom_app` applies, then cancel the matching comparison pairs.
  rw [Iso.app_hom, restrictPullbackIso_hom_app]
  have hcongr := (Iso.inv_comp_eq
    ((pullbackCongr₂.{u} _ (Opens.mapCompResLEIso f V U e)
      (Opens.sheafInclusionHom_comp_map_sheafHomResLE φ V U e)).app (unit S))).mpr
    (pullbackCongr₂_hom_app_pullbackObjUnitToUnit _ (Opens.mapCompResLEIso f V U e)
      (Opens.sheafInclusionHom_comp_map_sheafHomResLE φ V U e)).symm
  rw [Iso.app_inv] at hcongr
  simp only [Category.assoc, CategoryTheory.Functor.map_comp]
  rw [← CategoryTheory.Functor.map_comp_assoc, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp,
    pullbackObjUnitToUnit_comp, hcongr,
    ← pullbackObjUnitToUnit_comp, Iso.hom_inv_id_app_assoc]

/-- Compatibility of `(restrictPullbackIso φ V U e).inv.app (unit S)` with the unit-sheaf
comparisons on `V` and `U`. -/
@[reassoc]
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
      (W.sheafOfModulesEquivOverUnit M).inv ≫
          (W.sheafOfModulesEquivOver M).functor.map (overFunctorUnitIso M W).hom ≫
          (W.overFunctorCompSheafOfModulesEquivOver M).hom.app (unit M) ≫
          (W.sheafOfModulesRestrictIsoPullback.{u} M).hom.app (unit M) ≫
          pullbackObjUnitToUnit (W.sheafInclusionHom RingCat.{u} M) = 𝟙 _ := by
    have h := Opens.sheafOfModulesEquivOverUnit_inv_comp_sheafOfModulesRestrictUnitIso_hom W M
    rw [Opens.sheafOfModulesRestrictUnitIso_hom] at h
    exact h
  -- Cancel the monic unit-comparison morphism on `U` on the right, commute it past
  -- `restrictPullbackIso.inv` via `restrictPullbackIso_inv_app_pullbackObjUnitToUnit`, and
  -- collapse both sides using `hunitComp`.
  have : Mono ((U.sheafOfModulesRestrictIsoPullback.{u} R).hom.app (unit R) ≫
      pullbackObjUnitToUnit (U.sheafInclusionHom RingCat.{u} R)) :=
    mono_comp _ _
  refine (cancel_mono ((U.sheafOfModulesRestrictIsoPullback.{u} R).hom.app (unit R) ≫
    pullbackObjUnitToUnit (U.sheafInclusionHom RingCat.{u} R))).mp ?_
  erw [Category.assoc, Category.assoc,
    (U.sheafOfModulesRestrictIsoPullback.{u} R).hom.naturality_assoc,
    restrictPullbackIso_inv_app_pullbackObjUnitToUnit,
    ← CategoryTheory.Functor.map_comp_assoc]
  have hV :
      ((V.sheafOfModulesEquivOverUnit S).inv ≫
          (V.sheafOfModulesEquivOver S).functor.map (overFunctorUnitIso S V).hom ≫
          (V.overFunctorCompSheafOfModulesEquivOver S).hom.app (unit S)) ≫
        (V.sheafOfModulesRestrictIsoPullback.{u} S).hom.app (unit S) ≫
        pullbackObjUnitToUnit (V.sheafInclusionHom RingCat.{u} S) = 𝟙 _ := by
    have h := hunitComp V S
    erw [← Category.assoc
        ((V.sheafOfModulesEquivOver S).functor.map (overFunctorUnitIso S V).hom),
      ← Category.assoc (V.sheafOfModulesEquivOverUnit S).inv] at h
    exact h
  erw [hV, CategoryTheory.Functor.map_id, Category.id_comp,
    Category.assoc (pullbackObjUnitToUnit _),
    Category.assoc (U.sheafOfModulesEquivOverUnit R).inv,
    Category.assoc ((U.sheafOfModulesEquivOver R).functor.map _),
    hunitComp U R, Category.comp_id]

/-- Cancellation inside `eU.inverse.map` for the unit compatibility of `pullbackOver`. -/
private lemma pullbackOverUnitIso_inner
    {X Y : TopCat.{u}} {f : X ⟶ Y}
    {S : Y.Sheaf RingCat.{u}} {R : X.Sheaf RingCat.{u}}
    (φ : S ⟶ ((Opens.map f).sheafPushforwardContinuous RingCat.{u}
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).obj R)
    [(pushforward.{u} φ).IsRightAdjoint] (V : Opens Y) (U : Opens X)
    (e : U ≤ (Opens.map f).obj V) :
    (U.sheafOfModulesEquivOverUnit R).hom ≫
      (pullbackObjUnitIso (Opens.sheafHomResLE φ V U e)).inv ≫
      (pullback.{u} (Opens.sheafHomResLE φ V U e)).map
        ((V.sheafOfModulesEquivOverUnit S).inv ≫
          (V.sheafOfModulesEquivOver S).functor.map (overFunctorUnitIso S V).hom ≫
          (V.overFunctorCompSheafOfModulesEquivOver S).hom.app (unit S)) ≫
      (restrictPullbackIso φ V U e).inv.app (unit S) ≫
      (U.overFunctorCompSheafOfModulesEquivOver R).inv.app ((pullback.{u} φ).obj (unit S)) ≫
      (U.sheafOfModulesEquivOver R).functor.map
        ((overFunctor.{u} R U).map (pullbackObjUnitToUnit φ)) ≫
      (U.sheafOfModulesEquivOver R).functor.map (overFunctorUnitIso R U).inv = 𝟙 _ := by
  -- Push `(U.overFunctorCompSheafOfModulesEquivOver R).inv` past `pullbackObjUnitToUnit φ` by
  -- naturality, apply `restrictPullbackIso_inv_app_unit_square`, and cancel adjacent inverse pairs.
  have hnat := ((U.overFunctorCompSheafOfModulesEquivOver R).inv.naturality
    (pullbackObjUnitToUnit φ)).symm
  dsimp only [Functor.comp_map] at hnat
  erw [reassoc_of% hnat, restrictPullbackIso_inv_app_unit_square_assoc]
  have hinv_hom : (pullbackObjUnitIso (Opens.sheafHomResLE φ V U e)).inv ≫
      pullbackObjUnitToUnit (Opens.sheafHomResLE φ V U e) = 𝟙 _ := by
    rw [← pullbackObjUnitIso_hom, Iso.inv_hom_id]
  erw [Category.assoc (pullbackObjUnitToUnit _), reassoc_of% hinv_hom,
    Category.assoc (U.sheafOfModulesEquivOverUnit R).inv, Iso.hom_inv_id_assoc,
    Category.assoc ((U.sheafOfModulesEquivOver R).functor.map _), Iso.hom_inv_id_app_assoc,
    ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id]

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
  -- Insert `(overFunctorUnitIso R _).inv ≫ (overFunctorUnitIso R _).hom`, expand the three
  -- slice-pullback morphisms via `pullbackOverUnitIso_hom`, `pullbackOver_map`, and
  -- `overFunctorCompPullbackOverIso_hom_app`, push `unitIso.inv` past the `overFunctor` maps by
  -- naturality, and collapse the interior via `pullbackOverUnitIso_inner`.
  let U := (Opens.map f).obj V
  let eU := U.sheafOfModulesEquivOver R
  have hcomp :
      (overFunctor.{u} R U).map (pullbackObjUnitToUnit φ) =
        ((overFunctor.{u} R U).map (pullbackObjUnitToUnit φ) ≫
          (overFunctorUnitIso R U).inv) ≫ (overFunctorUnitIso R U).hom := by
    simp
  have hnat := (eU.unitIso.inv.naturality
    ((overFunctor.{u} R U).map (pullbackObjUnitToUnit φ) ≫
      (overFunctorUnitIso R U).inv)).symm
  dsimp only [Functor.id_map] at hnat
  rw [pullbackOverUnitIso_hom, pullbackOver_map, overFunctorCompPullbackOverIso_hom_app, hcomp]
  dsimp only [eU, U] at hnat ⊢
  have htail0 :
      (eU.inverse.map
          ((pullback.{u} (Opens.sheafHomResLE φ V U le_rfl)).map
              ((V.overFunctorCompSheafOfModulesEquivOver S).hom.app (unit S)) ≫
            (restrictPullbackIso φ V U le_rfl).inv.app (unit S) ≫
            (U.overFunctorCompSheafOfModulesEquivOver R).inv.app
              ((pullback.{u} φ).obj (unit S))) ≫
          eU.unitIso.inv.app ((overFunctor.{u} R U).obj ((pullback.{u} φ).obj (unit S)))) ≫
        ((overFunctor.{u} R U).map (pullbackObjUnitToUnit φ) ≫ (overFunctorUnitIso R U).inv) =
      eU.inverse.map
          ((pullback.{u} (Opens.sheafHomResLE φ V U le_rfl)).map
              ((V.overFunctorCompSheafOfModulesEquivOver S).hom.app (unit S)) ≫
            (restrictPullbackIso φ V U le_rfl).inv.app (unit S) ≫
            (U.overFunctorCompSheafOfModulesEquivOver R).inv.app
              ((pullback.{u} φ).obj (unit S)) ≫
            eU.functor.map ((overFunctor.{u} R U).map (pullbackObjUnitToUnit φ)) ≫
            eU.functor.map (overFunctorUnitIso R U).inv) ≫
        eU.unitIso.inv.app (unit (R.over U)) := by
    erw [Category.assoc, hnat, ← Category.assoc, ← eU.inverse.map_comp, eU.functor.map_comp,
      Category.assoc, Category.assoc]
  have htail :
      (eU.inverse.map
          ((pullback.{u} (Opens.sheafHomResLE φ V U le_rfl)).map
              ((V.overFunctorCompSheafOfModulesEquivOver S).hom.app (unit S)) ≫
            (restrictPullbackIso φ V U le_rfl).inv.app (unit S) ≫
            (U.overFunctorCompSheafOfModulesEquivOver R).inv.app
              ((pullback.{u} φ).obj (unit S))) ≫
          eU.unitIso.inv.app ((overFunctor.{u} R U).obj ((pullback.{u} φ).obj (unit S)))) ≫
        ((overFunctor.{u} R U).map (pullbackObjUnitToUnit φ) ≫ (overFunctorUnitIso R U).inv) ≫
        (overFunctorUnitIso R U).hom =
      eU.inverse.map
          ((pullback.{u} (Opens.sheafHomResLE φ V U le_rfl)).map
              ((V.overFunctorCompSheafOfModulesEquivOver S).hom.app (unit S)) ≫
            (restrictPullbackIso φ V U le_rfl).inv.app (unit S) ≫
            (U.overFunctorCompSheafOfModulesEquivOver R).inv.app
              ((pullback.{u} φ).obj (unit S)) ≫
            eU.functor.map ((overFunctor.{u} R U).map (pullbackObjUnitToUnit φ)) ≫
            eU.functor.map (overFunctorUnitIso R U).inv) ≫
        eU.unitIso.inv.app (unit (R.over U)) ≫ (overFunctorUnitIso R U).hom := by
    erw [← Category.assoc]
    exact (reassoc_of% htail0) (overFunctorUnitIso R U).hom
  have hinner :
      ((U.sheafOfModulesEquivOverUnit R).hom ≫
          (pullbackObjUnitIso (Opens.sheafHomResLE φ V U le_rfl)).inv ≫
          (pullback.{u} (Opens.sheafHomResLE φ V U le_rfl)).map
            (V.sheafOfModulesEquivOverUnit S).inv) ≫
        (pullback.{u} (Opens.sheafHomResLE φ V U le_rfl)).map
          ((V.sheafOfModulesEquivOver S).functor.map (overFunctorUnitIso S V).hom) ≫
        (pullback.{u} (Opens.sheafHomResLE φ V U le_rfl)).map
          ((V.overFunctorCompSheafOfModulesEquivOver S).hom.app (unit S)) ≫
        (restrictPullbackIso φ V U le_rfl).inv.app (unit S) ≫
        (U.overFunctorCompSheafOfModulesEquivOver R).inv.app ((pullback.{u} φ).obj (unit S)) ≫
        eU.functor.map ((overFunctor.{u} R U).map (pullbackObjUnitToUnit φ)) ≫
        eU.functor.map (overFunctorUnitIso R U).inv = 𝟙 _ := by
    erw [Category.assoc, Category.assoc,
      ← CategoryTheory.Functor.map_comp_assoc, ← CategoryTheory.Functor.map_comp_assoc]
    exact pullbackOverUnitIso_inner φ V U le_rfl
  dsimp only [eU, U] at htail hinner
  erw [Category.assoc, htail,
    ← eU.inverse.map_comp_assoc, ← eU.inverse.map_comp_assoc,
    hinner, CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id_app_assoc]

end UnitCompatibility

end SheafOfModules

end
