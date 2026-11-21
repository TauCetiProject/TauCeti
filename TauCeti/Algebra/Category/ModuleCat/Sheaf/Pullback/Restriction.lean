/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Jointly
public import Mathlib.Topology.Sheaves.Module
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Pullback.Basic
public import TauCeti.Topology.Sheaves.Functors
public import TauCeti.Topology.Sheaves.Over
import TauCeti.Algebra.Category.ModuleCat.Sheaf.LocalIsomorphism

/-!
# Open-subspace restriction and slice-site pullback of sheaves of modules

For a topological space `X`, a sheaf of rings `R` on `X`, and an open subset `U : Opens X`,
restriction of sheaves of `R`-modules to the open subspace `(Opens.toTopCat X).obj U` is defined
as pushforward along the open-image functor `U.isOpenEmbedding.functor`
(`TopologicalSpace.Opens.sheafOfModulesRestrict`), with restricted coefficient sheaf
`(U.isOpenEmbedding.sheafPullback RingCat).obj R`. Via the site adjunction
`U.isOpenEmbedding.isOpenMap.adjunction`, restriction is left adjoint to direct image along
`U.inclusion' : (Opens.toTopCat X).obj U ⟶ X`, hence naturally isomorphic to pullback along the
canonical ring map `U.sheafInclusionHom RingCat R`. At the same time, restriction at universe `u`
has its own left adjoint (extension by zero), so both `U.sheafOfModulesRestrict R` and pullback
along `U.sheafInclusionHom RingCat R` preserve all limits as well as all colimits. Under Mathlib's
slice equivalence `U.sheafOfModulesEquivOver R`, open-subspace restriction agrees with slice
restriction `SheafOfModules.overFunctor R U` and preserves free module sheaves. Consequently,
isomorphisms, monomorphisms, epimorphisms, and vanishing of module sheaves on `X` can be tested
after restriction or pullback to the members of an open cover.

For a continuous map `f : X ⟶ Y` and a morphism of sheaves of rings `φ : S ⟶ f_* R`, restricting a
sheaf of rings to opens `V ⊆ Y` and `U ⊆ f⁻¹(V)` produces the restricted ring-sheaf morphism
`TopologicalSpace.Opens.sheafHomResLE φ V U e` along
`TopologicalSpace.Opens.resLE f V U e : (Opens.toTopCat X).obj U ⟶ (Opens.toTopCat Y).obj V`
(from `TauCeti.Topology.Sheaves.Functors`). Module pullback commutes with open-subspace
restriction (`SheafOfModules.restrictPullbackIso`), yielding the slice-site pullback functor
`SheafOfModules.pullbackOver φ V` together with its unit and object comparisons
`SheafOfModules.pullbackOverUnitIso` and `SheafOfModules.pullbackOverObjIso`.

## Main declarations

* `TopologicalSpace.Opens.sheafOfModulesRestrict`: restriction of module sheaves to an open
  subspace, with `[simp]` section, restriction-map, and morphism-application formulas
  `sheafOfModulesRestrict_obj_val_obj`, `sheafOfModulesRestrict_obj_val_map`,
  `sheafOfModulesRestrict_map_val_app`, `sheafOfModulesRestrict_obj_val_presheaf_obj`, and
  `sheafOfModulesRestrict_obj_val_presheaf_map`;
* `TopologicalSpace.Opens.sheafOfModulesRestrictAdj` and
  `TopologicalSpace.Opens.sheafOfModulesRestrictIsoPullback`: the adjunction of open-subspace
  restriction with direct image and its identification with pullback;
* `SheafOfModules.restrictPullbackIso` and `SheafOfModules.pullbackOver`: compatibility of module
  pullback with open-subspace restriction, and the induced pullback between slice sites;
* `SheafOfModules.isIso_iff_pullback_of_isOpenCover`,
  `SheafOfModules.mono_iff_pullback_of_isOpenCover`,
  `SheafOfModules.epi_iff_pullback_of_isOpenCover`, and
  `SheafOfModules.isZero_iff_pullback_of_isOpenCover`: open-cover locality of isomorphisms,
  monomorphisms, epimorphisms, and zero objects for module sheaves on ringed spaces.

## References

* [The Stacks Project, Tag 008F](https://stacks.math.columbia.edu/tag/008F)
* [The Stacks Project, Tag 0097](https://stacks.math.columbia.edu/tag/0097)
-/

public section

open CategoryTheory Limits Opposite TopologicalSpace Topology

universe v u

noncomputable section

namespace TopologicalSpace.Opens

section ModuleRestriction

variable {X : TopCat.{u}} (U : Opens X) (R : X.Sheaf RingCat.{u})

/-- Restriction of sheaves of `R`-modules to an open subspace `U : Opens X`, defined as pushforward
along the open-image functor `U.isOpenEmbedding.functor`. -/
def sheafOfModulesRestrict :
    SheafOfModules.{v} R ⥤
      SheafOfModules.{v} ((U.isOpenEmbedding.sheafPullback RingCat.{u}).obj R) :=
  SheafOfModules.pushforward.{v} (F := U.isOpenEmbedding.functor)
    (𝟙 ((U.isOpenEmbedding.sheafPullback RingCat.{u}).obj R))

/-- Sections of `(U.sheafOfModulesRestrict R).obj M` over an open `W` of `U` are the sections of
`M` over the image open `U.isOpenEmbedding.functor.obj W.unop`. -/
@[simp]
theorem sheafOfModulesRestrict_obj_val_obj (M : SheafOfModules.{v} R)
    (W : (Opens ((Opens.toTopCat X).obj U))ᵒᵖ) :
    ((U.sheafOfModulesRestrict.{v} R).obj M).val.obj W =
      M.val.obj (op (U.isOpenEmbedding.functor.obj W.unop)) := by
  unfold sheafOfModulesRestrict
  rfl

/-- Restriction maps of `(U.sheafOfModulesRestrict R).obj M` are those of `M` along the image of
the inclusion in `X`. -/
@[simp]
theorem sheafOfModulesRestrict_obj_val_map (M : SheafOfModules.{v} R)
    {W W' : (Opens ((Opens.toTopCat X).obj U))ᵒᵖ} (g : W ⟶ W') :
    ((U.sheafOfModulesRestrict.{v} R).obj M).val.map g =
      eqToHom (sheafOfModulesRestrict_obj_val_obj U R M W) ≫
        M.val.map (U.isOpenEmbedding.functor.map g.unop).op ≫
        eqToHom (congrArg
          (ModuleCat.restrictScalars (R.obj.map (U.isOpenEmbedding.functor.map g.unop).op).hom).obj
          (sheafOfModulesRestrict_obj_val_obj U R M W').symm) := by
  unfold sheafOfModulesRestrict
  exact (Category.id_comp _).symm.trans (Category.comp_id _).symm

/-- Action of `U.sheafOfModulesRestrict R` on a morphism of module sheaves evaluates at the image
open `U.isOpenEmbedding.functor.obj W.unop`. -/
@[simp]
theorem sheafOfModulesRestrict_map_val_app {M N : SheafOfModules.{v} R} (φ : M ⟶ N)
    (W : (Opens ((Opens.toTopCat X).obj U))ᵒᵖ) :
    ((U.sheafOfModulesRestrict.{v} R).map φ).val.app W =
      eqToHom (sheafOfModulesRestrict_obj_val_obj U R M W) ≫
        φ.val.app (op (U.isOpenEmbedding.functor.obj W.unop)) ≫
        eqToHom (sheafOfModulesRestrict_obj_val_obj U R N W).symm := by
  unfold sheafOfModulesRestrict
  exact (Category.id_comp _).symm.trans (Category.comp_id _).symm

/-- Underlying presheaf sections of `(U.sheafOfModulesRestrict R).obj M` over `W` are those of `M`
over the image open `U.isOpenEmbedding.functor.obj W.unop`. -/
@[simp]
theorem sheafOfModulesRestrict_obj_val_presheaf_obj (M : SheafOfModules.{v} R)
    (W : (Opens ((Opens.toTopCat X).obj U))ᵒᵖ) :
    ((U.sheafOfModulesRestrict.{v} R).obj M).val.presheaf.obj W =
      M.val.presheaf.obj (op (U.isOpenEmbedding.functor.obj W.unop)) := by
  unfold sheafOfModulesRestrict
  rfl

/-- Underlying presheaf restriction maps of `(U.sheafOfModulesRestrict R).obj M` are those of `M`
along the image of the inclusion in `X`. -/
@[simp]
theorem sheafOfModulesRestrict_obj_val_presheaf_map (M : SheafOfModules.{v} R)
    {W W' : (Opens ((Opens.toTopCat X).obj U))ᵒᵖ} (g : W ⟶ W') :
    ((U.sheafOfModulesRestrict.{v} R).obj M).val.presheaf.map g =
      eqToHom (sheafOfModulesRestrict_obj_val_presheaf_obj U R M W) ≫
        M.val.presheaf.map (U.isOpenEmbedding.functor.map g.unop).op ≫
        eqToHom (sheafOfModulesRestrict_obj_val_presheaf_obj U R M W').symm := by
  unfold sheafOfModulesRestrict
  exact (Category.id_comp _).symm.trans (Category.comp_id _).symm

/-- Restriction of module sheaves to an open subspace `U` is left adjoint to pushforward along
`U.inclusion'`. -/
def sheafOfModulesRestrictAdj :
    U.sheafOfModulesRestrict.{v} R ⊣
      SheafOfModules.pushforward.{v} (U.sheafInclusionHom RingCat.{u} R) := by
  refine
    SheafOfModules.pushforwardPushforwardAdj (F := U.isOpenEmbedding.functor)
      U.isOpenEmbedding.isOpenMap.adjunction
      (𝟙 ((U.isOpenEmbedding.sheafPullback RingCat.{u}).obj R))
      (U.sheafInclusionHom RingCat.{u} R) ?_ ?_
  · refine NatTrans.ext (funext fun W ↦ ?_)
    exact (U.sheafInclusionHom_hom_app RingCat.{u} R W).symm.trans (Category.comp_id _).symm
  · refine NatTrans.ext (funext fun W ↦ ?_)
    let adj := U.isOpenEmbedding.isOpenMap.adjunction
    have h₁ : R.obj.map (adj.counit.app (U.isOpenEmbedding.functor.obj W.unop)).op ≫
        R.obj.map (U.isOpenEmbedding.functor.map (adj.unit.app W.unop)).op =
        𝟙 (R.obj.obj (op (U.isOpenEmbedding.functor.obj W.unop))) := by
      rw [← R.obj.map_comp, ← op_comp, adj.left_triangle_components W.unop]
      exact R.obj.map_id _
    have h : (U.sheafInclusionHom RingCat.{u} R).hom.app
          (op (U.isOpenEmbedding.functor.obj W.unop)) ≫
        R.obj.map (U.isOpenEmbedding.functor.map (adj.unit.app W.unop)).op =
        𝟙 (R.obj.obj (op (U.isOpenEmbedding.functor.obj W.unop))) :=
      (congrArg (· ≫ R.obj.map (U.isOpenEmbedding.functor.map (adj.unit.app W.unop)).op)
        (U.sheafInclusionHom_hom_app RingCat.{u} R
          (op (U.isOpenEmbedding.functor.obj W.unop)))).trans h₁
    exact (Category.id_comp _).trans h

/-- Open-subspace restriction of module sheaves is a left adjoint (right adjoint: direct image). -/
instance isLeftAdjoint_sheafOfModulesRestrict :
    (U.sheafOfModulesRestrict.{v} R).IsLeftAdjoint :=
  (U.sheafOfModulesRestrictAdj.{v} R).isLeftAdjoint

/-- Direct image of module sheaves along `U.inclusion'` is a right adjoint at every module universe
`v` (left adjoint: `U.sheafOfModulesRestrict`). -/
instance isRightAdjoint_pushforward_sheafInclusionHom :
    (SheafOfModules.pushforward.{v} (U.sheafInclusionHom RingCat.{u} R)).IsRightAdjoint :=
  (U.sheafOfModulesRestrictAdj.{v} R).isRightAdjoint

/-- The counit of `sheafOfModulesRestrictAdj` is an isomorphism. -/
instance isIso_sheafOfModulesRestrictAdj_counit :
    IsIso (U.sheafOfModulesRestrictAdj.{v} R).counit := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  have happ : ∀ W : (Opens ((Opens.toTopCat X).obj U))ᵒᵖ,
      IsIso (((U.sheafOfModulesRestrictAdj.{v} R).counit.app M).val.app W) := fun W ↦ by
    let W' : Opens ((Opens.toTopCat X).obj U) :=
      (Opens.map U.inclusion').obj (U.isOpenEmbedding.functor.obj W.unop)
    have heq : W' = W.unop :=
      Opens.map_functor_eq' U.inclusion' U.isOpenEmbedding W.unop
    have hhom : U.isOpenEmbedding.isOpenMap.adjunction.unit.app W.unop =
        eqToHom heq.symm :=
      Subsingleton.elim _ _
    have hmap : ⇑(((U.sheafOfModulesRestrictAdj.{v} R).counit.app M).val.app W) =
        ⇑(M.val.presheaf.map (eqToHom heq.symm).op) :=
      funext fun x ↦
        let x' : M.val.obj (op W') := x
        congrArg (fun k : W.unop ⟶ W' ↦ M.val.presheaf.map k.op x') hhom
    rw [ConcreteCategory.isIso_iff_bijective, hmap]
    exact (ConcreteCategory.isIso_iff_bijective _).mp
      (Functor.map_isIso M.val.presheaf (eqToHom heq.symm).op)
  have : IsIso ((SheafOfModules.forget _).map
      ((U.sheafOfModulesRestrictAdj.{v} R).counit.app M)) :=
    (PresheafOfModules.isoMk (fun W ↦ @asIso _ _ _ _ _ (happ W))
      (fun _ _ g ↦ ((U.sheafOfModulesRestrictAdj.{v} R).counit.app M).val.naturality g)).isIso_hom
  exact isIso_of_reflects_iso _ (SheafOfModules.forget _)

/-- Direct image of module sheaves along an open inclusion is full. -/
instance full_pushforward_sheafInclusionHom :
    (SheafOfModules.pushforward.{v} (U.sheafInclusionHom RingCat.{u} R)).Full :=
  (U.sheafOfModulesRestrictAdj.{v} R).fullyFaithfulROfIsIsoCounit.full

/-- Direct image of module sheaves along an open inclusion is faithful. -/
instance faithful_pushforward_sheafInclusionHom :
    (SheafOfModules.pushforward.{v} (U.sheafInclusionHom RingCat.{u} R)).Faithful :=
  (U.sheafOfModulesRestrictAdj.{v} R).fullyFaithfulROfIsIsoCounit.faithful

/-- At universe `u`, open-subspace restriction of module sheaves is also a right adjoint (left
adjoint: extension by zero). -/
instance isRightAdjoint_sheafOfModulesRestrict :
    (U.sheafOfModulesRestrict.{u} R).IsRightAdjoint :=
  SheafOfModules.isRightAdjoint_pushforward (F := U.isOpenEmbedding.functor)
    (𝟙 ((U.isOpenEmbedding.sheafPullback RingCat.{u}).obj R))

/-- Open-subspace restriction of module sheaves is an additive functor. -/
instance additive_sheafOfModulesRestrict :
    (U.sheafOfModulesRestrict.{v} R).Additive where
  map_add := rfl

/-- Open-subspace restriction of module sheaves is naturally isomorphic to pullback along
`U.sheafInclusionHom RingCat R`. -/
def sheafOfModulesRestrictIsoPullback :
    U.sheafOfModulesRestrict.{v} R ≅
      SheafOfModules.pullback.{v} (U.sheafInclusionHom RingCat.{u} R) :=
  (U.sheafOfModulesRestrictAdj.{v} R).leftAdjointUniq
    (SheafOfModules.pullbackPushforwardAdjunction.{v} (U.sheafInclusionHom RingCat.{u} R))

/-- Pullback of module sheaves along an open inclusion preserves all limits. -/
instance preservesLimits_pullback_sheafInclusionHom :
    PreservesLimits (SheafOfModules.pullback.{u} (U.sheafInclusionHom RingCat.{u} R)) :=
  preservesLimits_of_natIso (U.sheafOfModulesRestrictIsoPullback.{u} R)

/-- Restricting to the slice site over `U` and applying `U.sheafOfModulesEquivOver R` is naturally
isomorphic to open-subspace restriction `U.sheafOfModulesRestrict R`. -/
def overFunctorCompSheafOfModulesEquivOver :
    SheafOfModules.overFunctor.{v} R U ⋙ (U.sheafOfModulesEquivOver R).functor ≅
      U.sheafOfModulesRestrict.{v} R := by
  haveI : (U.overEquivalence.inverse ⋙ Over.forget U).IsContinuous
      (Opens.grothendieckTopology U) (Opens.grothendieckTopology X) :=
    Functor.isContinuous_comp _ _ _ ((Opens.grothendieckTopology X).over U) _
  refine SheafOfModules.pushforwardComp.{v} (U.overPullbackSheafEquivOver.app R).inv (𝟙 (R.over U))
    ≪≫ SheafOfModules.pushforwardCongr.{v} ?_
  ext : 2
  rfl

/-- Open-subspace restriction preserves the unit sheaf of modules. -/
def sheafOfModulesRestrictUnitIso :
    (U.sheafOfModulesRestrict.{u} R).obj (SheafOfModules.unit R) ≅
      SheafOfModules.unit ((U.isOpenEmbedding.sheafPullback RingCat.{u}).obj R) :=
  (U.sheafOfModulesRestrictIsoPullback.{u} R).app (SheafOfModules.unit R) ≪≫
    SheafOfModules.pullbackObjUnitIso (U.sheafInclusionHom RingCat.{u} R)

/-- Under `U.sheafOfModulesEquivOver R`, free module sheaves on the slice site over `U` correspond
to free module sheaves on the open subspace `U`. -/
def sheafOfModulesEquivOverFunctorObjFreeIso (I : Type u) :
    (U.sheafOfModulesEquivOver R).functor.obj (SheafOfModules.free I) ≅
      SheafOfModules.free I :=
  let F : SheafOfModules.{u} (R.over U) ⥤ SheafOfModules.{u} (U.sheafRestrict.obj R) :=
    (U.sheafOfModulesEquivOver R).functor
  haveI : PreservesColimitsOfShape (Discrete I) F :=
    (U.sheafOfModulesEquivOver R).toAdjunction.leftAdjoint_preservesColimits
      |>.preservesColimitsOfShape
  (SheafOfModules.mapFreeIso F I (U.sheafOfModulesEquivOverUnit R).symm).symm

/-- Open-subspace restriction sends the free module sheaf on `I` to the free module sheaf on `I`. -/
def sheafOfModulesRestrictFreeIso (I : Type u) :
    (U.sheafOfModulesRestrict.{u} R).obj (SheafOfModules.free I) ≅
      SheafOfModules.free I :=
  haveI : PreservesColimitsOfShape (Discrete I) (U.sheafOfModulesRestrict.{u} R) :=
    (U.sheafOfModulesRestrictAdj.{u} R).leftAdjoint_preservesColimits.preservesColimitsOfShape
  (SheafOfModules.mapFreeIso (U.sheafOfModulesRestrict.{u} R) I
    (U.sheafOfModulesRestrictUnitIso R).symm).symm

/-- A trivialization of `M.over U` by a free module sheaf induces a trivialization of the
open-subspace restriction `(U.sheafOfModulesRestrict R).obj M`. -/
def sheafOfModulesRestrictIsoFreeOfOverIsoFree (M : SheafOfModules.{u} R) {I : Type u}
    (e : M.over U ≅ SheafOfModules.free I) :
    (U.sheafOfModulesRestrict.{u} R).obj M ≅ SheafOfModules.free I :=
  ((U.overFunctorCompSheafOfModulesEquivOver R).app M).symm ≪≫
    (U.sheafOfModulesEquivOver R).functor.mapIso e ≪≫
    U.sheafOfModulesEquivOverFunctorObjFreeIso R I

/-- A trivialization of the open-subspace restriction `(U.sheafOfModulesRestrict R).obj M` by a free
module sheaf induces a trivialization of `M.over U`. -/
def overIsoFreeOfSheafOfModulesRestrictIsoFree (M : SheafOfModules.{u} R) {I : Type u}
    (e : (U.sheafOfModulesRestrict.{u} R).obj M ≅ SheafOfModules.free I) :
    M.over U ≅ SheafOfModules.free I :=
  (U.sheafOfModulesEquivOver R).fullyFaithfulFunctor.preimageIso
    ((U.overFunctorCompSheafOfModulesEquivOver R).app M ≪≫ e ≪≫
      (U.sheafOfModulesEquivOverFunctorObjFreeIso R I).symm)

end ModuleRestriction

end TopologicalSpace.Opens

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

/-- Slice-site pullback `pullbackOver φ V` computes the slice restriction of `(pullback φ).obj M`
to `(Opens.map f).obj V`. -/
def pullbackOverObjIso [(pushforward.{u} φ).IsRightAdjoint] (V : Opens Y)
    (M : SheafOfModules.{u} S) :
    (pullbackOver φ V).obj (M.over V) ≅ ((pullback.{u} φ).obj M).over ((Opens.map f).obj V) :=
  let eU : SheafOfModules.{u} (R.over ((Opens.map f).obj V)) ≌
      SheafOfModules.{u}
        ((((Opens.map f).obj V).isOpenEmbedding.sheafPullback RingCat.{u}).obj R) :=
    ((Opens.map f).obj V).sheafOfModulesEquivOver R
  eU.inverse.mapIso
      ((pullback.{u} (Opens.sheafHomResLE φ V ((Opens.map f).obj V) le_rfl)).mapIso
          ((V.overFunctorCompSheafOfModulesEquivOver S).app M) ≪≫
        ((restrictPullbackIso φ V ((Opens.map f).obj V) le_rfl).app M).symm ≪≫
        ((((Opens.map f).obj V).overFunctorCompSheafOfModulesEquivOver R).app
          ((pullback.{u} φ).obj M)).symm) ≪≫
    eU.unitIso.symm.app (((pullback.{u} φ).obj M).over ((Opens.map f).obj V))

end RingedSpacePullback

section OpenCoverLocality

variable {X : TopCat.{u}} {R : X.Sheaf RingCat.{u}}
  {ι : Type*} {U : ι → Opens X}

/-- Open-subspace restrictions to the members of an open cover jointly reflect isomorphisms of
module sheaves. -/
theorem jointlyReflectIsomorphisms_sheafOfModulesRestrict (hU : IsOpenCover U) :
    JointlyReflectIsomorphisms (fun i ↦ (U i).sheafOfModulesRestrict.{v} R) where
  isIso φ h := by
    refine isIso_of_coversTop ((Opens.coversTop_iff X U).mpr hU) fun i ↦ ?_
    have hmap : IsIso (((U i).sheafOfModulesEquivOver R).functor.map (φ.over (U i))) :=
      (NatIso.isIso_map_iff ((U i).overFunctorCompSheafOfModulesEquivOver R) φ).mpr (h i)
    exact isIso_of_reflects_iso (φ.over (U i)) ((U i).sheafOfModulesEquivOver R).functor

/-- Pullbacks along the open inclusions of an open cover jointly reflect isomorphisms of module
sheaves. -/
theorem jointlyReflectIsomorphisms_pullback_sheafInclusionHom (hU : IsOpenCover U) :
    JointlyReflectIsomorphisms
      (fun i ↦ pullback.{v} ((U i).sheafInclusionHom RingCat.{u} R)) where
  isIso φ h := by
    have : ∀ i, IsIso (((U i).sheafOfModulesRestrict.{v} R).map φ) := fun i ↦
      (NatIso.isIso_map_iff ((U i).sheafOfModulesRestrictIsoPullback.{v} R) φ).mpr (h i)
    exact (jointlyReflectIsomorphisms_sheafOfModulesRestrict hU).isIso φ

/-- A morphism of module sheaves on `X` is an isomorphism if and only if its restrictions to the
members of an open cover are isomorphisms. -/
theorem isIso_iff_sheafOfModulesRestrict_of_isOpenCover (hU : IsOpenCover U)
    {M N : SheafOfModules.{v} R} (φ : M ⟶ N) :
    IsIso φ ↔ ∀ i, IsIso (((U i).sheafOfModulesRestrict.{v} R).map φ) :=
  ⟨fun _ _ ↦ inferInstance, fun _ ↦
    (jointlyReflectIsomorphisms_sheafOfModulesRestrict hU).isIso φ⟩

/-- A morphism of module sheaves on `X` is an isomorphism if and only if its pullbacks to the
members of an open cover are isomorphisms. -/
theorem isIso_iff_pullback_of_isOpenCover (hU : IsOpenCover U)
    {M N : SheafOfModules.{v} R} (φ : M ⟶ N) :
    IsIso φ ↔ ∀ i, IsIso ((pullback.{v} ((U i).sheafInclusionHom RingCat.{u} R)).map φ) :=
  ⟨fun _ _ ↦ inferInstance, fun _ ↦
    (jointlyReflectIsomorphisms_pullback_sheafInclusionHom hU).isIso φ⟩

/-- Monomorphisms of module sheaves on `X` can be checked after open-subspace restriction to an open
cover. -/
theorem mono_iff_sheafOfModulesRestrict_of_isOpenCover (hU : IsOpenCover U)
    {M N : SheafOfModules.{u} R} (φ : M ⟶ N) :
    Mono φ ↔ ∀ i, Mono (((U i).sheafOfModulesRestrict.{u} R).map φ) :=
  (jointlyReflectIsomorphisms_sheafOfModulesRestrict hU).jointlyReflectMonomorphisms.mono_iff φ

/-- Monomorphisms of module sheaves on `X` can be checked after pullback to an open cover. -/
theorem mono_iff_pullback_of_isOpenCover (hU : IsOpenCover U)
    {M N : SheafOfModules.{u} R} (φ : M ⟶ N) :
    Mono φ ↔ ∀ i, Mono ((pullback.{u} ((U i).sheafInclusionHom RingCat.{u} R)).map φ) :=
  (jointlyReflectIsomorphisms_pullback_sheafInclusionHom hU).jointlyReflectMonomorphisms.mono_iff φ

/-- Epimorphisms of module sheaves on `X` can be checked after open-subspace restriction to an open
cover. -/
theorem epi_iff_sheafOfModulesRestrict_of_isOpenCover (hU : IsOpenCover U)
    {M N : SheafOfModules.{u} R} (φ : M ⟶ N) :
    Epi φ ↔ ∀ i, Epi (((U i).sheafOfModulesRestrict.{u} R).map φ) :=
  haveI : ∀ i, ((U i).sheafOfModulesRestrict.{u} R).PreservesEpimorphisms :=
    fun _ ↦ Functor.preservesEpimorphisms_of_isLeftAdjoint _
  (jointlyReflectIsomorphisms_sheafOfModulesRestrict hU).jointlyReflectEpimorphisms.epi_iff φ

/-- Epimorphisms of module sheaves on `X` can be checked after pullback to an open cover. -/
theorem epi_iff_pullback_of_isOpenCover (hU : IsOpenCover U)
    {M N : SheafOfModules.{u} R} (φ : M ⟶ N) :
    Epi φ ↔ ∀ i, Epi ((pullback.{u} ((U i).sheafInclusionHom RingCat.{u} R)).map φ) :=
  haveI : ∀ i, (pullback.{u} ((U i).sheafInclusionHom RingCat.{u} R)).PreservesEpimorphisms :=
    fun _ ↦ Functor.preservesEpimorphisms_of_isLeftAdjoint _
  (jointlyReflectIsomorphisms_pullback_sheafInclusionHom hU).jointlyReflectEpimorphisms.epi_iff φ

/-- A module sheaf on `X` is zero if and only if its restrictions to the members of an open cover
are zero. -/
theorem isZero_iff_sheafOfModulesRestrict_of_isOpenCover (hU : IsOpenCover U)
    (M : SheafOfModules.{v} R) :
    IsZero M ↔ ∀ i, IsZero (((U i).sheafOfModulesRestrict.{v} R).obj M) := by
  refine ⟨fun hM i ↦ ((U i).sheafOfModulesRestrict.{v} R).map_isZero hM, fun h ↦ ?_⟩
  rw [IsZero.iff_id_eq_zero]
  have : IsIso (0 : M ⟶ M) := by
    rw [isIso_iff_sheafOfModulesRestrict_of_isOpenCover hU]
    intro i
    rw [Functor.map_zero, ← (h i).eq_of_src (𝟙 _) 0]
    infer_instance
  rw [← cancel_epi (0 : M ⟶ M), comp_zero, zero_comp]

/-- A module sheaf on `X` is zero if and only if its pullbacks to the members of an open cover are
zero. -/
theorem isZero_iff_pullback_of_isOpenCover (hU : IsOpenCover U)
    (M : SheafOfModules.{v} R) :
    IsZero M ↔ ∀ i, IsZero ((pullback.{v} ((U i).sheafInclusionHom RingCat.{u} R)).obj M) := by
  rw [isZero_iff_sheafOfModulesRestrict_of_isOpenCover hU]
  exact forall_congr' fun i ↦ (((U i).sheafOfModulesRestrictIsoPullback.{v} R).app M).isZero_iff

end OpenCoverLocality

end SheafOfModules

end
