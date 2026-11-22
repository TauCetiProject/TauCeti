/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Sheaves.Module
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Pullback.Basic
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Pushforward.Basic
public import TauCeti.Topology.Sheaves.Functors
public import TauCeti.Topology.Sheaves.Over

/-!
# Open-subspace restriction of sheaves of modules

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
restriction `SheafOfModules.overFunctor R U` and preserves free module sheaves.

## Main declarations

* `TopologicalSpace.Opens.sheafOfModulesRestrict`: restriction of module sheaves to an open
  subspace, with `[simp]` section, restriction-map, and morphism-application formulas
  `sheafOfModulesRestrict_obj_val_obj`, `sheafOfModulesRestrict_obj_val_map`,
  `sheafOfModulesRestrict_map_val_app`, `sheafOfModulesRestrict_obj_val_presheaf_obj`, and
  `sheafOfModulesRestrict_obj_val_presheaf_map`;
* `TopologicalSpace.Opens.sheafOfModulesRestrictAdj` and
  `TopologicalSpace.Opens.sheafOfModulesRestrictIsoPullback`: the adjunction of open-subspace
  restriction with direct image and its identification with pullback;
* `TopologicalSpace.Opens.overFunctorCompSheafOfModulesEquivOver`,
  `TopologicalSpace.Opens.sheafOfModulesRestrictUnitIso`,
  `TopologicalSpace.Opens.sheafOfModulesEquivOverFunctorObjFreeIso`, and
  `TopologicalSpace.Opens.sheafOfModulesRestrictFreeIso`: compatibility of open-subspace
  restriction with slice restriction, the unit module sheaf, and free module sheaves.

## References

* [The Stacks Project, Tag 008F](https://stacks.math.columbia.edu/tag/008F)
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

/-- Through `sheafOfModulesEquivOverFunctorObjFreeIso`, the image of a free generator `ιFree i`
is `ιFree i` on the open subspace `U` precomposed with the unit comparison. -/
@[reassoc (attr := simp)]
theorem sheafOfModulesEquivOver_functor_map_ιFree_comp_sheafOfModulesEquivOverFunctorObjFreeIso_hom
    (I : Type u) (i : I) :
    (U.sheafOfModulesEquivOver R).functor.map (SheafOfModules.ιFree i) ≫
        (U.sheafOfModulesEquivOverFunctorObjFreeIso R I).hom =
      (U.sheafOfModulesEquivOverUnit R).hom ≫ SheafOfModules.ιFree i :=
  SheafOfModules.map_ιFree_mapFreeIso_inv _ I _ i

/-- Open-subspace restriction sends the free module sheaf on `I` to the free module sheaf on `I`. -/
def sheafOfModulesRestrictFreeIso (I : Type u) :
    (U.sheafOfModulesRestrict.{u} R).obj (SheafOfModules.free I) ≅
      SheafOfModules.free I :=
  haveI : PreservesColimitsOfShape (Discrete I) (U.sheafOfModulesRestrict.{u} R) :=
    (U.sheafOfModulesRestrictAdj.{u} R).leftAdjoint_preservesColimits.preservesColimitsOfShape
  (SheafOfModules.mapFreeIso (U.sheafOfModulesRestrict.{u} R) I
    (U.sheafOfModulesRestrictUnitIso R).symm).symm

/-- Through `sheafOfModulesRestrictFreeIso`, restricting a free generator `ιFree i` gives
`ιFree i` on the open subspace `U` precomposed with `sheafOfModulesRestrictUnitIso`. -/
@[reassoc (attr := simp)]
theorem sheafOfModulesRestrict_map_ιFree_comp_sheafOfModulesRestrictFreeIso_hom
    (I : Type u) (i : I) :
    (U.sheafOfModulesRestrict.{u} R).map (SheafOfModules.ιFree i) ≫
        (U.sheafOfModulesRestrictFreeIso R I).hom =
      (U.sheafOfModulesRestrictUnitIso R).hom ≫ SheafOfModules.ιFree i :=
  SheafOfModules.map_ιFree_mapFreeIso_inv _ I _ i

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

end
