/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Limits
public import TauCeti.AlgebraicGeometry.Sites.Etale.Over
public import TauCeti.CategoryTheory.Sites.ConstantSheaf
public import TauCeti.CategoryTheory.Sites.Point.Comap
public import TauCeti.CategoryTheory.Sites.Pullback

/-!
# Direct and inverse image of sheaves on the small étale site

Let `f : X ⟶ Y` be a morphism of schemes. Base change `f.smallEtaleBaseChange : Y.Etale ⥤ X.Etale`
sending `V ⟶ Y` to `V ×_Y X ⟶ X` preserves finite limits (hence is representably flat and final)
and preserves étale covering sieves, so it is continuous for the small étale topologies and defines
a morphism of sites `(X.Etale, smallEtaleTopology X) → (Y.Etale, smallEtaleTopology Y)`.

For any coefficient category `A`, precomposition along `f.smallEtaleBaseChange` gives the direct
image functor `f.smallEtalePushforward A : Sheaf (smallEtaleTopology X) A ⥤ Sheaf
(smallEtaleTopology Y) A`. When `A` is a complete and cocomplete concrete category whose forgetful
functor preserves limits, reflects isomorphisms, and preserves filtered colimits (for instance
`Type u`, `AddCommGrpCat.{u}`, or `ModuleCat.{u} Λ`), restricting along the dense affine étale
subsite `AffineEtale.Spec Y` shows that `f.smallEtalePushforward A` admits a left adjoint
`f.smallEtalePullback A : Sheaf (smallEtaleTopology Y) A ⥤ Sheaf (smallEtaleTopology X) A`.

We establish the main properties of `f.smallEtalePullback A`:

* **Pseudofunctoriality**: natural isomorphisms `(𝟙 X)^* ≅ 𝟭` (`smallEtalePullbackId`) and
  `(f ≫ g)^* ≅ g^* ⋙ f^*` (`smallEtalePullbackComp`), plus invariance of constant sheaves
  `f^* (M_Y) ≅ M_X` (`smallEtalePullbackConstantSheafIso`).
* **Étale morphism case**: when `j : X ⟶ Y` is étale, `j.smallEtaleMap ⊣ j.smallEtaleBaseChange`
  exhibits `j.smallEtalePushforward A` as a right adjoint for *any* category `A` without
  sheafification (`isRightAdjoint_smallEtalePushforward_of_etale`), identifying `j^*` with
  `j.smallEtaleMap.sheafPushforwardContinuous` (`smallEtalePullbackIsoMapPushforward`) and, for
  `U : Y.Etale`, with restriction to `Over U` followed by `U.overSheafEquiv A`
  (`AlgebraicGeometry.Scheme.Etale.smallEtalePullbackIsoOver`).
* **Geometric stalks and exactness**: for a geometric point `s : Spec Ω ⟶ X`,
  `f^* ⋙ (pointSmallEtale s).sheafFiber ≅ (pointSmallEtale (s ≫ f)).sheafFiber`
  (`smallEtalePullbackCompSheafFiberIso`). Since geometric points form a conservative family on
  `X.Etale` and stalks preserve finite limits, `f.smallEtalePullback A` preserves finite limits
  (`preservesFiniteLimits_smallEtalePullback`).

## References

* M. Artin, A. Grothendieck, J.-L. Verdier, *SGA 4*, Exposé VII, §3–4, functoriality of the small
  étale topos, and Exposé VIII, §3, stalks of inverse images at geometric points.
* The Stacks Project, [Tag 03YU](https://stacks.math.columbia.edu/tag/03YU) and
  [Tag 0400](https://stacks.math.columbia.edu/tag/0400).
-/

public section

universe u u'

open CategoryTheory Limits MorphismProperty

namespace AlgebraicGeometry.Scheme

namespace Hom

section BaseChange

variable {X Y Z : Scheme.{u}}

@[simp]
lemma smallEtaleBaseChange_obj_left (f : X ⟶ Y) (V : Y.Etale) :
    (f.smallEtaleBaseChange.obj V).left = pullback V.hom f :=
  (rfl)

@[simp]
lemma smallEtaleBaseChange_obj_hom (f : X ⟶ Y) (V : Y.Etale) :
    (f.smallEtaleBaseChange.obj V).hom = pullback.snd V.hom f :=
  (rfl)

@[simp]
lemma smallEtaleBaseChange_map_left (f : X ⟶ Y) {V W : Y.Etale} (g : V ⟶ W) :
    (f.smallEtaleBaseChange.map g).left =
      pullback.lift (pullback.fst V.hom f ≫ g.left) (pullback.snd V.hom f)
        (by simp [pullback.condition]) :=
  (rfl)

/-- Base change along `𝟙 X` on small étale sites is naturally isomorphic to `𝟭 X.Etale`. -/
noncomputable def smallEtaleBaseChangeId (X : Scheme.{u}) :
    smallEtaleBaseChange (𝟙 X) ≅ 𝟭 X.Etale :=
  conjugateIsoEquiv (smallEtaleMapPullbackAdj (𝟙 X)) .id (smallEtaleMapId X).symm

/-- Base change along `f ≫ g` on small étale sites is naturally isomorphic to base change along `g`
followed by base change along `f`. -/
noncomputable def smallEtaleBaseChangeComp (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).smallEtaleBaseChange ≅ g.smallEtaleBaseChange ⋙ f.smallEtaleBaseChange :=
  MorphismProperty.Over.pullbackComp f g

/-- Equal scheme morphisms induce naturally isomorphic base change functors on small étale sites. -/
noncomputable def smallEtaleBaseChangeCongr {f f' : X ⟶ Y} (h : f = f') :
    f.smallEtaleBaseChange ≅ f'.smallEtaleBaseChange :=
  MorphismProperty.Over.pullbackCongr h

instance preservesFiniteLimits_smallEtaleBaseChange (f : X ⟶ Y) :
    PreservesFiniteLimits f.smallEtaleBaseChange := by
  have := reflectsFiniteLimits_of_reflectsIsomorphisms (Etale.forget X)
  have := comp_preservesFiniteLimits (Etale.forget Y) (CategoryTheory.Over.pullback f)
  have := preservesFiniteLimits_of_natIso f.smallEtaleBaseChangeCompForgetIso.symm
  exact preservesFiniteLimits_of_reflects_of_preserves f.smallEtaleBaseChange (Etale.forget X)

instance representablyFlat_smallEtaleBaseChange (f : X ⟶ Y) :
    RepresentablyFlat f.smallEtaleBaseChange :=
  flat_of_preservesFiniteLimits _

instance final_smallEtaleBaseChange (f : X ⟶ Y) :
    f.smallEtaleBaseChange.Final :=
  final_of_representablyFlat _

/-- Base change of étale schemes along `f : X ⟶ Y` preserves covering sieves of the small étale
topology. -/
lemma coverPreserving_smallEtaleBaseChange (f : X ⟶ Y) :
    CoverPreserving (smallEtaleTopology Y) (smallEtaleTopology X) f.smallEtaleBaseChange where
  cover_preserve {W R} hR := by
    obtain ⟨ι, V, g, rfl⟩ := R.exists_eq_ofArrows
    rw [Sieve.functorPushforward_ofArrows, ofArrows_mem_smallEtaleTopology_iff]
    have hmap (i : ι) : (f.smallEtaleBaseChange.map (g i)).left =
        pullback.map (V i).hom f W.hom f (g i).left (𝟙 X) (𝟙 Y)
          ((Category.comp_id _).trans (CategoryTheory.Over.w ((Etale.forget Y).map (g i))).symm)
          ((Category.comp_id _).trans (Category.id_comp _).symm) :=
      pullback.hom_ext
        ((pullback.lift_fst _ _ _).trans (pullback.lift_fst _ _ _).symm)
        ((pullback.lift_snd _ _ _).trans
          ((Category.comp_id _).symm.trans (pullback.lift_snd _ _ _).symm))
    refine Set.eq_univ_of_forall fun z ↦ ?_
    have hz : pullback.fst W.hom f z ∈ ⋃ i, Set.range (g i).left := by
      rw [(ofArrows_mem_smallEtaleTopology_iff g).mp hR]
      trivial
    obtain ⟨_, ⟨i, rfl⟩, y, hy⟩ := hz
    refine Set.mem_iUnion.mpr ⟨i, ?_⟩
    have hmem : z ∈ Set.range (pullback.map (V i).hom f W.hom f (g i).left (𝟙 X) (𝟙 Y)
        ((Category.comp_id _).trans (CategoryTheory.Over.w ((Etale.forget Y).map (g i))).symm)
        ((Category.comp_id _).trans (Category.id_comp _).symm)) :=
      (Scheme.Pullback.range_map _ _ _ _ _ _ (𝟙 Y) _ _).symm ▸
        ⟨⟨y, hy⟩, pullback.snd W.hom f z, rfl⟩
    exact hmap i ▸ hmem

/-- Base change of étale schemes along `f : X ⟶ Y` is continuous for the small étale topologies. -/
instance isContinuous_smallEtaleBaseChange (f : X ⟶ Y) :
    f.smallEtaleBaseChange.IsContinuous (smallEtaleTopology Y) (smallEtaleTopology X) :=
  Functor.isContinuous_of_coverPreserving
    (compatiblePreservingOfFlat _ _) f.coverPreserving_smallEtaleBaseChange

end BaseChange

end Hom

namespace Etale

variable {S : Scheme.{u}} (U : S.Etale)

instance isContinuous_hom_smallEtaleBaseChange :
    U.hom.smallEtaleBaseChange.IsContinuous (smallEtaleTopology S) (smallEtaleTopology U.left) :=
  Hom.isContinuous_smallEtaleBaseChange (U.hom : U.left ⟶ S)

instance final_hom_smallEtaleBaseChange :
    U.hom.smallEtaleBaseChange.Final :=
  Hom.final_smallEtaleBaseChange (U.hom : U.left ⟶ S)

end Etale

namespace Hom

section PushforwardPullback

variable {X Y Z : Scheme.{u}}

/-- Direct image `f_*` of sheaves on the small étale site along a morphism of schemes `f : X ⟶ Y`,
defined by precomposing along `f.smallEtaleBaseChange`. -/
noncomputable abbrev smallEtalePushforward (f : X ⟶ Y) (A : Type*) [Category* A] :
    Sheaf (smallEtaleTopology X) A ⥤ Sheaf (smallEtaleTopology Y) A :=
  f.smallEtaleBaseChange.sheafPushforwardContinuous A (smallEtaleTopology Y) (smallEtaleTopology X)

/-- Direct image of small étale sheaves along `𝟙 X` identifies with the identity functor. -/
noncomputable def smallEtalePushforwardId (X : Scheme.{u}) (A : Type*) [Category* A] :
    smallEtalePushforward (𝟙 X) A ≅ 𝟭 (Sheaf (smallEtaleTopology X) A) :=
  Functor.sheafPushforwardContinuousId' (smallEtaleBaseChangeId X) A (smallEtaleTopology X)

/-- Direct image of small étale sheaves along `f ≫ g` identifies with `f_*` followed by `g_*`. -/
noncomputable def smallEtalePushforwardComp (f : X ⟶ Y) (g : Y ⟶ Z) (A : Type*) [Category* A] :
    (f ≫ g).smallEtalePushforward A ≅
      f.smallEtalePushforward A ⋙ g.smallEtalePushforward A :=
  (Functor.sheafPushforwardContinuousComp' (smallEtaleBaseChangeComp f g).symm A
    (smallEtaleTopology Z) (smallEtaleTopology Y) (smallEtaleTopology X)).symm

/-- Equal scheme morphisms induce naturally isomorphic direct image functors on small étale
sheaves. -/
noncomputable def smallEtalePushforwardCongr {f f' : X ⟶ Y} (h : f = f')
    (A : Type*) [Category* A] :
    f.smallEtalePushforward A ≅ f'.smallEtalePushforward A :=
  Functor.sheafPushforwardContinuousIso (smallEtaleBaseChangeCongr h) A
    (smallEtaleTopology Y) (smallEtaleTopology X)

/-- For a complete and cocomplete concrete category `A` whose forgetful functor preserves limits,
reflects isomorphisms, and preserves filtered colimits, `f.smallEtalePushforward A` has a left
adjoint. -/
instance isRightAdjoint_smallEtalePushforward (f : X ⟶ Y)
    {A : Type u'} [Category.{u} A]
    {FA : A → A → Type*} {CD : A → Type u}
    [∀ M N, FunLike (FA M N) (CD M) (CD N)] [ConcreteCategory.{u} A FA]
    [PreservesLimits (CategoryTheory.forget A)] [HasColimits A] [HasLimits A]
    [(CategoryTheory.forget A).ReflectsIsomorphisms]
    [PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget A)] :
    (f.smallEtalePushforward A).IsRightAdjoint := by
  have := Functor.isContinuous_comp
    (AffineEtale.Spec Y) f.smallEtaleBaseChange
    (AffineEtale.topology Y) (smallEtaleTopology Y) (smallEtaleTopology X)
  have := Functor.isRightAdjoint_sheafPushforwardContinuous_of_essentiallySmall.{u}
    (AffineEtale.Spec Y ⋙ f.smallEtaleBaseChange) A
    (AffineEtale.topology Y) (smallEtaleTopology X)
  exact Functor.isRightAdjoint_sheafPushforwardContinuous_of_isEquivalence
    f.smallEtaleBaseChange A (smallEtaleTopology Y) (smallEtaleTopology X)
    (AffineEtale.topology Y) (AffineEtale.Spec Y)

/-- When `j : X ⟶ Y` is étale, `j.smallEtalePushforward A` has a left adjoint for any category
`A`. -/
instance isRightAdjoint_smallEtalePushforward_of_etale (j : X ⟶ Y) [Etale j]
    (A : Type*) [Category* A] :
    (j.smallEtalePushforward A).IsRightAdjoint :=
  j.smallEtaleMapPullbackAdj.isRightAdjoint_sheafPushforwardContinuous A
    (smallEtaleTopology X) (smallEtaleTopology Y)

/-- Inverse image `f^*` of sheaves on the small étale site along `f : X ⟶ Y`, left adjoint to
`f.smallEtalePushforward A`. -/
noncomputable abbrev smallEtalePullback (f : X ⟶ Y) (A : Type*) [Category* A]
    [(f.smallEtalePushforward A).IsRightAdjoint] :
    Sheaf (smallEtaleTopology Y) A ⥤ Sheaf (smallEtaleTopology X) A :=
  f.smallEtaleBaseChange.sheafPullback A (smallEtaleTopology Y) (smallEtaleTopology X)

/-- The adjunction `f.smallEtalePullback A ⊣ f.smallEtalePushforward A` on small étale sheaves. -/
noncomputable abbrev smallEtaleAdjunction (f : X ⟶ Y) (A : Type*) [Category* A]
    [(f.smallEtalePushforward A).IsRightAdjoint] :
    f.smallEtalePullback A ⊣ f.smallEtalePushforward A :=
  f.smallEtaleBaseChange.sheafAdjunctionContinuous A (smallEtaleTopology Y) (smallEtaleTopology X)

/-- Inverse image of small étale sheaves along `𝟙 X` is naturally isomorphic to the identity
functor. -/
noncomputable def smallEtalePullbackId (X : Scheme.{u}) (A : Type*) [Category* A] :
    smallEtalePullback (𝟙 X) A ≅ 𝟭 (Sheaf (smallEtaleTopology X) A) :=
  Functor.sheafPullbackId' (smallEtaleBaseChangeId X) A (smallEtaleTopology X)

/-- Inverse image of small étale sheaves along `f ≫ g` is naturally isomorphic to `g^*` followed by
`f^*`. -/
noncomputable def smallEtalePullbackComp (f : X ⟶ Y) (g : Y ⟶ Z) (A : Type*) [Category* A]
    [(f.smallEtalePushforward A).IsRightAdjoint]
    [(g.smallEtalePushforward A).IsRightAdjoint]
    [((f ≫ g).smallEtalePushforward A).IsRightAdjoint] :
    (f ≫ g).smallEtalePullback A ≅ g.smallEtalePullback A ⋙ f.smallEtalePullback A :=
  (Functor.sheafPullbackComp' (smallEtaleBaseChangeComp f g).symm A
    (smallEtaleTopology Z) (smallEtaleTopology Y) (smallEtaleTopology X)).symm

/-- Equal scheme morphisms induce naturally isomorphic inverse image functors on small étale
sheaves. -/
noncomputable def smallEtalePullbackCongr {f f' : X ⟶ Y} (h : f = f')
    (A : Type*) [Category* A] [(f.smallEtalePushforward A).IsRightAdjoint]
    [(f'.smallEtalePushforward A).IsRightAdjoint] :
    f.smallEtalePullback A ≅ f'.smallEtalePullback A :=
  Functor.sheafPullbackIso (smallEtaleBaseChangeCongr h) A
    (smallEtaleTopology Y) (smallEtaleTopology X)

/-- Pulling back a constant sheaf along any morphism of schemes `f : X ⟶ Y` recovers the constant
sheaf on `X` with the same value. -/
noncomputable def smallEtalePullbackConstantSheafIso (f : X ⟶ Y) (A : Type*) [Category* A]
    [HasWeakSheafify (smallEtaleTopology Y) A] [HasWeakSheafify (smallEtaleTopology X) A]
    [(f.smallEtalePushforward A).IsRightAdjoint] (M : A) :
    (f.smallEtalePullback A).obj ((constantSheaf (smallEtaleTopology Y) A).obj M) ≅
      (constantSheaf (smallEtaleTopology X) A).obj M :=
  f.smallEtaleBaseChange.sheafPullbackConstantSheafIso A
    (smallEtaleTopology Y) (smallEtaleTopology X) M

/-- When `j : X ⟶ Y` is étale, `j.smallEtalePullback A` identifies naturally with sheaf
precomposition along `j.smallEtaleMap : X.Etale ⥤ Y.Etale`, i.e. restriction of étale sheaves on `Y`
to `X`-schemes viewed as `Y`-schemes via `j`. -/
noncomputable def smallEtalePullbackIsoMapPushforward (j : X ⟶ Y) [Etale j]
    (A : Type*) [Category* A] :
    j.smallEtalePullback A ≅
      j.smallEtaleMap.sheafPushforwardContinuous A (smallEtaleTopology X) (smallEtaleTopology Y) :=
  j.smallEtaleMapPullbackAdj.sheafPullbackIso A (smallEtaleTopology X) (smallEtaleTopology Y)

end PushforwardPullback

end Hom

namespace Etale

variable {S : Scheme.{u}} (U : S.Etale) (A : Type*) [Category* A]

instance isRightAdjoint_hom_smallEtalePushforward :
    (U.hom.smallEtalePushforward A).IsRightAdjoint :=
  Hom.isRightAdjoint_smallEtalePushforward_of_etale (U.hom : U.left ⟶ S) A

/-- For an étale `S`-scheme `U : S.Etale`, inverse image `U.hom.smallEtalePullback A` agrees
naturally with restricting sheaves on `S.Etale` to `CategoryTheory.Over U` and transporting across
`U.overSheafEquiv A`. -/
noncomputable def smallEtalePullbackIsoOver :
    (U.hom : U.left ⟶ S).smallEtalePullback A ≅
      (smallEtaleTopology S).overPullback A U ⋙ (U.overSheafEquiv A).functor :=
  (U.hom : U.left ⟶ S).smallEtalePullbackIsoMapPushforward A ≪≫
    (U.overPullbackCompOverSheafEquivIso A).symm

/-- On an étale sheaf `F` on `S`, `((U.hom : U.left ⟶ S).smallEtalePullback A).obj F` identifies
with `F.over U` transported across `U.overSheafEquiv A`. -/
noncomputable def smallEtalePullbackObjIsoOver (F : Sheaf (smallEtaleTopology S) A) :
    ((U.hom : U.left ⟶ S).smallEtalePullback A).obj F ≅
      (U.overSheafEquiv A).functor.obj (F.over U) :=
  (U.smallEtalePullbackIsoOver A).app F

end Etale

namespace Hom

section StalksAndExactness

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- For a geometric point `s : Spec Ω ⟶ X`, lifts of `s` to the base change `V ×_Y X` of `V :
Y.Etale` correspond bijectively to lifts of `s ≫ f` to `V`, giving a natural isomorphism of point
fibre functors. -/
noncomputable def pointSmallEtaleFiberCompIso {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s : Spec (.of Ω) ⟶ X) :
    f.smallEtaleBaseChange ⋙ (pointSmallEtale s).fiber ≅ (pointSmallEtale (s ≫ f)).fiber :=
  NatIso.ofComponents
    (fun V ↦ Equiv.toIso
      { toFun (φ : CategoryTheory.Over.mk s ⟶
            (Etale.forget X).obj (f.smallEtaleBaseChange.obj V)) :=
          CategoryTheory.Over.homMk (φ.left ≫ pullback.fst V.hom f)
            ((Category.assoc φ.left (pullback.fst V.hom f) V.hom).trans
              ((congrArg (φ.left ≫ ·) pullback.condition).trans
                ((Category.assoc φ.left (pullback.snd V.hom f) f).symm.trans
                  (congrArg (· ≫ f) (CategoryTheory.Over.w φ)))))
        invFun (ψ : CategoryTheory.Over.mk (s ≫ f) ⟶ (Etale.forget Y).obj V) :=
          CategoryTheory.Over.homMk
            (pullback.lift ψ.left s (CategoryTheory.Over.w ψ)) (pullback.lift_snd _ _ _)
        left_inv φ := CategoryTheory.Over.OverMorphism.ext
          (pullback.hom_ext (pullback.lift_fst _ _ _)
            ((pullback.lift_snd _ _ _).trans (CategoryTheory.Over.w φ).symm))
        right_inv _ := CategoryTheory.Over.OverMorphism.ext (pullback.lift_fst _ _ _) })
    (fun {V W} g ↦ ConcreteCategory.hom_ext _ _ fun φ ↦ CategoryTheory.Over.OverMorphism.ext
      ((Category.assoc (CategoryTheory.Over.Hom.left φ) _ (pullback.fst W.hom f)).trans
        ((congrArg (CategoryTheory.Over.Hom.left φ ≫ ·) (pullback.lift_fst _ _ _)).trans
          (Category.assoc (CategoryTheory.Over.Hom.left φ) (pullback.fst V.hom f) g.left).symm)))

/-- The inverse image of the point `pointSmallEtale s` of `X.Etale` along `f.smallEtaleBaseChange`
is isomorphic to `pointSmallEtale (s ≫ f)`. -/
noncomputable def pointSmallEtaleComapIso {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s : Spec (.of Ω) ⟶ X) :
    letI := GrothendieckTopology.Point.initiallySmall_elements_of_fiberIso
      (pointSmallEtale s) f.smallEtaleBaseChange (f.pointSmallEtaleFiberCompIso s)
    (pointSmallEtale s).comap f.smallEtaleBaseChange f.coverPreserving_smallEtaleBaseChange ≅
      pointSmallEtale (s ≫ f) :=
  (pointSmallEtale s).comapIsoOfFiberIso
    f.smallEtaleBaseChange f.coverPreserving_smallEtaleBaseChange (f.pointSmallEtaleFiberCompIso s)

/-- **Stalk of an inverse image sheaf.** At a geometric point `s : Spec Ω ⟶ X`, the stalk of
`(f.smallEtalePullback A).obj F` identifies naturally with the stalk of `F` at `s ≫ f`. -/
noncomputable def smallEtalePullbackCompSheafFiberIso
    (A : Type*) [Category* A] [HasProducts.{u} A] [HasColimitsOfSize.{u, u} A]
    [(f.smallEtalePushforward A).IsRightAdjoint]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X) :
    f.smallEtalePullback A ⋙ (pointSmallEtale s).sheafFiber ≅
      (pointSmallEtale (s ≫ f)).sheafFiber :=
  (pointSmallEtale s).sheafPullbackCompSheafFiberIso
    f.smallEtaleBaseChange f.coverPreserving_smallEtaleBaseChange
    (f.pointSmallEtaleFiberCompIso s) A

/-- Inverse image of small étale sheaves preserves finite limits for concrete categories `A` with
finite limits, `u`-products, and `u`-small colimits whose forgetful functor preserves finite limits,
reflects isomorphisms, and preserves `u`-small filtered colimits. -/
instance preservesFiniteLimits_smallEtalePullback
    {A : Type u'} [Category.{u} A]
    [(f.smallEtalePushforward A).IsRightAdjoint]
    [HasFiniteLimits A] [HasProducts.{u} A] [HasColimitsOfSize.{u, u} A]
    {FA : A → A → Type*} {CD : A → Type u}
    [∀ M N, FunLike (FA M N) (CD M) (CD N)] [ConcreteCategory.{u} A FA]
    [PreservesFiniteLimits (CategoryTheory.forget A)]
    [(CategoryTheory.forget A).ReflectsIsomorphisms]
    [PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget A)]
    [(smallEtaleTopology X).HasSheafCompose (CategoryTheory.forget A)] :
    PreservesFiniteLimits (f.smallEtalePullback A) where
  preservesFiniteLimits J _ _ := ⟨fun {K} ↦
    { preserves {c} hc := by
        have : ReflectsFiniteLimits (CategoryTheory.forget A) :=
          reflectsFiniteLimits_of_reflectsIsomorphisms (CategoryTheory.forget A)
        have : AB5OfSize.{u, u} A :=
          ⟨fun I _ _ ↦ HasExactColimitsOfShape.domain_of_functor I (CategoryTheory.forget A)⟩
        exact ⟨((isConservativeFamilyOfPoints_pointSmallEtale' X).jointlyReflectIsomorphisms A)
          |>.jointlyReflectsLimit fun Φ ↦ Classical.choice (by
            obtain ⟨Φ, ⟨x⟩⟩ := Φ
            exact ⟨IsLimit.mapConeEquiv (f.smallEtalePullbackCompSheafFiberIso A _).symm
              (isLimitOfPreserves _ hc)⟩)⟩ }⟩

end StalksAndExactness

end Hom

end AlgebraicGeometry.Scheme
