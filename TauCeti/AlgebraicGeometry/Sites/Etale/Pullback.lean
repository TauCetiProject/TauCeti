/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.Limits.MorphismProperty
public import TauCeti.AlgebraicGeometry.Sites.Etale.Over.Basic
public import TauCeti.CategoryTheory.Sites.ConstantSheaf
public import TauCeti.CategoryTheory.Sites.Point.Comap
public import TauCeti.CategoryTheory.Sites.Pullback
public import TauCeti.CategoryTheory.Sites.Sheaf

/-!
# Direct and inverse image of sheaves on the small étale site

For a morphism of schemes `f : X ⟶ Y`, base change `f.smallEtaleBaseChange : Y.Etale ⥤ X.Etale`
preserves finite limits and covering sieves, giving direct image `f.smallEtalePushforward A` and
(via the dense affine étale subsite `AffineEtale.Spec Y` when `A` has `u`-small limits/colimits and
weak sheafification) inverse image `f.smallEtalePullback A`:

* **Pseudofunctoriality**: `smallEtalePullbackId`, `smallEtalePullbackComp`,
  `smallEtalePullbackCongr`, and `smallEtalePullbackConstantSheafIso`.
* **Étale morphism case**: for étale `j : X ⟶ Y`, `j.smallEtaleMap ⊣ j.smallEtaleBaseChange`
  yields `isRightAdjoint_smallEtalePushforward_of_etale`, `smallEtalePullbackIsoMapPushforward`,
  and `AlgebraicGeometry.Scheme.Etale.smallEtalePullbackIsoOver`.
* **Geometric stalks and exactness**: `smallEtalePullbackCompSheafFiberIso` identifies stalks at
  `s : Spec Ω ⟶ X` with stalks at `s ≫ f`, `preservesFiniteLimits_smallEtalePullback` deduces
  left exactness from the conservative family of geometric points, and
  `preservesFiniteColimits_smallEtalePullback` records right exactness from the adjunction.
* **Local evaluation on sections**: `evalUnitSelf` pulls a section of a sheaf over an étale
  `S`-scheme `u : U ⟶ S` back to the terminal object of `U.Etale`, and
  `exists_etaleCover_of_mem_smallEtaleTopology_terminal` extracts a jointly surjective étale
  cover from a covering sieve of `Etale.mk (𝟙 S)`.

## References

* M. Artin, A. Grothendieck, J.-L. Verdier, *SGA 4*, Exposé VII, §3–4 and Exposé VIII, §3.
* The Stacks Project, [Tag 0400](https://stacks.math.columbia.edu/tag/0400).
-/

public section

universe u

open CategoryTheory Limits MorphismProperty

namespace AlgebraicGeometry.Scheme

namespace Hom

section BaseChange

variable {X Y : Scheme.{u}}

instance preservesFiniteLimits_smallEtaleBaseChange (f : X ⟶ Y) :
    PreservesFiniteLimits f.smallEtaleBaseChange :=
  let P : MorphismProperty Scheme.{u} := @Etale
  have : P.IsStableUnderBaseChange :=
    inferInstanceAs (MorphismProperty.IsStableUnderBaseChange @Etale)
  have : P.HasOfPostcompProperty P :=
    inferInstanceAs (MorphismProperty.HasOfPostcompProperty @Etale @Etale)
  inferInstanceAs (PreservesFiniteLimits (MorphismProperty.Over.pullback P ⊤ f))

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
    refine Set.eq_univ_of_forall fun z ↦ ?_
    have hz : pullback.fst W.hom f z ∈ ⋃ i, Set.range (g i).left := by
      rw [(ofArrows_mem_smallEtaleTopology_iff g).mp hR]; trivial
    obtain ⟨_, ⟨i, rfl⟩, y, hy⟩ := hz
    refine Set.mem_iUnion.mpr ⟨i, ?_⟩
    rw [f.smallEtaleBaseChange_map_left_eq_pullback_map (g i)]
    exact (Scheme.Pullback.range_map _ _ _ _ _ _ (𝟙 Y) _ _).symm.subset
      ⟨⟨y, hy⟩, pullback.snd W.hom f z, rfl⟩

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
noncomputable abbrev smallEtalePushforwardId (X : Scheme.{u}) (A : Type*) [Category* A] :
    smallEtalePushforward (𝟙 X) A ≅ 𝟭 (Sheaf (smallEtaleTopology X) A) :=
  Functor.sheafPushforwardContinuousId' (smallEtaleBaseChangeId X) A (smallEtaleTopology X)

/-- Direct image of small étale sheaves along `f ≫ g` identifies with `f_*` followed by `g_*`. -/
noncomputable abbrev smallEtalePushforwardComp (f : X ⟶ Y) (g : Y ⟶ Z) (A : Type*) [Category* A] :
    (f ≫ g).smallEtalePushforward A ≅
      f.smallEtalePushforward A ⋙ g.smallEtalePushforward A :=
  (Functor.sheafPushforwardContinuousComp' (smallEtaleBaseChangeComp f g).symm A
    (smallEtaleTopology Z) (smallEtaleTopology Y) (smallEtaleTopology X)).symm

/-- Equal scheme morphisms induce naturally isomorphic direct image functors on small étale
sheaves. -/
noncomputable abbrev smallEtalePushforwardCongr {f f' : X ⟶ Y} (h : f = f')
    (A : Type*) [Category* A] :
    f.smallEtalePushforward A ≅ f'.smallEtalePushforward A :=
  Functor.sheafPushforwardContinuousIso (smallEtaleBaseChangeCongr h) A
    (smallEtaleTopology Y) (smallEtaleTopology X)

/-- For a category `A` with `u`-small limits and colimits such that `smallEtaleTopology X` admits
weak sheafification in `A`, `f.smallEtalePushforward A` has a left adjoint. -/
instance isRightAdjoint_smallEtalePushforward (f : X ⟶ Y) {A : Type*} [Category* A]
    [HasLimitsOfSize.{u, u} A] [HasColimitsOfSize.{u, u} A]
    [HasWeakSheafify (smallEtaleTopology X) A] :
    (f.smallEtalePushforward A).IsRightAdjoint :=
  have := Functor.isEquivalence_of_isOneHypercoverDense.{u}
    (AffineEtale.Spec Y) (AffineEtale.topology Y) (smallEtaleTopology Y) A
  have := Functor.isContinuous_comp (AffineEtale.Spec Y) f.smallEtaleBaseChange
    (AffineEtale.topology Y) (smallEtaleTopology Y) (smallEtaleTopology X)
  have := Functor.isRightAdjoint_sheafPushforwardContinuous_of_essentiallySmall.{u}
    (AffineEtale.Spec Y ⋙ f.smallEtaleBaseChange) A (AffineEtale.topology Y) (smallEtaleTopology X)
  Functor.isRightAdjoint_sheafPushforwardContinuous_of_isEquivalence f.smallEtaleBaseChange A
    (smallEtaleTopology Y) (smallEtaleTopology X) (AffineEtale.topology Y) (AffineEtale.Spec Y)

/-- When `j : X ⟶ Y` is étale, `j.smallEtalePushforward A` has a left adjoint for any category
`A`. -/
instance isRightAdjoint_smallEtalePushforward_of_etale (j : X ⟶ Y) [Etale j]
    (A : Type*) [Category* A] :
    (j.smallEtalePushforward A).IsRightAdjoint :=
  j.smallEtaleMapBaseChangeAdj.isRightAdjoint_sheafPushforwardContinuous A
    (smallEtaleTopology X) (smallEtaleTopology Y)

/-- If `f_*` and `g_*` both admit left adjoints on small étale sheaves, then so does
`(f ≫ g)_*`. -/
lemma isRightAdjoint_smallEtalePushforward_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    (A : Type*) [Category* A] [(f.smallEtalePushforward A).IsRightAdjoint]
    [(g.smallEtalePushforward A).IsRightAdjoint] :
    ((f ≫ g).smallEtalePushforward A).IsRightAdjoint :=
  Functor.isRightAdjoint_of_iso (smallEtalePushforwardComp f g A).symm

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
noncomputable abbrev smallEtalePullbackId (X : Scheme.{u}) (A : Type*) [Category* A] :
    smallEtalePullback (𝟙 X) A ≅ 𝟭 (Sheaf (smallEtaleTopology X) A) :=
  Functor.sheafPullbackId' (smallEtaleBaseChangeId X) A (smallEtaleTopology X)

/-- Inverse image of small étale sheaves along `f ≫ g` is naturally isomorphic to `g^*` followed by
`f^*`. -/
noncomputable abbrev smallEtalePullbackComp (f : X ⟶ Y) (g : Y ⟶ Z) (A : Type*) [Category* A]
    [(f.smallEtalePushforward A).IsRightAdjoint] [(g.smallEtalePushforward A).IsRightAdjoint]
    [((f ≫ g).smallEtalePushforward A).IsRightAdjoint] :
    (f ≫ g).smallEtalePullback A ≅ g.smallEtalePullback A ⋙ f.smallEtalePullback A :=
  (Functor.sheafPullbackComp' (smallEtaleBaseChangeComp f g).symm A
    (smallEtaleTopology Z) (smallEtaleTopology Y) (smallEtaleTopology X)).symm

/-- Equal scheme morphisms induce naturally isomorphic inverse image functors on small étale
sheaves. -/
noncomputable abbrev smallEtalePullbackCongr {f f' : X ⟶ Y} (h : f = f')
    (A : Type*) [Category* A] [(f.smallEtalePushforward A).IsRightAdjoint]
    [(f'.smallEtalePushforward A).IsRightAdjoint] :
    f.smallEtalePullback A ≅ f'.smallEtalePullback A :=
  Functor.sheafPullbackIso (smallEtaleBaseChangeCongr h) A
    (smallEtaleTopology Y) (smallEtaleTopology X)

@[simp]
lemma smallEtalePullbackCongr_refl (f : X ⟶ Y) (A : Type*) [Category* A]
    [(f.smallEtalePushforward A).IsRightAdjoint] :
    smallEtalePullbackCongr (rfl : f = f) A = Iso.refl _ := by
  have h : smallEtaleBaseChangeCongr (rfl : f = f) = Iso.refl _ := by
    apply Iso.ext; ext V : 2; apply MorphismProperty.Over.Hom.ext
    exact (smallEtaleBaseChangeCongr_hom_app_left rfl V).trans
      ((pullback.congrHom_hom rfl rfl).trans pullback.map_id)
  rw [smallEtalePullbackCongr, h, Functor.sheafPullbackIso_refl]

/-- Pulling back a constant sheaf along any morphism of schemes `f : X ⟶ Y` recovers the constant
sheaf on `X` with the same value. -/
noncomputable abbrev smallEtalePullbackConstantSheafIso (f : X ⟶ Y) (A : Type*) [Category* A]
    [HasWeakSheafify (smallEtaleTopology Y) A] [HasWeakSheafify (smallEtaleTopology X) A]
    [(f.smallEtalePushforward A).IsRightAdjoint] (M : A) :
    (f.smallEtalePullback A).obj ((constantSheaf (smallEtaleTopology Y) A).obj M) ≅
      (constantSheaf (smallEtaleTopology X) A).obj M :=
  f.smallEtaleBaseChange.sheafPullbackConstantSheafIso A
    (smallEtaleTopology Y) (smallEtaleTopology X) M

/-- When `j : X ⟶ Y` is étale, `j.smallEtalePullback A` identifies naturally with sheaf
precomposition along `j.smallEtaleMap : X.Etale ⥤ Y.Etale`. -/
noncomputable abbrev smallEtalePullbackIsoMapPushforward (j : X ⟶ Y) [Etale j]
    (A : Type*) [Category* A] :
    j.smallEtalePullback A ≅
      j.smallEtaleMap.sheafPushforwardContinuous A (smallEtaleTopology X) (smallEtaleTopology Y) :=
  j.smallEtaleMapBaseChangeAdj.sheafPullbackIso A (smallEtaleTopology X) (smallEtaleTopology Y)

end PushforwardPullback

section EvalUnitSelf

/-- For an étale morphism `u : U ⟶ S`, the diagonal
`Etale.mk (𝟙 U) ⟶ u.smallEtaleBaseChange.obj (Etale.mk u)`. -/
noncomputable def smallEtaleBaseChangeSelfDiag {S U : Scheme.{u}} (u : U ⟶ S) [Etale u] :
    Etale.mk (𝟙 U) ⟶ u.smallEtaleBaseChange.obj (Etale.mk u) :=
  MorphismProperty.Over.homMk (pullback.lift (𝟙 U) (𝟙 U) rfl) (pullback.lift_snd _ _ _)

/-- Pulling a section of `F` over `Etale.mk u` back to the terminal object `Etale.mk (𝟙 U)` of
`U.Etale` along the adjunction unit and the diagonal `u.smallEtaleBaseChangeSelfDiag`. -/
noncomputable def evalUnitSelf {S U : Scheme.{u}} (u : U ⟶ S) [Etale u]
    {A : Type*} [Category* A] (F : Sheaf (smallEtaleTopology S) A) :
    F.obj.obj (Opposite.op (Etale.mk u)) ⟶
      ((u.smallEtalePullback A).obj F).obj.obj (Opposite.op (Etale.mk (𝟙 U))) :=
  ((u.smallEtaleAdjunction A).unit.app F).hom.app (Opposite.op (Etale.mk u)) ≫
    ((u.smallEtalePullback A).obj F).obj.map (u.smallEtaleBaseChangeSelfDiag).op

/-- `evalUnitSelf` is natural in the sheaf `F`. -/
@[reassoc]
lemma evalUnitSelf_naturality {S U : Scheme.{u}} (u : U ⟶ S) [Etale u]
    {A : Type*} [Category* A] {F G : Sheaf (smallEtaleTopology S) A} (φ : F ⟶ G) :
    φ.hom.app (Opposite.op (Etale.mk u)) ≫ u.evalUnitSelf G =
      u.evalUnitSelf F ≫
        ((u.smallEtalePullback A).map φ).hom.app (Opposite.op (Etale.mk (𝟙 U))) := by
  have h₁ := NatTrans.congr_app
    (congrArg (·.hom) ((u.smallEtaleAdjunction A).unit.naturality φ))
    (Opposite.op (Etale.mk u))
  have h₂ := ((u.smallEtalePullback A).map φ).hom.naturality (u.smallEtaleBaseChangeSelfDiag).op
  exact (Category.assoc _ _ _).symm.trans <|
    (eq_whisker h₁ _).trans <|
    (Category.assoc _ _ _).trans <|
    (whisker_eq _ h₂.symm).trans (Category.assoc _ _ _).symm

/-- On a constant sheaf, `evalUnitSelf` sends the canonical section over `Etale.mk u` to the
canonical section over `Etale.mk (𝟙 U)` transported by `smallEtalePullbackConstantSheafIso`. -/
@[reassoc]
lemma toSheafify_comp_evalUnitSelf {S U : Scheme.{u}} (u : U ⟶ S) [Etale u]
    (A : Type*) [Category* A] [HasWeakSheafify (smallEtaleTopology S) A]
    [HasWeakSheafify (smallEtaleTopology U) A] (M : A) :
    (toSheafify (smallEtaleTopology S) ((Functor.const S.Etaleᵒᵖ).obj M)).app
        (Opposite.op (Etale.mk u)) ≫
        u.evalUnitSelf ((constantSheaf (smallEtaleTopology S) A).obj M) =
      (toSheafify (smallEtaleTopology U) ((Functor.const U.Etaleᵒᵖ).obj M)).app
          (Opposite.op (Etale.mk (𝟙 U))) ≫
        (u.smallEtalePullbackConstantSheafIso A M).inv.hom.app
          (Opposite.op (Etale.mk (𝟙 U))) := by
  have hw := NatTrans.congr_app
    (u.smallEtaleBaseChange.whiskerLeft_toSheafify_comp_sheafPullbackConstantSheafIso_inv
      A (smallEtaleTopology S) (smallEtaleTopology U) M) (Opposite.op (Etale.mk u))
  simp only [Functor.whiskerLeft_app, NatTrans.comp_app] at hw
  have hnat := ((u.smallEtalePullbackConstantSheafIso A M).inv.hom.naturality
    (u.smallEtaleBaseChangeSelfDiag).op).symm
  have hrest := toSheafify_app_const_comp_map (smallEtaleTopology U) M
    (u.smallEtaleBaseChangeSelfDiag).op
  exact (Category.assoc _ _ _).symm.trans <|
    (eq_whisker hw.symm _).trans <|
    (Category.assoc _ _ _).trans <|
    (whisker_eq _ hnat).trans <|
    (Category.assoc _ _ _).symm.trans (eq_whisker hrest _)

/-- If `φ : F ⟶ const N` sends a section `s` over `Etale.mk u` to the constant section `n`, then
`u^* φ` composed with `smallEtalePullbackConstantSheafIso.hom` sends `u.evalUnitSelf F s` to the
constant section `n` over `Etale.mk (𝟙 U)`. -/
lemma smallEtalePullback_map_comp_constantSheafIso_evalUnitSelf {S U : Scheme.{u}}
    (u : U ⟶ S) [Etale u] {A : Type*} [Category* A]
    [HasWeakSheafify (smallEtaleTopology S) A] [HasWeakSheafify (smallEtaleTopology U) A]
    {FA : A → A → Type*} {CD : A → Type*} [∀ X Y, FunLike (FA X Y) (CD X) (CD Y)]
    [ConcreteCategory A FA] [(u.smallEtalePushforward A).IsRightAdjoint]
    {F : Sheaf (smallEtaleTopology S) A} {N : A}
    (φ : F ⟶ (constantSheaf (smallEtaleTopology S) A).obj N)
    {s : ToType (F.obj.obj (Opposite.op (Etale.mk u)))} {n : ToType N}
    (h : φ.hom.app (Opposite.op (Etale.mk u)) s =
      (toSheafify (smallEtaleTopology S) ((Functor.const S.Etaleᵒᵖ).obj N)).app
        (Opposite.op (Etale.mk u)) n) :
    (((u.smallEtalePullback A).map φ ≫
        (u.smallEtalePullbackConstantSheafIso A N).hom).hom.app
          (Opposite.op (Etale.mk (𝟙 U)))) (u.evalUnitSelf F s) =
      (toSheafify (smallEtaleTopology U) ((Functor.const U.Etaleᵒᵖ).obj N)).app
        (Opposite.op (Etale.mk (𝟙 U))) n := by
  have he := congrArg (u.evalUnitSelf ((constantSheaf (smallEtaleTopology S) A).obj N)) h
  have hl := ConcreteCategory.congr_hom (u.evalUnitSelf_naturality φ) s
  have hr := ConcreteCategory.congr_hom (u.toSheafify_comp_evalUnitSelf A N) n
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hl hr
  have he' := congrArg
    ((u.smallEtalePullbackConstantSheafIso A N).hom.hom.app (Opposite.op (Etale.mk (𝟙 U))))
    (hl.symm.trans (he.trans hr))
  rw [Sheaf.inv_hom_id_hom_app_apply] at he'
  simpa only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    ConcreteCategory.comp_apply] using he'

end EvalUnitSelf

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

@[simp]
lemma smallEtalePullbackIsoOver_hom :
    (U.smallEtalePullbackIsoOver A).hom =
      ((U.hom : U.left ⟶ S).smallEtalePullbackIsoMapPushforward A).hom ≫
        (U.overPullbackCompOverSheafEquivIso A).inv := (rfl)

@[simp]
lemma smallEtalePullbackIsoOver_inv :
    (U.smallEtalePullbackIsoOver A).inv =
      (U.overPullbackCompOverSheafEquivIso A).hom ≫
        ((U.hom : U.left ⟶ S).smallEtalePullbackIsoMapPushforward A).inv := (rfl)

/-- On an étale sheaf `F` on `S`, `((U.hom : U.left ⟶ S).smallEtalePullback A).obj F` identifies
with `F.over U` transported across `U.overSheafEquiv A`. -/
noncomputable abbrev smallEtalePullbackObjIsoOver (F : Sheaf (smallEtaleTopology S) A) :
    ((U.hom : U.left ⟶ S).smallEtalePullback A).obj F ≅
      (U.overSheafEquiv A).functor.obj (F.over U) :=
  (U.smallEtalePullbackIsoOver A).app F

end Etale

namespace Hom

section StalksAndExactness

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

section PointFiber

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X)

/-- For a geometric point `s : Spec Ω ⟶ X`, lifts of `s` to `V ×_Y X` correspond bijectively to
lifts of `s ≫ f` to `V`, giving a natural isomorphism of point fibre functors. -/
noncomputable def pointSmallEtaleFiberCompIso :
    f.smallEtaleBaseChange ⋙ (pointSmallEtale s).fiber ≅ (pointSmallEtale (s ≫ f)).fiber :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight f.smallEtaleBaseChangeCompForgetIso _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (Etale.forget Y)
      ((CategoryTheory.Over.mapPullbackAdj f).compCoyonedaIso.app
        (Opposite.op (CategoryTheory.Over.mk s))).symm

@[simp]
lemma pointSmallEtaleFiberCompIso_hom_app_left (V : Y.Etale)
    (φ : (f.smallEtaleBaseChange ⋙ (pointSmallEtale s).fiber).obj V) :
    dsimp% ((f.pointSmallEtaleFiberCompIso s).hom.app V φ).left =
      φ.left ≫ pullback.fst V.hom f := by
  have h : (f.pointSmallEtaleFiberCompIso s).hom.app V =
      (coyoneda.obj (Opposite.op (CategoryTheory.Over.mk s))).map
        (f.smallEtaleBaseChangeCompForgetIso.hom.app V) ≫
      ((CategoryTheory.Over.mapPullbackAdj f).homEquiv (CategoryTheory.Over.mk s)
        ((Etale.forget Y).obj V)).symm.toIso.hom :=
    (Category.id_comp _).trans (congrArg (_ ≫ ·) (Category.id_comp _))
  rw [h]
  exact congrArg (· ≫ pullback.fst V.hom f)
    (CategoryTheory.Comma.comp_left.trans
      ((congrArg (_ ≫ ·) (f.smallEtaleBaseChangeCompForgetIso_hom_app_left V)).trans
        (Category.comp_id _)))

@[simp]
lemma pointSmallEtaleFiberCompIso_inv_app_left (V : Y.Etale)
    (ψ : (pointSmallEtale (s ≫ f)).fiber.obj V) :
    dsimp% ((f.pointSmallEtaleFiberCompIso s).inv.app V ψ).left =
      pullback.lift ψ.left s (CategoryTheory.Over.w ψ) := by
  have h : ((f.pointSmallEtaleFiberCompIso s).hom.app V
      ((f.pointSmallEtaleFiberCompIso s).inv.app V ψ)).left = ψ.left :=
    congrArg (fun g : (pointSmallEtale (s ≫ f)).fiber.obj V ⟶ _ ↦ (g ψ).left)
      ((f.pointSmallEtaleFiberCompIso s).inv_hom_id_app V)
  rw [pointSmallEtaleFiberCompIso_hom_app_left] at h
  exact pullback.hom_ext (h.trans (pullback.lift_fst _ _ _).symm)
    ((CategoryTheory.Over.w ((f.pointSmallEtaleFiberCompIso s).inv.app V ψ)).trans
      (pullback.lift_snd _ _ _).symm)

/-- The inverse image of the point `pointSmallEtale s` of `X.Etale` along `f.smallEtaleBaseChange`
is isomorphic to `pointSmallEtale (s ≫ f)`. -/
noncomputable abbrev pointSmallEtaleComapIso :
    letI := initiallySmall_elements_of_iso.{u} (f.pointSmallEtaleFiberCompIso s)
    (pointSmallEtale s).comap f.smallEtaleBaseChange f.coverPreserving_smallEtaleBaseChange ≅
      pointSmallEtale (s ≫ f) :=
  (pointSmallEtale s).comapIsoOfFiberIso
    f.smallEtaleBaseChange f.coverPreserving_smallEtaleBaseChange (f.pointSmallEtaleFiberCompIso s)

end PointFiber

/-- **Stalk of an inverse image sheaf.** At a geometric point `s : Spec Ω ⟶ X`, the stalk of
`(f.smallEtalePullback A).obj F` identifies naturally with the stalk of `F` at `s ≫ f`. -/
noncomputable abbrev smallEtalePullbackCompSheafFiberIso
    (A : Type*) [Category* A] [HasProducts.{u} A] [HasColimitsOfSize.{u, u} A]
    [(f.smallEtalePushforward A).IsRightAdjoint]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X) :
    f.smallEtalePullback A ⋙ (pointSmallEtale s).sheafFiber ≅
      (pointSmallEtale (s ≫ f)).sheafFiber :=
  (pointSmallEtale s).sheafPullbackCompSheafFiberIso
    f.smallEtaleBaseChange (f.pointSmallEtaleFiberCompIso s) A

/-- Inverse image of small étale sheaves preserves finite limits when `f.smallEtalePushforward A`
is a right adjoint and `A` is a concrete category with finite limits, `u`-products, `u`-small
colimits, and `AB5OfSize.{u, u}` whose forgetful functor reflects isomorphisms, preserves
`u`-small filtered colimits, and satisfies `HasSheafCompose` on `smallEtaleTopology X`. -/
instance preservesFiniteLimits_smallEtalePullback
    {A : Type*} [Category* A]
    [(f.smallEtalePushforward A).IsRightAdjoint]
    [HasFiniteLimits A] [HasProducts.{u} A] [HasColimitsOfSize.{u, u} A] [AB5OfSize.{u, u} A]
    {FA : A → A → Type*} {CD : A → Type u}
    [∀ M N, FunLike (FA M N) (CD M) (CD N)] [ConcreteCategory.{u} A FA]
    [(CategoryTheory.forget A).ReflectsIsomorphisms]
    [PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget A)]
    [(smallEtaleTopology X).HasSheafCompose (CategoryTheory.forget A)] :
    PreservesFiniteLimits (f.smallEtalePullback A) := by
  let p (x : X) : Spec (.of (SeparableClosure (X.residueField x))) ⟶ X :=
    (SpecToEquivOfField (SeparableClosure (X.residueField x)) _).invFun
      ⟨x, CommRingCat.ofHom (algebraMap (X.residueField x) _)⟩
  have hΦ : JointlyReflectIsomorphisms fun x : X ↦ (pointSmallEtale (p x)).sheafFiber (A := A) :=
    ⟨fun φ h ↦
      have : ∀ Φ : (ObjectProperty.ofObj fun x : X ↦ pointSmallEtale (p x)).FullSubcategory,
          IsIso (Φ.obj.sheafFiber.map φ) := fun ⟨_, ⟨x⟩⟩ ↦ h x
      ((isConservativeFamilyOfPoints_pointSmallEtale' X).jointlyReflectIsomorphisms A).isIso φ⟩
  exact f.smallEtaleBaseChange.preservesFiniteLimits_sheafPullback_of_jointlyReflectIsomorphisms.{u}
    (fun x ↦ pointSmallEtale (p x)) (fun x ↦ pointSmallEtale (p x ≫ f))
    (fun x ↦ f.pointSmallEtaleFiberCompIso (p x)) hΦ

/-- Inverse image of small étale sheaves preserves finite colimits, being a left adjoint. -/
instance preservesFiniteColimits_smallEtalePullback
    {A : Type*} [Category* A] [(f.smallEtalePushforward A).IsRightAdjoint] :
    PreservesFiniteColimits (f.smallEtalePullback A) where
  preservesFiniteColimits _ _ _ := inferInstance

end StalksAndExactness

end Hom

/-- A covering sieve on the terminal étale `S`-scheme `Etale.mk (𝟙 S)` yields a `Type u`-indexed
jointly surjective family of nonempty étale `S`-schemes whose morphisms to `Etale.mk (𝟙 S)` lie in
the sieve. -/
theorem exists_etaleCover_of_mem_smallEtaleTopology_terminal {S : Scheme.{u}}
    {R : Sieve (Etale.mk (𝟙 S))} (hR : R ∈ smallEtaleTopology S (Etale.mk (𝟙 S))) :
    ∃ (ι : Type u) (U : ι → Scheme.{u}) (u : ∀ i, U i ⟶ S) (hu : ∀ i, Etale (u i)),
      (∀ i, Nonempty (U i)) ∧
        (∀ i, ∃ g : @Etale.mk S (U i) (u i) (hu i) ⟶ Etale.mk (𝟙 S), R g) ∧
        (⋃ i, Set.range (u i) = .univ) := by
  obtain ⟨ι', V, g', heq⟩ := R.exists_eq_ofArrows
  have hcov := (ofArrows_mem_smallEtaleTopology_iff g').mp (heq ▸ hR)
  have hg' (j : ι') : ((g' j).left : (V j).left ⟶ S) = (V j).hom :=
    (Category.comp_id _).symm.trans (CategoryTheory.Over.w ((Etale.forget S).map (g' j)))
  choose idx hidx using fun s : S ↦ Set.mem_iUnion.mp (hcov ▸ Set.mem_univ s)
  refine ⟨S, fun s ↦ (V (idx s)).left, fun s ↦ (V (idx s)).hom, fun s ↦ (V (idx s)).prop,
    fun s ↦ ?_, fun s ↦ ?_, Set.eq_univ_of_forall fun s ↦ ?_⟩
  · obtain ⟨z, -⟩ := hidx s
    exact ⟨z⟩
  · exact ⟨g' (idx s), heq.symm ▸ Sieve.ofArrows_mk V g' (idx s)⟩
  · obtain ⟨z, hz⟩ := hidx s
    exact Set.mem_iUnion.mpr ⟨s, z, (congrArg (fun f : (V (idx s)).left ⟶ S ↦ f z)
      (hg' (idx s)).symm).trans hz⟩

end AlgebraicGeometry.Scheme
