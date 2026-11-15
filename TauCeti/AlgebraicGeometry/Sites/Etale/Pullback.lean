/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Limits
public import TauCeti.AlgebraicGeometry.Morphisms.Etale.Basic
public import TauCeti.CategoryTheory.MorphismProperty.CommaSites
public import TauCeti.CategoryTheory.Sites.ConstantSheaf
public import TauCeti.CategoryTheory.Sites.LocallyConstant
public import TauCeti.CategoryTheory.Sites.Point.Comap
public import TauCeti.CategoryTheory.Sites.Pullback

/-!
# Pullback of étale sheaves, geometric stalks, and étale descent of local constancy

For a morphism of schemes `f : X ⟶ Y`, base change along `f` defines a functor
`f.smallEtaleBaseChange : Y.Etale ⥤ X.Etale` sending an étale `Y`-scheme `V ⟶ Y` to
`V ×_Y X ⟶ X`. Because `f.smallEtaleBaseChange` preserves finite limits and étale coverings, it is
representably flat, final, cover-preserving, and continuous for the small étale topologies, hence
forms the site-level functor of a morphism of sites `(X_ét) → (Y_ét)`.

Although `Y.Etale` is a large category (`Type (u + 1)`), Mathlib's small affine étale subsite
`Y.AffineEtale` is `u`-essentially small and `1`-hypercover dense in `Y.Etale`. Using the dense
subsite transport from `TauCeti.CategoryTheory.Sites.Pullback`, the sheaf pushforward
`f.smallEtaleBaseChange.sheafPushforwardContinuous` admits a left adjoint
`f.smallEtalePullback A : Sheaf Y.smallEtaleTopology A ⥤ Sheaf X.smallEtaleTopology A` whenever
`A` has `u`-small colimits, weak sheafification on `X_ét`, and the affine-to-small étale sheaf
comparison on `Y` is an equivalence (satisfied in particular by `Type u`, `AddCommGrpCat.{u}`,
`ModuleCat.{u} Λ`, and `CommRingCat.{u}`).

We establish the core properties of `f.smallEtalePullback A`:
* **Functoriality and constant sheaves**: natural isomorphisms `(𝟙 X)^* ≅ 𝟭`,
  `(f ≫ g)^* ≅ g^* ⋙ f^*`, congruence in `f`, and `f^* (M_{Y_ét}) ≅ M_{X_ét}` for constant sheaves.
* **Geometric stalks and exactness**: for every geometric point `x : Spec Ω ⟶ X`, the stalk of
  `f^* F` at `x` identifies naturally with the stalk of `F` at `x ≫ f`
  (`AlgebraicGeometry.Scheme.Hom.smallEtalePullbackCompSheafFiberIso`). Because geometric points
  form a conservative family on `X_ét` and stalks commute with finite limits under `AB5`, it
  follows that `f.smallEtalePullback A` preserves finite limits (so `f^*` is exact on abelian
  étale sheaves).
* **Restriction along étale morphisms and slice equivalence**: when `f : X ⟶ Y` is étale, `f^*`
  identifies with restriction (sheaf pushforward) along `MorphismProperty.Over.map ⊤ ‹Etale f›`.
  Consequently, for `U : S.Etale`, sheaves on the localized site `(S.Etale / U, J_ét/U)` are
  equivalent to étale sheaves on `U.left` (`AlgebraicGeometry.Scheme.Etale.overSheafEquiv`),
  intertwining `overPullback` with `U.hom.smallEtalePullback`.
* **Local constancy and étale descent**: `IsLocallyConstantIn S.smallEtaleTopology P` is
  characterized by constant-sheaf trivializations after `U.hom.smallEtalePullback`, is stable
  under pullback along arbitrary morphisms of schemes, and can be tested on any jointly surjective
  family of étale morphisms (in particular on any étale cover or surjective étale morphism).

## Main declarations

* `AlgebraicGeometry.Scheme.Hom.smallEtaleBaseChange`: base change `Y.Etale ⥤ X.Etale` along
  `f : X ⟶ Y`, with `AlgebraicGeometry.Scheme.smallEtaleBaseChangeId` and
  `AlgebraicGeometry.Scheme.Hom.smallEtaleBaseChangeComp`.
* `AlgebraicGeometry.Scheme.Hom.smallEtalePullback`: inverse image of étale sheaves along
  `f : X ⟶ Y`, with `AlgebraicGeometry.Scheme.smallEtalePullbackId`,
  `AlgebraicGeometry.Scheme.Hom.smallEtalePullbackComp`, and
  `AlgebraicGeometry.Scheme.Hom.smallEtalePullbackConstantSheafIso`.
* `AlgebraicGeometry.Scheme.Hom.smallEtalePullbackCompSheafFiberIso`: stalk comparison
  `(f^* F)_x ≅ F_{x ≫ f}` at a geometric point `x : Spec Ω ⟶ X`.
* `AlgebraicGeometry.Scheme.Hom.preservesFiniteLimits_smallEtalePullback`: left exactness of
  `f.smallEtalePullback A`.
* `AlgebraicGeometry.Scheme.Hom.smallEtalePullbackIsoPushforwardOfEtale`,
  `AlgebraicGeometry.Scheme.Etale.overSheafEquiv`, and
  `AlgebraicGeometry.Scheme.Etale.overPullbackCompOverSheafEquivIso`: identification of `f^*` for
  étale `f` and of the slice étale site over `U : S.Etale` with `U.left`'s small étale site.
* `CategoryTheory.Sheaf.IsLocallyConstantIn.smallEtalePullback`,
  `CategoryTheory.Sheaf.isLocallyConstantIn_smallEtaleTopology_iff_of_iUnion_range_eq_univ`,
  `CategoryTheory.Sheaf.isLocallyConstantIn_smallEtaleTopology_iff_of_cover`, and
  `CategoryTheory.Sheaf.isLocallyConstantIn_smallEtaleTopology_iff_of_surjective`: base-change
  stability and étale descent of locally constant étale sheaves.

## References

* M. Artin, A. Grothendieck, J.-L. Verdier, *SGA 4*, Exposé VII, §1–3 (morphism of étale sites),
  Exposé VIII, §3 (stalks of inverse images), and Exposé IX, §2 (locally constant sheaves).
* The Stacks Project, [Tag 03YU](https://stacks.math.columbia.edu/tag/03YU) (functoriality of the
  small étale site) and [Tag 0954](https://stacks.math.columbia.edu/tag/0954) (locally constant
  étale sheaves).
-/

public section

universe u v' u'

open CategoryTheory Limits Opposite MorphismProperty

namespace AlgebraicGeometry.Scheme

section BaseChange

variable {X Y Z : Scheme.{u}}

/-- Base change along `f : X ⟶ Y`, from schemes étale over `Y` to schemes étale over `X`: an étale
`V ⟶ Y` is sent to `V ×_Y X ⟶ X`. -/
noncomputable def Hom.smallEtaleBaseChange (f : X ⟶ Y) : Y.Etale ⥤ X.Etale :=
  MorphismProperty.Over.pullback @Etale ⊤ f

/-- On underlying schemes over `X`, `f.smallEtaleBaseChange` is base change along `f`. -/
noncomputable def Hom.smallEtaleBaseChangeCompForgetIso (f : X ⟶ Y) :
    f.smallEtaleBaseChange ⋙ Etale.forget X ≅ Etale.forget Y ⋙ CategoryTheory.Over.pullback f :=
  Iso.refl _

/-- For `V : Y.Etale`, the first projection of `V ×_Y X` fits into a commutative square with `V.hom`
and `(f.smallEtaleBaseChange.obj V).hom ≫ f`. -/
lemma Hom.exists_hom_comp_eq_of_smallEtaleBaseChange (f : X ⟶ Y) (V : Y.Etale) :
    ∃ g : (f.smallEtaleBaseChange.obj V).left ⟶ V.left,
      g ≫ V.hom = (f.smallEtaleBaseChange.obj V).hom ≫ f :=
  ⟨pullback.fst V.hom f, pullback.condition⟩

/-- Base change along `𝟙 X` on `X.Etale` identifies naturally with the identity functor. -/
noncomputable def smallEtaleBaseChangeId (X : Scheme.{u}) :
    Hom.smallEtaleBaseChange (𝟙 X) ≅ 𝟭 X.Etale :=
  MorphismProperty.Over.pullbackId @Etale X

/-- Base change on small étale sites commutes with composition up to natural isomorphism. -/
noncomputable def Hom.smallEtaleBaseChangeComp (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).smallEtaleBaseChange ≅ g.smallEtaleBaseChange ⋙ f.smallEtaleBaseChange :=
  MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) f g

/-- Equal morphisms of schemes induce naturally isomorphic base-change functors on small étale
sites. -/
noncomputable def Hom.smallEtaleBaseChangeCongr {f g : X ⟶ Y} (h : f = g) :
    f.smallEtaleBaseChange ≅ g.smallEtaleBaseChange :=
  MorphismProperty.Over.pullbackCongr (P := @Etale) (Q := ⊤) h

instance Hom.preservesFiniteLimits_smallEtaleBaseChange (f : X ⟶ Y) :
    PreservesFiniteLimits f.smallEtaleBaseChange := by
  have : PreservesFiniteLimits (f.smallEtaleBaseChange ⋙ Etale.forget X) :=
    preservesFiniteLimits_of_natIso f.smallEtaleBaseChangeCompForgetIso.symm
  have : ReflectsFiniteLimits (Etale.forget X) :=
    ⟨fun _ _ _ ↦ reflectsLimitsOfShape_of_reflectsIsomorphisms⟩
  exact ⟨fun _ _ _ ↦
    preservesLimitsOfShape_of_reflects_of_preserves f.smallEtaleBaseChange (Etale.forget X)⟩

instance Hom.representablyFlat_smallEtaleBaseChange (f : X ⟶ Y) :
    RepresentablyFlat f.smallEtaleBaseChange :=
  flat_of_preservesFiniteLimits f.smallEtaleBaseChange

instance Hom.final_smallEtaleBaseChange (f : X ⟶ Y) :
    f.smallEtaleBaseChange.Final :=
  CategoryTheory.final_of_representablyFlat f.smallEtaleBaseChange

private lemma locallyCoverDense_over_forget_etale (S : Scheme.{u}) :
    @Functor.LocallyCoverDense _ (MorphismProperty.Comma.instCategory _ _ _ _ _) _ _
      (MorphismProperty.Over.forget @AlgebraicGeometry.Etale ⊤ S) (etaleTopology.over S) :=
  Scheme.locallyCoverDense_of_le S
    (le_rfl : (@AlgebraicGeometry.Etale : MorphismProperty Scheme.{u}) ≤ @AlgebraicGeometry.Etale)

/-- Base change along `f : X ⟶ Y` preserves coverings for the small étale topologies. -/
lemma Hom.coverPreserving_smallEtaleBaseChange (f : X ⟶ Y) :
    CoverPreserving Y.smallEtaleTopology X.smallEtaleTopology f.smallEtaleBaseChange :=
  have := locallyCoverDense_over_forget_etale Y
  have := locallyCoverDense_over_forget_etale X
  MorphismProperty.coverPreserving_over_pullback etaleTopology @AlgebraicGeometry.Etale f

instance Hom.isContinuous_smallEtaleBaseChange (f : X ⟶ Y) :
    f.smallEtaleBaseChange.IsContinuous Y.smallEtaleTopology X.smallEtaleTopology :=
  have := locallyCoverDense_over_forget_etale Y
  have := locallyCoverDense_over_forget_etale X
  MorphismProperty.isContinuous_over_pullback etaleTopology @AlgebraicGeometry.Etale f

end BaseChange

section Pullback

variable {X Y Z : Scheme.{u}}

/-- The étale sheaf pushforward along `f : X ⟶ Y` admits a left adjoint whenever `A` has `u`-small
colimits, weak sheafification on `X_ét`, and the affine-to-small étale sheaf pushforward on `Y` is
an equivalence. -/
instance Hom.isRightAdjoint_smallEtaleBaseChange_sheafPushforwardContinuous
    (f : X ⟶ Y) (A : Type u') [Category.{v'} A]
    [HasColimitsOfSize.{u, u} A] [HasWeakSheafify X.smallEtaleTopology A]
    [((AffineEtale.Spec Y).sheafPushforwardContinuous A
      (AffineEtale.topology Y) Y.smallEtaleTopology).IsEquivalence] :
    (f.smallEtaleBaseChange.sheafPushforwardContinuous A
      Y.smallEtaleTopology X.smallEtaleTopology).IsRightAdjoint :=
  have := Functor.isContinuous_comp (AffineEtale.Spec Y) f.smallEtaleBaseChange
    (AffineEtale.topology Y) Y.smallEtaleTopology X.smallEtaleTopology
  have := Functor.isRightAdjoint_sheafPushforwardContinuous_of_essentiallySmall.{u}
    (AffineEtale.Spec Y ⋙ f.smallEtaleBaseChange) A
    (AffineEtale.topology Y) X.smallEtaleTopology
  Functor.isRightAdjoint_sheafPushforwardContinuous_of_isEquivalence
    (AffineEtale.Spec Y) f.smallEtaleBaseChange A
    (AffineEtale.topology Y) Y.smallEtaleTopology X.smallEtaleTopology

/-- Pullback (inverse image) `f^* : Sheaf Y.smallEtaleTopology A ⥤ Sheaf X.smallEtaleTopology A` of
étale sheaves along a morphism of schemes `f : X ⟶ Y`. -/
noncomputable abbrev Hom.smallEtalePullback (f : X ⟶ Y) (A : Type u') [Category.{v'} A]
    [(f.smallEtaleBaseChange.sheafPushforwardContinuous A
      Y.smallEtaleTopology X.smallEtaleTopology).IsRightAdjoint] :
    Sheaf Y.smallEtaleTopology A ⥤ Sheaf X.smallEtaleTopology A :=
  f.smallEtaleBaseChange.sheafPullback A Y.smallEtaleTopology X.smallEtaleTopology

/-- The `(f^*, f_*)` adjunction on étale sheaves for a morphism of schemes `f : X ⟶ Y`. -/
noncomputable def Hom.smallEtaleAdjunction (f : X ⟶ Y) (A : Type u') [Category.{v'} A]
    [(f.smallEtaleBaseChange.sheafPushforwardContinuous A
      Y.smallEtaleTopology X.smallEtaleTopology).IsRightAdjoint] :
    f.smallEtalePullback A ⊣
      f.smallEtaleBaseChange.sheafPushforwardContinuous A
        Y.smallEtaleTopology X.smallEtaleTopology :=
  f.smallEtaleBaseChange.sheafAdjunctionContinuous A Y.smallEtaleTopology X.smallEtaleTopology

/-- Pullback of étale sheaves along `𝟙 X` identifies with the identity functor. -/
noncomputable def smallEtalePullbackId (X : Scheme.{u}) (A : Type u') [Category.{v'} A]
    [((Hom.smallEtaleBaseChange (𝟙 X)).sheafPushforwardContinuous A
      X.smallEtaleTopology X.smallEtaleTopology).IsRightAdjoint] :
    Hom.smallEtalePullback (𝟙 X) A ≅ 𝟭 (Sheaf X.smallEtaleTopology A) :=
  Functor.sheafPullbackId' A X.smallEtaleTopology (smallEtaleBaseChangeId X)

/-- Pullback of étale sheaves along a composite `f ≫ g` identifies with `g^* ⋙ f^*`. -/
noncomputable def Hom.smallEtalePullbackComp (f : X ⟶ Y) (g : Y ⟶ Z)
    (A : Type u') [Category.{v'} A]
    [(f.smallEtaleBaseChange.sheafPushforwardContinuous A
      Y.smallEtaleTopology X.smallEtaleTopology).IsRightAdjoint]
    [(g.smallEtaleBaseChange.sheafPushforwardContinuous A
      Z.smallEtaleTopology Y.smallEtaleTopology).IsRightAdjoint]
    [((f ≫ g).smallEtaleBaseChange.sheafPushforwardContinuous A
      Z.smallEtaleTopology X.smallEtaleTopology).IsRightAdjoint] :
    (f ≫ g).smallEtalePullback A ≅ g.smallEtalePullback A ⋙ f.smallEtalePullback A :=
  Functor.sheafPullbackComp' A Z.smallEtaleTopology Y.smallEtaleTopology X.smallEtaleTopology
    (f.smallEtaleBaseChangeComp g).symm

/-- Equal morphisms of schemes induce naturally isomorphic étale sheaf pullback functors. -/
noncomputable def Hom.smallEtalePullbackCongr {f g : X ⟶ Y} (h : f = g)
    (A : Type u') [Category.{v'} A]
    [(f.smallEtaleBaseChange.sheafPushforwardContinuous A
      Y.smallEtaleTopology X.smallEtaleTopology).IsRightAdjoint]
    [(g.smallEtaleBaseChange.sheafPushforwardContinuous A
      Y.smallEtaleTopology X.smallEtaleTopology).IsRightAdjoint] :
    f.smallEtalePullback A ≅ g.smallEtalePullback A :=
  Functor.sheafPullbackIso A Y.smallEtaleTopology X.smallEtaleTopology
    (Hom.smallEtaleBaseChangeCongr h)

/-- Pullback of a constant étale sheaf with value `M` along `f : X ⟶ Y` is the constant étale sheaf
with value `M`. -/
noncomputable def Hom.smallEtalePullbackConstantSheafIso (f : X ⟶ Y)
    (A : Type u') [Category.{v'} A]
    [HasWeakSheafify Y.smallEtaleTopology A] [HasWeakSheafify X.smallEtaleTopology A]
    [(f.smallEtaleBaseChange.sheafPushforwardContinuous A
      Y.smallEtaleTopology X.smallEtaleTopology).IsRightAdjoint]
    (M : A) :
    (f.smallEtalePullback A).obj ((constantSheaf Y.smallEtaleTopology A).obj M) ≅
      (constantSheaf X.smallEtaleTopology A).obj M :=
  f.smallEtaleBaseChange.sheafPullbackConstantSheafIso A
    Y.smallEtaleTopology X.smallEtaleTopology M

end Pullback

section Stalk

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ X)

/-- By the universal property of fiber products (`Over.mapPullbackAdj f`), lifts of a geometric
point `x : Spec Ω ⟶ X` to `V ×_Y X` correspond naturally to lifts of `x ≫ f` to `V`. -/
noncomputable def Hom.smallEtaleBaseChangeCompPointSmallEtaleFiberIso :
    f.smallEtaleBaseChange ⋙ (pointSmallEtale x).fiber ≅ (pointSmallEtale (x ≫ f)).fiber :=
  let e₀ : (CategoryTheory.Over.map f).obj (CategoryTheory.Over.mk x) ≅
      CategoryTheory.Over.mk (x ≫ f) :=
    CategoryTheory.Over.isoMk (Iso.refl _) (Category.id_comp _)
  let eAdj : CategoryTheory.Over.pullback f ⋙ coyoneda.obj (op (CategoryTheory.Over.mk x)) ≅
      coyoneda.obj (op ((CategoryTheory.Over.map f).obj (CategoryTheory.Over.mk x))) :=
    NatIso.ofComponents
      (fun W ↦ ((CategoryTheory.Over.mapPullbackAdj f).homEquiv
        (CategoryTheory.Over.mk x) W).symm.toIso)
      (fun g ↦ by
        ext u
        exact (CategoryTheory.Over.mapPullbackAdj f).homEquiv_naturality_right_symm u g)
  Functor.isoWhiskerRight f.smallEtaleBaseChangeCompForgetIso
    (coyoneda.obj (op (CategoryTheory.Over.mk x))) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (Etale.forget Y) (eAdj ≪≫ coyoneda.mapIso e₀.op.symm)

/-- **Stalk of an étale sheaf pullback.** For a morphism `f : X ⟶ Y` and a geometric point
`x : Spec Ω ⟶ X`, the stalk of `f^* F` at `x` identifies naturally with the stalk of `F` at
`x ≫ f`. -/
noncomputable def Hom.smallEtalePullbackCompSheafFiberIso
    (A : Type u') [Category.{v'} A] [HasProducts.{u} A] [HasColimitsOfSize.{u, u} A]
    [(f.smallEtaleBaseChange.sheafPushforwardContinuous A
      Y.smallEtaleTopology X.smallEtaleTopology).IsRightAdjoint] :
    f.smallEtalePullback A ⋙ (pointSmallEtale x).sheafFiber ≅
      (pointSmallEtale (x ≫ f)).sheafFiber :=
  GrothendieckTopology.Point.sheafFiberComapIsoOfFiberIso
    (pointSmallEtale x) (pointSmallEtale (x ≫ f))
    f.smallEtaleBaseChange f.coverPreserving_smallEtaleBaseChange
    (f.smallEtaleBaseChangeCompPointSmallEtaleFiberIso x) A

/-- **Left exactness of étale sheaf pullback.** Because geometric points form a conservative family
on `X.smallEtaleTopology` and stalks commute with finite limits under `AB5`,
`f.smallEtalePullback A` preserves finite limits. -/
instance Hom.preservesFiniteLimits_smallEtalePullback
    (A : Type u') [Category.{v'} A]
    [HasFiniteLimits A] [HasProducts.{u} A] [HasColimitsOfSize.{u, u} A] [AB5OfSize.{u, u} A]
    {FC : A → A → Type*} {CC : A → Type u}
    [∀ M N, FunLike (FC M N) (CC M) (CC N)] [ConcreteCategory.{u} A FC]
    [(CategoryTheory.forget A).ReflectsIsomorphisms]
    [PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget A)]
    [X.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
    [(f.smallEtaleBaseChange.sheafPushforwardContinuous A
      Y.smallEtaleTopology X.smallEtaleTopology).IsRightAdjoint] :
    PreservesFiniteLimits (f.smallEtalePullback A) where
  preservesFiniteLimits _ _ _ := ⟨fun {_} ↦ ⟨fun {_} hc ↦
    ⟨((isConservativeFamilyOfPoints_pointSmallEtale' X).jointlyReflectIsomorphisms A)
      |>.jointlyReflectsLimit fun Φ ↦ Classical.choice (by
        obtain ⟨_, ⟨s⟩⟩ := Φ
        exact ⟨IsLimit.mapConeEquiv (f.smallEtalePullbackCompSheafFiberIso _ A).symm
          (isLimitOfPreserves (pointSmallEtale (_ ≫ f)).sheafFiber hc)⟩)⟩⟩⟩

end Stalk

section EtaleRestriction

variable {X Y S : Scheme.{u}}

/-- For an étale morphism `f : X ⟶ Y`, post-composition with `f` defines a functor
`X.Etale ⥤ Y.Etale` left adjoint to `f.smallEtaleBaseChange`. -/
abbrev Hom.smallEtaleMap (f : X ⟶ Y) [AlgebraicGeometry.Etale f] : X.Etale ⥤ Y.Etale :=
  MorphismProperty.Over.map (P := @AlgebraicGeometry.Etale) ⊤
    (inferInstance : AlgebraicGeometry.Etale f)

/-- For an étale morphism `f : X ⟶ Y`, `f.smallEtaleMap` preserves coverings for the small étale
topologies. -/
lemma Hom.coverPreserving_smallEtaleMap (f : X ⟶ Y) [AlgebraicGeometry.Etale f] :
    CoverPreserving X.smallEtaleTopology Y.smallEtaleTopology f.smallEtaleMap :=
  have := locallyCoverDense_over_forget_etale Y
  have := locallyCoverDense_over_forget_etale X
  MorphismProperty.coverPreserving_over_map (P := @AlgebraicGeometry.Etale) etaleTopology
    (inferInstance : AlgebraicGeometry.Etale f)

instance Hom.isContinuous_smallEtaleMap (f : X ⟶ Y) [AlgebraicGeometry.Etale f] :
    f.smallEtaleMap.IsContinuous X.smallEtaleTopology Y.smallEtaleTopology :=
  have := locallyCoverDense_over_forget_etale Y
  have := locallyCoverDense_over_forget_etale X
  MorphismProperty.isContinuous_over_map (P := @AlgebraicGeometry.Etale) etaleTopology
    (inferInstance : AlgebraicGeometry.Etale f)

/-- When `f : X ⟶ Y` is étale, `f.smallEtaleMap : X.Etale ⥤ Y.Etale` is left adjoint to
`f.smallEtaleBaseChange`. -/
noncomputable def Hom.smallEtaleMapPullbackAdj (f : X ⟶ Y) [AlgebraicGeometry.Etale f] :
    f.smallEtaleMap ⊣ f.smallEtaleBaseChange :=
  MorphismProperty.Over.mapPullbackAdj @AlgebraicGeometry.Etale ⊤ f inferInstance trivial

/-- When `f : X ⟶ Y` is étale, `f.smallEtaleMap` is left adjoint to `f.smallEtaleBaseChange`, so
`f.smallEtalePullback A` identifies naturally with restriction (sheaf pushforward) along
`f.smallEtaleMap`. -/
noncomputable def Hom.smallEtalePullbackIsoPushforwardOfEtale (f : X ⟶ Y)
    [AlgebraicGeometry.Etale f] (A : Type u') [Category.{v'} A]
    [(f.smallEtaleBaseChange.sheafPushforwardContinuous A
      Y.smallEtaleTopology X.smallEtaleTopology).IsRightAdjoint] :
    f.smallEtalePullback A ≅
      f.smallEtaleMap.sheafPushforwardContinuous A X.smallEtaleTopology Y.smallEtaleTopology :=
  Adjunction.leftAdjointUniq (f.smallEtaleAdjunction A)
    (f.smallEtaleMapPullbackAdj.sheafPushforwardContinuous
      X.smallEtaleTopology Y.smallEtaleTopology)

/-- For `U : S.Etale`, sheaves on the slice étale site `(S.Etale / U, S.smallEtaleTopology.over U)`
are equivalent to étale sheaves on `U.left`. -/
noncomputable def Etale.overSheafEquiv (U : S.Etale) (A : Type u') [Category.{v'} A] :
    Sheaf (S.smallEtaleTopology.over U) A ≌ Sheaf U.left.smallEtaleTopology A :=
  have := locallyCoverDense_over_forget_etale S
  have := locallyCoverDense_over_forget_etale U.left
  MorphismProperty.overRestrictedSheafEquiv (P := @AlgebraicGeometry.Etale) etaleTopology U A

/-- Under `Etale.overSheafEquiv U A`, restricting an étale sheaf on `S` to the slice site over `U`
identifies with pulling it back along the étale structure morphism `U.left ↘ S`. -/
noncomputable def Etale.overPullbackCompOverSheafEquivIso (U : S.Etale)
    (A : Type u') [Category.{v'} A]
    [((Hom.smallEtaleBaseChange (U.left ↘ S)).sheafPushforwardContinuous A
      S.smallEtaleTopology U.left.smallEtaleTopology).IsRightAdjoint] :
    S.smallEtaleTopology.overPullback A U ⋙ (Etale.overSheafEquiv U A).functor ≅
      Hom.smallEtalePullback (U.left ↘ S) A :=
  have := locallyCoverDense_over_forget_etale S
  have := locallyCoverDense_over_forget_etale U.left
  MorphismProperty.overPullbackCompOverRestrictedSheafEquivIso
    (P := @AlgebraicGeometry.Etale) etaleTopology U A ≪≫
    (Hom.smallEtalePullbackIsoPushforwardOfEtale (U.left ↘ S) A).symm

end EtaleRestriction

end AlgebraicGeometry.Scheme

namespace CategoryTheory.Sheaf

open AlgebraicGeometry AlgebraicGeometry.Scheme

section LocallyConstant

variable {S X Y : Scheme.{u}} {A : Type u'} [Category.{v'} A]

/-- On the small étale site of `S`, a morphism `g : U ⟶ V` belongs to `F.locallyConstantSieve P V`
if and only if `(U.left ↘ S)^* F` is isomorphic on `U.left` to a constant étale sheaf with value in
`P`. -/
lemma mem_locallyConstantSieve_smallEtaleTopology_iff
    [HasWeakSheafify S.smallEtaleTopology A]
    (P : ObjectProperty A) (F : Sheaf S.smallEtaleTopology A)
    {U V : S.Etale} (g : U ⟶ V)
    [HasWeakSheafify U.left.smallEtaleTopology A]
    [((Hom.smallEtaleBaseChange (U.left ↘ S)).sheafPushforwardContinuous A
      S.smallEtaleTopology U.left.smallEtaleTopology).IsRightAdjoint] :
    F.locallyConstantSieve P V g ↔
      ∃ M, P M ∧ Nonempty ((Hom.smallEtalePullback (U.left ↘ S) A).obj F ≅
        (constantSheaf U.left.smallEtaleTopology A).obj M) := by
  rw [locallyConstantSieve_apply]
  refine exists_congr fun M ↦ and_congr_right fun _ ↦ ⟨fun ⟨e⟩ ↦ ?_, fun ⟨e⟩ ↦ ?_⟩
  · exact ⟨((Etale.overPullbackCompOverSheafEquivIso U A).app F).symm ≪≫
      (Etale.overSheafEquiv U A).functor.mapIso e ≪≫
      (Etale.overPullbackCompOverSheafEquivIso U A).app _ ≪≫
      Hom.smallEtalePullbackConstantSheafIso (U.left ↘ S) A M⟩
  · exact ⟨(Etale.overSheafEquiv U A).functor.preimageIso
      ((Etale.overPullbackCompOverSheafEquivIso U A).app F ≪≫ e ≪≫
        (Hom.smallEtalePullbackConstantSheafIso (U.left ↘ S) A M).symm ≪≫
        ((Etale.overPullbackCompOverSheafEquivIso U A).app _).symm)⟩

variable [∀ T : Scheme.{u}, HasWeakSheafify T.smallEtaleTopology A]
  [∀ {T₁ T₂ : Scheme.{u}} (h : T₁ ⟶ T₂),
    (h.smallEtaleBaseChange.sheafPushforwardContinuous A
      T₂.smallEtaleTopology T₁.smallEtaleTopology).IsRightAdjoint]

/-- **Base-change stability of locally constant étale sheaves.** The pullback of a locally constant
étale sheaf with values in `P` along an arbitrary morphism of schemes `f : X ⟶ Y` is locally
constant with values in `P`. -/
theorem IsLocallyConstantIn.smallEtalePullback {P : ObjectProperty A}
    {F : Sheaf Y.smallEtaleTopology A}
    (hF : F.IsLocallyConstantIn Y.smallEtaleTopology P) (f : X ⟶ Y) :
    ((f.smallEtalePullback A).obj F).IsLocallyConstantIn X.smallEtaleTopology P := by
  have hTY : IsTerminal (Etale.mk (𝟙 Y)) :=
    IsTerminal.isTerminalOfObj (Etale.forget Y) _ CategoryTheory.Over.mkIdTerminal
  have hTX : IsTerminal (f.smallEtaleBaseChange.obj (Etale.mk (𝟙 Y))) :=
    IsTerminal.isTerminalObj f.smallEtaleBaseChange _ hTY
  rw [isLocallyConstantIn_iff_of_isTerminal P _ hTX]
  refine X.smallEtaleTopology.superset_covering ?_
    (f.coverPreserving_smallEtaleBaseChange.cover_preserve
      ((isLocallyConstantIn_iff P F).mp hF (Etale.mk (𝟙 Y))))
  rintro W _ ⟨V, u, k, hk, rfl⟩
  refine (((f.smallEtalePullback A).obj F).locallyConstantSieve P _).downward_closed ?_ k
  rw [mem_locallyConstantSieve_smallEtaleTopology_iff] at hk ⊢
  obtain ⟨M, hM, ⟨eV⟩⟩ := hk
  obtain ⟨π₁, hπ₁⟩ := f.exists_hom_comp_eq_of_smallEtaleBaseChange V
  refine ⟨M, hM, ⟨?_⟩⟩
  exact ((Hom.smallEtalePullbackComp ((f.smallEtaleBaseChange.obj V).left ↘ X) f A).app F).symm ≪≫
    ((Hom.smallEtalePullbackCongr hπ₁.symm A).app F) ≪≫
    ((Hom.smallEtalePullbackComp π₁ (V.left ↘ Y) A).app F) ≪≫
    (π₁.smallEtalePullback A).mapIso eV ≪≫
    π₁.smallEtalePullbackConstantSheafIso A M

/-- **Étale descent of local constancy.** For a jointly surjective family of étale morphisms
`g i : U i ⟶ S`, an étale sheaf `F` on `S` is locally constant with values in `P` if and only if
each pullback `(g i)^* F` is locally constant with values in `P` on `U i`. -/
theorem isLocallyConstantIn_smallEtaleTopology_iff_of_iUnion_range_eq_univ
    {P : ObjectProperty A} (F : Sheaf S.smallEtaleTopology A)
    {ι : Type*} {U : ι → Scheme.{u}} (g : ∀ i, U i ⟶ S) [∀ i, AlgebraicGeometry.Etale (g i)]
    (hg : ⋃ i, Set.range (g i) = .univ) :
    F.IsLocallyConstantIn S.smallEtaleTopology P ↔
      ∀ i, (((g i).smallEtalePullback A).obj F).IsLocallyConstantIn (U i).smallEtaleTopology P := by
  refine ⟨fun hF i ↦ hF.smallEtalePullback (g i), fun h ↦ ?_⟩
  have hTS : IsTerminal (Etale.mk (𝟙 S)) :=
    IsTerminal.isTerminalOfObj (Etale.forget S) _ CategoryTheory.Over.mkIdTerminal
  let φ : ∀ i, Etale.mk (g i) ⟶ Etale.mk (𝟙 S) :=
    fun i ↦ MorphismProperty.Over.homMk (g i) (Category.comp_id (g i))
  have hφ : Sieve.ofArrows _ φ ∈ S.smallEtaleTopology (Etale.mk (𝟙 S)) := by
    rw [ofArrows_mem_smallEtaleTopology_iff]
    exact hg
  rw [isLocallyConstantIn_iff_of_sieve_mem_of_isTerminal P F hTS hφ]
  rintro W _ ⟨Z, u, _, ⟨i⟩, rfl⟩
  rw [← F.pullback_locallyConstantSieve P u]
  apply S.smallEtaleTopology.pullback_stable
  let eᵢ : (g i).smallEtaleMap.obj (Etale.mk (𝟙 (U i))) ≅ Etale.mk (g i) :=
    (MorphismProperty.Over.isoMk (Iso.refl _) rfl :
      (g i).smallEtaleMap.obj (Etale.mk (𝟙 (U i))) ≅ Etale.mk (g i))
  rw [← F.pullback_locallyConstantSieve P eᵢ.inv]
  apply S.smallEtaleTopology.pullback_stable
  refine S.smallEtaleTopology.superset_covering ?_
    ((g i).coverPreserving_smallEtaleMap.cover_preserve
      ((isLocallyConstantIn_iff P _).mp (h i) (Etale.mk (𝟙 (U i)))))
  rintro W' _ ⟨V, v, k, hk, rfl⟩
  refine (F.locallyConstantSieve P _).downward_closed ?_ k
  rw [mem_locallyConstantSieve_smallEtaleTopology_iff] at hk ⊢
  obtain ⟨M, hM, ⟨eV⟩⟩ := hk
  -- `MorphismProperty.Over.map` is a `def`, so `((g i).smallEtaleMap.obj V).left` and `V.left`
  -- agree at `default` transparency, while `IsRightAdjoint` synthesis in `smallEtalePullbackComp`
  -- runs at `instances` transparency; aligning the carrier to `V.left` avoids `eqToHom`s.
  change ∃ M, P M ∧ Nonempty ((Hom.smallEtalePullback ((V.left ↘ U i) ≫ g i) A).obj F ≅
    (constantSheaf V.left.smallEtaleTopology A).obj M)
  exact ⟨M, hM, ⟨(Hom.smallEtalePullbackComp (V.left ↘ U i) (g i) A).app F ≪≫ eV⟩⟩

/-- Local constancy of an étale sheaf can be tested on any étale cover of `S`. -/
theorem isLocallyConstantIn_smallEtaleTopology_iff_of_cover
    {P : ObjectProperty A} (F : Sheaf S.smallEtaleTopology A)
    (𝒰 : S.Cover (Scheme.precoverage @AlgebraicGeometry.Etale)) :
    F.IsLocallyConstantIn S.smallEtaleTopology P ↔
      ∀ i : 𝒰.I₀, (((𝒰.f i).smallEtalePullback A).obj F).IsLocallyConstantIn
        (𝒰.X i).smallEtaleTopology P :=
  isLocallyConstantIn_smallEtaleTopology_iff_of_iUnion_range_eq_univ F 𝒰.f
    (Set.eq_univ_iff_forall.mpr fun x ↦
      Set.mem_iUnion.mpr (((ofArrows_mem_precoverage_iff _).1 𝒰.mem₀).1 x))

/-- Local constancy of an étale sheaf can be tested after pullback along any surjective étale
morphism `g : X ⟶ S`. -/
theorem isLocallyConstantIn_smallEtaleTopology_iff_of_surjective
    {P : ObjectProperty A} (F : Sheaf S.smallEtaleTopology A)
    (g : X ⟶ S) [AlgebraicGeometry.Etale g] [Surjective g] :
    F.IsLocallyConstantIn S.smallEtaleTopology P ↔
      ((g.smallEtalePullback A).obj F).IsLocallyConstantIn X.smallEtaleTopology P :=
  (isLocallyConstantIn_smallEtaleTopology_iff_of_iUnion_range_eq_univ F (fun _ : Unit ↦ g)
    (by rw [Set.range_eq_univ.mpr g.surjective, Set.iUnion_const])).trans Unique.forall_iff

end LocallyConstant

end CategoryTheory.Sheaf
