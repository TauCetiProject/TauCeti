/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Limits
public import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
public import TauCeti.AlgebraicGeometry.Morphisms.Etale.Basic
public import TauCeti.CategoryTheory.MorphismProperty.CommaSites
public import TauCeti.CategoryTheory.Sites.ConstantSheaf
public import TauCeti.CategoryTheory.Sites.LocallyConstant
public import TauCeti.CategoryTheory.Sites.Point.Comap
public import TauCeti.CategoryTheory.Sites.Pullback
import Mathlib.AlgebraicGeometry.Cover.MorphismProperty

/-!
# Pullback of étale sheaves, geometric stalks, and étale descent of local constancy

For a morphism of schemes `f : X ⟶ Y`, base change along `f` defines a functor
`f.smallEtaleBaseChange : Y.Etale ⥤ X.Etale` sending an étale `V ⟶ Y` to `V ×_Y X ⟶ X`, with first
projection `f.smallEtaleBaseChangeFst V : (f.smallEtaleBaseChange.obj V).left ⟶ V.left`. Because
`f.smallEtaleBaseChange` preserves finite limits and étale coverings, it is representably flat,
final, cover-preserving, and continuous for the small étale topologies, hence forms the site-level
functor of a morphism of sites `(X_ét) → (Y_ét)`.

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
* **Geometric stalks and left exactness**: for every geometric point `x : Spec Ω ⟶ X`, the stalk of
  `f^* F` at `x` identifies naturally with the stalk of `F` at `x ≫ f`
  (`AlgebraicGeometry.Scheme.Hom.smallEtalePullbackCompSheafFiberIso`). When `A` has finite limits,
  `u`-small products and colimits, and a `u`-concrete forgetful functor that reflects isomorphisms,
  preserves finite limits and `u`-small filtered colimits, and satisfies `HasSheafCompose` on
  `X_ét` (satisfied in particular by `Type u`, `AddCommGrpCat.{u}`, `ModuleCat.{u} Λ`, and
  `CommRingCat.{u}`), `f.smallEtalePullback A` preserves finite limits.
* **Restriction along étale morphisms and slice equivalence**: when `f : X ⟶ Y` is étale, `f^*`
  identifies with restriction (sheaf pushforward) along `MorphismProperty.Over.map ⊤ ‹Etale f›`.
  Consequently, for `U : S.Etale`, sheaves on the localized site `(S.Etale / U, J_ét/U)` are
  equivalent to étale sheaves on `U.left` (`AlgebraicGeometry.Scheme.Etale.overSheafEquiv`),
  intertwining `overPullback` with `U.hom.smallEtalePullback`.
* **Local constancy and étale locality**: `IsLocallyConstantIn S.smallEtaleTopology P` is
  characterized by constant-sheaf trivializations after `U.hom.smallEtalePullback`, is stable
  under pullback along arbitrary morphisms of schemes, and can be tested on any jointly surjective
  family of étale morphisms (in particular on any étale cover or surjective étale morphism).

## Main declarations

* `AlgebraicGeometry.Scheme.Hom.smallEtaleBaseChange` and
  `AlgebraicGeometry.Scheme.Hom.smallEtaleBaseChangeFst`: base change `Y.Etale ⥤ X.Etale` along
  `f : X ⟶ Y` and its first projection, with `AlgebraicGeometry.Scheme.smallEtaleBaseChangeId` and
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
  `Sheaf.isLocallyConstantIn_smallEtaleTopology_iff_of_etale_of_iUnion_range_eq_univ`,
  `CategoryTheory.Sheaf.isLocallyConstantIn_smallEtaleTopology_iff_of_etale_cover`, and
  `CategoryTheory.Sheaf.isLocallyConstantIn_smallEtaleTopology_iff_of_etale_of_surjective`:
  base-change stability and étale locality of the predicate `IsLocallyConstantIn`.

## References

* M. Artin, A. Grothendieck, J.-L. Verdier, *SGA 4*, Exposé VII, §1–3 (morphism of étale sites),
  Exposé VIII, §3 (stalks of inverse images), and Exposé IX, §2 (locally constant sheaves).
* The Stacks Project, Lemmas 34.4.17–34.4.18
  ([Tag 021I](https://stacks.math.columbia.edu/tag/021I) and
  [Tag 021J](https://stacks.math.columbia.edu/tag/021J), functoriality of the small étale site)
  and Section 59.64 ([Tag 03RV](https://stacks.math.columbia.edu/tag/03RV), locally constant étale
  sheaves).
-/

public section

universe u v' u'

open CategoryTheory Limits Opposite MorphismProperty

namespace AlgebraicGeometry.Scheme

section BaseChange

variable {X Y Z : Scheme.{u}}

/-- The identity morphism `𝟙 S`, viewed as an object of the small étale site `S.Etale`, is
terminal. -/
noncomputable def Etale.mkIdTerminal (S : Scheme.{u}) : IsTerminal (Etale.mk (𝟙 S)) :=
  have : MorphismProperty.ContainsIdentities @AlgebraicGeometry.Etale :=
    MorphismProperty.IsMultiplicative.toContainsIdentities
  MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale S

/-- Base change along `f : X ⟶ Y`, from schemes étale over `Y` to schemes étale over `X`: an étale
`V ⟶ Y` is sent to `V ×_Y X ⟶ X`. -/
noncomputable def Hom.smallEtaleBaseChange (f : X ⟶ Y) : Y.Etale ⥤ X.Etale :=
  MorphismProperty.Over.pullback @Etale ⊤ f

lemma Hom.smallEtaleBaseChange_eq (f : X ⟶ Y) :
    f.smallEtaleBaseChange = MorphismProperty.Over.pullback @Etale ⊤ f :=
  (rfl)

/-- The first projection `(V ×_Y X) ⟶ V` of the base change of `V : Y.Etale` along `f : X ⟶ Y`. -/
noncomputable def Hom.smallEtaleBaseChangeFst (f : X ⟶ Y) (V : Y.Etale) :
    (f.smallEtaleBaseChange.obj V).left ⟶ V.left :=
  pullback.fst V.hom f

@[reassoc (attr := simp)]
lemma Hom.smallEtaleBaseChangeFst_hom (f : X ⟶ Y) (V : Y.Etale) :
    f.smallEtaleBaseChangeFst V ≫ V.hom =
      (f.smallEtaleBaseChange.obj V).hom ≫ f :=
  pullback.condition

/-- For `V : Y.Etale`, `f.smallEtaleBaseChange.obj V` together with `f.smallEtaleBaseChangeFst V`
and its structure morphism to `X` forms a pullback square over `V.left ↘ Y` and `f`. -/
lemma Hom.isPullback_smallEtaleBaseChange (f : X ⟶ Y) (V : Y.Etale) :
    IsPullback (f.smallEtaleBaseChangeFst V) ((f.smallEtaleBaseChange.obj V).left ↘ X)
      (V.left ↘ Y) f :=
  IsPullback.of_hasPullback V.hom f

@[reassoc (attr := simp)]
lemma Hom.smallEtaleBaseChange_map_left_fst (f : X ⟶ Y) {U V : Y.Etale} (g : U ⟶ V) :
    (f.smallEtaleBaseChange.map g).left ≫ f.smallEtaleBaseChangeFst V =
      f.smallEtaleBaseChangeFst U ≫ g.left := by
  dsimp [Hom.smallEtaleBaseChange, MorphismProperty.Over.pullback, Hom.smallEtaleBaseChangeFst]
  exact pullback.lift_fst _ _ _

/-- On underlying schemes over `X`, `f.smallEtaleBaseChange` is base change along `f`. -/
noncomputable def Hom.smallEtaleBaseChangeCompForgetIso (f : X ⟶ Y) :
    f.smallEtaleBaseChange ⋙ Etale.forget X ≅ Etale.forget Y ⋙ CategoryTheory.Over.pullback f :=
  Iso.refl _

@[reassoc (attr := simp)]
lemma Hom.smallEtaleBaseChangeCompForgetIso_hom_app_left_fst (f : X ⟶ Y) (V : Y.Etale) :
    ((f.smallEtaleBaseChangeCompForgetIso.hom.app V).left :
      (f.smallEtaleBaseChange.obj V).left ⟶ pullback V.hom f) ≫
      pullback.fst V.hom f = f.smallEtaleBaseChangeFst V :=
  Category.id_comp _

@[reassoc (attr := simp)]
lemma Hom.smallEtaleBaseChangeCompForgetIso_inv_app_left_fst (f : X ⟶ Y) (V : Y.Etale) :
    ((f.smallEtaleBaseChangeCompForgetIso.inv.app V).left :
      pullback V.hom f ⟶ (f.smallEtaleBaseChange.obj V).left) ≫
      f.smallEtaleBaseChangeFst V = pullback.fst V.hom f :=
  Category.id_comp _

/-- Base change along `𝟙 X` on `X.Etale` identifies naturally with the identity functor. -/
noncomputable def smallEtaleBaseChangeId (X : Scheme.{u}) :
    Hom.smallEtaleBaseChange (𝟙 X) ≅ 𝟭 X.Etale :=
  MorphismProperty.Over.pullbackId @Etale X

@[simp]
lemma smallEtaleBaseChangeId_hom_app_left (X : Scheme.{u}) (V : X.Etale) :
    ((smallEtaleBaseChangeId X).hom.app V).left = Hom.smallEtaleBaseChangeFst (𝟙 X) V :=
  MorphismProperty.Over.pullbackId_hom_app_left (P := @AlgebraicGeometry.Etale) X V

@[reassoc (attr := simp)]
lemma smallEtaleBaseChangeId_inv_app_left_fst (X : Scheme.{u}) (V : X.Etale) :
    ((smallEtaleBaseChangeId X).inv.app V).left ≫ Hom.smallEtaleBaseChangeFst (𝟙 X) V =
      𝟙 V.left :=
  MorphismProperty.Over.pullbackId_inv_app_left_fst (P := @AlgebraicGeometry.Etale) X V

/-- Base change on small étale sites commutes with composition up to natural isomorphism. -/
noncomputable def Hom.smallEtaleBaseChangeComp (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).smallEtaleBaseChange ≅ g.smallEtaleBaseChange ⋙ f.smallEtaleBaseChange :=
  MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) f g

@[reassoc (attr := simp)]
lemma Hom.smallEtaleBaseChangeComp_hom_app_left_fst_fst (f : X ⟶ Y) (g : Y ⟶ Z) (V : Z.Etale) :
    ((f.smallEtaleBaseChangeComp g).hom.app V).left ≫
      f.smallEtaleBaseChangeFst (g.smallEtaleBaseChange.obj V) ≫ g.smallEtaleBaseChangeFst V =
        (f ≫ g).smallEtaleBaseChangeFst V := by
  change (pullback.congrHom (rfl : V.hom = V.hom) (rfl : f ≫ g = f ≫ g) ≪≫
      (pullbackLeftPullbackSndIso V.hom g f).symm).hom ≫
    pullback.fst (pullback.snd V.hom g) f ≫ pullback.fst V.hom g =
      pullback.fst V.hom (f ≫ g)
  simp

@[reassoc (attr := simp)]
lemma Hom.smallEtaleBaseChangeComp_inv_app_left_fst (f : X ⟶ Y) (g : Y ⟶ Z) (V : Z.Etale) :
    ((f.smallEtaleBaseChangeComp g).inv.app V).left ≫ (f ≫ g).smallEtaleBaseChangeFst V =
      f.smallEtaleBaseChangeFst (g.smallEtaleBaseChange.obj V) ≫ g.smallEtaleBaseChangeFst V := by
  rw [← Hom.smallEtaleBaseChangeComp_hom_app_left_fst_fst]
  have h := congrArg (fun k : (g.smallEtaleBaseChange ⋙ f.smallEtaleBaseChange).obj V ⟶
      (g.smallEtaleBaseChange ⋙ f.smallEtaleBaseChange).obj V ↦ k.left)
    ((f.smallEtaleBaseChangeComp g).inv_hom_id_app V)
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ _) h).trans (Category.id_comp _))

/-- Equal morphisms of schemes induce naturally isomorphic base-change functors on small étale
sites. -/
noncomputable def Hom.smallEtaleBaseChangeCongr {f g : X ⟶ Y} (h : f = g) :
    f.smallEtaleBaseChange ≅ g.smallEtaleBaseChange :=
  MorphismProperty.Over.pullbackCongr (P := @Etale) (Q := ⊤) h

@[reassoc (attr := simp)]
lemma Hom.smallEtaleBaseChangeCongr_hom_app_left_fst {f g : X ⟶ Y} (h : f = g) (V : Y.Etale) :
    ((Hom.smallEtaleBaseChangeCongr h).hom.app V).left ≫ g.smallEtaleBaseChangeFst V =
      f.smallEtaleBaseChangeFst V := by
  subst h
  change (pullback.congrHom (rfl : V.hom = V.hom) (rfl : f = f)).hom ≫
    pullback.fst V.hom f = pullback.fst V.hom f
  simp

@[reassoc (attr := simp)]
lemma Hom.smallEtaleBaseChangeCongr_inv_app_left_fst {f g : X ⟶ Y} (h : f = g) (V : Y.Etale) :
    ((Hom.smallEtaleBaseChangeCongr h).inv.app V).left ≫ f.smallEtaleBaseChangeFst V =
      g.smallEtaleBaseChangeFst V := by
  subst h
  change (pullback.congrHom (rfl : V.hom = V.hom) (rfl : f = f)).inv ≫
    pullback.fst V.hom f = pullback.fst V.hom f
  simp

@[simp]
lemma Hom.smallEtaleBaseChangeCongr_refl (f : X ⟶ Y) :
    Hom.smallEtaleBaseChangeCongr (rfl : f = f) = Iso.refl f.smallEtaleBaseChange := by
  ext V
  apply MorphismProperty.Over.Hom.ext
  change (pullback.congrHom (rfl : V.hom = V.hom) (rfl : f = f)).hom = 𝟙 (pullback V.hom f)
  simp

instance Hom.preservesFiniteLimits_smallEtaleBaseChange (f : X ⟶ Y) :
    PreservesFiniteLimits f.smallEtaleBaseChange :=
  MorphismProperty.Over.instPreservesFiniteLimitsTopPullback (P := @AlgebraicGeometry.Etale) f

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
noncomputable abbrev Hom.smallEtaleAdjunction (f : X ⟶ Y) (A : Type u') [Category.{v'} A]
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

lemma smallEtalePullbackId_eq (X : Scheme.{u}) (A : Type u') [Category.{v'} A]
    [((Hom.smallEtaleBaseChange (𝟙 X)).sheafPushforwardContinuous A
      X.smallEtaleTopology X.smallEtaleTopology).IsRightAdjoint] :
    smallEtalePullbackId X A =
      Functor.sheafPullbackId' A X.smallEtaleTopology (smallEtaleBaseChangeId X) :=
  (rfl)

@[simp]
lemma conjugateEquiv_smallEtalePullbackId_hom (X : Scheme.{u}) (A : Type u') [Category.{v'} A]
    [((Hom.smallEtaleBaseChange (𝟙 X)).sheafPushforwardContinuous A
      X.smallEtaleTopology X.smallEtaleTopology).IsRightAdjoint] :
    conjugateEquiv Adjunction.id (Hom.smallEtaleAdjunction (𝟙 X) A)
      (smallEtalePullbackId X A).hom =
      (Functor.sheafPushforwardContinuousId' (smallEtaleBaseChangeId X)
        A X.smallEtaleTopology).inv := by
  rw [smallEtalePullbackId_eq, Functor.sheafPullbackId'_eq, Iso.trans_hom,
    ← conjugateEquiv_comp, Functor.conjugateEquiv_sheafPullbackId_hom,
    Functor.conjugateEquiv_sheafPullbackIso_hom]
  rfl

@[simp]
lemma conjugateEquiv_smallEtalePullbackId_inv (X : Scheme.{u}) (A : Type u') [Category.{v'} A]
    [((Hom.smallEtaleBaseChange (𝟙 X)).sheafPushforwardContinuous A
      X.smallEtaleTopology X.smallEtaleTopology).IsRightAdjoint] :
    conjugateEquiv (Hom.smallEtaleAdjunction (𝟙 X) A) Adjunction.id
      (smallEtalePullbackId X A).inv =
      (Functor.sheafPushforwardContinuousId' (smallEtaleBaseChangeId X)
        A X.smallEtaleTopology).hom := by
  rw [smallEtalePullbackId_eq, Functor.sheafPullbackId'_eq, Iso.trans_inv,
    ← conjugateEquiv_comp, Functor.conjugateEquiv_sheafPullbackIso_inv,
    Functor.conjugateEquiv_sheafPullbackId_inv]
  rfl

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

lemma Hom.smallEtalePullbackComp_eq (f : X ⟶ Y) (g : Y ⟶ Z)
    (A : Type u') [Category.{v'} A]
    [(f.smallEtaleBaseChange.sheafPushforwardContinuous A
      Y.smallEtaleTopology X.smallEtaleTopology).IsRightAdjoint]
    [(g.smallEtaleBaseChange.sheafPushforwardContinuous A
      Z.smallEtaleTopology Y.smallEtaleTopology).IsRightAdjoint]
    [((f ≫ g).smallEtaleBaseChange.sheafPushforwardContinuous A
      Z.smallEtaleTopology X.smallEtaleTopology).IsRightAdjoint] :
    f.smallEtalePullbackComp g A =
      Functor.sheafPullbackComp' A Z.smallEtaleTopology Y.smallEtaleTopology X.smallEtaleTopology
        (f.smallEtaleBaseChangeComp g).symm :=
  (rfl)

@[simp]
lemma Hom.conjugateEquiv_smallEtalePullbackComp_hom (f : X ⟶ Y) (g : Y ⟶ Z)
    (A : Type u') [Category.{v'} A]
    [(f.smallEtaleBaseChange.sheafPushforwardContinuous A
      Y.smallEtaleTopology X.smallEtaleTopology).IsRightAdjoint]
    [(g.smallEtaleBaseChange.sheafPushforwardContinuous A
      Z.smallEtaleTopology Y.smallEtaleTopology).IsRightAdjoint]
    [((f ≫ g).smallEtaleBaseChange.sheafPushforwardContinuous A
      Z.smallEtaleTopology X.smallEtaleTopology).IsRightAdjoint] :
    conjugateEquiv ((g.smallEtaleAdjunction A).comp (f.smallEtaleAdjunction A))
      ((f ≫ g).smallEtaleAdjunction A)
      (f.smallEtalePullbackComp g A).hom =
      (Functor.sheafPushforwardContinuousComp' (f.smallEtaleBaseChangeComp g).symm
        A Z.smallEtaleTopology Y.smallEtaleTopology X.smallEtaleTopology).hom := by
  have := Functor.isContinuous_comp g.smallEtaleBaseChange f.smallEtaleBaseChange
    Z.smallEtaleTopology Y.smallEtaleTopology X.smallEtaleTopology
  have := Functor.isRightAdjoint_sheafPushforwardContinuous_comp A
    Z.smallEtaleTopology Y.smallEtaleTopology X.smallEtaleTopology
    g.smallEtaleBaseChange f.smallEtaleBaseChange
  rw [Hom.smallEtalePullbackComp_eq, Functor.sheafPullbackComp'_eq, Iso.trans_hom,
    ← conjugateEquiv_comp, Functor.conjugateEquiv_sheafPullbackComp_hom,
    Functor.conjugateEquiv_sheafPullbackIso_hom]
  rfl

@[simp]
lemma Hom.conjugateEquiv_smallEtalePullbackComp_inv (f : X ⟶ Y) (g : Y ⟶ Z)
    (A : Type u') [Category.{v'} A]
    [(f.smallEtaleBaseChange.sheafPushforwardContinuous A
      Y.smallEtaleTopology X.smallEtaleTopology).IsRightAdjoint]
    [(g.smallEtaleBaseChange.sheafPushforwardContinuous A
      Z.smallEtaleTopology Y.smallEtaleTopology).IsRightAdjoint]
    [((f ≫ g).smallEtaleBaseChange.sheafPushforwardContinuous A
      Z.smallEtaleTopology X.smallEtaleTopology).IsRightAdjoint] :
    conjugateEquiv ((f ≫ g).smallEtaleAdjunction A)
      ((g.smallEtaleAdjunction A).comp (f.smallEtaleAdjunction A))
      (f.smallEtalePullbackComp g A).inv =
      (Functor.sheafPushforwardContinuousComp' (f.smallEtaleBaseChangeComp g).symm
        A Z.smallEtaleTopology Y.smallEtaleTopology X.smallEtaleTopology).inv := by
  have := Functor.isContinuous_comp g.smallEtaleBaseChange f.smallEtaleBaseChange
    Z.smallEtaleTopology Y.smallEtaleTopology X.smallEtaleTopology
  have := Functor.isRightAdjoint_sheafPushforwardContinuous_comp A
    Z.smallEtaleTopology Y.smallEtaleTopology X.smallEtaleTopology
    g.smallEtaleBaseChange f.smallEtaleBaseChange
  rw [Hom.smallEtalePullbackComp_eq, Functor.sheafPullbackComp'_eq, Iso.trans_inv,
    ← conjugateEquiv_comp, Functor.conjugateEquiv_sheafPullbackIso_inv,
    Functor.conjugateEquiv_sheafPullbackComp_inv]
  rfl

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

lemma Hom.smallEtalePullbackCongr_eq {f g : X ⟶ Y} (h : f = g)
    (A : Type u') [Category.{v'} A]
    [(f.smallEtaleBaseChange.sheafPushforwardContinuous A
      Y.smallEtaleTopology X.smallEtaleTopology).IsRightAdjoint]
    [(g.smallEtaleBaseChange.sheafPushforwardContinuous A
      Y.smallEtaleTopology X.smallEtaleTopology).IsRightAdjoint] :
    Hom.smallEtalePullbackCongr h A =
      Functor.sheafPullbackIso A Y.smallEtaleTopology X.smallEtaleTopology
        (Hom.smallEtaleBaseChangeCongr h) :=
  (rfl)

@[simp]
lemma Hom.conjugateEquiv_smallEtalePullbackCongr_hom {f g : X ⟶ Y} (h : f = g)
    (A : Type u') [Category.{v'} A]
    [(f.smallEtaleBaseChange.sheafPushforwardContinuous A
      Y.smallEtaleTopology X.smallEtaleTopology).IsRightAdjoint]
    [(g.smallEtaleBaseChange.sheafPushforwardContinuous A
      Y.smallEtaleTopology X.smallEtaleTopology).IsRightAdjoint] :
    conjugateEquiv (g.smallEtaleAdjunction A) (f.smallEtaleAdjunction A)
      (Hom.smallEtalePullbackCongr h A).hom =
      Functor.sheafPushforwardContinuousNatTrans (Hom.smallEtaleBaseChangeCongr h).hom
        A Y.smallEtaleTopology X.smallEtaleTopology :=
  Functor.conjugateEquiv_sheafPullbackIso_hom _ _ _ (Hom.smallEtaleBaseChangeCongr h)

@[simp]
lemma Hom.conjugateEquiv_smallEtalePullbackCongr_inv {f g : X ⟶ Y} (h : f = g)
    (A : Type u') [Category.{v'} A]
    [(f.smallEtaleBaseChange.sheafPushforwardContinuous A
      Y.smallEtaleTopology X.smallEtaleTopology).IsRightAdjoint]
    [(g.smallEtaleBaseChange.sheafPushforwardContinuous A
      Y.smallEtaleTopology X.smallEtaleTopology).IsRightAdjoint] :
    conjugateEquiv (f.smallEtaleAdjunction A) (g.smallEtaleAdjunction A)
      (Hom.smallEtalePullbackCongr h A).inv =
      Functor.sheafPushforwardContinuousNatTrans (Hom.smallEtaleBaseChangeCongr h).inv
        A Y.smallEtaleTopology X.smallEtaleTopology :=
  Functor.conjugateEquiv_sheafPullbackIso_inv _ _ _ (Hom.smallEtaleBaseChangeCongr h)

@[simp]
lemma Hom.smallEtalePullbackCongr_refl (f : X ⟶ Y) (A : Type u') [Category.{v'} A]
    [(f.smallEtaleBaseChange.sheafPushforwardContinuous A
      Y.smallEtaleTopology X.smallEtaleTopology).IsRightAdjoint] :
    Hom.smallEtalePullbackCongr (rfl : f = f) A = Iso.refl (f.smallEtalePullback A) := by
  rw [Hom.smallEtalePullbackCongr_eq, Hom.smallEtaleBaseChangeCongr_refl,
    Functor.sheafPullbackIso_refl]

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

lemma Hom.smallEtalePullbackConstantSheafIso_hom (f : X ⟶ Y)
    (A : Type u') [Category.{v'} A]
    [HasWeakSheafify Y.smallEtaleTopology A] [HasWeakSheafify X.smallEtaleTopology A]
    [(f.smallEtaleBaseChange.sheafPushforwardContinuous A
      Y.smallEtaleTopology X.smallEtaleTopology).IsRightAdjoint]
    (M : A) :
    (f.smallEtalePullbackConstantSheafIso A M).hom =
      f.smallEtaleBaseChange.sheafPullbackConstantSheafHom A
        Y.smallEtaleTopology X.smallEtaleTopology M :=
  f.smallEtaleBaseChange.sheafPullbackConstantSheafIso_hom A
    Y.smallEtaleTopology X.smallEtaleTopology M

@[reassoc (attr := simp)]
lemma Hom.smallEtalePullbackConstantSheafIso_inv_naturality (f : X ⟶ Y)
    (A : Type u') [Category.{v'} A]
    [HasWeakSheafify Y.smallEtaleTopology A] [HasWeakSheafify X.smallEtaleTopology A]
    [(f.smallEtaleBaseChange.sheafPushforwardContinuous A
      Y.smallEtaleTopology X.smallEtaleTopology).IsRightAdjoint]
    {M N : A} (φ : M ⟶ N) :
    (constantSheaf X.smallEtaleTopology A).map φ ≫
      (f.smallEtalePullbackConstantSheafIso A N).inv =
      (f.smallEtalePullbackConstantSheafIso A M).inv ≫
        (f.smallEtalePullback A).map ((constantSheaf Y.smallEtaleTopology A).map φ) :=
  f.smallEtaleBaseChange.sheafPullbackConstantSheafIso_inv_naturality A
    Y.smallEtaleTopology X.smallEtaleTopology φ

@[reassoc (attr := simp)]
lemma Hom.smallEtalePullbackConstantSheafIso_hom_naturality (f : X ⟶ Y)
    (A : Type u') [Category.{v'} A]
    [HasWeakSheafify Y.smallEtaleTopology A] [HasWeakSheafify X.smallEtaleTopology A]
    [(f.smallEtaleBaseChange.sheafPushforwardContinuous A
      Y.smallEtaleTopology X.smallEtaleTopology).IsRightAdjoint]
    {M N : A} (φ : M ⟶ N) :
    (f.smallEtalePullback A).map ((constantSheaf Y.smallEtaleTopology A).map φ) ≫
      (f.smallEtalePullbackConstantSheafIso A N).hom =
      (f.smallEtalePullbackConstantSheafIso A M).hom ≫
        (constantSheaf X.smallEtaleTopology A).map φ := by
  rw [← Iso.eq_comp_inv, Category.assoc, ← Iso.inv_comp_eq]
  exact (f.smallEtalePullbackConstantSheafIso_inv_naturality A φ).symm

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
  Functor.isoWhiskerRight f.smallEtaleBaseChangeCompForgetIso
    (coyoneda.obj (op (CategoryTheory.Over.mk x))) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (Etale.forget Y)
      (((CategoryTheory.Over.mapPullbackAdj f).compCoyonedaIso.app
        (op (CategoryTheory.Over.mk x))).symm ≪≫ coyoneda.mapIso e₀.op.symm)

@[simp]
lemma Hom.smallEtaleBaseChangeCompPointSmallEtaleFiberIso_hom_app_left
    (V : Y.Etale) (u : (pointSmallEtale x).fiber.obj (f.smallEtaleBaseChange.obj V)) : dsimp%
    ((f.smallEtaleBaseChangeCompPointSmallEtaleFiberIso x).hom.app V u).left =
      u.left ≫ f.smallEtaleBaseChangeFst V :=
  (Category.id_comp _).trans (congrArg (· ≫ pullback.fst V.hom f) (Category.comp_id u.left))

@[simp]
lemma Hom.smallEtaleBaseChangeCompPointSmallEtaleFiberIso_inv_app_left_fst
    (V : Y.Etale) (v : (pointSmallEtale (x ≫ f)).fiber.obj V) : dsimp%
    ((f.smallEtaleBaseChangeCompPointSmallEtaleFiberIso x).inv.app V v).left ≫
      f.smallEtaleBaseChangeFst V = v.left :=
  (Hom.smallEtaleBaseChangeCompPointSmallEtaleFiberIso_hom_app_left f x V
    ((f.smallEtaleBaseChangeCompPointSmallEtaleFiberIso x).inv.app V v)).symm.trans
    (congrArg (fun w : (pointSmallEtale (x ≫ f)).fiber.obj V ↦ w.left)
      (CategoryTheory.types_congr_hom
        ((f.smallEtaleBaseChangeCompPointSmallEtaleFiberIso x).inv_hom_id_app V) v))

@[simp]
lemma Hom.smallEtaleBaseChangeCompPointSmallEtaleFiberIso_inv_app_left_fst_assoc
    (V : Y.Etale) (v : (pointSmallEtale (x ≫ f)).fiber.obj V)
    {Z : Scheme.{u}} (k : V.left ⟶ Z) : dsimp%
    ((f.smallEtaleBaseChangeCompPointSmallEtaleFiberIso x).inv.app V v).left ≫
      f.smallEtaleBaseChangeFst V ≫ k = v.left ≫ k :=
  (Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ k)
      (Hom.smallEtaleBaseChangeCompPointSmallEtaleFiberIso_inv_app_left_fst f x V v))

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

lemma Hom.smallEtalePullbackCompSheafFiberIso_eq
    (A : Type u') [Category.{v'} A] [HasProducts.{u} A] [HasColimitsOfSize.{u, u} A]
    [(f.smallEtaleBaseChange.sheafPushforwardContinuous A
      Y.smallEtaleTopology X.smallEtaleTopology).IsRightAdjoint] :
    f.smallEtalePullbackCompSheafFiberIso x A =
      GrothendieckTopology.Point.sheafFiberComapIsoOfFiberIso
        (pointSmallEtale x) (pointSmallEtale (x ≫ f))
        f.smallEtaleBaseChange f.coverPreserving_smallEtaleBaseChange
        (f.smallEtaleBaseChangeCompPointSmallEtaleFiberIso x) A :=
  (rfl)

/-- Under the inverse of `Hom.smallEtalePullbackCompSheafFiberIso`, the germ of a section of
`F : Sheaf Y.smallEtaleTopology A` over `V : Y.Etale` at a lift `v` of `x ≫ f` is the germ of its
image under the `(f^*, f_*)` adjunction unit over `V ×_Y X` at the corresponding lift of `x`. -/
@[simp]
lemma Hom.toPresheafFiber_smallEtalePullbackCompSheafFiberIso_inv_app
    (A : Type u') [Category.{v'} A] [HasProducts.{u} A] [HasColimitsOfSize.{u, u} A]
    [(f.smallEtaleBaseChange.sheafPushforwardContinuous A
      Y.smallEtaleTopology X.smallEtaleTopology).IsRightAdjoint]
    (F : Sheaf Y.smallEtaleTopology A) (V : Y.Etale)
    (v : (pointSmallEtale (x ≫ f)).fiber.obj V) :
    (pointSmallEtale (x ≫ f)).toPresheafFiber V v F.obj ≫
        (f.smallEtalePullbackCompSheafFiberIso x A).inv.app F =
      ((f.smallEtaleAdjunction A).unit.app F).hom.app (op V) ≫
        (pointSmallEtale x).toPresheafFiber (f.smallEtaleBaseChange.obj V)
          ((f.smallEtaleBaseChangeCompPointSmallEtaleFiberIso x).inv.app V v)
          ((f.smallEtalePullback A).obj F).obj :=
  GrothendieckTopology.Point.toPresheafFiber_sheafFiberComapIsoOfFiberIso_inv_app
    (pointSmallEtale x) (pointSmallEtale (x ≫ f))
    f.smallEtaleBaseChange f.coverPreserving_smallEtaleBaseChange
    (f.smallEtaleBaseChangeCompPointSmallEtaleFiberIso x) A V v F

@[simp]
lemma Hom.toPresheafFiber_smallEtalePullbackCompSheafFiberIso_inv_app_assoc
    (A : Type u') [Category.{v'} A] [HasProducts.{u} A] [HasColimitsOfSize.{u, u} A]
    [(f.smallEtaleBaseChange.sheafPushforwardContinuous A
      Y.smallEtaleTopology X.smallEtaleTopology).IsRightAdjoint]
    (F : Sheaf Y.smallEtaleTopology A) (V : Y.Etale)
    (v : (pointSmallEtale (x ≫ f)).fiber.obj V)
    {Z : A} (h : (pointSmallEtale x).sheafFiber.obj ((f.smallEtalePullback A).obj F) ⟶ Z) :
    (pointSmallEtale (x ≫ f)).toPresheafFiber V v F.obj ≫
        ((f.smallEtalePullbackCompSheafFiberIso x A).inv.app F :
          _ ⟶ (pointSmallEtale x).sheafFiber.obj ((f.smallEtalePullback A).obj F)) ≫ h =
      ((f.smallEtaleAdjunction A).unit.app F).hom.app (op V) ≫
        (pointSmallEtale x).toPresheafFiber (f.smallEtaleBaseChange.obj V)
          ((f.smallEtaleBaseChangeCompPointSmallEtaleFiberIso x).inv.app V v)
          ((f.smallEtalePullback A).obj F).obj ≫ h :=
  GrothendieckTopology.Point.toPresheafFiber_sheafFiberComapIsoOfFiberIso_inv_app_assoc
    (pointSmallEtale x) (pointSmallEtale (x ≫ f))
    f.smallEtaleBaseChange f.coverPreserving_smallEtaleBaseChange
    (f.smallEtaleBaseChangeCompPointSmallEtaleFiberIso x) A V v F h

/-- Under `Hom.smallEtalePullbackCompSheafFiberIso`, the germ at `u` of the `(f^*, f_*)` unit on a
section of `F` over `V : Y.Etale` maps to the germ of that section at the corresponding lift of
`x ≫ f`. -/
@[reassoc]
lemma Hom.unit_toPresheafFiber_smallEtalePullbackCompSheafFiberIso_hom_app
    (A : Type u') [Category.{v'} A] [HasProducts.{u} A] [HasColimitsOfSize.{u, u} A]
    [(f.smallEtaleBaseChange.sheafPushforwardContinuous A
      Y.smallEtaleTopology X.smallEtaleTopology).IsRightAdjoint]
    (F : Sheaf Y.smallEtaleTopology A) (V : Y.Etale)
    (u : (pointSmallEtale x).fiber.obj (f.smallEtaleBaseChange.obj V)) :
    ((f.smallEtaleAdjunction A).unit.app F).hom.app (op V) ≫
        (pointSmallEtale x).toPresheafFiber (f.smallEtaleBaseChange.obj V) u
          ((f.smallEtalePullback A).obj F).obj ≫
        (f.smallEtalePullbackCompSheafFiberIso x A).hom.app F =
      (pointSmallEtale (x ≫ f)).toPresheafFiber V
        ((f.smallEtaleBaseChangeCompPointSmallEtaleFiberIso x).hom.app V u) F.obj :=
  GrothendieckTopology.Point.unit_toPresheafFiber_sheafFiberComapIsoOfFiberIso_hom_app
    (pointSmallEtale x) (pointSmallEtale (x ≫ f))
    f.smallEtaleBaseChange f.coverPreserving_smallEtaleBaseChange
    (f.smallEtaleBaseChangeCompPointSmallEtaleFiberIso x) A V u F

/-- **Left exactness of étale sheaf pullback.** Suppose `A` has finite limits, `u`-small products
and colimits, and a `u`-concrete forgetful functor that reflects isomorphisms, preserves finite
limits and `u`-small filtered colimits, and satisfies `HasSheafCompose` on `X.smallEtaleTopology`.
Then `f.smallEtalePullback A` preserves finite limits. -/
instance Hom.preservesFiniteLimits_smallEtalePullback
    (A : Type u') [Category.{v'} A]
    [HasFiniteLimits A] [HasProducts.{u} A] [HasColimitsOfSize.{u, u} A]
    {FC : A → A → Type*} {CC : A → Type u}
    [∀ M N, FunLike (FC M N) (CC M) (CC N)] [ConcreteCategory.{u} A FC]
    [(CategoryTheory.forget A).ReflectsIsomorphisms]
    [PreservesFiniteLimits (CategoryTheory.forget A)]
    [PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget A)]
    [X.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
    [(f.smallEtaleBaseChange.sheafPushforwardContinuous A
      Y.smallEtaleTopology X.smallEtaleTopology).IsRightAdjoint] :
    PreservesFiniteLimits (f.smallEtalePullback A) where
  preservesFiniteLimits _ _ _ :=
    have : AB5OfSize.{u, u} A :=
      ⟨fun _ _ _ ↦ HasExactColimitsOfShape.domain_of_functor _ (CategoryTheory.forget A)⟩
    ⟨fun {_} ↦ ⟨fun {_} hc ↦
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

@[reassoc (attr := simp)]
lemma Hom.smallEtaleMapPullbackAdj_unit_app_left_fst (f : X ⟶ Y) [AlgebraicGeometry.Etale f]
    (U : X.Etale) :
    (f.smallEtaleMapPullbackAdj.unit.app U).left ≫
      f.smallEtaleBaseChangeFst (f.smallEtaleMap.obj U) = 𝟙 U.left := by
  dsimp [Hom.smallEtaleMapPullbackAdj, MorphismProperty.Over.mapPullbackAdj,
    Hom.smallEtaleBaseChangeFst]
  exact pullback.lift_fst _ _ _

@[simp]
lemma Hom.smallEtaleMapPullbackAdj_counit_app_left (f : X ⟶ Y) [AlgebraicGeometry.Etale f]
    (V : Y.Etale) :
    (f.smallEtaleMapPullbackAdj.counit.app V).left = f.smallEtaleBaseChangeFst V := by
  dsimp [Hom.smallEtaleMapPullbackAdj, MorphismProperty.Over.mapPullbackAdj,
    Hom.smallEtaleBaseChangeFst]
  rfl

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

@[reassoc (attr := simp)]
lemma Hom.unit_smallEtalePullbackIsoPushforwardOfEtale_hom_app (f : X ⟶ Y)
    [AlgebraicGeometry.Etale f] (A : Type u') [Category.{v'} A]
    [(f.smallEtaleBaseChange.sheafPushforwardContinuous A
      Y.smallEtaleTopology X.smallEtaleTopology).IsRightAdjoint]
    (F : Sheaf Y.smallEtaleTopology A) :
    (f.smallEtaleAdjunction A).unit.app F ≫
      (f.smallEtaleBaseChange.sheafPushforwardContinuous A
        Y.smallEtaleTopology X.smallEtaleTopology).map
          ((f.smallEtalePullbackIsoPushforwardOfEtale A).hom.app F) =
      (f.smallEtaleMapPullbackAdj.sheafPushforwardContinuous
        X.smallEtaleTopology Y.smallEtaleTopology).unit.app F :=
  Adjunction.unit_leftAdjointUniq_hom_app _ _ F

@[reassoc (attr := simp)]
lemma Hom.smallEtalePullbackIsoPushforwardOfEtale_hom_app_counit (f : X ⟶ Y)
    [AlgebraicGeometry.Etale f] (A : Type u') [Category.{v'} A]
    [(f.smallEtaleBaseChange.sheafPushforwardContinuous A
      Y.smallEtaleTopology X.smallEtaleTopology).IsRightAdjoint]
    (F : Sheaf X.smallEtaleTopology A) :
    (f.smallEtalePullbackIsoPushforwardOfEtale A).hom.app
      ((f.smallEtaleBaseChange.sheafPushforwardContinuous A
        Y.smallEtaleTopology X.smallEtaleTopology).obj F) ≫
      (f.smallEtaleMapPullbackAdj.sheafPushforwardContinuous
        X.smallEtaleTopology Y.smallEtaleTopology).counit.app F =
      (f.smallEtaleAdjunction A).counit.app F :=
  Adjunction.leftAdjointUniq_hom_app_counit _ _ F

/-- The forward functor `(S.Etale / U) ⥤ U.left.Etale` of the iterated slice equivalence on small
étale sites. -/
def Etale.iteratedSliceForward (U : S.Etale) : CategoryTheory.Over U ⥤ U.left.Etale :=
  MorphismProperty.Over.iteratedSliceForward (P := @AlgebraicGeometry.Etale) U

/-- The backward functor `U.left.Etale ⥤ (S.Etale / U)` of the iterated slice equivalence on small
étale sites. -/
def Etale.iteratedSliceBackward (U : S.Etale) : U.left.Etale ⥤ CategoryTheory.Over U :=
  MorphismProperty.Over.iteratedSliceBackward (P := @AlgebraicGeometry.Etale) U

@[simp]
lemma Etale.iteratedSliceBackward_forget (U : S.Etale) :
    Etale.iteratedSliceBackward U ⋙ CategoryTheory.Over.forget U =
      Hom.smallEtaleMap (U.left ↘ S) :=
  MorphismProperty.Over.iteratedSliceBackward_forget (P := @AlgebraicGeometry.Etale) U

/-- For `U : S.Etale`, sheaves on the slice étale site `(S.Etale / U, S.smallEtaleTopology.over U)`
are equivalent to étale sheaves on `U.left`. -/
noncomputable def Etale.overSheafEquiv (U : S.Etale) (A : Type u') [Category.{v'} A] :
    Sheaf (S.smallEtaleTopology.over U) A ≌ Sheaf U.left.smallEtaleTopology A :=
  have := locallyCoverDense_over_forget_etale S
  have := locallyCoverDense_over_forget_etale U.left
  MorphismProperty.overRestrictedSheafEquiv (P := @AlgebraicGeometry.Etale) etaleTopology U A

@[simp]
lemma Etale.overSheafEquiv_functor_obj_obj (U : S.Etale) (A : Type u') [Category.{v'} A]
    (F : Sheaf (S.smallEtaleTopology.over U) A) :
    ((Etale.overSheafEquiv U A).functor.obj F).obj =
      (Etale.iteratedSliceBackward U).op ⋙ F.obj := by
  have := locallyCoverDense_over_forget_etale S
  have := locallyCoverDense_over_forget_etale U.left
  exact MorphismProperty.overRestrictedSheafEquiv_functor_obj_obj
    (P := @AlgebraicGeometry.Etale) etaleTopology U A F

@[simp]
lemma Etale.overSheafEquiv_inverse_obj_obj (U : S.Etale) (A : Type u') [Category.{v'} A]
    (F : Sheaf U.left.smallEtaleTopology A) :
    ((Etale.overSheafEquiv U A).inverse.obj F).obj =
      (Etale.iteratedSliceForward U).op ⋙ F.obj := by
  have := locallyCoverDense_over_forget_etale S
  have := locallyCoverDense_over_forget_etale U.left
  exact MorphismProperty.overRestrictedSheafEquiv_inverse_obj_obj
    (P := @AlgebraicGeometry.Etale) etaleTopology U A F

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

lemma Etale.overPullbackCompOverSheafEquivIso_hom_comp_smallEtalePullbackIsoPushforwardOfEtale_hom
    (U : S.Etale) (A : Type u') [Category.{v'} A]
    [((Hom.smallEtaleBaseChange (U.left ↘ S)).sheafPushforwardContinuous A
      S.smallEtaleTopology U.left.smallEtaleTopology).IsRightAdjoint]
    (F : Sheaf S.smallEtaleTopology A) :
    ((Etale.overPullbackCompOverSheafEquivIso U A).hom.app F ≫
      (Hom.smallEtalePullbackIsoPushforwardOfEtale (U.left ↘ S) A).hom.app F).hom =
        eqToHom (by
          simp only [Functor.comp_obj, Etale.overSheafEquiv_functor_obj_obj,
            ← Etale.iteratedSliceBackward_forget]
          rfl) := by
  have := locallyCoverDense_over_forget_etale S
  have := locallyCoverDense_over_forget_etale U.left
  have h : (Etale.overPullbackCompOverSheafEquivIso U A).hom.app F ≫
      (Hom.smallEtalePullbackIsoPushforwardOfEtale (U.left ↘ S) A).hom.app F =
      (MorphismProperty.overPullbackCompOverRestrictedSheafEquivIso
        (P := @AlgebraicGeometry.Etale) etaleTopology U A).hom.app F :=
    (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
      ((Hom.smallEtalePullbackIsoPushforwardOfEtale (U.left ↘ S) A).inv_hom_id_app F)).trans
      (Category.comp_id _))
  exact (congrArg InducedCategory.Hom.hom h).trans
    (MorphismProperty.overPullbackCompOverRestrictedSheafEquivIso_hom_app_hom
      (P := @AlgebraicGeometry.Etale) etaleTopology U A F)

lemma Etale.smallEtalePullbackIsoPushforwardOfEtale_inv_comp_overPullbackCompOverSheafEquivIso_inv
    (U : S.Etale) (A : Type u') [Category.{v'} A]
    [((Hom.smallEtaleBaseChange (U.left ↘ S)).sheafPushforwardContinuous A
      S.smallEtaleTopology U.left.smallEtaleTopology).IsRightAdjoint]
    (F : Sheaf S.smallEtaleTopology A) :
    ((Hom.smallEtalePullbackIsoPushforwardOfEtale (U.left ↘ S) A).inv.app F ≫
      (Etale.overPullbackCompOverSheafEquivIso U A).inv.app F).hom =
        eqToHom (by
          simp only [Functor.comp_obj, Etale.overSheafEquiv_functor_obj_obj,
            ← Etale.iteratedSliceBackward_forget]
          rfl) := by
  have := locallyCoverDense_over_forget_etale S
  have := locallyCoverDense_over_forget_etale U.left
  have h : (Hom.smallEtalePullbackIsoPushforwardOfEtale (U.left ↘ S) A).inv.app F ≫
      (Etale.overPullbackCompOverSheafEquivIso U A).inv.app F =
      (MorphismProperty.overPullbackCompOverRestrictedSheafEquivIso
        (P := @AlgebraicGeometry.Etale) etaleTopology U A).inv.app F :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _)
      ((Hom.smallEtalePullbackIsoPushforwardOfEtale (U.left ↘ S) A).inv_hom_id_app F)).trans
      (Category.id_comp _))
  exact (congrArg InducedCategory.Hom.hom h).trans
    (MorphismProperty.overPullbackCompOverRestrictedSheafEquivIso_inv_app_hom
      (P := @AlgebraicGeometry.Etale) etaleTopology U A F)

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
  have hTX : IsTerminal (f.smallEtaleBaseChange.obj (Etale.mk (𝟙 Y))) :=
    IsTerminal.isTerminalObj f.smallEtaleBaseChange _ (Etale.mkIdTerminal Y)
  rw [isLocallyConstantIn_iff_of_isTerminal P _ hTX]
  refine X.smallEtaleTopology.superset_covering ?_
    (f.coverPreserving_smallEtaleBaseChange.cover_preserve
      ((isLocallyConstantIn_iff P F).mp hF (Etale.mk (𝟙 Y))))
  rintro W _ ⟨V, u, k, hk, rfl⟩
  refine (((f.smallEtalePullback A).obj F).locallyConstantSieve P _).downward_closed ?_ k
  rw [mem_locallyConstantSieve_smallEtaleTopology_iff] at hk ⊢
  obtain ⟨M, hM, ⟨eV⟩⟩ := hk
  refine ⟨M, hM, ⟨?_⟩⟩
  exact ((Hom.smallEtalePullbackComp ((f.smallEtaleBaseChange.obj V).left ↘ X) f A).app F).symm ≪≫
    ((Hom.smallEtalePullbackCongr (f.smallEtaleBaseChangeFst_hom V).symm A).app F) ≪≫
    ((Hom.smallEtalePullbackComp (f.smallEtaleBaseChangeFst V) (V.left ↘ Y) A).app F) ≪≫
    ((f.smallEtaleBaseChangeFst V).smallEtalePullback A).mapIso eV ≪≫
    (f.smallEtaleBaseChangeFst V).smallEtalePullbackConstantSheafIso A M

/-- **Étale descent of local constancy.** For a jointly surjective family of étale morphisms
`g i : U i ⟶ S`, an étale sheaf `F` on `S` is locally constant with values in `P` if and only if
each pullback `(g i)^* F` is locally constant with values in `P` on `U i`. -/
theorem isLocallyConstantIn_smallEtaleTopology_iff_of_etale_of_iUnion_range_eq_univ
    {P : ObjectProperty A} (F : Sheaf S.smallEtaleTopology A)
    {ι : Type*} {U : ι → Scheme.{u}} (g : ∀ i, U i ⟶ S) [∀ i, AlgebraicGeometry.Etale (g i)]
    (hg : ⋃ i, Set.range (g i) = .univ) :
    F.IsLocallyConstantIn S.smallEtaleTopology P ↔
      ∀ i, (((g i).smallEtalePullback A).obj F).IsLocallyConstantIn (U i).smallEtaleTopology P := by
  refine ⟨fun hF i ↦ hF.smallEtalePullback (g i), fun h ↦ ?_⟩
  let φ : ∀ i, Etale.mk (g i) ⟶ Etale.mk (𝟙 S) :=
    fun i ↦ MorphismProperty.Over.homMk (g i) (Category.comp_id (g i))
  have hφ : Sieve.ofArrows _ φ ∈ S.smallEtaleTopology (Etale.mk (𝟙 S)) := by
    rw [ofArrows_mem_smallEtaleTopology_iff]
    exact hg
  rw [isLocallyConstantIn_iff_of_sieve_mem_of_isTerminal P F (Etale.mkIdTerminal S) hφ]
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
theorem isLocallyConstantIn_smallEtaleTopology_iff_of_etale_cover
    {P : ObjectProperty A} (F : Sheaf S.smallEtaleTopology A)
    (𝒰 : S.Cover (Scheme.precoverage @AlgebraicGeometry.Etale)) :
    F.IsLocallyConstantIn S.smallEtaleTopology P ↔
      ∀ i : 𝒰.I₀, (((𝒰.f i).smallEtalePullback A).obj F).IsLocallyConstantIn
        (𝒰.X i).smallEtaleTopology P := by
  have : JointlySurjective (Scheme.precoverage @AlgebraicGeometry.Etale) :=
    Scheme.instJointlySurjectivePrecoverage (P := @AlgebraicGeometry.Etale)
  exact isLocallyConstantIn_smallEtaleTopology_iff_of_etale_of_iUnion_range_eq_univ F 𝒰.f
    𝒰.iUnion_range

/-- Local constancy of an étale sheaf can be tested after pullback along any surjective étale
morphism `g : X ⟶ S`. -/
theorem isLocallyConstantIn_smallEtaleTopology_iff_of_etale_of_surjective
    {P : ObjectProperty A} (F : Sheaf S.smallEtaleTopology A)
    (g : X ⟶ S) [AlgebraicGeometry.Etale g] [Surjective g] :
    F.IsLocallyConstantIn S.smallEtaleTopology P ↔
      ((g.smallEtalePullback A).obj F).IsLocallyConstantIn X.smallEtaleTopology P :=
  (isLocallyConstantIn_smallEtaleTopology_iff_of_etale_of_iUnion_range_eq_univ F (fun _ : Unit ↦ g)
    (by rw [Set.range_eq_univ.mpr g.surjective, Set.iUnion_const])).trans Unique.forall_iff

end LocallyConstant

end CategoryTheory.Sheaf
