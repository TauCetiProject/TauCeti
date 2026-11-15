/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.Equivalence
public import TauCeti.AlgebraicGeometry.Morphisms.Etale.Basic
public import TauCeti.CategoryTheory.MorphismProperty.Over

/-!
# Functoriality and localization of the small étale site

For any morphism of schemes `f : X ⟶ Y`, base change defines a functor
`f.smallEtaleBaseChange : Y.Etale ⥤ X.Etale` sending `V ⟶ Y` to `V ×_Y X ⟶ X`, compatible with
identities and composition up to natural isomorphism (`smallEtaleBaseChangeId`,
`smallEtaleBaseChangeComp`). When `j : X ⟶ Y` is étale, postcomposition defines a functor
`j.smallEtaleMap : X.Etale ⥤ Y.Etale` left adjoint to `j.smallEtaleBaseChange`
(`j.smallEtaleMapPullbackAdj`).

For a scheme `S` and an étale `S`-scheme `U : S.Etale`, any morphism `V ⟶ U` in `S.Etale` has an
étale underlying morphism `V.left ⟶ U.left` by right cancellation of étale morphisms, and
postcomposing an étale `U.left`-scheme with `U.hom : U.left ⟶ S` produces an étale `S`-scheme over
`U`. Thus `CategoryTheory.Over U` is equivalent to `U.left.Etale`
(`AlgebraicGeometry.Scheme.Etale.iteratedSliceEquiv`), and this equivalence identifies the localized
Grothendieck topology `(smallEtaleTopology S).over U` with `smallEtaleTopology U.left`.

Consequently:

* For any coefficient category `A`, sheaves on the localized site `(Over U, (smallEtaleTopology
  S).over U)` are equivalent to étale sheaves on `U.left`
  (`AlgebraicGeometry.Scheme.Etale.overSheafEquiv`).
* For an étale morphism `j : X ⟶ Y`, postcomposition `j.smallEtaleMap : X.Etale ⥤ Y.Etale` is both
  continuous and cocontinuous for the small étale topologies.
* Restricting an étale sheaf `F` on `S` to `Over U` and transporting across `U.overSheafEquiv A`
  agrees naturally with `U.hom.smallEtaleMap.sheafPushforwardContinuous`
  (`AlgebraicGeometry.Scheme.Etale.overPullbackCompOverSheafEquivIso`).

## References

* M. Artin, A. Grothendieck, J.-L. Verdier, *SGA 4*, Exposé VII, §1.5, localization of the small
  étale site.
* The Stacks Project, [Tag 03YU](https://stacks.math.columbia.edu/tag/03YU).
-/

public section

universe u

open CategoryTheory Limits MorphismProperty

namespace AlgebraicGeometry.Scheme

namespace Hom

variable {X Y Z : Scheme.{u}}

/-- Postcomposition along an étale morphism `j : X ⟶ Y`, sending an étale `X`-scheme `W ⟶ X` to
`W ⟶ X ⟶ Y`. -/
-- The body is exposed so `(j.smallEtaleMap.obj W).left` reduces to `W.left` in dependent morphism
-- types, matching `Hom.smallEtaleBaseChange`.
@[expose]
noncomputable def smallEtaleMap (j : X ⟶ Y) [Etale j] : X.Etale ⥤ Y.Etale :=
  MorphismProperty.Over.map ⊤ ‹Etale j›

@[simp]
lemma smallEtaleMap_obj_left (j : X ⟶ Y) [Etale j] (W : X.Etale) :
    (j.smallEtaleMap.obj W).left = W.left :=
  (rfl)

@[simp]
lemma smallEtaleMap_obj_hom (j : X ⟶ Y) [Etale j] (W : X.Etale) :
    (j.smallEtaleMap.obj W).hom = W.hom ≫ j :=
  (rfl)

@[simp]
lemma smallEtaleMap_map_left (j : X ⟶ Y) [Etale j] {V W : X.Etale} (g : V ⟶ W) :
    (j.smallEtaleMap.map g).left = g.left :=
  (rfl)

/-- Postcomposition along the identity morphism on `X` is naturally isomorphic to `𝟭 X.Etale`. -/
noncomputable def smallEtaleMapId (X : Scheme.{u}) : smallEtaleMap (𝟙 X) ≅ 𝟭 X.Etale :=
  MorphismProperty.Over.mapId ⊤ X

@[simp]
lemma smallEtaleMapId_hom_app_left (X : Scheme.{u}) (W : X.Etale) :
    ((smallEtaleMapId X).hom.app W).left = 𝟙 W.left :=
  (rfl)

@[simp]
lemma smallEtaleMapId_inv_app_left (X : Scheme.{u}) (W : X.Etale) :
    ((smallEtaleMapId X).inv.app W).left = 𝟙 W.left :=
  (rfl)

/-- Postcomposition along a composite of étale morphisms is the composite of the postcomposition
functors. -/
noncomputable def smallEtaleMapComp (j : X ⟶ Y) (k : Y ⟶ Z) [Etale j] [Etale k] :
    (j ≫ k).smallEtaleMap ≅ j.smallEtaleMap ⋙ k.smallEtaleMap :=
  MorphismProperty.Over.mapComp ⊤ ‹Etale j› ‹Etale k›

@[simp]
lemma smallEtaleMapComp_hom_app_left (j : X ⟶ Y) (k : Y ⟶ Z) [Etale j] [Etale k] (W : X.Etale) :
    ((smallEtaleMapComp j k).hom.app W).left = 𝟙 W.left :=
  (rfl)

@[simp]
lemma smallEtaleMapComp_inv_app_left (j : X ⟶ Y) (k : Y ⟶ Z) [Etale j] [Etale k] (W : X.Etale) :
    ((smallEtaleMapComp j k).inv.app W).left = 𝟙 W.left :=
  (rfl)

/-- Equal étale morphisms induce naturally isomorphic postcomposition functors on small étale
sites. -/
noncomputable def smallEtaleMapCongr {j j' : X ⟶ Y} (h : j = j') [Etale j] [Etale j'] :
    j.smallEtaleMap ≅ j'.smallEtaleMap :=
  MorphismProperty.Over.mapCongr ⊤ h ‹Etale j›

@[simp]
lemma smallEtaleMapCongr_hom_app_left {j j' : X ⟶ Y} (h : j = j') [Etale j] [Etale j']
    (W : X.Etale) :
    ((smallEtaleMapCongr h).hom.app W).left = 𝟙 W.left :=
  (rfl)

@[simp]
lemma smallEtaleMapCongr_inv_app_left {j j' : X ⟶ Y} (h : j = j') [Etale j] [Etale j']
    (W : X.Etale) :
    ((smallEtaleMapCongr h).inv.app W).left = 𝟙 W.left :=
  (rfl)

/-- Base change along `f : X ⟶ Y`, from schemes étale over `Y` to schemes étale over `X`: an étale
`V ⟶ Y` is sent to `V ×_Y X ⟶ X`. -/
-- The body is exposed so `(f.smallEtaleBaseChange.obj V).left` and `.hom` reduce in dependent
-- morphism types.
@[expose]
noncomputable def smallEtaleBaseChange (f : X ⟶ Y) : Y.Etale ⥤ X.Etale :=
  MorphismProperty.Over.pullback @Etale ⊤ f

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

/-- On underlying schemes, `f.smallEtaleBaseChange.map g` is `pullback.map` along `g.left` and
`𝟙 X`. -/
lemma smallEtaleBaseChange_map_left_eq_pullback_map (f : X ⟶ Y) {V W : Y.Etale} (g : V ⟶ W) :
    (f.smallEtaleBaseChange.map g).left =
      pullback.map V.hom f W.hom f g.left (𝟙 X) (𝟙 Y) (by simp) (by simp) := by
  rw [smallEtaleBaseChange_map_left]
  change (_ : pullback V.hom f ⟶ pullback W.hom f) = _
  ext <;> simp

/-- On underlying schemes over `X`, `smallEtaleBaseChange f` is base change along `f`. -/
noncomputable def smallEtaleBaseChangeCompForgetIso (f : X ⟶ Y) :
    f.smallEtaleBaseChange ⋙ Etale.forget X ≅ Etale.forget Y ⋙ CategoryTheory.Over.pullback f :=
  Iso.refl _

/-- For an étale morphism `j : X ⟶ Y`, postcomposition `j.smallEtaleMap` is left adjoint to base
change `j.smallEtaleBaseChange`. -/
noncomputable def smallEtaleMapPullbackAdj (j : X ⟶ Y) [Etale j] :
    j.smallEtaleMap ⊣ j.smallEtaleBaseChange :=
  MorphismProperty.Over.mapPullbackAdj @Etale ⊤ j ‹Etale j› trivial

/-- Base change along `𝟙 X` on small étale sites is naturally isomorphic to `𝟭 X.Etale`. -/
noncomputable def smallEtaleBaseChangeId (X : Scheme.{u}) :
    smallEtaleBaseChange (𝟙 X) ≅ 𝟭 X.Etale :=
  conjugateIsoEquiv (smallEtaleMapPullbackAdj (𝟙 X)) .id (smallEtaleMapId X).symm

@[simp]
lemma smallEtaleBaseChangeId_hom_app_left (X : Scheme.{u}) (V : X.Etale) :
    ((smallEtaleBaseChangeId X).hom.app V).left = pullback.fst V.hom (𝟙 X) :=
  Category.id_comp _

@[simp]
lemma smallEtaleBaseChangeId_inv_app_left (X : Scheme.{u}) (V : X.Etale) :
    ((smallEtaleBaseChangeId X).inv.app V).left =
      pullback.lift (𝟙 V.left) V.hom (Category.comp_id V.hom) :=
  have h₁ : ((smallEtaleBaseChangeId X).inv.app V).left ≫ pullback.fst V.hom (𝟙 X) = 𝟙 V.left :=
    smallEtaleBaseChangeId_hom_app_left X V ▸
      congrArg (·.left) ((smallEtaleBaseChangeId X).inv_hom_id_app V)
  have h₂ : ((smallEtaleBaseChangeId X).inv.app V).left ≫ pullback.snd V.hom (𝟙 X) = V.hom :=
    MorphismProperty.Over.w ((smallEtaleBaseChangeId X).inv.app V)
  pullback.hom_ext (h₁.trans (pullback.lift_fst _ _ _).symm)
    (h₂.trans (pullback.lift_snd _ _ _).symm)

/-- Base change along `f ≫ g` on small étale sites is naturally isomorphic to base change along `g`
followed by base change along `f`. -/
noncomputable def smallEtaleBaseChangeComp (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).smallEtaleBaseChange ≅ g.smallEtaleBaseChange ⋙ f.smallEtaleBaseChange :=
  MorphismProperty.Over.pullbackComp f g

@[simp]
lemma smallEtaleBaseChangeComp_hom_app_left (f : X ⟶ Y) (g : Y ⟶ Z) (V : Z.Etale) :
    ((smallEtaleBaseChangeComp f g).hom.app V).left =
      (pullbackLeftPullbackSndIso V.hom g f).inv := by
  change (pullback.congrHom rfl rfl ≪≫ (pullbackLeftPullbackSndIso V.hom g f).symm).hom = _
  simp

@[simp]
lemma smallEtaleBaseChangeComp_inv_app_left (f : X ⟶ Y) (g : Y ⟶ Z) (V : Z.Etale) :
    ((smallEtaleBaseChangeComp f g).inv.app V).left =
      (pullbackLeftPullbackSndIso V.hom g f).hom := by
  change (pullback.congrHom rfl rfl ≪≫ (pullbackLeftPullbackSndIso V.hom g f).symm).inv = _
  simp

/-- Equal scheme morphisms induce naturally isomorphic base change functors on small étale sites. -/
noncomputable def smallEtaleBaseChangeCongr {f f' : X ⟶ Y} (h : f = f') :
    f.smallEtaleBaseChange ≅ f'.smallEtaleBaseChange :=
  MorphismProperty.Over.pullbackCongr h

@[simp]
lemma smallEtaleBaseChangeCongr_hom_app_left {f f' : X ⟶ Y} (h : f = f') (V : Y.Etale) :
    ((smallEtaleBaseChangeCongr h).hom.app V).left = (pullback.congrHom rfl h).hom :=
  (rfl)

@[simp]
lemma smallEtaleBaseChangeCongr_inv_app_left {f f' : X ⟶ Y} (h : f = f') (V : Y.Etale) :
    ((smallEtaleBaseChangeCongr h).inv.app V).left = (pullback.congrHom rfl h).inv :=
  (rfl)

/-- Postcomposition along an étale morphism preserves covering sieves of the small étale
topology. -/
lemma coverPreserving_smallEtaleMap (j : X ⟶ Y) [Etale j] :
    CoverPreserving (smallEtaleTopology X) (smallEtaleTopology Y) j.smallEtaleMap where
  cover_preserve {W R} hR := by
    obtain ⟨ι, V, f, rfl⟩ := R.exists_eq_ofArrows
    rw [Sieve.functorPushforward_ofArrows, ofArrows_mem_smallEtaleTopology_iff]
    exact (ofArrows_mem_smallEtaleTopology_iff f).mp hR

end Hom

namespace Etale

variable {S : Scheme.{u}} (U : S.Etale)

/-- The slice category `CategoryTheory.Over U` of `S.Etale` over `U` is equivalent to the small
étale category `U.left.Etale`. -/
-- The body is exposed so dependent `.left` and `.hom` types of mapped morphisms compute.
@[expose]
noncomputable def iteratedSliceEquiv : CategoryTheory.Over U ≌ U.left.Etale :=
  MorphismProperty.Over.iteratedSliceEquiv U

@[simp]
lemma iteratedSliceEquiv_functor_obj_left (V : CategoryTheory.Over U) :
    (U.iteratedSliceEquiv.functor.obj V).left = V.left.left :=
  (rfl)

@[simp]
lemma iteratedSliceEquiv_functor_obj_hom (V : CategoryTheory.Over U) :
    (U.iteratedSliceEquiv.functor.obj V).hom = V.hom.left :=
  (rfl)

@[simp]
lemma iteratedSliceEquiv_functor_map_left {V W : CategoryTheory.Over U} (f : V ⟶ W) :
    (U.iteratedSliceEquiv.functor.map f).left = f.left.left :=
  (rfl)

@[simp]
lemma iteratedSliceEquiv_inverse_obj_left_left (W : U.left.Etale) :
    (U.iteratedSliceEquiv.inverse.obj W).left.left = W.left :=
  (rfl)

@[simp]
lemma iteratedSliceEquiv_inverse_obj_hom_left (W : U.left.Etale) :
    ((U.iteratedSliceEquiv.inverse.obj W).hom).left = W.hom :=
  (rfl)

@[simp]
lemma iteratedSliceEquiv_inverse_map_left_left {V W : U.left.Etale} (g : V ⟶ W) :
    ((U.iteratedSliceEquiv.inverse.map g).left).left = g.left :=
  (rfl)

/-- Postcomposing `U.iteratedSliceEquiv.inverse` with `CategoryTheory.Over.forget U` recovers
postcomposition `U.hom.smallEtaleMap`. -/
noncomputable def iteratedSliceEquivInverseCompForgetIso :
    U.iteratedSliceEquiv.inverse ⋙ CategoryTheory.Over.forget U ≅
      (U.hom : U.left ⟶ S).smallEtaleMap :=
  MorphismProperty.Over.iteratedSliceBackwardCompForgetIso U

/-- Postcomposing `U.iteratedSliceEquiv.functor` with `U.hom.smallEtaleMap` recovers
`CategoryTheory.Over.forget U`. -/
noncomputable def iteratedSliceEquivFunctorCompMapIso :
    U.iteratedSliceEquiv.functor ⋙ (U.hom : U.left ⟶ S).smallEtaleMap ≅
      CategoryTheory.Over.forget U :=
  MorphismProperty.Over.iteratedSliceForwardCompMapIso U

/-- `U.iteratedSliceEquiv.inverse : U.left.Etale ⥤ CategoryTheory.Over U` identifies
`smallEtaleTopology U.left` with the localized topology `(smallEtaleTopology S).over U`. -/
instance isDenseSubsite_iteratedSliceEquiv_inverse :
    U.iteratedSliceEquiv.inverse.IsDenseSubsite
      (smallEtaleTopology U.left) ((smallEtaleTopology S).over U) where
  functorPushforward_mem_iff {W R} := by
    obtain ⟨ι, Z, f, rfl⟩ := R.exists_eq_ofArrows
    rw [Sieve.functorPushforward_ofArrows, GrothendieckTopology.mem_over_iff,
      Sieve.overEquiv_ofArrows, ofArrows_mem_smallEtaleTopology_iff,
      ofArrows_mem_smallEtaleTopology_iff]
    simp_rw [iteratedSliceEquiv_inverse_map_left_left]
    exact Iff.rfl

/-- Sheaves on the localized small étale site `(Over U, (smallEtaleTopology S).over U)` are
equivalent to sheaves on the small étale site of `U.left`. -/
noncomputable def overSheafEquiv (A : Type*) [Category* A] :
    Sheaf ((smallEtaleTopology S).over U) A ≌ Sheaf (smallEtaleTopology U.left) A :=
  U.iteratedSliceEquiv.sheafCongr ((smallEtaleTopology S).over U) (smallEtaleTopology U.left) A

/-- The forward functor of `U.overSheafEquiv A` is pushforward of sheaves along
`U.iteratedSliceEquiv.inverse`. -/
noncomputable def overSheafEquivFunctorIso (A : Type*) [Category* A] :
    (U.overSheafEquiv A).functor ≅
      U.iteratedSliceEquiv.inverse.sheafPushforwardContinuous A
        (smallEtaleTopology U.left) ((smallEtaleTopology S).over U) :=
  Iso.refl _

/-- For `U : S.Etale`, postcomposition `U.hom.smallEtaleMap` is continuous for the small étale
topologies. -/
instance isContinuous_hom_smallEtaleMap :
    U.hom.smallEtaleMap.IsContinuous (smallEtaleTopology U.left) (smallEtaleTopology S) := by
  have := Functor.isContinuous_comp
    U.iteratedSliceEquiv.inverse (CategoryTheory.Over.forget U)
    (smallEtaleTopology U.left) ((smallEtaleTopology S).over U) (smallEtaleTopology S)
  exact Functor.isContinuous_of_iso U.iteratedSliceEquivInverseCompForgetIso
    (smallEtaleTopology U.left) (smallEtaleTopology S)

/-- For `U : S.Etale`, postcomposition `U.hom.smallEtaleMap` is cocontinuous for the small étale
topologies. -/
instance isCocontinuous_hom_smallEtaleMap :
    U.hom.smallEtaleMap.IsCocontinuous (smallEtaleTopology U.left) (smallEtaleTopology S) := by
  have := isCocontinuous_comp (L := smallEtaleTopology S)
    U.iteratedSliceEquiv.inverse (CategoryTheory.Over.forget U)
    (smallEtaleTopology U.left) ((smallEtaleTopology S).over U)
  exact Functor.IsCocontinuous.of_iso U.iteratedSliceEquivInverseCompForgetIso

end Etale

namespace Hom

variable {X Y : Scheme.{u}} (j : X ⟶ Y) [Etale j]

/-- Postcomposition `j.smallEtaleMap` along an étale morphism is continuous for the small étale
topologies. -/
instance isContinuous_smallEtaleMap :
    j.smallEtaleMap.IsContinuous (smallEtaleTopology X) (smallEtaleTopology Y) :=
  (Etale.mk j).isContinuous_hom_smallEtaleMap

/-- Postcomposition `j.smallEtaleMap` along an étale morphism is cocontinuous for the small étale
topologies. -/
instance isCocontinuous_smallEtaleMap :
    j.smallEtaleMap.IsCocontinuous (smallEtaleTopology X) (smallEtaleTopology Y) :=
  (Etale.mk j).isCocontinuous_hom_smallEtaleMap

end Hom

namespace Etale

variable {S : Scheme.{u}} (U : S.Etale) (A : Type*) [Category* A]

/-- Restricting a sheaf on `S.Etale` to `CategoryTheory.Over U` and transporting across
`U.overSheafEquiv A` agrees naturally with sheaf pushforward along `U.hom.smallEtaleMap`. -/
noncomputable def overPullbackCompOverSheafEquivIso :
    (smallEtaleTopology S).overPullback A U ⋙ (U.overSheafEquiv A).functor ≅
      (U.hom : U.left ⟶ S).smallEtaleMap.sheafPushforwardContinuous A
        (smallEtaleTopology U.left) (smallEtaleTopology S) :=
  letI : ((U.hom : U.left ⟶ S).smallEtaleMap).IsContinuous
      (smallEtaleTopology U.left) (smallEtaleTopology S) :=
    U.isContinuous_hom_smallEtaleMap
  Functor.isoWhiskerLeft _ (U.overSheafEquivFunctorIso A) ≪≫
    Functor.sheafPushforwardContinuousComp' U.iteratedSliceEquivInverseCompForgetIso A
      (smallEtaleTopology U.left) ((smallEtaleTopology S).over U) (smallEtaleTopology S)

/-- On an étale sheaf `F` on `S`, transporting `F.over U` across `U.overSheafEquiv A` identifies
with `((U.hom : U.left ⟶ S).smallEtaleMap.sheafPushforwardContinuous A _ _).obj F`. -/
noncomputable def overSheafEquivObjOverIso (F : Sheaf (smallEtaleTopology S) A) :
    (U.overSheafEquiv A).functor.obj (F.over U) ≅
      ((U.hom : U.left ⟶ S).smallEtaleMap.sheafPushforwardContinuous A
        (smallEtaleTopology U.left) (smallEtaleTopology S)).obj F :=
  (U.overPullbackCompOverSheafEquivIso A).app F

end Etale

end AlgebraicGeometry.Scheme
