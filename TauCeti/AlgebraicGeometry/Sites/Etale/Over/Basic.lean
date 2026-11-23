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

For a morphism of schemes `f : X ⟶ Y`, base change defines `f.smallEtaleBaseChange : Y.Etale ⥤
X.Etale` (`smallEtaleBaseChangeId`, `smallEtaleBaseChangeComp`). For étale `j : X ⟶ Y`,
postcomposition `j.smallEtaleMap : X.Etale ⥤ Y.Etale` is left adjoint to `j.smallEtaleBaseChange`
(`j.smallEtaleMapBaseChangeAdj`) and is both continuous and cocontinuous.

For `U : S.Etale`, `AlgebraicGeometry.Scheme.Etale.iteratedSliceEquiv : Over U ≌ U.left.Etale`
identifies `(smallEtaleTopology S).over U` with `smallEtaleTopology U.left`, inducing
`AlgebraicGeometry.Scheme.Etale.overSheafEquiv` and identifying restriction to `Over U` with
`U.hom.smallEtaleMap.sheafPushforwardContinuous`
(`AlgebraicGeometry.Scheme.Etale.overPullbackCompOverSheafEquivIso`).

## References

* M. Artin, A. Grothendieck, J.-L. Verdier, *SGA 4*, Exposé VII, §1.5.
-/

public section

universe u

open CategoryTheory Limits MorphismProperty

namespace AlgebraicGeometry.Scheme

namespace Hom

variable {X Y Z : Scheme.{u}}

section Map

variable (j : X ⟶ Y) [Etale j]

/-- Postcomposition along an étale morphism `j : X ⟶ Y`, sending an étale `X`-scheme `W ⟶ X` to
`W ⟶ X ⟶ Y`. -/
-- Exposed so `(j.smallEtaleMap.obj W).left` reduces to `W.left` in dependent morphism types.
@[expose]
noncomputable def smallEtaleMap : X.Etale ⥤ Y.Etale :=
  MorphismProperty.Over.map ⊤ ‹Etale j›

@[simp]
lemma smallEtaleMap_obj_left (W : X.Etale) : (j.smallEtaleMap.obj W).left = W.left := (rfl)

@[simp]
lemma smallEtaleMap_obj_hom (W : X.Etale) : (j.smallEtaleMap.obj W).hom = W.hom ≫ j := (rfl)

@[simp]
lemma smallEtaleMap_map_left {V W : X.Etale} (g : V ⟶ W) :
    (j.smallEtaleMap.map g).left = g.left := (rfl)

end Map

/-- Postcomposition along the identity morphism on `X` is naturally isomorphic to `𝟭 X.Etale`. -/
noncomputable def smallEtaleMapId (X : Scheme.{u}) : smallEtaleMap (𝟙 X) ≅ 𝟭 X.Etale :=
  MorphismProperty.Over.mapId ⊤ X

@[simp]
lemma smallEtaleMapId_hom_app_left (X : Scheme.{u}) (W : X.Etale) :
    ((smallEtaleMapId X).hom.app W).left = 𝟙 W.left := (rfl)

@[simp]
lemma smallEtaleMapId_inv_app_left (X : Scheme.{u}) (W : X.Etale) :
    ((smallEtaleMapId X).inv.app W).left = 𝟙 W.left := (rfl)

/-- Postcomposition along a composite of étale morphisms is the composite of the postcomposition
functors. -/
noncomputable def smallEtaleMapComp (j : X ⟶ Y) (k : Y ⟶ Z) [Etale j] [Etale k] :
    (j ≫ k).smallEtaleMap ≅ j.smallEtaleMap ⋙ k.smallEtaleMap :=
  MorphismProperty.Over.mapComp ⊤ ‹Etale j› ‹Etale k›

@[simp]
lemma smallEtaleMapComp_hom_app_left (j : X ⟶ Y) (k : Y ⟶ Z) [Etale j] [Etale k] (W : X.Etale) :
    ((smallEtaleMapComp j k).hom.app W).left = 𝟙 W.left := (rfl)

@[simp]
lemma smallEtaleMapComp_inv_app_left (j : X ⟶ Y) (k : Y ⟶ Z) [Etale j] [Etale k] (W : X.Etale) :
    ((smallEtaleMapComp j k).inv.app W).left = 𝟙 W.left := (rfl)

section MapCongr

variable {j j' : X ⟶ Y} (h : j = j') [Etale j] [Etale j']

/-- Equal étale morphisms induce naturally isomorphic postcomposition functors on small étale
sites. -/
noncomputable def smallEtaleMapCongr : j.smallEtaleMap ≅ j'.smallEtaleMap :=
  MorphismProperty.Over.mapCongr ⊤ h ‹Etale j›

@[simp]
lemma smallEtaleMapCongr_hom_app_left (W : X.Etale) :
    ((smallEtaleMapCongr h).hom.app W).left = 𝟙 W.left := (rfl)

@[simp]
lemma smallEtaleMapCongr_inv_app_left (W : X.Etale) :
    ((smallEtaleMapCongr h).inv.app W).left = 𝟙 W.left := (rfl)

end MapCongr

section BaseChange

variable (f : X ⟶ Y)

/-- Base change along `f : X ⟶ Y`, from schemes étale over `Y` to schemes étale over `X`: an étale
`V ⟶ Y` is sent to `V ×_Y X ⟶ X`. -/
-- Exposed so `(f.smallEtaleBaseChange.obj V).left` and `.hom` reduce in dependent types.
@[expose]
noncomputable def smallEtaleBaseChange : Y.Etale ⥤ X.Etale :=
  MorphismProperty.Over.pullback @Etale ⊤ f

@[simp]
lemma smallEtaleBaseChange_obj_left (V : Y.Etale) :
    (f.smallEtaleBaseChange.obj V).left = pullback V.hom f := (rfl)

@[simp]
lemma smallEtaleBaseChange_obj_hom (V : Y.Etale) :
    (f.smallEtaleBaseChange.obj V).hom = pullback.snd V.hom f := (rfl)

@[simp]
lemma smallEtaleBaseChange_map_left {V W : Y.Etale} (g : V ⟶ W) :
    (f.smallEtaleBaseChange.map g).left =
      pullback.lift (pullback.fst V.hom f ≫ g.left) (pullback.snd V.hom f)
        (by simp [pullback.condition]) := (rfl)

/-- On underlying schemes, `f.smallEtaleBaseChange.map g` is `pullback.map` along `g.left` and
`𝟙 X`. -/
lemma smallEtaleBaseChange_map_left_eq_pullback_map {V W : Y.Etale} (g : V ⟶ W) :
    (f.smallEtaleBaseChange.map g).left =
      pullback.map V.hom f W.hom f g.left (𝟙 X) (𝟙 Y) (by simp) (by simp) := by
  rw [smallEtaleBaseChange_map_left]
  apply pullback.hom_ext <;> simp

/-- On underlying schemes over `X`, `smallEtaleBaseChange f` is base change along `f`. -/
noncomputable def smallEtaleBaseChangeCompForgetIso :
    f.smallEtaleBaseChange ⋙ Etale.forget X ≅ Etale.forget Y ⋙ CategoryTheory.Over.pullback f :=
  Iso.refl _

@[simp]
lemma smallEtaleBaseChangeCompForgetIso_hom_app_left (V : Y.Etale) :
    (f.smallEtaleBaseChangeCompForgetIso.hom.app V).left = 𝟙 (pullback V.hom f) := (rfl)

@[simp]
lemma smallEtaleBaseChangeCompForgetIso_inv_app_left (V : Y.Etale) :
    (f.smallEtaleBaseChangeCompForgetIso.inv.app V).left = 𝟙 (pullback V.hom f) := (rfl)

end BaseChange

section Adj

variable (j : X ⟶ Y) [Etale j]

/-- For an étale morphism `j : X ⟶ Y`, postcomposition `j.smallEtaleMap` is left adjoint to base
change `j.smallEtaleBaseChange`. -/
noncomputable def smallEtaleMapBaseChangeAdj : j.smallEtaleMap ⊣ j.smallEtaleBaseChange :=
  MorphismProperty.Over.mapPullbackAdj @Etale ⊤ j ‹Etale j› trivial

@[simp]
lemma smallEtaleMapBaseChangeAdj_unit_app_left (W : X.Etale) :
    (j.smallEtaleMapBaseChangeAdj.unit.app W).left =
      pullback.lift (𝟙 W.left) W.hom (by simp) := (rfl)

@[simp]
lemma smallEtaleMapBaseChangeAdj_counit_app_left (V : Y.Etale) :
    (j.smallEtaleMapBaseChangeAdj.counit.app V).left = pullback.fst V.hom j := (rfl)

end Adj

/-- Base change along `𝟙 X` on small étale sites is naturally isomorphic to `𝟭 X.Etale`. -/
noncomputable def smallEtaleBaseChangeId (X : Scheme.{u}) :
    smallEtaleBaseChange (𝟙 X) ≅ 𝟭 X.Etale :=
  conjugateIsoEquiv (smallEtaleMapBaseChangeAdj (𝟙 X)) .id (smallEtaleMapId X).symm

@[simp]
lemma smallEtaleBaseChangeId_hom_app_left (X : Scheme.{u}) (V : X.Etale) :
    ((smallEtaleBaseChangeId X).hom.app V).left = pullback.fst V.hom (𝟙 X) := by
  rw [smallEtaleBaseChangeId, conjugateIsoEquiv_apply_hom, conjugateEquiv_adjunction_id]
  exact (MorphismProperty.Comma.comp_left _ _).trans (by
    simp only [Iso.symm_hom, smallEtaleMapId_inv_app_left,
      smallEtaleMapBaseChangeAdj_counit_app_left]; exact Category.id_comp _)

@[simp]
lemma smallEtaleBaseChangeId_inv_app_left (X : Scheme.{u}) (V : X.Etale) :
    ((smallEtaleBaseChangeId X).inv.app V).left =
      pullback.lift (𝟙 V.left) V.hom (Category.comp_id V.hom) :=
  have h₁ : ((smallEtaleBaseChangeId X).inv.app V).left ≫ pullback.fst V.hom (𝟙 X) = 𝟙 V.left :=
    smallEtaleBaseChangeId_hom_app_left X V ▸
      congrArg (·.left) ((smallEtaleBaseChangeId X).inv_hom_id_app V)
  pullback.hom_ext (h₁.trans (pullback.lift_fst _ _ _).symm)
    ((MorphismProperty.Over.w ((smallEtaleBaseChangeId X).inv.app V)).trans
      (pullback.lift_snd _ _ _).symm)

/-- Base change along a composite `fg = f ≫ g` on small étale sites is naturally isomorphic to base
change along `g` followed by base change along `f`. -/
-- Exposed so projection lemmas for arbitrary factorizations `fg = f ≫ g` can unfold it.
@[expose]
noncomputable def smallEtaleBaseChangeComp (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z := f ≫ g)
    (hfg : fg = f ≫ g := by cat_disch) :
    fg.smallEtaleBaseChange ≅ g.smallEtaleBaseChange ⋙ f.smallEtaleBaseChange :=
  MorphismProperty.Over.pullbackComp f g fg hfg

@[simp]
lemma smallEtaleBaseChangeComp_hom_app_left (f : X ⟶ Y) (g : Y ⟶ Z) (V : Z.Etale) :
    ((smallEtaleBaseChangeComp f g).hom.app V).left =
      (pullbackLeftPullbackSndIso V.hom g f).inv :=
  (MorphismProperty.Over.pullbackComp_hom_app_left f g (f ≫ g) rfl V).trans
    ((congrArg (· ≫ _) pullback.map_id).trans (Category.id_comp _))

@[simp]
lemma smallEtaleBaseChangeComp_inv_app_left (f : X ⟶ Y) (g : Y ⟶ Z) (V : Z.Etale) :
    ((smallEtaleBaseChangeComp f g).inv.app V).left =
      (pullbackLeftPullbackSndIso V.hom g f).hom :=
  (MorphismProperty.Over.pullbackComp_inv_app_left f g (f ≫ g) rfl V).trans
    ((congrArg (_ ≫ ·) pullback.map_id).trans (Category.comp_id _))

/-- Equal scheme morphisms induce naturally isomorphic base change functors on small étale sites. -/
-- Exposed so projection lemmas in `TauCeti.AlgebraicGeometry.Sites.Etale.BaseChange` can unfold it.
@[expose]
noncomputable def smallEtaleBaseChangeCongr {f f' : X ⟶ Y} (h : f = f') :
    f.smallEtaleBaseChange ≅ f'.smallEtaleBaseChange :=
  MorphismProperty.Over.pullbackCongr h

@[simp]
lemma smallEtaleBaseChangeCongr_hom_app_left {f f' : X ⟶ Y} (h : f = f') (V : Y.Etale) :
    ((smallEtaleBaseChangeCongr h).hom.app V).left = (pullback.congrHom rfl h).hom := (rfl)

@[simp]
lemma smallEtaleBaseChangeCongr_inv_app_left {f f' : X ⟶ Y} (h : f = f') (V : Y.Etale) :
    ((smallEtaleBaseChangeCongr h).inv.app V).left = (pullback.congrHom rfl h).inv := (rfl)

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
-- The body is exposed so `U.iteratedSliceEquiv.functor`/`.inverse` reduce in dependent types.
@[expose]
noncomputable def iteratedSliceEquiv : CategoryTheory.Over U ≌ U.left.Etale :=
  MorphismProperty.Over.iteratedSliceEquiv U

@[simp]
lemma iteratedSliceEquiv_functor_obj_left (V : CategoryTheory.Over U) :
    (U.iteratedSliceEquiv.functor.obj V).left = V.left.left := (rfl)

@[simp]
lemma iteratedSliceEquiv_functor_obj_hom (V : CategoryTheory.Over U) :
    (U.iteratedSliceEquiv.functor.obj V).hom = V.hom.left := (rfl)

@[simp]
lemma iteratedSliceEquiv_functor_map_left {V W : CategoryTheory.Over U} (f : V ⟶ W) :
    (U.iteratedSliceEquiv.functor.map f).left = f.left.left := (rfl)

@[simp]
lemma iteratedSliceEquiv_inverse_obj_left (W : U.left.Etale) :
    (U.iteratedSliceEquiv.inverse.obj W).left = (U.hom : U.left ⟶ S).smallEtaleMap.obj W := (rfl)

@[simp]
lemma iteratedSliceEquiv_inverse_obj_hom_left (W : U.left.Etale) :
    (U.iteratedSliceEquiv.inverse.obj W).hom.left = W.hom := (rfl)

@[simp]
lemma iteratedSliceEquiv_inverse_map_left_left {V W : U.left.Etale} (g : V ⟶ W) :
    (U.iteratedSliceEquiv.inverse.map g).left.left = g.left := (rfl)

/-- Postcomposing `U.iteratedSliceEquiv.inverse` with `CategoryTheory.Over.forget U` recovers
postcomposition `U.hom.smallEtaleMap`. -/
noncomputable def iteratedSliceEquivInverseCompForgetIso :
    U.iteratedSliceEquiv.inverse ⋙ CategoryTheory.Over.forget U ≅
      (U.hom : U.left ⟶ S).smallEtaleMap :=
  MorphismProperty.Over.iteratedSliceBackwardCompForgetIso U

@[simp]
lemma iteratedSliceEquivInverseCompForgetIso_hom_app_left (W : U.left.Etale) :
    (U.iteratedSliceEquivInverseCompForgetIso.hom.app W).left = 𝟙 W.left :=
  MorphismProperty.Over.iteratedSliceBackwardCompForgetIso_hom_app_left U W

@[simp]
lemma iteratedSliceEquivInverseCompForgetIso_inv_app_left (W : U.left.Etale) :
    (U.iteratedSliceEquivInverseCompForgetIso.inv.app W).left = 𝟙 W.left :=
  MorphismProperty.Over.iteratedSliceBackwardCompForgetIso_inv_app_left U W

/-- Postcomposing `U.iteratedSliceEquiv.functor` with `U.hom.smallEtaleMap` recovers
`CategoryTheory.Over.forget U`. -/
noncomputable def iteratedSliceEquivFunctorCompMapIso :
    U.iteratedSliceEquiv.functor ⋙ (U.hom : U.left ⟶ S).smallEtaleMap ≅
      CategoryTheory.Over.forget U :=
  MorphismProperty.Over.iteratedSliceForwardCompMapIso U

@[simp]
lemma iteratedSliceEquivFunctorCompMapIso_hom_app_left (V : CategoryTheory.Over U) :
    (U.iteratedSliceEquivFunctorCompMapIso.hom.app V).left = 𝟙 V.left.left :=
  MorphismProperty.Over.iteratedSliceForwardCompMapIso_hom_app_left U V

@[simp]
lemma iteratedSliceEquivFunctorCompMapIso_inv_app_left (V : CategoryTheory.Over U) :
    (U.iteratedSliceEquivFunctorCompMapIso.inv.app V).left = 𝟙 V.left.left :=
  MorphismProperty.Over.iteratedSliceForwardCompMapIso_inv_app_left U V

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

/-- For `U : S.Etale`, postcomposition `U.hom.smallEtaleMap` is continuous for the small étale
topologies. -/
instance isContinuous_hom_smallEtaleMap :
    U.hom.smallEtaleMap.IsContinuous (smallEtaleTopology U.left) (smallEtaleTopology S) :=
  have := Functor.isContinuous_comp U.iteratedSliceEquiv.inverse (CategoryTheory.Over.forget U)
    (smallEtaleTopology U.left) ((smallEtaleTopology S).over U) (smallEtaleTopology S)
  Functor.isContinuous_of_iso U.iteratedSliceEquivInverseCompForgetIso
    (smallEtaleTopology U.left) (smallEtaleTopology S)

/-- For `U : S.Etale`, postcomposition `U.hom.smallEtaleMap` is cocontinuous for the small étale
topologies. -/
instance isCocontinuous_hom_smallEtaleMap :
    U.hom.smallEtaleMap.IsCocontinuous (smallEtaleTopology U.left) (smallEtaleTopology S) :=
  have := isCocontinuous_comp (L := smallEtaleTopology S)
    U.iteratedSliceEquiv.inverse (CategoryTheory.Over.forget U)
    (smallEtaleTopology U.left) ((smallEtaleTopology S).over U)
  Functor.IsCocontinuous.of_iso U.iteratedSliceEquivInverseCompForgetIso

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

/-- Sheaves on the localized small étale site `(Over U, (smallEtaleTopology S).over U)` are
equivalent to sheaves on the small étale site of `U.left`. -/
noncomputable abbrev overSheafEquiv :
    Sheaf ((smallEtaleTopology S).over U) A ≌ Sheaf (smallEtaleTopology U.left) A :=
  U.iteratedSliceEquiv.sheafCongr ((smallEtaleTopology S).over U) (smallEtaleTopology U.left) A

/-- The forward functor of `U.overSheafEquiv A` is pushforward of sheaves along
`U.iteratedSliceEquiv.inverse`. -/
noncomputable def overSheafEquivFunctorIso :
    (U.overSheafEquiv A).functor ≅
      U.iteratedSliceEquiv.inverse.sheafPushforwardContinuous A
        (smallEtaleTopology U.left) ((smallEtaleTopology S).over U) :=
  Iso.refl _

@[simp]
lemma overSheafEquivFunctorIso_hom_app_hom_app (F : Sheaf ((smallEtaleTopology S).over U) A)
    (W : U.left.Etaleᵒᵖ) :
    ((U.overSheafEquivFunctorIso A).hom.app F).hom.app W =
      𝟙 (F.obj.obj (U.iteratedSliceEquiv.inverse.op.obj W)) := (rfl)

@[simp]
lemma overSheafEquivFunctorIso_inv_app_hom_app (F : Sheaf ((smallEtaleTopology S).over U) A)
    (W : U.left.Etaleᵒᵖ) :
    ((U.overSheafEquivFunctorIso A).inv.app F).hom.app W =
      𝟙 (F.obj.obj (U.iteratedSliceEquiv.inverse.op.obj W)) := (rfl)

/-- The inverse functor of `U.overSheafEquiv A` is pushforward of sheaves along
`U.iteratedSliceEquiv.functor`. -/
noncomputable def overSheafEquivInverseIso :
    (U.overSheafEquiv A).inverse ≅
      U.iteratedSliceEquiv.functor.sheafPushforwardContinuous A
        ((smallEtaleTopology S).over U) (smallEtaleTopology U.left) :=
  Iso.refl _

@[simp]
lemma overSheafEquivInverseIso_hom_app_hom_app (F : Sheaf (smallEtaleTopology U.left) A)
    (V : (CategoryTheory.Over U)ᵒᵖ) :
    ((U.overSheafEquivInverseIso A).hom.app F).hom.app V =
      𝟙 (F.obj.obj (U.iteratedSliceEquiv.functor.op.obj V)) := (rfl)

@[simp]
lemma overSheafEquivInverseIso_inv_app_hom_app (F : Sheaf (smallEtaleTopology U.left) A)
    (V : (CategoryTheory.Over U)ᵒᵖ) :
    ((U.overSheafEquivInverseIso A).inv.app F).hom.app V =
      𝟙 (F.obj.obj (U.iteratedSliceEquiv.functor.op.obj V)) := (rfl)

/-- Restricting a sheaf on `S.Etale` to `CategoryTheory.Over U` and transporting across
`U.overSheafEquiv A` agrees naturally with sheaf pushforward along `U.hom.smallEtaleMap`. -/
noncomputable def overPullbackCompOverSheafEquivIso :
    (smallEtaleTopology S).overPullback A U ⋙ (U.overSheafEquiv A).functor ≅
      (U.hom : U.left ⟶ S).smallEtaleMap.sheafPushforwardContinuous A
        (smallEtaleTopology U.left) (smallEtaleTopology S) :=
  letI := U.isContinuous_hom_smallEtaleMap
  Functor.isoWhiskerLeft _ (U.overSheafEquivFunctorIso A) ≪≫
    Functor.sheafPushforwardContinuousComp' U.iteratedSliceEquivInverseCompForgetIso A
      (smallEtaleTopology U.left) ((smallEtaleTopology S).over U) (smallEtaleTopology S)

@[simp]
lemma overPullbackCompOverSheafEquivIso_hom_app_hom_app
    (F : Sheaf (smallEtaleTopology S) A) (W : U.left.Etaleᵒᵖ) :
    ((U.overPullbackCompOverSheafEquivIso A).hom.app F).hom.app W =
      F.obj.map (U.iteratedSliceEquivInverseCompForgetIso.inv.app W.unop).op := by
  simp only [overPullbackCompOverSheafEquivIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.sheafPushforwardContinuousComp'_hom_app_hom_app,
    ObjectProperty.FullSubcategory.comp_hom, overSheafEquivFunctorIso_hom_app_hom_app]
  exact Category.id_comp _

@[simp]
lemma overPullbackCompOverSheafEquivIso_inv_app_hom_app
    (F : Sheaf (smallEtaleTopology S) A) (W : U.left.Etaleᵒᵖ) :
    ((U.overPullbackCompOverSheafEquivIso A).inv.app F).hom.app W =
      F.obj.map (U.iteratedSliceEquivInverseCompForgetIso.hom.app W.unop).op := by
  simp only [overPullbackCompOverSheafEquivIso, Iso.trans_inv, NatTrans.comp_app,
    Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app,
    Functor.sheafPushforwardContinuousComp'_inv_app_hom_app,
    ObjectProperty.FullSubcategory.comp_hom, overSheafEquivFunctorIso_inv_app_hom_app]
  exact Category.comp_id _

/-- On an étale sheaf `F` on `S`, transporting `F.over U` across `U.overSheafEquiv A` identifies
with `((U.hom : U.left ⟶ S).smallEtaleMap.sheafPushforwardContinuous A _ _).obj F`. -/
noncomputable abbrev overSheafEquivObjOverIso (F : Sheaf (smallEtaleTopology S) A) :
    (U.overSheafEquiv A).functor.obj (F.over U) ≅
      ((U.hom : U.left ⟶ S).smallEtaleMap.sheafPushforwardContinuous A
        (smallEtaleTopology U.left) (smallEtaleTopology S)).obj F :=
  (U.overPullbackCompOverSheafEquivIso A).app F

/-- Pushforward along `U.iteratedSliceEquiv.inverse` is an equivalence of sheaf categories: it is
the forward functor of `U.overSheafEquiv A`. -/
instance isEquivalence_sheafPushforwardContinuous_iteratedSliceEquiv_inverse :
    (U.iteratedSliceEquiv.inverse.sheafPushforwardContinuous A (smallEtaleTopology U.left)
      ((smallEtaleTopology S).over U)).IsEquivalence :=
  (U.overSheafEquiv A).isEquivalence_functor

end Etale

end AlgebraicGeometry.Scheme
