/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Preorder.TransfiniteCompositionOfShape
public import TauCeti.CategoryTheory.Limits.Preserves.Shapes.Preorder

/-!
# Cobase change of transfinite compositions

Let `h : TransfiniteCompositionOfShape J f` present `f : X ⟶ Y` as the transfinite composition of
a well-order-continuous functor `h.F : J ⥤ C`, and let `g : X ⟶ Z` be any morphism. Then the
cobase change `pushout.inr f g : Z ⟶ pushout f g` is the transfinite composition of the pushouts
along `g` of the stages of `h` (`CategoryTheory.TransfiniteCompositionOfShape.pushout`), and the
square comparing each map between two stages of `h` with its cobase change is a pushout
(`CategoryTheory.TransfiniteCompositionOfShape.isPushout_pushoutStageMap`).

The stages of `h` are objects under `X`
(`CategoryTheory.TransfiniteCompositionOfShape.stagesUnder`), whose colimit is `Under.mk f`.
Their cobase changes are their images under the functor `Under.pushout g : Under X ⥤ Under Z`,
which preserves colimits as a left adjoint, followed by the forgetful functor `Under Z ⥤ C`, which
preserves the connected colimits indexed by the nonempty linear orders `J` and `Set.Iio j`.

This is the categorical input for the stability of relative cell complexes under cobase change.

## Main definitions

* `CategoryTheory.TransfiniteCompositionOfShape.toStage`: the map from the source of `f` to a stage.
* `CategoryTheory.TransfiniteCompositionOfShape.pushout`: the cobase change of a transfinite
  composition.

## Main results

* `CategoryTheory.TransfiniteCompositionOfShape.isPushout_pushoutStageMap`: each map between two
  stages of the cobase change is the pushout of the corresponding map of `h`.

## References

* M. Hovey, *Model Categories*, Mathematical Surveys and Monographs 63, American Mathematical
  Society, 1999, Section 2.1, for the stability of transfinite compositions of pushouts under
  cobase change.
-/

public section

universe w' v u

namespace CategoryTheory.TransfiniteCompositionOfShape

open Limits

variable {C : Type u} [Category.{v} C]
  {J : Type w'} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  {X Y : C} {f : X ⟶ Y} (h : TransfiniteCompositionOfShape J f)

/-- The map from the source of `f` to the `j`-th stage of `h`, through `X ≅ h.F.obj ⊥`. -/
noncomputable def toStage (j : J) : X ⟶ h.F.obj j :=
  h.isoBot.inv ≫ h.F.map (homOfLE bot_le)

/-- The maps from the source of `f` to the stages are compatible with the maps between stages. -/
@[reassoc (attr := simp)]
lemma toStage_comp_map {j k : J} (φ : j ⟶ k) : h.toStage j ≫ h.F.map φ = h.toStage k := by
  rw [toStage, Category.assoc, ← Functor.map_comp]
  rfl

/-- The map from the source of `f` to the bottom stage is the inverse of `h.isoBot`. -/
@[simp]
lemma toStage_bot : h.toStage ⊥ = h.isoBot.inv := by
  simp [toStage, homOfLE_refl]

/-- The map from the source of `f` to a stage, followed by the map to the colimit, is `f`. -/
@[reassoc (attr := simp)]
lemma toStage_comp_incl_app (j : J) : h.toStage j ≫ h.incl.app j = f := by
  rw [toStage, Category.assoc, h.incl.naturality]
  simp [h.fac]

/-- The stages of `h` as objects under `X`, through the maps `h.toStage j`. Exposed so that the
stages of `h.pushout g` are the pushouts `pushout (h.toStage j) g` by definition. -/
@[expose, simps]
noncomputable def stagesUnder : J ⥤ Under X where
  obj j := Under.mk (h.toStage j)
  map φ := Under.homMk (h.F.map φ) (h.toStage_comp_map φ)
  map_id j := Under.UnderMorphism.ext (h.F.map_id j)
  map_comp φ ψ := Under.UnderMorphism.ext (h.F.map_comp φ ψ)

/-- The stages of `h` under `X` are well-order-continuous, since the forgetful functor from
`Under X` creates the connected colimits indexed by `Set.Iio j`. -/
instance : h.stagesUnder.IsWellOrderContinuous where
  nonempty_isColimit j hj := by
    obtain ⟨k, hk⟩ := not_isMin_iff.1 hj.1
    have : Nonempty (Set.Iio j) := ⟨⟨k, hk⟩⟩
    exact ⟨isColimitOfReflects (Under.forget X) (h.F.isColimitOfIsWellOrderContinuous j hj)⟩

/-- The cocone over `h.stagesUnder` with vertex `Under.mk f`, given by the maps to the colimit.
Exposed so that its image under `Under.pushout g` is the cocone of `h.pushout g` by definition. -/
@[expose, simps]
noncomputable def underCocone : Cocone h.stagesUnder where
  pt := Under.mk f
  ι :=
    { app j := Under.homMk (h.incl.app j) (h.toStage_comp_incl_app j)
      naturality _ _ φ := Under.UnderMorphism.ext (h.incl.naturality φ) }

/-- `Under.mk f` is the colimit of the stages of `h`, viewed under `X`. -/
noncomputable def isColimitUnderCocone : IsColimit h.underCocone :=
  isColimitOfReflects (Under.forget X) h.isColimit

variable {Z : C} (g : X ⟶ Z) [HasPushoutsAlong g]

/-- The map between the cobase changes along `g` of two stages of `h`. Exposed so that it is the
map between the stages of `h.pushout g` by definition. -/
@[expose] noncomputable def pushoutStageMap {j k : J} (φ : j ⟶ k) :
    Limits.pushout (h.toStage j) g ⟶ Limits.pushout (h.toStage k) g :=
  pushout.desc (h.F.map φ ≫ pushout.inl _ _) (pushout.inr _ _) (by
    rw [← Category.assoc, h.toStage_comp_map, pushout.condition])

/-- `h.pushoutStageMap g φ` restricts to `h.F.map φ` on the stages. -/
@[reassoc (attr := simp)]
lemma inl_pushoutStageMap {j k : J} (φ : j ⟶ k) :
    pushout.inl (h.toStage j) g ≫ h.pushoutStageMap g φ = h.F.map φ ≫ pushout.inl _ _ :=
  pushout.inl_desc _ _ _

/-- `h.pushoutStageMap g φ` is the identity on the target of `g`. -/
@[reassoc (attr := simp)]
lemma inr_pushoutStageMap {j k : J} (φ : j ⟶ k) :
    pushout.inr (h.toStage j) g ≫ h.pushoutStageMap g φ = pushout.inr _ _ :=
  pushout.inr_desc _ _ _

/-- The square comparing a map between two stages of `h` with its cobase change along `g` is a
pushout. -/
lemma isPushout_pushoutStageMap {j k : J} (φ : j ⟶ k) :
    IsPushout (h.F.map φ) (pushout.inl (h.toStage j) g) (pushout.inl (h.toStage k) g)
      (h.pushoutStageMap g φ) := by
  refine IsPushout.of_left ?_ (h.inl_pushoutStageMap g φ).symm
    (IsPushout.of_hasPushout (h.toStage j) g)
  rw [h.toStage_comp_map, h.inr_pushoutStageMap]
  exact IsPushout.of_hasPushout _ _

/-- The cobase change of the bottom stage is the target of `g`. -/
instance : IsIso (pushout.inr (h.toStage ⊥) g) := by
  rw [toStage_bot]
  infer_instance

/-- The map from the cobase change along `g` of the `j`-th stage of `h` to `pushout f g`. Exposed
so that it is the image of the map from the `j`-th stage of `h` to `f`'s target under
`Under.pushout g` by definition. -/
@[expose] noncomputable def pushoutStageIncl (j : J) :
    Limits.pushout (h.toStage j) g ⟶ Limits.pushout f g :=
  pushout.desc (h.incl.app j ≫ pushout.inl f g) (pushout.inr f g) (by
    rw [h.toStage_comp_incl_app_assoc, pushout.condition])

/-- `h.pushoutStageIncl g j` restricts to the map from the `j`-th stage to the colimit. -/
@[reassoc (attr := simp)]
lemma inl_pushoutStageIncl (j : J) :
    pushout.inl (h.toStage j) g ≫ h.pushoutStageIncl g j = h.incl.app j ≫ pushout.inl f g :=
  pushout.inl_desc _ _ _

/-- `h.pushoutStageIncl g j` is `pushout.inr f g` on the target of `g`. -/
@[reassoc (attr := simp)]
lemma inr_pushoutStageIncl (j : J) :
    pushout.inr (h.toStage j) g ≫ h.pushoutStageIncl g j = pushout.inr f g :=
  pushout.inr_desc _ _ _

/-- The maps `h.pushoutStageIncl g j` are compatible with the maps between the stages. -/
@[reassoc (attr := simp)]
lemma pushoutStageMap_pushoutStageIncl {j k : J} (φ : j ⟶ k) :
    h.pushoutStageMap g φ ≫ h.pushoutStageIncl g k = h.pushoutStageIncl g j := by
  apply pushout.hom_ext <;> simp

/-- **Cobase change of a transfinite composition.** The cobase change `pushout.inr f g` of a
transfinite composition `h` of `f` along `g` is a transfinite composition. Its `j`-th stage
is the pushout of `h.toStage j` along `g`, the image of the `j`-th stage of `h` under
`Under.pushout g`. The body is exposed so that its stages and the maps between them are the
pushouts `pushout (h.toStage j) g` and the maps `h.pushoutStageMap g φ` by definition. -/
@[expose] noncomputable def pushout : TransfiniteCompositionOfShape J (Limits.pushout.inr f g) where
  F := (h.stagesUnder ⋙ Under.pushout g) ⋙ Under.forget Z
  isoBot := (asIso (pushout.inr (h.toStage ⊥) g)).symm
  incl :=
    { app j := h.pushoutStageIncl g j
      naturality j k φ :=
        (h.pushoutStageMap_pushoutStageIncl g φ).trans (Category.comp_id _).symm }
  isColimit :=
    (isColimitOfPreserves (Under.pushout g ⋙ Under.forget Z) h.isColimitUnderCocone).ofIsoColimit
      (Cocone.ext (Iso.refl _) fun _ ↦ Category.comp_id _)
  fac := h.inr_pushoutStageIncl g ⊥

/-- The `j`-th stage of `h.pushout g` is the pushout of `h.toStage j` along `g`. -/
lemma pushout_F_obj (j : J) :
    (h.pushout g).F.obj j = Limits.pushout (h.toStage j) g :=
  rfl

/-- The maps between the stages of `h.pushout g` are the maps `h.pushoutStageMap g φ`. -/
@[simp]
lemma pushout_F_map {j k : J} (φ : j ⟶ k) :
    (h.pushout g).F.map φ = h.pushoutStageMap g φ :=
  (rfl)

/-- The maps from the stages of `h.pushout g` to `pushout f g` are `h.pushoutStageIncl g j`. -/
@[simp]
lemma pushout_incl_app (j : J) :
    (h.pushout g).incl.app j = h.pushoutStageIncl g j :=
  (rfl)

end CategoryTheory.TransfiniteCompositionOfShape
