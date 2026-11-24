/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective

/-!
# Sheafification of a comparison into a restricted presheaf

Let `G : C ⥤ D` be continuous and cocontinuous for topologies `J` on `C` and `K` on `D`, so that
restriction along `G` commutes with sheafification
(`Functor.pushforwardContinuousSheafificationCompatibility`). A morphism of presheaves
`e : P ⟶ G.op ⋙ Q` then sheafifies to a morphism from the sheafification of `P` to the
restriction of the sheafification of `Q`, and this sheafified comparison is compatible with the
canonical maps of `P` and `Q` into their sheafifications.

Mathlib's compatibility assumes that `G.op` has pointwise right Kan extensions. For a concrete
category `A` in which the morphisms inverted by sheafification are the locally bijective ones, on
both sites (`CategoryTheory.GrothendieckTopology.WEqualsLocallyBijective`), restriction along `G`
also commutes with sheafification without that assumption, because restriction along a
cocontinuous functor preserves local injectivity and local surjectivity
(`CategoryTheory.Presheaf.isLocallyInjective_whisker`,
`CategoryTheory.Presheaf.isLocallySurjective_whisker`). This applies for instance to
`Over.forget U` on the small étale site with values in `ModuleCat Λ`, where the Kan extensions
are not available.

## Main results

* `CategoryTheory.Functor.toSheafify_comp_sheafifyMap_comp_sheafificationCompatibility_hom`: the
  canonical map of `P` followed by the sheafified comparison is `e` followed by the restriction of
  the canonical map of `Q`.
* `CategoryTheory.GrothendieckTopology.W.whiskerLeft_op`: restriction along a cocontinuous
  functor sends morphisms inverted by sheafification to morphisms inverted by sheafification.
* `CategoryTheory.Functor.sheafPushforwardContinuousPresheafToSheafIso`: the restriction along
  `G` of the sheafification of `Q` is the sheafification of the restriction of `Q`, under the
  locally bijective hypotheses above.
-/

public section

open CategoryTheory

namespace CategoryTheory.Functor

variable {C : Type*} [Category* C] {D : Type*} [Category* D] (G : C ⥤ D)
  (A : Type*) [Category* A] (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [G.IsContinuous J K] [G.IsCocontinuous J K]
  [∀ (F : Cᵒᵖ ⥤ A), G.op.HasPointwiseRightKanExtension F]
  [HasWeakSheafify J A] [HasWeakSheafify K A]

/-- Sheafifying a comparison `e : P ⟶ G.op ⋙ Q` and composing with the compatibility of
restriction along `G` with sheafification sends the canonical map of `P` into its sheafification
to `e` followed by the restriction of the canonical map of `Q`. -/
@[reassoc]
lemma toSheafify_comp_sheafifyMap_comp_sheafificationCompatibility_hom {P : Cᵒᵖ ⥤ A}
    {Q : Dᵒᵖ ⥤ A} (e : P ⟶ G.op ⋙ Q) :
    toSheafify J P ≫ sheafifyMap J e ≫
        ((G.pushforwardContinuousSheafificationCompatibility A J K).hom.app Q).hom =
      e ≫ whiskerLeft G.op (toSheafify K Q) := by
  rw [← reassoc_of% toSheafify_naturality]
  exact e ≫= G.toSheafify_pullbackSheafificationCompatibility A J K Q

end CategoryTheory.Functor

namespace CategoryTheory

variable {C : Type*} [Category* C] {D : Type*} [Category* D] {A : Type*} [Category* A]
  {FA : A → A → Type*} {CA : A → Type*} [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)]
  [ConcreteCategory A FA]

include FA CA

/-- Restriction along a cocontinuous functor sends morphisms of presheaves which become
isomorphisms after sheafification to morphisms with the same property. -/
theorem GrothendieckTopology.W.whiskerLeft_op {K : GrothendieckTopology D}
    [K.WEqualsLocallyBijective A] {P Q : Dᵒᵖ ⥤ A} {f : P ⟶ Q} (hf : K.W f) (G : C ⥤ D)
    (J : GrothendieckTopology C) [G.IsCocontinuous J K] [J.WEqualsLocallyBijective A] :
    J.W (Functor.whiskerLeft G.op f) :=
  have := hf.isLocallyInjective
  have := hf.isLocallySurjective
  have := Presheaf.isLocallyInjective_whisker J K G f
  have := Presheaf.isLocallySurjective_whisker J K G f
  GrothendieckTopology.W_of_isLocallyBijective _ _

namespace Functor

variable (G : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [G.IsContinuous J K] [G.IsCocontinuous J K] [J.WEqualsLocallyBijective A]
  [K.WEqualsLocallyBijective A] [HasWeakSheafify J A] [HasWeakSheafify K A]

/-- **Restriction of a sheafification.** The restriction along `G` of the sheafification of a
presheaf `Q` is the sheafification of the restriction of `Q`. -/
noncomputable def sheafPushforwardContinuousPresheafToSheafIso (Q : Dᵒᵖ ⥤ A) :
    (G.sheafPushforwardContinuous A J K).obj ((presheafToSheaf K A).obj Q) ≅
      (presheafToSheaf J A).obj (G.op ⋙ Q) :=
  have := (J.W_iff _).1 ((K.W_toSheafify Q).whiskerLeft_op G J)
  sheafificationIso _ ≪≫
    (presheafToSheaf J A).mapIso
      ((G.sheafPushforwardContinuousCompSheafToPresheafIso A J K).app _) ≪≫
    (asIso ((presheafToSheaf J A).map (whiskerLeft G.op (toSheafify K Q)))).symm

/-- The inverse of `sheafPushforwardContinuousPresheafToSheafIso G J K Q` is the morphism induced
on sheafifications by the restriction of the unit `Q ⟶ sheafify Q`: it sends the unit of the
restriction of `Q` to the restriction of the unit of `Q`. -/
@[reassoc (attr := simp)]
theorem toSheafify_sheafPushforwardContinuousPresheafToSheafIso_inv_hom (Q : Dᵒᵖ ⥤ A) :
    toSheafify J (G.op ⋙ Q) ≫ (G.sheafPushforwardContinuousPresheafToSheafIso J K Q).inv.hom =
      whiskerLeft G.op (toSheafify K Q) := by
  simp only [sheafPushforwardContinuousPresheafToSheafIso, Functor.comp_obj, ObjectProperty.ι_obj,
    Functor.whiskeringLeft_obj_obj, Iso.trans_inv, Iso.symm_inv, asIso_hom, Functor.mapIso_inv,
    Iso.app_inv, Category.assoc, ObjectProperty.FullSubcategory.comp_hom, sheafificationIso_inv_hom,
    isoSheafify_inv, sheafifyMap_sheafifyLift, Category.comp_id, toSheafify_sheafifyLift]
  -- The remaining identity component of `sheafPushforwardContinuousCompSheafToPresheafIso` is
  -- indexed by the sections of the restriction of `(presheafToSheaf K A).obj Q`, which are those
  -- of `sheafify K Q` only after unfolding `sheafPushforwardContinuous`, so `simp` cannot drop it.
  exact Category.comp_id _

end Functor

end CategoryTheory
