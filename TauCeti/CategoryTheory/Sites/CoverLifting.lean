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
  locally bijective hypotheses above. It is natural in `Q`
  (`sheafPushforwardContinuousPresheafToSheafIso_hom_naturality`) and in the functor `G`
  (`whiskerRight_op_comp_sheafPushforwardContinuousPresheafToSheafIso_hom_hom`), the identity for
  the identity functor (`sheafPushforwardContinuousPresheafToSheafIso_id_hom_hom`), and compatible
  with composition of functors
  (`whiskerLeft_sheafPushforwardContinuousPresheafToSheafIso_hom_hom_comp_hom_hom`).
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

/-- The restriction along `G` of the unit `Q ⟶ sheafify Q`, followed by
`sheafPushforwardContinuousPresheafToSheafIso G J K Q`, is the unit of the restriction of `Q`. -/
@[simp, reassoc]
theorem whiskerLeft_toSheafify_comp_sheafPushforwardContinuousPresheafToSheafIso_hom_hom
    (Q : Dᵒᵖ ⥤ A) :
    whiskerLeft G.op (toSheafify K Q) ≫
        (G.sheafPushforwardContinuousPresheafToSheafIso J K Q).hom.hom =
      toSheafify J (G.op ⋙ Q) := by
  -- The source of `(… ).hom.hom` is `sheafify K Q` restricted along `G` only after unfolding
  -- `sheafPushforwardContinuous`, so the defining property of the inverse is applied by `exact`.
  have h := toSheafify_sheafPushforwardContinuousPresheafToSheafIso_inv_hom G J K Q =≫
    (G.sheafPushforwardContinuousPresheafToSheafIso J K Q).hom.hom
  rw [Category.assoc, ← ObjectProperty.FullSubcategory.comp_hom, Iso.inv_hom_id] at h
  exact h.symm.trans (Category.comp_id _)

/-- The isomorphisms `sheafPushforwardContinuousPresheafToSheafIso G J K Q` are natural in `Q`. -/
@[reassoc]
theorem sheafPushforwardContinuousPresheafToSheafIso_hom_naturality {Q Q' : Dᵒᵖ ⥤ A}
    (φ : Q ⟶ Q') :
    (G.sheafPushforwardContinuous A J K).map ((presheafToSheaf K A).map φ) ≫
        (G.sheafPushforwardContinuousPresheafToSheafIso J K Q').hom =
      (G.sheafPushforwardContinuousPresheafToSheafIso J K Q).hom ≫
        (presheafToSheaf J A).map (whiskerLeft G.op φ) := by
  rw [← cancel_epi (G.sheafPushforwardContinuousPresheafToSheafIso J K Q).inv,
    Iso.inv_hom_id_assoc,
    ← cancel_mono (G.sheafPushforwardContinuousPresheafToSheafIso J K Q').inv,
    Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  ext1
  refine sheafify_hom_ext J _ _ (ObjectProperty.FullSubcategory.property _) ?_
  simp only [ObjectProperty.FullSubcategory.comp_hom,
    toSheafify_sheafPushforwardContinuousPresheafToSheafIso_inv_hom_assoc]
  rw [← toSheafify_naturality_assoc,
    toSheafify_sheafPushforwardContinuousPresheafToSheafIso_inv_hom]
  -- The restriction of a morphism of sheaves along `G` is the whiskering of its underlying morphism
  -- of presheaves by definition of `sheafPushforwardContinuous`, but its source is
  -- `sheafify K Q` only after unfolding, so `Functor.whiskerLeft_comp` applies through `exact`.
  exact (Functor.whiskerLeft_comp G.op (toSheafify K Q) (sheafifyMap K φ)).symm.trans
    ((congrArg (whiskerLeft G.op) (toSheafify_naturality K φ).symm).trans
      (Functor.whiskerLeft_comp G.op φ (toSheafify K Q')))

omit [G.IsContinuous J K] [G.IsCocontinuous J K] in
/-- For the identity functor, `sheafPushforwardContinuousPresheafToSheafIso` is the identity. -/
theorem sheafPushforwardContinuousPresheafToSheafIso_id_hom_hom (Q : Cᵒᵖ ⥤ A) :
    ((𝟭 C).sheafPushforwardContinuousPresheafToSheafIso J J Q).hom.hom = 𝟙 _ := by
  have h : ((𝟭 C).sheafPushforwardContinuousPresheafToSheafIso J J Q).inv.hom = 𝟙 _ :=
    sheafify_hom_ext J _ _ (ObjectProperty.FullSubcategory.property _)
      ((toSheafify_sheafPushforwardContinuousPresheafToSheafIso_inv_hom (𝟭 C) J J Q).trans
        (Category.comp_id _).symm)
  have h₂ : ((𝟭 C).sheafPushforwardContinuousPresheafToSheafIso J J Q).inv.hom ≫
      ((𝟭 C).sheafPushforwardContinuousPresheafToSheafIso J J Q).hom.hom = 𝟙 _ :=
    congrArg InducedCategory.Hom.hom
      ((𝟭 C).sheafPushforwardContinuousPresheafToSheafIso J J Q).inv_hom_id
  rw [h] at h₂
  exact (Category.id_comp _).symm.trans h₂

/-- The isomorphisms `sheafPushforwardContinuousPresheafToSheafIso` are natural in the functor: a
natural transformation `α : G ⟶ G'` gives a commutative square relating the restrictions along `G`
and `G'` of the sheafification of `Q` to the sheafifications of the restrictions of `Q`. -/
@[reassoc]
theorem whiskerRight_op_comp_sheafPushforwardContinuousPresheafToSheafIso_hom_hom {G' : C ⥤ D}
    [G'.IsContinuous J K] [G'.IsCocontinuous J K] (α : G ⟶ G') (Q : Dᵒᵖ ⥤ A) :
    whiskerRight (NatTrans.op α) (sheafify K Q) ≫
        (G.sheafPushforwardContinuousPresheafToSheafIso J K Q).hom.hom =
      (G'.sheafPushforwardContinuousPresheafToSheafIso J K Q).hom.hom ≫
        sheafifyMap J (whiskerRight (NatTrans.op α) Q) := by
  refine (cancel_epi (G'.sheafPushforwardContinuousPresheafToSheafIso J K Q).inv.hom).1 ?_
  refine sheafify_hom_ext J _ _ (ObjectProperty.FullSubcategory.property _) ?_
  have hx : whiskerLeft G'.op (toSheafify K Q) ≫ whiskerRight (NatTrans.op α) (sheafify K Q) =
      whiskerRight (NatTrans.op α) Q ≫ whiskerLeft G.op (toSheafify K Q) :=
    NatTrans.ext (funext fun X ↦ ((toSheafify K Q).naturality (α.app X.unop).op).symm)
  have e₁ := toSheafify_sheafPushforwardContinuousPresheafToSheafIso_inv_hom G' J K Q
  have e₂ :=
    whiskerLeft_toSheafify_comp_sheafPushforwardContinuousPresheafToSheafIso_hom_hom G J K Q
  have e₃ :=
    whiskerLeft_toSheafify_comp_sheafPushforwardContinuousPresheafToSheafIso_hom_hom G' J K Q
  -- The composites below are only type correct up to unfolding `sheafPushforwardContinuous`, so
  -- `rw` cannot be used and the steps are chained as terms.
  exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) e₁)).trans
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hx).trans ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) e₂).trans ((toSheafify_naturality J _).trans
        ((congrArg (· ≫ _) e₃.symm).trans ((congrArg (fun x ↦ (x ≫ _) ≫ _) e₁.symm).trans
          ((Category.assoc _ _ _).trans (Category.assoc _ _ _)))))))))

/-- The isomorphisms `sheafPushforwardContinuousPresheafToSheafIso` are compatible with
composition of functors: restricting along `G` and then along `G'` is restricting along
`G' ⋙ G`. -/
theorem whiskerLeft_sheafPushforwardContinuousPresheafToSheafIso_hom_hom_comp_hom_hom
    {C' : Type*} [Category* C'] (G' : C' ⥤ C) (J' : GrothendieckTopology C')
    [G'.IsContinuous J' J] [G'.IsCocontinuous J' J] [(G' ⋙ G).IsContinuous J' K]
    [(G' ⋙ G).IsCocontinuous J' K] [J'.WEqualsLocallyBijective A] [HasWeakSheafify J' A]
    (Q : Dᵒᵖ ⥤ A) :
    whiskerLeft G'.op (G.sheafPushforwardContinuousPresheafToSheafIso J K Q).hom.hom ≫
        (G'.sheafPushforwardContinuousPresheafToSheafIso J' J (G.op ⋙ Q)).hom.hom =
      ((G' ⋙ G).sheafPushforwardContinuousPresheafToSheafIso J' K Q).hom.hom := by
  refine (cancel_epi ((G' ⋙ G).sheafPushforwardContinuousPresheafToSheafIso J' K Q).inv.hom).1 ?_
  refine sheafify_hom_ext J' _ _ (ObjectProperty.FullSubcategory.property _) ?_
  have e₁ := toSheafify_sheafPushforwardContinuousPresheafToSheafIso_inv_hom (G' ⋙ G) J' K Q
  have e₂ :=
    whiskerLeft_toSheafify_comp_sheafPushforwardContinuousPresheafToSheafIso_hom_hom G J K Q
  have e₃ := whiskerLeft_toSheafify_comp_sheafPushforwardContinuousPresheafToSheafIso_hom_hom
    G' J' J (G.op ⋙ Q)
  have e₄ := whiskerLeft_toSheafify_comp_sheafPushforwardContinuousPresheafToSheafIso_hom_hom
    (G' ⋙ G) J' K Q
  -- As above, the composites are only type correct up to unfolding, so the steps are chained as
  -- terms; `whiskerLeft (G' ⋙ G).op` is `whiskerLeft G'.op ∘ whiskerLeft G.op` by definition.
  exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) e₁)).trans
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ _) (Functor.whiskerLeft_comp G'.op _ _).symm).trans
        ((congrArg (fun x ↦ whiskerLeft G'.op x ≫ _) e₂).trans (e₃.trans
          (((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) e₁)).trans e₄).symm))))

end Functor

end CategoryTheory
