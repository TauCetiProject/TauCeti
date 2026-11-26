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
  locally bijective hypotheses above. Morphisms out of the restriction of a sheafification are
  determined on the restricted unit (`whiskerLeft_toSheafify_hom_ext`). It is natural in `Q`
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

omit [G.IsContinuous J K] [HasWeakSheafify J A] in
/-- Morphisms from the restriction along `G` of the sheafification of `Q` to a sheaf are determined
by their composites with the restriction of the unit `Q ⟶ sheafify Q`, which becomes an
isomorphism after sheafification. -/
theorem whiskerLeft_toSheafify_hom_ext {Q : Dᵒᵖ ⥤ A} {P : Cᵒᵖ ⥤ A} (hP : Presheaf.IsSheaf J P)
    {f g : G.op ⋙ sheafify K Q ⟶ P}
    (h : whiskerLeft G.op (toSheafify K Q) ≫ f = whiskerLeft G.op (toSheafify K Q) ≫ g) :
    f = g :=
  ((K.W_toSheafify Q).whiskerLeft_op G J P hP).1 h

/-- The isomorphisms `sheafPushforwardContinuousPresheafToSheafIso G J K Q` are natural in `Q`. -/
@[reassoc]
theorem sheafPushforwardContinuousPresheafToSheafIso_hom_naturality {Q Q' : Dᵒᵖ ⥤ A}
    (φ : Q ⟶ Q') :
    (G.sheafPushforwardContinuous A J K).map ((presheafToSheaf K A).map φ) ≫
        (G.sheafPushforwardContinuousPresheafToSheafIso J K Q').hom =
      (G.sheafPushforwardContinuousPresheafToSheafIso J K Q).hom ≫
        (presheafToSheaf J A).map (whiskerLeft G.op φ) := by
  ext1
  refine whiskerLeft_toSheafify_hom_ext G J K (ObjectProperty.FullSubcategory.property _) ?_
  have hn : whiskerLeft G.op (toSheafify K Q) ≫ whiskerLeft G.op (sheafifyMap K φ) =
      whiskerLeft G.op φ ≫ whiskerLeft G.op (toSheafify K Q') := by
    rw [← Functor.whiskerLeft_comp, ← Functor.whiskerLeft_comp, toSheafify_naturality]
  simp only [ObjectProperty.FullSubcategory.comp_hom]
  -- Both sides are `whiskerLeft G.op φ ≫ toSheafify J (G.op ⋙ Q')`. The restriction of a morphism
  -- of sheaves along `G` is the whiskering of its underlying morphism of presheaves only after
  -- unfolding `sheafPushforwardContinuous`, so the steps are chained as terms.
  exact ((reassoc_of% hn) _).trans ((congrArg (_ ≫ ·)
    (whiskerLeft_toSheafify_comp_sheafPushforwardContinuousPresheafToSheafIso_hom_hom
      G J K Q')).trans
      ((toSheafify_naturality J (whiskerLeft G.op φ)).trans
        ((whiskerLeft_toSheafify_comp_sheafPushforwardContinuousPresheafToSheafIso_hom_hom_assoc
          G J K Q _).symm.trans (Category.assoc _ _ _))))

omit [G.IsContinuous J K] [G.IsCocontinuous J K] in
/-- For the identity functor, `sheafPushforwardContinuousPresheafToSheafIso` is the identity. -/
theorem sheafPushforwardContinuousPresheafToSheafIso_id_hom_hom (Q : Cᵒᵖ ⥤ A) :
    ((𝟭 C).sheafPushforwardContinuousPresheafToSheafIso J J Q).hom.hom = 𝟙 _ :=
  whiskerLeft_toSheafify_hom_ext (𝟭 C) J J (ObjectProperty.FullSubcategory.property _)
    ((whiskerLeft_toSheafify_comp_sheafPushforwardContinuousPresheafToSheafIso_hom_hom
      (𝟭 C) J J Q).trans (Category.comp_id _).symm)

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
  refine whiskerLeft_toSheafify_hom_ext G' J K (ObjectProperty.FullSubcategory.property _) ?_
  have hx : whiskerLeft G'.op (toSheafify K Q) ≫ whiskerRight (NatTrans.op α) (sheafify K Q) =
      whiskerRight (NatTrans.op α) Q ≫ whiskerLeft G.op (toSheafify K Q) :=
    NatTrans.ext (funext fun X ↦ ((toSheafify K Q).naturality (α.app X.unop).op).symm)
  -- Both sides are `whiskerRight (NatTrans.op α) Q ≫ toSheafify J (G.op ⋙ Q)`; the composites are
  -- only type correct up to unfolding `sheafPushforwardContinuous`, so the steps are chained as
  -- terms.
  exact ((reassoc_of% hx) _).trans ((congrArg (_ ≫ ·)
    (whiskerLeft_toSheafify_comp_sheafPushforwardContinuousPresheafToSheafIso_hom_hom
      G J K Q)).trans
      ((toSheafify_naturality J _).trans
        ((whiskerLeft_toSheafify_comp_sheafPushforwardContinuousPresheafToSheafIso_hom_hom_assoc
          G' J K Q _).symm.trans (Category.assoc _ _ _))))

/-- The isomorphisms `sheafPushforwardContinuousPresheafToSheafIso` are compatible with
composition of functors: restricting along `G` and then along `G'` is restricting along
`G' ⋙ G`. -/
theorem whiskerLeft_sheafPushforwardContinuousPresheafToSheafIso_hom_hom_comp_hom_hom
    {C' : Type*} [Category* C'] (G' : C' ⥤ C) (J' : GrothendieckTopology C')
    [G'.IsContinuous J' J] [G'.IsCocontinuous J' J] [J'.WEqualsLocallyBijective A]
    [HasWeakSheafify J' A] (Q : Dᵒᵖ ⥤ A) :
    letI := isContinuous_comp G' G J' J K
    letI := isCocontinuous_comp G' G J' J (L := K)
    whiskerLeft G'.op (G.sheafPushforwardContinuousPresheafToSheafIso J K Q).hom.hom ≫
        (G'.sheafPushforwardContinuousPresheafToSheafIso J' J (G.op ⋙ Q)).hom.hom =
      ((G' ⋙ G).sheafPushforwardContinuousPresheafToSheafIso J' K Q).hom.hom := by
  have := isContinuous_comp G' G J' J K
  have := isCocontinuous_comp G' G J' J (L := K)
  refine whiskerLeft_toSheafify_hom_ext (G' ⋙ G) J' K
    (ObjectProperty.FullSubcategory.property _) ?_
  -- Both sides are `toSheafify J' ((G' ⋙ G).op ⋙ Q)`. As above, the composites are only type
  -- correct up to unfolding, so the steps are chained as terms; `whiskerLeft (G' ⋙ G).op` is
  -- `whiskerLeft G'.op ∘ whiskerLeft G.op` by definition.
  exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _)
    ((Functor.whiskerLeft_comp G'.op _ _).symm.trans (congrArg (whiskerLeft G'.op)
      (whiskerLeft_toSheafify_comp_sheafPushforwardContinuousPresheafToSheafIso_hom_hom
        G J K Q))))).trans
    ((whiskerLeft_toSheafify_comp_sheafPushforwardContinuousPresheafToSheafIso_hom_hom
      G' J' J (G.op ⋙ Q)).trans
      (whiskerLeft_toSheafify_comp_sheafPushforwardContinuousPresheafToSheafIso_hom_hom
        (G' ⋙ G) J' K Q).symm)

end Functor

end CategoryTheory
