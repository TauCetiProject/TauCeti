/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Functoriality of derived functors of exact functors

An exact functor `F : C₁ ⥤ C₂` between abelian categories induces Mathlib's derived functor
`F.mapDerivedCategory : D(C₁) ⥤ D(C₂)`, and a natural transformation `τ : F ⟶ G` of exact
functors induces the natural transformation `NatTrans.mapDerivedCategory τ` between the derived
functors. This file records that the induced natural transformations are functorial in `τ`
(`CategoryTheory.NatTrans.mapDerivedCategory_id`,
`CategoryTheory.NatTrans.mapDerivedCategory_comp`), so that an isomorphism of exact functors
induces a natural isomorphism of derived functors (`CategoryTheory.NatIso.mapDerivedCategory`).

Mathlib compares the derived functor of a composite with the composite of derived functors by
`CategoryTheory.Functor.mapDerivedCategoryCompIso`. Composing it with the natural transformation
induced by `τ : F ⋙ G ⟶ H` gives a natural transformation `F' ⋙ G' ⟶ H'` between the derived
functors; on a complex `K` it is described by
`CategoryTheory.Functor.mapDerivedCategoryCompIso_hom_app_comp_mapDerivedCategory_app_Q_obj`.
These comparisons satisfy the associativity and unit laws of a pseudofunctor
(`CategoryTheory.Functor.mapDerivedCategoryCompIso_associativity`,
`CategoryTheory.Functor.mapDerivedCategoryCompIso_left_unitality`,
`CategoryTheory.Functor.mapDerivedCategoryCompIso_right_unitality`): if two comparisons agree on
the abelian level, so do the induced comparisons on derived categories, where an identification
of an exact functor with the identity induces one of its derived functor with the identity
through Mathlib's `CategoryTheory.Functor.mapDerivedCategoryIdIso`, described on objects placed
in any degree by `CategoryTheory.Functor.mapDerivedCategoryIdIso_hom_app_singleFunctor_obj'`.
This is the coherence used for derived restriction of module sheaves to nested open subschemes.
-/

public section

open CategoryTheory Limits DerivedCategory

universe w₁ w₂ w₃ w₄

variable {C₁ : Type*} [Category* C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
  {C₂ : Type*} [Category* C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
  {C₃ : Type*} [Category* C₃] [Abelian C₃] [HasDerivedCategory.{w₃} C₃]
  {C₄ : Type*} [Category* C₄] [Abelian C₄] [HasDerivedCategory.{w₄} C₄]

namespace CategoryTheory.NatTrans

variable {F G H : C₁ ⥤ C₂} [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]

/-- The natural transformation induced by the identity transformation is the identity. -/
@[simp]
lemma mapDerivedCategory_id : NatTrans.mapDerivedCategory (𝟙 F) = 𝟙 F.mapDerivedCategory := by
  rw [NatTrans.mapDerivedCategory, NatTrans.mapHomologicalComplex_id, Functor.whiskerRight_id']
  exact Localization.liftNatTrans_id ..

/-- The natural transformation induced by a composite of natural transformations is the composite
of the induced natural transformations. -/
@[simp, reassoc]
lemma mapDerivedCategory_comp (τ : F ⟶ G) (τ' : G ⟶ H) :
    NatTrans.mapDerivedCategory (τ ≫ τ') =
      NatTrans.mapDerivedCategory τ ≫ NatTrans.mapDerivedCategory τ' := by
  rw [NatTrans.mapDerivedCategory, NatTrans.mapHomologicalComplex_comp, Functor.whiskerRight_comp]
  exact (Localization.comp_liftNatTrans ..).symm

end CategoryTheory.NatTrans

namespace CategoryTheory.NatIso

variable {F G : C₁ ⥤ C₂} [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- An isomorphism of exact functors induces a natural isomorphism of their derived functors. -/
noncomputable def mapDerivedCategory (α : F ≅ G) :
    F.mapDerivedCategory ≅ G.mapDerivedCategory :=
  Localization.liftNatIso Q (HomologicalComplex.quasiIso C₁ (ComplexShape.up ℤ)) _ _ _ _
    (Functor.isoWhiskerRight (NatIso.mapHomologicalComplex α (ComplexShape.up ℤ)) Q)

/-- The forward map of the induced isomorphism is Mathlib's induced natural transformation. -/
@[simp]
lemma mapDerivedCategory_hom (α : F ≅ G) :
    (mapDerivedCategory α).hom = NatTrans.mapDerivedCategory α.hom := (rfl)

/-- The inverse map of the induced isomorphism is Mathlib's induced natural transformation. -/
@[simp]
lemma mapDerivedCategory_inv (α : F ≅ G) :
    (mapDerivedCategory α).inv = NatTrans.mapDerivedCategory α.inv := (rfl)

/-- The induced isomorphism commutes with integer shifts. -/
instance (α : F ≅ G) : NatTrans.CommShift (mapDerivedCategory α).hom ℤ :=
  inferInstanceAs (NatTrans.CommShift (NatTrans.mapDerivedCategory α.hom) ℤ)

end CategoryTheory.NatIso

namespace CategoryTheory.Functor

/-- On an object `X` placed in degree `n`, Mathlib's identification
`mapDerivedCategoryIdIso` of the derived functor of the identity with the identity is the
identification `mapDerivedCategorySingleFunctor n` of that derived functor on objects in degree
`n`. Mathlib states this in degree `0` as `mapDerivedCategoryIdIso_hom_app_singleFunctor_obj`. -/
lemma mapDerivedCategoryIdIso_hom_app_singleFunctor_obj' (X : C₁) (n : ℤ) :
    (mapDerivedCategoryIdIso C₁).hom.app ((singleFunctor C₁ n).obj X) =
      ((𝟭 C₁).mapDerivedCategorySingleFunctor n).hom.app X := by
  simp [← Q_obj_single_obj, mapDerivedCategoryIdIso_hom_app,
    mapDerivedCategorySingleFunctor_hom_app,
    HomologicalComplex.singleMapHomologicalComplex_id_hom_app, singleFunctorIsoCompQ_hom_app,
    singleFunctorIsoCompQ_inv_app]

section Comp

variable (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₃) {H : C₁ ⥤ C₃}
  [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]

/-- On the image of a complex `K`, the comparison `F' ⋙ G' ⟶ H'` of derived functors induced by
`τ : F ⋙ G ⟶ H` is `Q` applied to `τ` on the terms of `K`, up to the identifications
`mapDerivedCategoryFactors` of the derived functors on complexes. -/
@[reassoc]
lemma mapDerivedCategoryCompIso_hom_app_comp_mapDerivedCategory_app_Q_obj (τ : F ⋙ G ⟶ H)
    (K : CochainComplex C₁ ℤ) :
    (mapDerivedCategoryCompIso F G).hom.app (Q.obj K) ≫
      (NatTrans.mapDerivedCategory τ).app (Q.obj K) =
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
        G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex _).obj K) ≫
          Q.map ((NatTrans.mapHomologicalComplex τ (.up ℤ)).app K) ≫
            H.mapDerivedCategoryFactors.inv.app K := by
  -- Mathlib's comparison is induced by the identity of `F ⋙ G` on complexes.
  have : (mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).hom.app K = 𝟙 _ :=
    congr_app (NatTrans.mapHomologicalComplex_id (.up ℤ) (F ⋙ G)) K
  simp [mapDerivedCategoryCompIso_hom_app_Q_obj, NatTrans.mapDerivedCategory_app_Q_obj, this]

end Comp

section Associativity

variable (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₃) (H : C₃ ⥤ C₄) {FG : C₁ ⥤ C₃} {GH : C₂ ⥤ C₄}
  {FGH : C₁ ⥤ C₄}
  [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [FG.Additive] [PreservesFiniteLimits FG] [PreservesFiniteColimits FG]
  [GH.Additive] [PreservesFiniteLimits GH] [PreservesFiniteColimits GH]
  [FGH.Additive] [PreservesFiniteLimits FGH] [PreservesFiniteColimits FGH]

/-- Associativity of the comparisons of derived functors of composites. Let `τ₁, τ₂` and `τ₃, τ₄`
be two ways of comparing `F ⋙ G ⋙ H` with an exact functor `FGH`, through `FG` and through `GH`,
which agree on the abelian level. Then the induced comparisons of
`F.mapDerivedCategory ⋙ G.mapDerivedCategory ⋙ H.mapDerivedCategory` with
`FGH.mapDerivedCategory`, each built from `mapDerivedCategoryCompIso` and the derived
`τᵢ`, agree as well. -/
theorem mapDerivedCategoryCompIso_associativity (τ₁ : F ⋙ G ⟶ FG) (τ₂ : FG ⋙ H ⟶ FGH)
    (τ₃ : G ⋙ H ⟶ GH) (τ₄ : F ⋙ GH ⟶ FGH)
    (h : whiskerRight τ₁ H ≫ τ₂ = (associator F G H).hom ≫ whiskerLeft F τ₃ ≫ τ₄) :
    whiskerRight ((mapDerivedCategoryCompIso F G).hom ≫ NatTrans.mapDerivedCategory τ₁)
        H.mapDerivedCategory ≫
      (mapDerivedCategoryCompIso FG H).hom ≫ NatTrans.mapDerivedCategory τ₂ =
    (associator _ _ _).hom ≫
      whiskerLeft F.mapDerivedCategory
        ((mapDerivedCategoryCompIso G H).hom ≫ NatTrans.mapDerivedCategory τ₃) ≫
      (mapDerivedCategoryCompIso F GH).hom ≫ NatTrans.mapDerivedCategory τ₄ := by
  -- Both sides are determined by their values on complexes `Q.obj K`, followed by the
  -- identification of `FGH'` on complexes. There, each comparison is computed by
  -- `mapDerivedCategoryCompIso_hom_app_comp_mapDerivedCategory_app_Q_obj`, after moving
  -- `F'(Q.obj K)` to `Q.obj (F K)` by naturality on the right. Both sides become `Q` of chain
  -- maps, which agree termwise by `h` (`hK`).
  refine Localization.natTrans_ext Q (HomologicalComplex.quasiIso C₁ (.up ℤ)) fun K ↦ ?_
  have hK : (H.mapHomologicalComplex _).map ((NatTrans.mapHomologicalComplex τ₁ (.up ℤ)).app K) ≫
      (NatTrans.mapHomologicalComplex τ₂ (.up ℤ)).app K =
      (NatTrans.mapHomologicalComplex τ₃ (.up ℤ)).app ((F.mapHomologicalComplex _).obj K) ≫
        (NatTrans.mapHomologicalComplex τ₄ (.up ℤ)).app K := by
    ext n
    simpa using congr_app h (K.X n)
  rw [← cancel_mono (FGH.mapDerivedCategoryFactors.hom.app K)]
  simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app, associator_hom_app,
    Category.id_comp, Category.assoc,
    mapDerivedCategoryCompIso_hom_app_comp_mapDerivedCategory_app_Q_obj_assoc, Iso.inv_hom_id_app,
    Functor.comp_obj, Category.comp_id]
  rw [← NatTrans.naturality_assoc, ← NatTrans.naturality_assoc,
    ← H.mapDerivedCategory.map_comp_assoc]
  dsimp only [Functor.comp_obj, Functor.comp_map]
  simp only [Category.assoc,
    mapDerivedCategoryCompIso_hom_app_comp_mapDerivedCategory_app_Q_obj_assoc, Iso.inv_hom_id_app,
    Iso.inv_hom_id_app_assoc, Functor.comp_obj, Category.comp_id, Functor.map_comp,
    mapDerivedCategoryFactors_hom_naturality_assoc]
  simp only [← Q.map_comp, hK]

end Associativity

section Unitality

/-- Left unit law for the comparisons of derived functors of composites. If `σ : F ⟶ 𝟭 C₁`
identifies `F` with the identity and `τ : F ⋙ G ⟶ G` is the induced comparison, then the
comparison of `F' ⋙ G'` with `G'` induced by `τ` is the one induced by `σ'` and Mathlib's
`mapDerivedCategoryIdIso`. -/
theorem mapDerivedCategoryCompIso_left_unitality {F : C₁ ⥤ C₁} {G : C₁ ⥤ C₂}
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (σ : F ⟶ 𝟭 C₁) (τ : F ⋙ G ⟶ G)
    (h : τ = whiskerRight σ G ≫ (leftUnitor G).hom) :
    (mapDerivedCategoryCompIso F G).hom ≫ NatTrans.mapDerivedCategory τ =
      whiskerRight (NatTrans.mapDerivedCategory σ ≫ (mapDerivedCategoryIdIso C₁).hom)
        G.mapDerivedCategory ≫ (leftUnitor _).hom := by
  refine Localization.natTrans_ext Q (HomologicalComplex.quasiIso C₁ (.up ℤ)) fun K ↦ ?_
  have hK : (NatTrans.mapHomologicalComplex τ (.up ℤ)).app K =
      (G.mapHomologicalComplex _).map ((NatTrans.mapHomologicalComplex σ (.up ℤ)).app K ≫
        (mapHomologicalComplexIdIso C₁ (.up ℤ)).hom.app K) := by
    ext n
    simpa using congr_app h (K.X n)
  rw [← cancel_mono (G.mapDerivedCategoryFactors.hom.app K)]
  simp only [NatTrans.comp_app, Category.assoc,
    mapDerivedCategoryCompIso_hom_app_comp_mapDerivedCategory_app_Q_obj_assoc, Iso.inv_hom_id_app,
    Functor.comp_obj, Category.comp_id]
  simp only [whiskerRight_app, leftUnitor_hom_app, Functor.comp_obj, Functor.id_obj,
    Category.id_comp, NatTrans.comp_app, NatTrans.mapDerivedCategory_app_Q_obj,
    mapDerivedCategoryIdIso_hom_app, Category.assoc, Iso.inv_hom_id_app_assoc, ← Q.map_comp, hK]
  rw [Functor.map_comp_assoc, mapDerivedCategoryFactors_hom_naturality]

/-- Right unit law for the comparisons of derived functors of composites. If `σ : G ⟶ 𝟭 C₂`
identifies `G` with the identity and `τ : F ⋙ G ⟶ F` is the induced comparison, then the
comparison of `F' ⋙ G'` with `F'` induced by `τ` is the one induced by `σ'` and Mathlib's
`mapDerivedCategoryIdIso`. -/
theorem mapDerivedCategoryCompIso_right_unitality {F : C₁ ⥤ C₂} {G : C₂ ⥤ C₂}
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (σ : G ⟶ 𝟭 C₂) (τ : F ⋙ G ⟶ F)
    (h : τ = whiskerLeft F σ ≫ (rightUnitor F).hom) :
    (mapDerivedCategoryCompIso F G).hom ≫ NatTrans.mapDerivedCategory τ =
      whiskerLeft F.mapDerivedCategory
        (NatTrans.mapDerivedCategory σ ≫ (mapDerivedCategoryIdIso C₂).hom) ≫
        (rightUnitor _).hom := by
  refine Localization.natTrans_ext Q (HomologicalComplex.quasiIso C₁ (.up ℤ)) fun K ↦ ?_
  have hK : (NatTrans.mapHomologicalComplex τ (.up ℤ)).app K =
      (NatTrans.mapHomologicalComplex σ (.up ℤ)).app ((F.mapHomologicalComplex _).obj K) ≫
        (mapHomologicalComplexIdIso C₂ (.up ℤ)).hom.app ((F.mapHomologicalComplex _).obj K) := by
    ext n
    simpa using congr_app h (K.X n)
  -- Move `F'(Q.obj K)` to `Q.obj (F K)` by naturality of the comparison of `G'` with `𝟭`.
  have hF := (NatTrans.mapDerivedCategory σ ≫ (mapDerivedCategoryIdIso C₂).hom).naturality
    (F.mapDerivedCategoryFactors.hom.app K)
  simp only [NatTrans.comp_app, Functor.comp_obj, Functor.id_map, Category.assoc] at hF
  rw [← cancel_mono (F.mapDerivedCategoryFactors.hom.app K)]
  simp only [NatTrans.comp_app, Category.assoc,
    mapDerivedCategoryCompIso_hom_app_comp_mapDerivedCategory_app_Q_obj_assoc, Iso.inv_hom_id_app,
    Category.comp_id, whiskerLeft_app, rightUnitor_hom_app, Functor.comp_obj, Functor.id_obj,
    ← hF]
  simp only [NatTrans.mapDerivedCategory_app_Q_obj, mapDerivedCategoryIdIso_hom_app,
    Category.assoc, Iso.inv_hom_id_app_assoc, ← Q.map_comp, hK]

end Unitality

end CategoryTheory.Functor
