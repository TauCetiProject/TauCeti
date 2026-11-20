/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Functoriality of derived functors of exact functors

An exact functor `F : C₁ ⥤ C₂` between abelian categories induces Mathlib's functor
`F.mapDerivedCategory : D(C₁) ⥤ D(C₂)`, and a natural transformation `τ : F ⟶ G` of exact
functors induces `NatTrans.mapDerivedCategory τ`. This file records that the second construction
is functorial (`CategoryTheory.NatTrans.mapDerivedCategory_id`,
`CategoryTheory.NatTrans.mapDerivedCategory_comp`), so that an isomorphism of exact functors
induces an isomorphism of derived functors (`CategoryTheory.NatIso.mapDerivedCategory`).

Mathlib compares the derived functor of a composite with the composite of derived functors by
`CategoryTheory.Functor.mapDerivedCategoryCompIso`. Composing it with the derived functor of a
natural transformation `τ : F ⋙ G ⟶ H` gives the comparison `F' ⋙ G' ⟶ H'` of the derived functors
attached to `τ`; on a complex `K` it is described by
`CategoryTheory.Functor.mapDerivedCategoryCompIso_hom_app_comp_mapDerivedCategory_app_Q_obj`.
These comparisons satisfy the associativity law of a pseudofunctor
(`CategoryTheory.Functor.mapDerivedCategoryCompIso_associativity`): if two ways of comparing
`F ⋙ G ⋙ H` with an exact functor agree on the abelian level, so do the two induced comparisons
on derived categories. This is the coherence used for derived restriction of module sheaves to
nested open subschemes.
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

variable (F) in
/-- The derived functor of the identity transformation is the identity. -/
@[simp]
lemma mapDerivedCategory_id : NatTrans.mapDerivedCategory (𝟙 F) = 𝟙 F.mapDerivedCategory :=
  Localization.natTrans_ext Q (HomologicalComplex.quasiIso C₁ (.up ℤ)) fun K ↦ by
    simp [mapDerivedCategory_app_Q_obj]

/-- The derived functor of a composite of natural transformations is the composite of their
derived functors. -/
@[simp, reassoc]
lemma mapDerivedCategory_comp (τ : F ⟶ G) (τ' : G ⟶ H) :
    NatTrans.mapDerivedCategory (τ ≫ τ') =
      NatTrans.mapDerivedCategory τ ≫ NatTrans.mapDerivedCategory τ' :=
  Localization.natTrans_ext Q (HomologicalComplex.quasiIso C₁ (.up ℤ)) fun K ↦ by
    simp [mapDerivedCategory_app_Q_obj]

end CategoryTheory.NatTrans

namespace CategoryTheory.NatIso

variable {F G : C₁ ⥤ C₂} [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- An isomorphism of exact functors induces an isomorphism of their derived actions. -/
noncomputable def mapDerivedCategory (α : F ≅ G) :
    F.mapDerivedCategory ≅ G.mapDerivedCategory :=
  Localization.liftNatIso Q (HomologicalComplex.quasiIso C₁ (ComplexShape.up ℤ)) _ _ _ _
    (Functor.isoWhiskerRight (NatIso.mapHomologicalComplex α (ComplexShape.up ℤ)) Q)

/-- The forward map of the derived isomorphism is Mathlib's derived natural transformation. -/
@[simp]
lemma mapDerivedCategory_hom (α : F ≅ G) :
    (mapDerivedCategory α).hom = NatTrans.mapDerivedCategory α.hom := (rfl)

/-- The inverse map of the derived isomorphism is Mathlib's derived natural transformation. -/
@[simp]
lemma mapDerivedCategory_inv (α : F ≅ G) :
    (mapDerivedCategory α).inv = NatTrans.mapDerivedCategory α.inv := (rfl)

/-- The derived isomorphism commutes with integer shifts. -/
instance (α : F ≅ G) : NatTrans.CommShift (mapDerivedCategory α).hom ℤ :=
  inferInstanceAs (NatTrans.CommShift (NatTrans.mapDerivedCategory α.hom) ℤ)

end CategoryTheory.NatIso

namespace CategoryTheory.Functor

section Comp

variable {F : C₁ ⥤ C₂} {G : C₂ ⥤ C₃} {H : C₁ ⥤ C₃}
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
  have : (mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).hom.app K = 𝟙 _ := by
    ext; simp
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
  -- Both sides are determined by their values on complexes `Q.obj K`. There, the left side is
  -- computed directly, and the right side after moving `F.mapDerivedCategory.obj (Q.obj K)` to
  -- `Q.obj` of the complex `F(K)` by naturality (`hF`). Both become `Q` of chain maps, which agree
  -- termwise by `h` (`hK`).
  refine Localization.natTrans_ext Q (HomologicalComplex.quasiIso C₁ (.up ℤ)) fun K ↦ ?_
  have hF (α : G.mapDerivedCategory ⋙ H.mapDerivedCategory ⟶ GH.mapDerivedCategory) :
      α.app (F.mapDerivedCategory.obj (Q.obj K)) =
        H.mapDerivedCategory.map (G.mapDerivedCategory.map
          (F.mapDerivedCategoryFactors.hom.app K)) ≫
          α.app (Q.obj ((F.mapHomologicalComplex _).obj K)) ≫
            GH.mapDerivedCategory.map (F.mapDerivedCategoryFactors.inv.app K) := by
    have := α.naturality (F.mapDerivedCategoryFactors.hom.app K)
    dsimp at this
    rw [reassoc_of% this, ← Functor.map_comp]
    simp
  have hK : (H.mapHomologicalComplex _).map ((NatTrans.mapHomologicalComplex τ₁ (.up ℤ)).app K) ≫
      (NatTrans.mapHomologicalComplex τ₂ (.up ℤ)).app K =
      (NatTrans.mapHomologicalComplex τ₃ (.up ℤ)).app ((F.mapHomologicalComplex _).obj K) ≫
        (NatTrans.mapHomologicalComplex τ₄ (.up ℤ)).app K := by
    ext n
    simpa using congr_app h (K.X n)
  have h₃ := hF ((mapDerivedCategoryCompIso G H).hom ≫ NatTrans.mapDerivedCategory τ₃)
  simp only [NatTrans.comp_app] at h₃
  simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app, associator_hom_app,
    Category.id_comp, Category.assoc]
  rw [reassoc_of% h₃, mapDerivedCategoryCompIso_hom_app_comp_mapDerivedCategory_app_Q_obj,
    mapDerivedCategoryCompIso_hom_app_comp_mapDerivedCategory_app_Q_obj,
    mapDerivedCategoryCompIso_hom_app_comp_mapDerivedCategory_app_Q_obj_assoc,
    mapDerivedCategoryCompIso_hom_app_comp_mapDerivedCategory_app_Q_obj]
  simp only [Functor.map_comp, Category.assoc]
  rw [← H.mapDerivedCategory.map_comp_assoc (FG.mapDerivedCategoryFactors.inv.app K),
    Iso.inv_hom_id_app, Functor.map_id, Category.id_comp,
    ← GH.mapDerivedCategory.map_comp_assoc (F.mapDerivedCategoryFactors.inv.app K),
    Iso.inv_hom_id_app, Functor.map_id, Category.id_comp, Iso.inv_hom_id_app_assoc,
    mapDerivedCategoryFactors_hom_naturality_assoc, ← Q.map_comp_assoc, hK, Q.map_comp_assoc]

end Associativity

end CategoryTheory.Functor
