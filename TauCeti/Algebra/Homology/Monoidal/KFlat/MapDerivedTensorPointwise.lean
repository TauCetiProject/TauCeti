/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Monoidal.KFlat.LeftDerivedTensor
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# The canonical comparison for an exact functor and derived tensor

An exact additive functor equipped with a comparison for unbounded cochain tensor products
has a canonical morphism from the derived tensor of its images to the image of the derived
tensor. The universal property of the absolute left derived tensor defines this morphism
without choosing resolutions. When the cochain comparison is invertible, compatible K-flat
replacements make the derived comparison invertible.

## References

* [Stacks Project, Tag 08DX](https://stacks.math.columbia.edu/tag/08DX).
* The construction uses Mathlib's `Functor.leftDerived₂Lift` and Tau Ceti's absolute
  left derived tensor and its K-flat computation isomorphisms.
* The identity law adapts the counit-naturality test in
  [Tau Ceti PR #47457](https://github.com/TauCetiProject/TauCeti/pull/47457).
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory

universe w₁ w₂

variable {C : Type*} [Category* C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  [∀ (X₁ X₂ : GradedObject ℤ C), GradedObject.HasTensor X₁ X₂]
  [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((MonoidalCategory.curriedTensor C).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((MonoidalCategory.curriedTensor C).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [BraidedCategory C]
  [(CochainComplex.KFlat.localizerMorphism C).IsLeftDerivabilityStructure]
  [HasDerivedCategory.{w₁} C]
variable {D : Type*} [Category* D] [Abelian D] [MonoidalCategory D] [MonoidalPreadditive D]
  [∀ (X₁ X₂ : GradedObject ℤ D), GradedObject.HasTensor X₁ X₂]
  [∀ X₁, PreservesColimit (Functor.empty.{0} D) ((MonoidalCategory.curriedTensor D).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} D) ((MonoidalCategory.curriedTensor D).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ D), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [BraidedCategory D]
  [(CochainComplex.KFlat.localizerMorphism D).IsLeftDerivabilityStructure]
  [HasDerivedCategory.{w₂} D]

namespace CategoryTheory.Functor

variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- Apply the exact derived functor after tensoring. -/
abbrev mapDerivedTensor :=
  TauCeti.derivedTensor C ⋙ (whiskeringRight _ _ _).obj F.mapDerivedCategory

/-- Tensor the two images under the exact derived functor. -/
abbrev derivedTensorOfMap :=
  (((whiskeringLeft₂ (DerivedCategory D)).obj F.mapDerivedCategory).obj
    F.mapDerivedCategory).obj (TauCeti.derivedTensor D)

/-- The common cochain bifunctor used to compare the two tensor counits. -/
abbrev mapDerivedTensorCochain := MonoidalCategory.curriedTensor (CochainComplex C ℤ) ⋙
  (whiskeringRight _ _ _).obj (DerivedCategory.Q ⋙ F.mapDerivedCategory)

/-- The absolute tensor counit after applying the exact derived functor. -/
def mapDerivedTensorCounit :
    (((whiskeringLeft₂ (DerivedCategory D)).obj DerivedCategory.Q).obj
      DerivedCategory.Q).obj (mapDerivedTensor F) ⟶ mapDerivedTensorCochain F :=
  whiskerRight (TauCeti.derivedTensorCounit C)
    ((whiskeringRight _ _ _).obj F.mapDerivedCategory)

omit [MonoidalCategory D] [MonoidalPreadditive D]
  [∀ (X₁ X₂ : GradedObject ℤ D), GradedObject.HasTensor X₁ X₂]
  [∀ X₁, PreservesColimit (Functor.empty.{0} D) ((MonoidalCategory.curriedTensor D).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} D) ((MonoidalCategory.curriedTensor D).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ D), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [BraidedCategory D]
  [(CochainComplex.KFlat.localizerMorphism D).IsLeftDerivabilityStructure] in
/-- Component formula for the tensor counit after applying the exact derived functor. -/
@[simp]
lemma mapDerivedTensorCounit_app_app (K L : CochainComplex C ℤ) :
    ((F.mapDerivedTensorCounit).app K).app L =
      F.mapDerivedCategory.map (((TauCeti.derivedTensorCounit C).app K).app L) := (rfl)

instance : (mapDerivedTensor F).IsLeftDerivedFunctor₂ (mapDerivedTensorCounit F)
    (quasiIso C (.up ℤ)) (quasiIso C (.up ℤ)) :=
  isLeftDerivedFunctor₂_comp_of_isLeftDerivedFunctor₂_tensor DerivedCategory.Q
    (Localization.inverts _ _) (TauCeti.derivedTensorCounit C) F.mapDerivedCategory

variable (χ :
  (((whiskeringLeft₂ (CochainComplex D ℤ)).obj (F.mapHomologicalComplex (.up ℤ))).obj
    (F.mapHomologicalComplex (.up ℤ))).obj
      (MonoidalCategory.curriedTensor (CochainComplex D ℤ)) ⟶
  MonoidalCategory.curriedTensor (CochainComplex C ℤ) ⋙
    (whiskeringRight _ _ _).obj (F.mapHomologicalComplex (.up ℤ)))

/-- The derived tensor counit of the target category `D`, evaluated on the images and
transported using the cochain tensor map `χ` to the cochain bifunctor of
`mapDerivedTensorCounit`. -/
def derivedTensorOfMapCounit :
    (((whiskeringLeft₂ (DerivedCategory D)).obj DerivedCategory.Q).obj
      DerivedCategory.Q).obj (derivedTensorOfMap F) ⟶ mapDerivedTensorCochain F := by
  let e := F.mapDerivedCategoryFactors.{w₁, w₂}
  let W := whiskeringLeft₂ (C₁ := CochainComplex C ℤ) (C₂ := CochainComplex C ℤ)
    (D₁ := DerivedCategory D) (D₂ := DerivedCategory D) (DerivedCategory D)
  exact (((W.mapIso e).app (DerivedCategory.Q ⋙ F.mapDerivedCategory)).app
      (TauCeti.derivedTensor D)).hom ≫
    (((W.obj (F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)).mapIso e).app
      (TauCeti.derivedTensor D)).hom ≫
    (((whiskeringLeft₂ (DerivedCategory D)).obj (F.mapHomologicalComplex (.up ℤ))).obj
      (F.mapHomologicalComplex (.up ℤ))).map (TauCeti.derivedTensorCounit D) ≫
    whiskerRight χ ((whiskeringRight _ _ _).obj DerivedCategory.Q) ≫
    whiskerLeft (MonoidalCategory.curriedTensor (CochainComplex C ℤ))
      (((whiskeringRight _ _ _).mapIso e).inv)

omit [BraidedCategory C]
  [(CochainComplex.KFlat.localizerMorphism C).IsLeftDerivabilityStructure] in
/-- Component formula for the transported tensor counit. -/
@[simp]
lemma derivedTensorOfMapCounit_app_app (K L : CochainComplex C ℤ) :
    ((derivedTensorOfMapCounit F χ).app K).app L =
      ((TauCeti.derivedTensor D).map (F.mapDerivedCategoryFactors.hom.app K)).app _ ≫
      ((TauCeti.derivedTensor D).obj _).map (F.mapDerivedCategoryFactors.hom.app L) ≫
      ((TauCeti.derivedTensorCounit D).app _).app _ ≫
      DerivedCategory.Q.map ((χ.app K).app L) ≫
      F.mapDerivedCategoryFactors.inv.app (K ⊗ L) := (rfl)

/-- The canonical comparison from the derived tensor of the images to the image of the
unbounded derived tensor. No compatible K-flat replacement is needed to define it. -/
def mapDerivedTensorComparison : derivedTensorOfMap F ⟶ mapDerivedTensor F :=
  leftDerived₂Lift (mapDerivedTensor F) (mapDerivedTensorCounit F)
    (quasiIso C (.up ℤ)) (quasiIso C (.up ℤ)) (derivedTensorOfMap F) (derivedTensorOfMapCounit F χ)

/-- The canonical comparison intertwines the two tensor counits. -/
@[reassoc (attr := simp)]
lemma mapDerivedTensorComparison_fac_app_app (K L : CochainComplex C ℤ) :
    ((F.mapDerivedTensorComparison χ).app (DerivedCategory.Q.obj K)).app
      (DerivedCategory.Q.obj L) ≫ F.mapDerivedCategory.map
        (((TauCeti.derivedTensorCounit C).app K).app L) =
      ((derivedTensorOfMapCounit F χ).app K).app L :=
  leftDerived₂_fac_app_app _ _ _ _ _ _ K L

/-- The counit equation uniquely determines the canonical comparison. -/
lemma mapDerivedTensorComparison_unique (γ : derivedTensorOfMap F ⟶ mapDerivedTensor F)
    (hγ : ∀ K L : CochainComplex C ℤ,
      (γ.app (DerivedCategory.Q.obj K)).app (DerivedCategory.Q.obj L) ≫
        F.mapDerivedCategory.map (((TauCeti.derivedTensorCounit C).app K).app L) =
      ((derivedTensorOfMapCounit F χ).app K).app L) : γ = F.mapDerivedTensorComparison χ := by
  refine leftDerived₂_ext (LF := mapDerivedTensor F) (L₁ := DerivedCategory.Q)
    (L₂ := DerivedCategory.Q) (α := mapDerivedTensorCounit F) (W₁ := quasiIso C (.up ℤ))
    (W₂ := quasiIso C (.up ℤ)) ?_
  ext K L
  exact (hγ K L).trans (F.mapDerivedTensorComparison_fac_app_app χ K L).symm

/-- On a K-flat left model whose image is K-flat, the comparison is the composite of
ordinary cochain compatibility with the two K-flat tensor computation isomorphisms. -/
@[simp]
lemma mapDerivedTensorComparison_app_app_of_isKFlat_left_of_isKFlat_map
    (K L : CochainComplex C ℤ) [K.IsKFlat]
    [CochainComplex.IsKFlat ((F.mapHomologicalComplex (.up ℤ)).obj K)] :
    ((F.mapDerivedTensorComparison χ).app (DerivedCategory.Q.obj K)).app
      (DerivedCategory.Q.obj L) =
      (((TauCeti.derivedTensor D).mapIso (F.mapDerivedCategoryFactors.app K)).app _).hom ≫
        (((TauCeti.derivedTensor D).obj _).mapIso (F.mapDerivedCategoryFactors.app L)).hom ≫
        (CochainComplex.derivedTensorKFlatLeftIso
          ((F.mapHomologicalComplex (.up ℤ)).obj K)
          ((F.mapHomologicalComplex (.up ℤ)).obj L)).hom ≫
        DerivedCategory.Q.map ((χ.app K).app L) ≫
        F.mapDerivedCategoryFactors.inv.app (K ⊗ L) ≫
        (F.mapDerivedCategory.mapIso (CochainComplex.derivedTensorKFlatLeftIso K L)).inv := by
  rw [← cancel_mono (F.mapDerivedCategory.map
    (((TauCeti.derivedTensorCounit C).app K).app L)), mapDerivedTensorComparison_fac_app_app]
  simp [Category.assoc]

/-- An invertible cochain tensor component and K-flatness of the left complex and its image
make the canonical component invertible. -/
instance isIso_mapDerivedTensorComparison_app_app_of_isKFlat_left_of_isKFlat_map
    (K L : CochainComplex C ℤ) [IsIso ((χ.app K).app L)]
    [K.IsKFlat] [CochainComplex.IsKFlat ((F.mapHomologicalComplex (.up ℤ)).obj K)] :
    IsIso (((F.mapDerivedTensorComparison χ).app (DerivedCategory.Q.obj K)).app
      (DerivedCategory.Q.obj L)) := by
  rw [F.mapDerivedTensorComparison_app_app_of_isKFlat_left_of_isKFlat_map χ K L]
  infer_instance

/-- For an invertible cochain tensor map, pointwise compatible K-flat replacements suffice
for the canonical derived tensor comparison to be an isomorphism. No functorial choice of
replacements is required. -/
theorem isIso_mapDerivedTensorComparison_of_exists_quasiIso_isKFlat_and_isKFlat_map [IsIso χ]
    (h : ∀ K : CochainComplex C ℤ, ∃ (P : CochainComplex C ℤ) (f : P ⟶ K),
      QuasiIso f ∧ P.IsKFlat ∧
        CochainComplex.IsKFlat ((F.mapHomologicalComplex (.up ℤ)).obj P)) :
    IsIso (F.mapDerivedTensorComparison χ) := by
  have hmodels (K L : CochainComplex C ℤ) :
      IsIso (((F.mapDerivedTensorComparison χ).app (DerivedCategory.Q.obj K)).app
        (DerivedCategory.Q.obj L)) := by
    obtain ⟨P, f, hf, hP, hFP⟩ := h K
    let e := (asIso (DerivedCategory.Q.map f)).prod (Iso.refl (DerivedCategory.Q.obj L))
    exact (NatTrans.isIso_app_iff_of_iso
      (uncurry.map (F.mapDerivedTensorComparison χ)) e).1
      (isIso_mapDerivedTensorComparison_app_app_of_isKFlat_left_of_isKFlat_map F χ P L)
  have hderived (X Y : DerivedCategory C) :
      IsIso (((F.mapDerivedTensorComparison χ).app X).app Y) := by
    let e := (DerivedCategory.Q.objObjPreimageIso X).prod
      (DerivedCategory.Q.objObjPreimageIso Y)
    exact (NatTrans.isIso_app_iff_of_iso
      (uncurry.map (F.mapDerivedTensorComparison χ)) e).1 (hmodels _ _)
  have (X : DerivedCategory C) : IsIso ((F.mapDerivedTensorComparison χ).app X) :=
    NatIso.isIso_of_isIso_app _
  exact NatIso.isIso_of_isIso_app _

end CategoryTheory.Functor

namespace TauCeti

/-- The structural identity comparison on the derived tensor bifunctor. -/
def identityDerivedComparison : derivedTensorOfMap (𝟭 C) ≅ mapDerivedTensor (𝟭 C) := by
  let e := mapDerivedCategoryIdIso C
  let T := TauCeti.derivedTensor C
  let W := whiskeringLeft₂ (C₁ := DerivedCategory C) (C₂ := DerivedCategory C)
    (D₁ := DerivedCategory C) (D₂ := DerivedCategory C) (DerivedCategory C)
  exact (((W.mapIso e).app (𝟭 C).mapDerivedCategory).app T) ≪≫
    (((W.obj (𝟭 _)).mapIso e).app T) ≪≫
    (isoWhiskerLeft T ((whiskeringRight _ _ _).mapIso e) ≪≫ rightUnitor T).symm

/-- Component formula for the structural identity comparison on derived tensors. -/
@[simp]
lemma identityDerivedComparison_hom_app_app (X Y : DerivedCategory C) :
    ((identityDerivedComparison (C := C)).hom.app X).app Y =
      ((derivedTensor C).map ((mapDerivedCategoryIdIso C).hom.app X)).app _ ≫
        ((derivedTensor C).obj X).map ((mapDerivedCategoryIdIso C).hom.app Y) ≫
        (mapDerivedCategoryIdIso C).inv.app (((derivedTensor C).obj X).obj Y) := by
  simp [identityDerivedComparison]

/-- Component formula for the inverse structural identity comparison on derived tensors. -/
@[simp]
lemma identityDerivedComparison_inv_app_app (X Y : DerivedCategory C) :
    ((identityDerivedComparison (C := C)).inv.app X).app Y =
      (mapDerivedCategoryIdIso C).hom.app (((derivedTensor C).obj X).obj Y) ≫
        ((derivedTensor C).obj X).map ((mapDerivedCategoryIdIso C).inv.app Y) ≫
        ((derivedTensor C).map ((mapDerivedCategoryIdIso C).inv.app X)).app _ := by
  simp [identityDerivedComparison]

end TauCeti

namespace CategoryTheory.Functor

/-- The canonical comparison for the identity functor is the structural identity comparison. -/
@[simp]
lemma mapDerivedTensorComparison_id :
    (𝟭 C).mapDerivedTensorComparison (TauCeti.identityCochainComparison (C := C)).inv =
      (TauCeti.identityDerivedComparison (C := C)).hom := by
  symm
  apply mapDerivedTensorComparison_unique
  intro K L
  let e := mapHomologicalComplexIdIso C (.up ℤ)
  let T := TauCeti.derivedTensor C
  let ε := TauCeti.derivedTensorCounit C
  -- First transport the tensor counit along the derived identity isomorphism.
  have h₁ :
      (𝟭 C).mapDerivedCategory.map ((ε.app K).app L) ≫
          (mapDerivedCategoryIdIso C).hom.app (DerivedCategory.Q.obj (K ⊗ L)) =
        (mapDerivedCategoryIdIso C).hom.app
          ((T.obj (DerivedCategory.Q.obj K)).obj (DerivedCategory.Q.obj L)) ≫
          (ε.app K).app L :=
    (mapDerivedCategoryIdIso C).hom.naturality ((ε.app K).app L)
  -- Then apply tensor counit naturality in each cochain variable.
  have h₂ :
      (T.map (DerivedCategory.Q.map (e.hom.app K))).app _ ≫
          (ε.app K).app (((𝟭 C).mapHomologicalComplex (.up ℤ)).obj L) =
        (ε.app (((𝟭 C).mapHomologicalComplex (.up ℤ)).obj K)).app _ ≫
          DerivedCategory.Q.map (e.hom.app K ▷ _) :=
    NatTrans.congr_app (ε.naturality (e.hom.app K))
      (((𝟭 C).mapHomologicalComplex (.up ℤ)).obj L)
  have h₃ :
      (T.obj (DerivedCategory.Q.obj K)).map (DerivedCategory.Q.map (e.hom.app L)) ≫
          (ε.app K).app L =
        (ε.app K).app (((𝟭 C).mapHomologicalComplex (.up ℤ)).obj L) ≫
          DerivedCategory.Q.map (K ◁ e.hom.app L) :=
    (ε.app K).naturality (e.hom.app L)
  have hc :
      (T.map (DerivedCategory.Q.map (e.hom.app K))).app _ ≫
          (T.obj (DerivedCategory.Q.obj K)).map (DerivedCategory.Q.map (e.hom.app L)) ≫
          (ε.app K).app L =
        (ε.app (((𝟭 C).mapHomologicalComplex (.up ℤ)).obj K)).app _ ≫
          DerivedCategory.Q.map (e.hom.app K ⊗ₘ e.hom.app L) := by
    calc
      _ = (T.map (DerivedCategory.Q.map (e.hom.app K))).app _ ≫
          (ε.app K).app _ ≫ DerivedCategory.Q.map (K ◁ e.hom.app L) := by rw [h₃]
      _ = _ := by rw [← Category.assoc, h₂]; simp [Category.assoc, ← Functor.map_comp,
        MonoidalCategory.tensorHom_def]
  dsimp only [T, ε, e] at h₁ hc
  rw [← cancel_mono ((mapDerivedCategoryIdIso C).hom.app
    (DerivedCategory.Q.obj (K ⊗ L)))]
  simp only [TauCeti.identityDerivedComparison_hom_app_app, Category.assoc]
  rw [h₁]
  simp [Category.assoc, derivedTensorOfMapCounit_app_app, mapDerivedCategoryIdIso_hom_app,
    TauCeti.identityCochainComparison_inv_app_app, ← NatTrans.naturality_assoc, hc]

end CategoryTheory.Functor
