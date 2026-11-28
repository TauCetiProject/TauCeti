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
without choosing resolutions. The supplied cochain comparison has components
`F(K) ⊗ F(L) ⟶ F(K ⊗ L)` and need not be invertible. Quasi-isomorphic components on
compatible K-flat replacements suffice for the derived comparison to be invertible.

## References

* [Stacks Project, Tag 08DX](https://stacks.math.columbia.edu/tag/08DX).
* The construction uses Mathlib's `Functor.leftDerived₂Lift` and Tau Ceti's absolute
  left derived tensor and its K-flat computation isomorphisms.
* Adapted from the retained canonical comparison in
  [Tau Ceti PR #47483](https://github.com/TauCetiProject/TauCeti/pull/47483).
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
      F.mapDerivedCategory.map (((TauCeti.derivedTensorCounit C).app K).app L) := by
  simp [mapDerivedTensorCounit]

/-- Postcomposing the source derived tensor and its counit with the exact derived functor
still gives a left derived bifunctor with respect to quasi-isomorphisms in both variables. -/
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
      F.mapDerivedCategoryFactors.inv.app (K ⊗ L) := by
  simp [derivedTensorOfMapCounit]

/-- The canonical comparison from the derived tensor of the images to the image of the
unbounded derived tensor. The cochain map `χ` has components
`F(K) ⊗ F(L) ⟶ F(K ⊗ L)` and need not be invertible. No compatible K-flat
replacement is needed to define the comparison. -/
def mapDerivedTensorComparison : derivedTensorOfMap F ⟶ mapDerivedTensor F :=
  leftDerived₂Lift (mapDerivedTensor F) (mapDerivedTensorCounit F)
    (quasiIso C (.up ℤ)) (quasiIso C (.up ℤ)) (derivedTensorOfMap F) (derivedTensorOfMapCounit F χ)

/-- Whiskering the comparison by `Q` in both variables intertwines the two tensor counits. -/
@[reassoc (attr := simp)]
lemma mapDerivedTensorComparison_fac :
    (((whiskeringLeft₂ (DerivedCategory D)).obj DerivedCategory.Q).obj
      DerivedCategory.Q).map (F.mapDerivedTensorComparison χ) ≫
        F.mapDerivedTensorCounit = F.derivedTensorOfMapCounit χ :=
  leftDerived₂_fac _ _ _ _ _ _

/-- The canonical comparison intertwines the two tensor counits. -/
@[reassoc (attr := simp)]
lemma mapDerivedTensorComparison_fac_app_app (K L : CochainComplex C ℤ) :
    ((F.mapDerivedTensorComparison χ).app (DerivedCategory.Q.obj K)).app
      (DerivedCategory.Q.obj L) ≫ F.mapDerivedCategory.map
        (((TauCeti.derivedTensorCounit C).app K).app L) =
      ((derivedTensorOfMapCounit F χ).app K).app L := by
  simpa only [NatTrans.comp_app, whiskeringLeft₂_obj_obj_map_app_app,
    mapDerivedTensorCounit_app_app] using
      congr(($(F.mapDerivedTensorComparison_fac χ).app K).app L)

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

/-- A quasi-isomorphic cochain tensor component and K-flatness of the left complex and its
image make the canonical component invertible. -/
instance isIso_mapDerivedTensorComparison_app_app_of_isKFlat_left_of_isKFlat_map
    (K L : CochainComplex C ℤ) [QuasiIso ((χ.app K).app L)]
    [K.IsKFlat] [CochainComplex.IsKFlat ((F.mapHomologicalComplex (.up ℤ)).obj K)] :
    IsIso (((F.mapDerivedTensorComparison χ).app (DerivedCategory.Q.obj K)).app
      (DerivedCategory.Q.obj L)) := by
  rw [F.mapDerivedTensorComparison_app_app_of_isKFlat_left_of_isKFlat_map χ K L]
  infer_instance

/-- Pointwise compatible K-flat replacements, on which the cochain tensor maps are
quasi-isomorphisms for every second input, make the derived comparison an isomorphism.
Neither functorial replacements nor K-flatness of the second input are required. -/
theorem isIso_mapDerivedTensorComparison_of_exists_quasiIso_isKFlat_and_isKFlat_map
    (h : ∀ K : CochainComplex C ℤ, ∃ (P : CochainComplex C ℤ) (f : P ⟶ K),
      QuasiIso f ∧ P.IsKFlat ∧
        CochainComplex.IsKFlat ((F.mapHomologicalComplex (.up ℤ)).obj P) ∧
        ∀ L, QuasiIso ((χ.app P).app L)) :
    IsIso (F.mapDerivedTensorComparison χ) := by
  have hmodels (K L : CochainComplex C ℤ) :
      IsIso (((F.mapDerivedTensorComparison χ).app (DerivedCategory.Q.obj K)).app
        (DerivedCategory.Q.obj L)) := by
    obtain ⟨P, f, hf, hP, hFP, hχ⟩ := h K
    have := hχ L
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
