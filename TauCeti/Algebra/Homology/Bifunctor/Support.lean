/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Bifunctor
public import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# Supported summands of a bifunctor totalization

A term of Mathlib's bifunctor totalization is the coproduct of its summands
over the fiber of the total index map. When all but one or two summands are
zero, the term identifies with the remaining summand or their binary
biproduct. The comparisons below use the existing totalization inclusions
and desc maps. Their characteristic equations compute the supported
inclusions and the inverse maps.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex

variable {C₁ C₂ D I₁ I₂ J : Type*} [Category* C₁] [Category* C₂] [Category* D]
  [HasZeroMorphisms C₁] [HasZeroMorphisms C₂] [Preadditive D]
  {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
  (K₁ : HomologicalComplex C₁ c₁) (K₂ : HomologicalComplex C₂ c₂)
  (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms]
  [∀ X₁, (F.obj X₁).PreservesZeroMorphisms]
  (c : ComplexShape J) [TotalComplexShape c₁ c₂ c]
  [HasMapBifunctor K₁ K₂ F c] [DecidableEq J]

private def singleSummandMap (p₀ : I₁) (q₀ : I₂) (p : I₁) (q : I₂) :
    (F.obj (K₁.X p)).obj (K₂.X q) ⟶ (F.obj (K₁.X p₀)).obj (K₂.X q₀) := by
  classical
  by_cases h : p = p₀ ∧ q = q₀
  · rcases h with ⟨rfl, rfl⟩
    exact 𝟙 _
  · exact 0

omit [F.PreservesZeroMorphisms] [∀ X₁, (F.obj X₁).PreservesZeroMorphisms] in
private theorem singleSummandMap_eq (p₀ : I₁) (q₀ : I₂) :
    singleSummandMap K₁ K₂ F p₀ q₀ p₀ q₀ = 𝟙 _ := by
  classical
  simp [singleSummandMap]

/-- A totalization term with only one potentially nonzero summand is that summand. -/
def mapBifunctorSingleSummandIso (p₀ : I₁) (q₀ : I₂) (j : J)
    (h : ComplexShape.π c₁ c₂ c (p₀, q₀) = j)
    (hzero : ∀ p q, ComplexShape.π c₁ c₂ c (p, q) = j →
      ¬ (p = p₀ ∧ q = q₀) → IsZero ((F.obj (K₁.X p)).obj (K₂.X q))) :
    (mapBifunctor K₁ K₂ F c).X j ≅ (F.obj (K₁.X p₀)).obj (K₂.X q₀) where
  hom := mapBifunctorDesc (fun p q _ ↦ singleSummandMap K₁ K₂ F p₀ q₀ p q)
  inv := ιMapBifunctor K₁ K₂ F c p₀ q₀ j h
  hom_inv_id := by
    classical
    apply mapBifunctor.hom_ext
    intro p q hpq
    by_cases h₀ : p = p₀ ∧ q = q₀
    · rcases h₀ with ⟨rfl, rfl⟩
      simp only [ι_mapBifunctorDesc_assoc, singleSummandMap_eq,
        Category.id_comp, Category.comp_id]
    · exact (hzero p q hpq h₀).eq_of_src _ _
  inv_hom_id := by
    simp only [ι_mapBifunctorDesc, singleSummandMap_eq]

/-- The unique supported inclusion is the inverse of the single-summand comparison. -/
@[reassoc (attr := simp)]
theorem ι_mapBifunctorSingleSummandIso_hom (p₀ : I₁) (q₀ : I₂) (j : J)
    (h : ComplexShape.π c₁ c₂ c (p₀, q₀) = j)
    (hzero : ∀ p q, ComplexShape.π c₁ c₂ c (p, q) = j →
      ¬ (p = p₀ ∧ q = q₀) → IsZero ((F.obj (K₁.X p)).obj (K₂.X q))) :
    ιMapBifunctor K₁ K₂ F c p₀ q₀ j h ≫
      (mapBifunctorSingleSummandIso K₁ K₂ F c p₀ q₀ j h hzero).hom = 𝟙 _ := by
  simp only [mapBifunctorSingleSummandIso, ι_mapBifunctorDesc, singleSummandMap_eq]

/-- The inverse of the single-summand comparison is the totalization inclusion. -/
@[simp]
theorem mapBifunctorSingleSummandIso_inv (p₀ : I₁) (q₀ : I₂) (j : J)
    (h : ComplexShape.π c₁ c₂ c (p₀, q₀) = j)
    (hzero : ∀ p q, ComplexShape.π c₁ c₂ c (p, q) = j →
      ¬ (p = p₀ ∧ q = q₀) → IsZero ((F.obj (K₁.X p)).obj (K₂.X q))) :
    (mapBifunctorSingleSummandIso K₁ K₂ F c p₀ q₀ j h hzero).inv =
      ιMapBifunctor K₁ K₂ F c p₀ q₀ j h := by
  rfl

section Two

private def twoSummandMap (p₀ : I₁) (q₀ : I₂) (p₁ : I₁) (q₁ : I₂)
    [HasBinaryBiproduct ((F.obj (K₁.X p₀)).obj (K₂.X q₀))
      ((F.obj (K₁.X p₁)).obj (K₂.X q₁))]
    (p : I₁) (q : I₂) :
    (F.obj (K₁.X p)).obj (K₂.X q) ⟶
      (F.obj (K₁.X p₀)).obj (K₂.X q₀) ⊞ (F.obj (K₁.X p₁)).obj (K₂.X q₁) := by
  classical
  by_cases h₀ : p = p₀ ∧ q = q₀
  · rcases h₀ with ⟨rfl, rfl⟩
    exact biprod.inl
  · by_cases h₁ : p = p₁ ∧ q = q₁
    · rcases h₁ with ⟨rfl, rfl⟩
      exact biprod.inr
    · exact 0

omit [F.PreservesZeroMorphisms] [∀ X₁, (F.obj X₁).PreservesZeroMorphisms] in
private theorem twoSummandMap_left (p₀ : I₁) (q₀ : I₂) (p₁ : I₁) (q₁ : I₂)
    [HasBinaryBiproduct ((F.obj (K₁.X p₀)).obj (K₂.X q₀))
      ((F.obj (K₁.X p₁)).obj (K₂.X q₁))] :
    twoSummandMap K₁ K₂ F p₀ q₀ p₁ q₁ p₀ q₀ = biprod.inl := by
  classical
  simp [twoSummandMap]

omit [F.PreservesZeroMorphisms] [∀ X₁, (F.obj X₁).PreservesZeroMorphisms] in
private theorem twoSummandMap_right (p₀ : I₁) (q₀ : I₂) (p₁ : I₁) (q₁ : I₂)
    [HasBinaryBiproduct ((F.obj (K₁.X p₀)).obj (K₂.X q₀))
      ((F.obj (K₁.X p₁)).obj (K₂.X q₁))]
    (hne : (p₁, q₁) ≠ (p₀, q₀)) :
    twoSummandMap K₁ K₂ F p₀ q₀ p₁ q₁ p₁ q₁ = biprod.inr := by
  classical
  have h : ¬ (p₁ = p₀ ∧ q₁ = q₀) := by
    rintro ⟨hp, hq⟩
    exact hne (Prod.ext hp hq)
  simp [twoSummandMap, h]

/-- A totalization term with two potentially nonzero summands is their binary biproduct. -/
def mapBifunctorTwoSummandIso (p₀ : I₁) (q₀ : I₂) (p₁ : I₁) (q₁ : I₂) (j : J)
    [HasBinaryBiproduct ((F.obj (K₁.X p₀)).obj (K₂.X q₀))
      ((F.obj (K₁.X p₁)).obj (K₂.X q₁))]
    (h₀ : ComplexShape.π c₁ c₂ c (p₀, q₀) = j)
    (h₁ : ComplexShape.π c₁ c₂ c (p₁, q₁) = j) (hne : (p₁, q₁) ≠ (p₀, q₀))
    (hzero : ∀ p q, ComplexShape.π c₁ c₂ c (p, q) = j →
      ¬ ((p = p₀ ∧ q = q₀) ∨ (p = p₁ ∧ q = q₁)) →
        IsZero ((F.obj (K₁.X p)).obj (K₂.X q))) :
    (mapBifunctor K₁ K₂ F c).X j ≅
      (F.obj (K₁.X p₀)).obj (K₂.X q₀) ⊞ (F.obj (K₁.X p₁)).obj (K₂.X q₁) where
  hom := mapBifunctorDesc (fun p q _ ↦ twoSummandMap K₁ K₂ F p₀ q₀ p₁ q₁ p q)
  inv := biprod.desc (ιMapBifunctor K₁ K₂ F c p₀ q₀ j h₀)
    (ιMapBifunctor K₁ K₂ F c p₁ q₁ j h₁)
  hom_inv_id := by
    classical
    apply mapBifunctor.hom_ext
    intro p q hpq
    by_cases h₀' : p = p₀ ∧ q = q₀
    · rcases h₀' with ⟨rfl, rfl⟩
      simp only [ι_mapBifunctorDesc_assoc, twoSummandMap_left,
        biprod.inl_desc, Category.comp_id]
    · by_cases h₁' : p = p₁ ∧ q = q₁
      · rcases h₁' with ⟨rfl, rfl⟩
        simp only [ι_mapBifunctorDesc_assoc, twoSummandMap_right K₁ K₂ F p₀ q₀ p q hne,
          biprod.inr_desc, Category.comp_id]
      · exact (hzero p q hpq (by tauto)).eq_of_src _ _
  inv_hom_id := by
    apply biprod.hom_ext'
    · simp only [biprod.inl_desc_assoc, ι_mapBifunctorDesc,
        twoSummandMap_left, Category.comp_id]
    · simp only [biprod.inr_desc_assoc, ι_mapBifunctorDesc,
        twoSummandMap_right K₁ K₂ F p₀ q₀ p₁ q₁ hne, Category.comp_id]

/-- The first supported inclusion computes as the first biproduct inclusion. -/
@[reassoc (attr := simp)]
theorem ι_mapBifunctorTwoSummandIso_hom_left (p₀ : I₁) (q₀ : I₂) (p₁ : I₁) (q₁ : I₂) (j : J)
    [HasBinaryBiproduct ((F.obj (K₁.X p₀)).obj (K₂.X q₀))
      ((F.obj (K₁.X p₁)).obj (K₂.X q₁))]
    (h₀ : ComplexShape.π c₁ c₂ c (p₀, q₀) = j)
    (h₁ : ComplexShape.π c₁ c₂ c (p₁, q₁) = j) (hne : (p₁, q₁) ≠ (p₀, q₀))
    (hzero : ∀ p q, ComplexShape.π c₁ c₂ c (p, q) = j →
      ¬ ((p = p₀ ∧ q = q₀) ∨ (p = p₁ ∧ q = q₁)) →
        IsZero ((F.obj (K₁.X p)).obj (K₂.X q))) :
    ιMapBifunctor K₁ K₂ F c p₀ q₀ j h₀ ≫
      (mapBifunctorTwoSummandIso K₁ K₂ F c p₀ q₀ p₁ q₁ j h₀ h₁ hne hzero).hom =
        biprod.inl := by
  simp only [mapBifunctorTwoSummandIso, ι_mapBifunctorDesc, twoSummandMap_left]

/-- The second supported inclusion computes as the second biproduct inclusion. -/
@[reassoc (attr := simp)]
theorem ι_mapBifunctorTwoSummandIso_hom_right (p₀ : I₁) (q₀ : I₂) (p₁ : I₁) (q₁ : I₂) (j : J)
    [HasBinaryBiproduct ((F.obj (K₁.X p₀)).obj (K₂.X q₀))
      ((F.obj (K₁.X p₁)).obj (K₂.X q₁))]
    (h₀ : ComplexShape.π c₁ c₂ c (p₀, q₀) = j)
    (h₁ : ComplexShape.π c₁ c₂ c (p₁, q₁) = j) (hne : (p₁, q₁) ≠ (p₀, q₀))
    (hzero : ∀ p q, ComplexShape.π c₁ c₂ c (p, q) = j →
      ¬ ((p = p₀ ∧ q = q₀) ∨ (p = p₁ ∧ q = q₁)) →
        IsZero ((F.obj (K₁.X p)).obj (K₂.X q))) :
    ιMapBifunctor K₁ K₂ F c p₁ q₁ j h₁ ≫
      (mapBifunctorTwoSummandIso K₁ K₂ F c p₀ q₀ p₁ q₁ j h₀ h₁ hne hzero).hom =
        biprod.inr := by
  simp only [mapBifunctorTwoSummandIso, ι_mapBifunctorDesc,
    twoSummandMap_right K₁ K₂ F p₀ q₀ p₁ q₁ hne]

/-- The inverse two-summand comparison is the desc map of the supported inclusions. -/
@[simp]
theorem mapBifunctorTwoSummandIso_inv (p₀ : I₁) (q₀ : I₂) (p₁ : I₁) (q₁ : I₂) (j : J)
    [HasBinaryBiproduct ((F.obj (K₁.X p₀)).obj (K₂.X q₀))
      ((F.obj (K₁.X p₁)).obj (K₂.X q₁))]
    (h₀ : ComplexShape.π c₁ c₂ c (p₀, q₀) = j)
    (h₁ : ComplexShape.π c₁ c₂ c (p₁, q₁) = j) (hne : (p₁, q₁) ≠ (p₀, q₀))
    (hzero : ∀ p q, ComplexShape.π c₁ c₂ c (p, q) = j →
      ¬ ((p = p₀ ∧ q = q₀) ∨ (p = p₁ ∧ q = q₁)) →
        IsZero ((F.obj (K₁.X p)).obj (K₂.X q))) :
    (mapBifunctorTwoSummandIso K₁ K₂ F c p₀ q₀ p₁ q₁ j h₀ h₁ hne hzero).inv =
      biprod.desc (ιMapBifunctor K₁ K₂ F c p₀ q₀ j h₀)
        (ιMapBifunctor K₁ K₂ F c p₁ q₁ j h₁) := by
  rfl

end Two

end HomologicalComplex
