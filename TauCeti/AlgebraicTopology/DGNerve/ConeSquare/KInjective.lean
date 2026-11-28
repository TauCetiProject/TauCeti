/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGNerve.ConeSquare.Basic
public import TauCeti.AlgebraicTopology.DGNerve.FullSubcategory
public import TauCeti.CategoryTheory.DG.CochainComplex.KInjective
public import TauCeti.Algebra.Homology.HomotopyCategory.KInjective

/-!
# Cone squares in the dg nerve of K-injective complexes

K-injective complexes are closed under mapping cones and mapping cocones. Thus the
coherent cone and cocone squares of complexes lift to their full dg subcategory. The
lifts retain the original triangle coherences, including the negative second projection
in the cocone square. Their images under the inclusion are the ambient squares.

This is the candidate-diagram construction for the K-injective enhancement of
Lurie's *Higher Algebra*, Definition 1.3.5.8. Universal properties are separate results.
-/

public section

noncomputable section

universe v u

open CategoryTheory Limits MonoidalCategory Simplicial SSet CochainComplex
open scoped ZeroObject

namespace TauCeti.KInjectiveDGCategory

variable (R : Type v) [CommRing R] {C : Type u} [Category.{v} C] [Abelian C]
  [Linear R C] {X Y : CochainComplex C ℤ} (f : X ⟶ Y) [X.IsKInjective] [Y.IsKInjective]

local instance : (0 : CochainComplex C ℤ).IsKInjective :=
  isKInjective_of_isZero (isZero_zero _)

/-- The lifted `mappingConeTriangle` in the K-injective dg nerve. -/
def mappingConeTriangle : (dgNerve R (KInjectiveDGCategory C)) _⦋2⦌ :=
  (dgNerve.mappingConeTriangle R f).liftDGFullSubcategory
    (P := fun K : CochainComplex C ℤ ↦ K.IsKInjective) (by
    intro i
    rw [dgNerve.mappingConeTriangle_obj]
    fin_cases i <;> dsimp <;> infer_instance)

/-- Forgetting the lifted triangle gives the original triangle of complexes. -/
@[simp]
lemma mapDGNerveSimplex_inclusion_mappingConeTriangle :
    (DGFullSubcategory.inclusion (R := R)).mapDGNerveSimplex (mappingConeTriangle R f) =
      dgNerve.mappingConeTriangle R f := by
  rw [mappingConeTriangle]
  exact DGNerve.Simplex.mapDGNerveSimplex_inclusion_liftDGFullSubcategory _ _

/-- The lifted `mappingConeZeroTriangle` in the K-injective dg nerve. -/
def mappingConeZeroTriangle : (dgNerve R (KInjectiveDGCategory C)) _⦋2⦌ :=
  (dgNerve.mappingConeZeroTriangle R f).liftDGFullSubcategory
    (P := fun K : CochainComplex C ℤ ↦ K.IsKInjective) (by
    intro i
    rw [dgNerve.mappingConeZeroTriangle_obj]
    fin_cases i <;> dsimp <;> infer_instance)

/-- Forgetting the lifted triangle gives the original triangle of complexes. -/
@[simp]
lemma mapDGNerveSimplex_inclusion_mappingConeZeroTriangle :
    (DGFullSubcategory.inclusion (R := R)).mapDGNerveSimplex (mappingConeZeroTriangle R f) =
      dgNerve.mappingConeZeroTriangle R f := by
  rw [mappingConeZeroTriangle]
  exact DGNerve.Simplex.mapDGNerveSimplex_inclusion_liftDGFullSubcategory _ _

/-- The lifted `mappingCoconeTriangle` in the K-injective dg nerve. -/
def mappingCoconeTriangle : (dgNerve R (KInjectiveDGCategory C)) _⦋2⦌ :=
  (dgNerve.mappingCoconeTriangle R f).liftDGFullSubcategory
    (P := fun K : CochainComplex C ℤ ↦ K.IsKInjective) (by
    intro i
    rw [dgNerve.mappingCoconeTriangle_obj]
    fin_cases i <;> dsimp <;> infer_instance)

/-- Forgetting the lifted triangle gives the original triangle of complexes. -/
@[simp]
lemma mapDGNerveSimplex_inclusion_mappingCoconeTriangle :
    (DGFullSubcategory.inclusion (R := R)).mapDGNerveSimplex (mappingCoconeTriangle R f) =
      dgNerve.mappingCoconeTriangle R f := by
  rw [mappingCoconeTriangle]
  exact DGNerve.Simplex.mapDGNerveSimplex_inclusion_liftDGFullSubcategory _ _

/-- The lifted `mappingCoconeZeroTriangle` in the K-injective dg nerve. -/
def mappingCoconeZeroTriangle : (dgNerve R (KInjectiveDGCategory C)) _⦋2⦌ :=
  (dgNerve.mappingCoconeZeroTriangle R f).liftDGFullSubcategory
    (P := fun K : CochainComplex C ℤ ↦ K.IsKInjective) (by
    intro i
    rw [dgNerve.mappingCoconeZeroTriangle_obj]
    fin_cases i <;> dsimp <;> infer_instance)

/-- Forgetting the lifted triangle gives the original triangle of complexes. -/
@[simp]
lemma mapDGNerveSimplex_inclusion_mappingCoconeZeroTriangle :
    (DGFullSubcategory.inclusion (R := R)).mapDGNerveSimplex (mappingCoconeZeroTriangle R f) =
      dgNerve.mappingCoconeZeroTriangle R f := by
  rw [mappingCoconeZeroTriangle]
  exact DGNerve.Simplex.mapDGNerveSimplex_inclusion_liftDGFullSubcategory _ _

/-- The underlying complex at each vertex of the lifted triangle. -/
@[simp]
lemma mappingConeTriangle_obj_obj (i : Fin 3) :
    ((mappingConeTriangle R f).obj i).obj =
      ![X, Y, mappingCone f] i := by
  rw [mappingConeTriangle]
  -- The vertex of the lift has the ambient vertex as its underlying complex.
  erw [DGNerve.Simplex.liftDGFullSubcategory_obj]
  exact congr_fun (dgNerve.mappingConeTriangle_obj R f) i

/-- Lifting the triangle retains its specified homotopy. -/
@[simp]
lemma mappingConeTriangle_coh :
    (mappingConeTriangle R f).coh 0 2 {1} (-1) (by decide) (by decide) (by simp) ≍
      mappingCone.inl f := by
  rw [mappingConeTriangle]
  -- Coherences of the full dg subcategory are the ambient cochains.
  erw [DGNerve.Simplex.liftDGFullSubcategory_coh]
  exact dgNerve.mappingConeTriangle_coh R f

/-- The underlying complex at each vertex of the lifted triangle. -/
@[simp]
lemma mappingConeZeroTriangle_obj_obj (i : Fin 3) :
    ((mappingConeZeroTriangle R f).obj i).obj =
      ![X, (0 : CochainComplex C ℤ), mappingCone f] i := by
  rw [mappingConeZeroTriangle]
  -- The vertex of the lift has the ambient vertex as its underlying complex.
  erw [DGNerve.Simplex.liftDGFullSubcategory_obj]
  exact congr_fun (dgNerve.mappingConeZeroTriangle_obj R f) i

/-- Lifting the triangle retains its specified homotopy. -/
@[simp]
lemma mappingConeZeroTriangle_coh :
    (mappingConeZeroTriangle R f).coh 0 2 {1} (-1) (by decide) (by decide) (by simp) ≍
      (0 : HomComplex.Cochain X (mappingCone f) (-1)) := by
  rw [mappingConeZeroTriangle]
  -- Coherences of the full dg subcategory are the ambient cochains.
  erw [DGNerve.Simplex.liftDGFullSubcategory_coh]
  exact dgNerve.mappingConeZeroTriangle_coh R f

/-- The underlying complex at each vertex of the lifted triangle. -/
@[simp]
lemma mappingCoconeTriangle_obj_obj (i : Fin 3) :
    ((mappingCoconeTriangle R f).obj i).obj =
      ![mappingCocone f, X, Y] i := by
  rw [mappingCoconeTriangle]
  -- The vertex of the lift has the ambient vertex as its underlying complex.
  erw [DGNerve.Simplex.liftDGFullSubcategory_obj]
  exact congr_fun (dgNerve.mappingCoconeTriangle_obj R f) i

/-- Lifting the triangle retains its specified homotopy. -/
@[simp]
lemma mappingCoconeTriangle_coh :
    (mappingCoconeTriangle R f).coh 0 2 {1} (-1) (by decide) (by decide) (by simp) ≍
      -mappingCocone.snd f := by
  rw [mappingCoconeTriangle]
  -- Coherences of the full dg subcategory are the ambient cochains.
  erw [DGNerve.Simplex.liftDGFullSubcategory_coh]
  exact dgNerve.mappingCoconeTriangle_coh R f

/-- The underlying complex at each vertex of the lifted triangle. -/
@[simp]
lemma mappingCoconeZeroTriangle_obj_obj (i : Fin 3) :
    ((mappingCoconeZeroTriangle R f).obj i).obj =
      ![mappingCocone f, (0 : CochainComplex C ℤ), Y] i := by
  rw [mappingCoconeZeroTriangle]
  -- The vertex of the lift has the ambient vertex as its underlying complex.
  erw [DGNerve.Simplex.liftDGFullSubcategory_obj]
  exact congr_fun (dgNerve.mappingCoconeZeroTriangle_obj R f) i

/-- Lifting the triangle retains its specified homotopy. -/
@[simp]
lemma mappingCoconeZeroTriangle_coh :
    (mappingCoconeZeroTriangle R f).coh 0 2 {1} (-1) (by decide) (by decide) (by simp) ≍
      (0 : HomComplex.Cochain (mappingCocone f) Y (-1)) := by
  rw [mappingCoconeZeroTriangle]
  -- Coherences of the full dg subcategory are the ambient cochains.
  erw [DGNerve.Simplex.liftDGFullSubcategory_coh]
  exact dgNerve.mappingCoconeZeroTriangle_coh R f

/-- The candidate mappingCone square in the dg nerve of K-injective complexes. -/
def mappingConeSquare : Δ[1] ⊗ Δ[1] ⟶ dgNerve R (KInjectiveDGCategory C) :=
  prodStdSimplex₁.squareDesc (SSet.yonedaEquiv.symm (mappingConeZeroTriangle R f))
    (SSet.yonedaEquiv.symm (mappingConeTriangle R f)) (by
      rw [stdSimplex.δ_comp_yonedaEquiv_symm, stdSimplex.δ_comp_yonedaEquiv_symm]
      congr 1
      rw [dgNerve_δ, dgNerve_δ, mappingConeZeroTriangle, mappingConeTriangle]
      -- The ambient simplices have native nerve types; `erw` crosses that wrapper.
      erw [← DGNerve.Simplex.liftDGFullSubcategory_map,
        ← DGNerve.Simplex.liftDGFullSubcategory_map]
      congr 1
      have h := (dgNerve.mappingConeZeroTriangle_δ_one R f).trans
        (dgNerve.mappingConeTriangle_δ_one R f).symm
      dsimp [dgNerve, SimplicialObject.δ] at h
      exact h)

/-- The upper triangle of the K-injective square is the lifted triangle through zero. -/
@[reassoc (attr := simp)]
lemma ι_zero_mappingConeSquare :
    prodStdSimplex₁.ι 0 ≫ mappingConeSquare R f =
      SSet.yonedaEquiv.symm (mappingConeZeroTriangle R f) := by
  simp [mappingConeSquare]

/-- The lower triangle of the K-injective square is the lifted cone or cocone homotopy. -/
@[reassoc (attr := simp)]
lemma ι_one_mappingConeSquare :
    prodStdSimplex₁.ι 1 ≫ mappingConeSquare R f =
      SSet.yonedaEquiv.symm (mappingConeTriangle R f) := by
  simp [mappingConeSquare]

/-- The inclusion sends the K-injective square to the original square of complexes. -/
@[reassoc (attr := simp)]
lemma mappingConeSquare_comp_inclusion :
    mappingConeSquare R f ≫ (DGFullSubcategory.inclusion (R := R)).mapDGNerve =
      dgNerve.mappingConeSquare R f := by
  apply prodStdSimplex₁.square_hom_ext
  · rw [ι_zero_mappingConeSquare_assoc, dgNerve.ι_zero_mappingConeSquare,
      SSet.yonedaEquiv_symm_comp, EnrichedFunctor.mapDGNerve_app,
      mapDGNerveSimplex_inclusion_mappingConeZeroTriangle]
  · rw [ι_one_mappingConeSquare_assoc, dgNerve.ι_one_mappingConeSquare,
      SSet.yonedaEquiv_symm_comp, EnrichedFunctor.mapDGNerve_app,
      mapDGNerveSimplex_inclusion_mappingConeTriangle]

/-- The candidate mappingCocone square in the dg nerve of K-injective complexes. -/
def mappingCoconeSquare : Δ[1] ⊗ Δ[1] ⟶ dgNerve R (KInjectiveDGCategory C) :=
  prodStdSimplex₁.squareDesc (SSet.yonedaEquiv.symm (mappingCoconeZeroTriangle R f))
    (SSet.yonedaEquiv.symm (mappingCoconeTriangle R f)) (by
      rw [stdSimplex.δ_comp_yonedaEquiv_symm, stdSimplex.δ_comp_yonedaEquiv_symm]
      congr 1
      rw [dgNerve_δ, dgNerve_δ, mappingCoconeZeroTriangle, mappingCoconeTriangle]
      -- The ambient simplices have native nerve types; `erw` crosses that wrapper.
      erw [← DGNerve.Simplex.liftDGFullSubcategory_map,
        ← DGNerve.Simplex.liftDGFullSubcategory_map]
      congr 1
      have h := (dgNerve.mappingCoconeZeroTriangle_δ_one R f).trans
        (dgNerve.mappingCoconeTriangle_δ_one R f).symm
      dsimp [dgNerve, SimplicialObject.δ] at h
      exact h)

/-- The upper triangle of the K-injective square is the lifted triangle through zero. -/
@[reassoc (attr := simp)]
lemma ι_zero_mappingCoconeSquare :
    prodStdSimplex₁.ι 0 ≫ mappingCoconeSquare R f =
      SSet.yonedaEquiv.symm (mappingCoconeZeroTriangle R f) := by
  simp [mappingCoconeSquare]

/-- The lower triangle of the K-injective square is the lifted cone or cocone homotopy. -/
@[reassoc (attr := simp)]
lemma ι_one_mappingCoconeSquare :
    prodStdSimplex₁.ι 1 ≫ mappingCoconeSquare R f =
      SSet.yonedaEquiv.symm (mappingCoconeTriangle R f) := by
  simp [mappingCoconeSquare]

/-- The inclusion sends the K-injective square to the original square of complexes. -/
@[reassoc (attr := simp)]
lemma mappingCoconeSquare_comp_inclusion :
    mappingCoconeSquare R f ≫ (DGFullSubcategory.inclusion (R := R)).mapDGNerve =
      dgNerve.mappingCoconeSquare R f := by
  apply prodStdSimplex₁.square_hom_ext
  · rw [ι_zero_mappingCoconeSquare_assoc, dgNerve.ι_zero_mappingCoconeSquare,
      SSet.yonedaEquiv_symm_comp, EnrichedFunctor.mapDGNerve_app,
      mapDGNerveSimplex_inclusion_mappingCoconeZeroTriangle]
  · rw [ι_one_mappingCoconeSquare_assoc, dgNerve.ι_one_mappingCoconeSquare,
      SSet.yonedaEquiv_symm_comp, EnrichedFunctor.mapDGNerve_app,
      mapDGNerveSimplex_inclusion_mappingCoconeTriangle]

end TauCeti.KInjectiveDGCategory
