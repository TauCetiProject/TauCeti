/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Zigzag.Braid.PairTerms
public import Mathlib.Algebra.Homology.Homotopy

/-!
# Commutation of nonadjacent graded zigzag braid complexes

For distinct nonadjacent vertices, the actual tensor product of braid complexes has
only the mixed vertex terms and the regular bimodule term. Unit identifications put
these terms in the two-term complex with differential given by the two evaluations.
Swapping the two vertex summands then gives commutation.

The component identifications describe the commuting map explicitly: in degree zero it
is the identity of the regular bimodule, and in degree minus one it exchanges the two
vertex summands by the biproduct braiding. The supported totalization-inclusion formulas
identify each individual tensor summand with its unit or vertex component.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe u w

variable (k : Type w) [CommRing k] {V : Type u} (G : SimpleGraph V) [Finite V]

local notation "Γ" => zigzagAlgebraInternalGrading k G
local notation "F" => (GradedModuleCat.bimoduleTensor Γ Γ Γ :
  GradedBimoduleCat k Γ ⥤ GradedBimoduleCat k Γ ⥤ GradedBimoduleCat k Γ)
local notation "Z" => zigzagGradedBimodule k G
local notation "U" => zigzagGradedBraidBimodule k G
local notation "B" => zigzagBraidComplex k G
local notation "T" => zigzagBraidComplexTensor k G
local notation "c" => ComplexShape.up ℤ

private def commutingNormal (i j : V) :
    HomologicalComplex (GradedModuleCat.{max u w} (zigzagEnvelopingGrading k G).piece) c :=
  HomologicalComplex.double
    (biprod.desc (zigzagBraidEvaluationHom k G i) (zigzagBraidEvaluationHom k G j))
    (i₀ := -1) (i₁ := 0) (by simp)

private def normalXMinusOneIso (i j : V) : (commutingNormal k G i j).X (-1) ≅ U i ⊞ U j :=
  HomologicalComplex.doubleXIso₀ _ _

private def normalXZeroIso (i j : V) : (commutingNormal k G i j).X 0 ≅ Z :=
  HomologicalComplex.doubleXIso₁ _ _ (by decide)

private theorem normal_d (i j : V) :
    (commutingNormal k G i j).d (-1) 0 =
      (normalXMinusOneIso k G i j).hom ≫
        biprod.desc (zigzagBraidEvaluationHom k G i) (zigzagBraidEvaluationHom k G j) ≫
          (normalXZeroIso k G i j).inv :=
  HomologicalComplex.double_d _ _ (by decide)

private theorem isZero_normal_X (i j : V) (p : ℤ) (h₀ : p ≠ -1) (h₁ : p ≠ 0) :
    IsZero ((commutingNormal k G i j).X p) :=
  HomologicalComplex.isZero_double_X _ _ p h₀ h₁

private def tensorNormalComponentIso (i j : V) (hij : i ≠ j) (hadj : ¬ G.Adj i j) (p : ℤ) :
    (T i j).X p ≅ (commutingNormal k G i j).X p := by
  by_cases h₀ : p = -1
  · subst p
    exact zigzagBraidComplexTensorXMinusOneIso k G i j ≪≫
      (normalXMinusOneIso k G i j).symm
  · by_cases h₁ : p = 0
    · subst p
      exact zigzagBraidComplexTensorXZeroIso k G i j ≪≫ (normalXZeroIso k G i j).symm
    · exact (isZero_zigzagBraidComplexTensor_X_of_ne_of_not_adj hij hadj h₀ h₁).iso
        (isZero_normal_X k G i j p h₀ h₁)

private def tensorNormalIso (i j : V) (hij : i ≠ j) (hadj : ¬ G.Adj i j) :
    T i j ≅ commutingNormal k G i j :=
  HomologicalComplex.Hom.isoOfComponents (tensorNormalComponentIso k G i j hij hadj) (by
    intro p q hpq
    rw [ComplexShape.up_Rel] at hpq
    by_cases hp : p = -1
    · subst p
      have hq : q = 0 := by omega
      subst q
      -- Compute the two supported components of the componentwise isomorphism.
      change ((zigzagBraidComplexTensorXMinusOneIso k G i j).hom ≫
          (normalXMinusOneIso k G i j).inv) ≫ (commutingNormal k G i j).d (-1) 0 =
        (T i j).d (-1) 0 ≫ (zigzagBraidComplexTensorXZeroIso k G i j).hom ≫
          (normalXZeroIso k G i j).inv
      rw [normal_d]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      exact congrArg (fun f ↦ f ≫ (normalXZeroIso k G i j).inv)
        (zigzagBraidComplexTensor_d k G i j).symm
    · by_cases hp' : p = 0
      · exact (isZero_normal_X k G i j q (by omega) (by omega)).eq_of_tgt _ _
      · exact (isZero_zigzagBraidComplexTensor_X_of_ne_of_not_adj hij hadj hp hp').eq_of_src _ _)

private theorem braiding_evaluations (i j : V) :
    (biprod.braiding (U i) (U j)).hom ≫
        biprod.desc (zigzagBraidEvaluationHom k G j) (zigzagBraidEvaluationHom k G i) =
      biprod.desc (zigzagBraidEvaluationHom k G i) (zigzagBraidEvaluationHom k G j) := by
  apply biprod.hom_ext' <;> simp [biprod.braiding_hom]

private def normalSwapComponentIso (i j : V) (p : ℤ) :
    (commutingNormal k G i j).X p ≅ (commutingNormal k G j i).X p := by
  by_cases h₀ : p = -1
  · subst p
    exact normalXMinusOneIso k G i j ≪≫ biprod.braiding (U i) (U j) ≪≫
      (normalXMinusOneIso k G j i).symm
  · by_cases h₁ : p = 0
    · subst p
      exact normalXZeroIso k G i j ≪≫ (normalXZeroIso k G j i).symm
    · exact (isZero_normal_X k G i j p h₀ h₁).iso (isZero_normal_X k G j i p h₀ h₁)

private def normalSwapIso (i j : V) : commutingNormal k G i j ≅ commutingNormal k G j i :=
  HomologicalComplex.Hom.isoOfComponents (normalSwapComponentIso k G i j) (by
    intro p q hpq
    rw [ComplexShape.up_Rel] at hpq
    by_cases hp : p = -1
    · subst p
      have hq : q = 0 := by omega
      subst q
      -- Compute the two supported components of the summand swap.
      change ((normalXMinusOneIso k G i j).hom ≫ (biprod.braiding (U i) (U j)).hom ≫
          (normalXMinusOneIso k G j i).inv) ≫ (commutingNormal k G j i).d (-1) 0 =
        (commutingNormal k G i j).d (-1) 0 ≫ (normalXZeroIso k G i j).hom ≫
          (normalXZeroIso k G j i).inv
      rw [normal_d, normal_d]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      exact congrArg (fun f ↦ (normalXMinusOneIso k G i j).hom ≫ f ≫
        (normalXZeroIso k G j i).inv) (braiding_evaluations k G i j)
    · by_cases hp' : p = 0
      · exact (isZero_normal_X k G j i q (by omega) (by omega)).eq_of_tgt _ _
      · exact (isZero_normal_X k G i j p hp hp').eq_of_src _ _)

/-- The actual graded braid complexes commute under tensoring at distinct nonadjacent vertices. -/
def zigzagBraidComplexTensorCommIso (i j : V) (hij : i ≠ j) (hadj : ¬ G.Adj i j) :
    T i j ≅ T j i :=
  tensorNormalIso k G i j hij hadj ≪≫ normalSwapIso k G i j ≪≫
    (tensorNormalIso k G j i hij.symm (fun h ↦ hadj h.symm)).symm

/-- The nonadjacent commuting isomorphism gives a homotopy equivalence of
actual graded complexes. -/
def zigzagBraidComplexTensorCommHomotopyEquiv (i j : V) (hij : i ≠ j) (hadj : ¬ G.Adj i j) :
    HomotopyEquiv (T i j) (T j i) :=
  HomotopyEquiv.ofIso (zigzagBraidComplexTensorCommIso k G i j hij hadj)

/-- In degree zero the commuting map is the identity under the regular-bimodule identifications. -/
@[reassoc (attr := simp)]
theorem zigzagBraidComplexTensorCommIso_hom_f_zero
    (i j : V) (hij : i ≠ j) (hadj : ¬ G.Adj i j) :
    (zigzagBraidComplexTensorCommIso k G i j hij hadj).hom.f 0 ≫
        (zigzagBraidComplexTensorXZeroIso k G j i).hom =
      (zigzagBraidComplexTensorXZeroIso k G i j).hom := by
  -- Compute the supported components of the three componentwise isomorphisms.
  change ((zigzagBraidComplexTensorXZeroIso k G i j).hom ≫ (normalXZeroIso k G i j).inv) ≫
      ((normalXZeroIso k G i j).hom ≫ (normalXZeroIso k G j i).inv) ≫
        ((normalXZeroIso k G j i).hom ≫ (zigzagBraidComplexTensorXZeroIso k G j i).inv) ≫
          (zigzagBraidComplexTensorXZeroIso k G j i).hom = _
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- In degree minus one the commuting map exchanges the vertex summands by biproduct braiding. -/
@[reassoc (attr := simp)]
theorem zigzagBraidComplexTensorCommIso_hom_f_minus_one
    (i j : V) (hij : i ≠ j) (hadj : ¬ G.Adj i j) :
    (zigzagBraidComplexTensorCommIso k G i j hij hadj).hom.f (-1) ≫
        (zigzagBraidComplexTensorXMinusOneIso k G j i).hom =
      (zigzagBraidComplexTensorXMinusOneIso k G i j).hom ≫ (biprod.braiding (U i) (U j)).hom := by
  -- The degree-minus-one component swaps the two vertex summands.
  change ((zigzagBraidComplexTensorXMinusOneIso k G i j).hom ≫
      (normalXMinusOneIso k G i j).inv) ≫
        ((normalXMinusOneIso k G i j).hom ≫ (biprod.braiding (U i) (U j)).hom ≫
          (normalXMinusOneIso k G j i).inv) ≫
            ((normalXMinusOneIso k G j i).hom ≫
              (zigzagBraidComplexTensorXMinusOneIso k G j i).inv) ≫
                (zigzagBraidComplexTensorXMinusOneIso k G j i).hom = _
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

end TauCeti
