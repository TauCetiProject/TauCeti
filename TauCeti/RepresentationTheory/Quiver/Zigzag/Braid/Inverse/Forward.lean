/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Zigzag.Braid.Inverse.Maps
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Braid.InverseEndpoints
public import TauCeti.Algebra.Homology.Contraction.ThreeTerm

/-!
# The graded braid complex followed by its inverse

The cochain totalization of `Bᵢ ⊗ Bᵢ'` is supported in degrees −1, 0 and 1. Its terms are
Ui, Z ⊞ (Ui{−2} ⊞ Ui), and Ui{−2}. A sign change in the volume coordinate makes the
first differential's Ui block the identity; the second differential restricts to the
identity on Ui{−2}. The three-term cancellation criterion then contracts this complex
to the regular graded bimodule Z in degree zero:
`TauCeti.zigzagBraidComplexTensorInverseHomotopyEquiv`. The component comparisons use
the braid complexes of `TauCeti.zigzagBraidComplex` and the cochain totalization signs.

## References

* M. Khovanov and P. Seidel, *Quivers, Floer cohomology, and braid group actions*, J. Amer. Math.
  Soc. 15 (2002) (the complexes `R_i` and `R_i'` of the zigzag algebra `A_m`).
* R. S. Huerfano and M. Khovanov, *A category for the adjoint representation*, J. Algebra 246
  (2001) (zigzag algebras of arbitrary graphs and the same complexes).
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe u w

variable (k : Type w) [CommRing k] {V : Type u} (G : SimpleGraph V) [Finite V]

local notation "Γ" => zigzagAlgebraInternalGrading k G
local notation "U" => zigzagGradedBraidBimodule k G
local notation "F" => (GradedModuleCat.bimoduleTensor Γ Γ Γ :
  GradedBimoduleCat k Γ ⥤ GradedBimoduleCat k Γ ⥤ GradedBimoduleCat k Γ)
local notation "T" => zigzagBraidInverseComplexTensor k G

attribute [local instance] zigzagAlgebraIntegerGradedAlgebra

private theorem isZero_forwardInverseProduct_X (i : V) (n : ℤ)
    (h₀ : n ≠ -1) (h₁ : n ≠ 0) (h₂ : n ≠ 1) :
    IsZero ((T i).X n) := by
  apply (IsZero.iff_id_eq_zero _).2
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  rw [ComplexShape.π_eq_add] at hpq
  exact (isZero_zigzagBraidInverseComplexTensor_pair k G i p q (by omega)).eq_of_src _ _

private def forwardMinusPairIso (i : V) :
    ((F).obj ((zigzagBraidComplex k G i).X (-1))).obj
      ((zigzagBraidInverseComplex k G i).X 0) ≅ U i :=
  ((F).flip.obj ((zigzagBraidInverseComplex k G i).X 0)).mapIso
      (zigzagBraidComplexXIso₀ k G i) ≪≫
    ((F).obj (U i)).mapIso (zigzagBraidInverseComplexXIso₀ k G i) ≪≫
      zigzagBimoduleRightUnitor k G (U i)

private def forwardOnePairIso (i : V) :
    ((F).obj ((zigzagBraidComplex k G i).X 0)).obj
      ((zigzagBraidInverseComplex k G i).X 1) ≅ (U i).shiftObj (-2) :=
  ((F).flip.obj ((zigzagBraidInverseComplex k G i).X 1)).mapIso
      (zigzagBraidComplexXIso₁ k G i) ≪≫
    ((F).obj (zigzagGradedBimodule k G)).mapIso
      (zigzagBraidInverseComplexXIso₁ k G i) ≪≫
        zigzagBimoduleLeftUnitor k G ((U i).shiftObj (-2))

private def forwardRegularPairIso (i : V) :
    ((F).obj ((zigzagBraidComplex k G i).X 0)).obj
      ((zigzagBraidInverseComplex k G i).X 0) ≅ zigzagGradedBimodule k G :=
  ((F).flip.obj ((zigzagBraidInverseComplex k G i).X 0)).mapIso
      (zigzagBraidComplexXIso₁ k G i) ≪≫
    ((F).obj (zigzagGradedBimodule k G)).mapIso (zigzagBraidInverseComplexXIso₀ k G i) ≪≫
      zigzagBimoduleRightUnitor k G (zigzagGradedBimodule k G)

private def forwardMiddlePairIso (i : V) :
    ((F).obj ((zigzagBraidComplex k G i).X (-1))).obj
      ((zigzagBraidInverseComplex k G i).X 1) ≅ (U i).shiftObj (-2) ⊞ U i :=
  ((F).flip.obj ((zigzagBraidInverseComplex k G i).X 1)).mapIso
      (zigzagBraidComplexXIso₀ k G i) ≪≫
    ((F).obj (U i)).mapIso (zigzagBraidInverseComplexXIso₁ k G i) ≪≫
      zigzagBraidSelfTensorShiftRightIso k G i ≪≫
        biprod.mapIso (Iso.refl _) (-Iso.refl (U i))

private def forwardZeroIso (i : V) :
    (T i).X 0 ≅ zigzagGradedBimodule k G ⊞ ((U i).shiftObj (-2) ⊞ U i) :=
  HomologicalComplex.mapBifunctorTwoSummandIso (zigzagBraidComplex k G i)
      (zigzagBraidInverseComplex k G i) F (ComplexShape.up ℤ) 0 0 (-1) 1 0 (by simp) (by simp)
      (by simp) (fun p q hpq _ ↦ isZero_zigzagBraidInverseComplexTensor_pair k G i p q (by
        rw [ComplexShape.π_eq_add] at hpq
        omega)) ≪≫
    biprod.mapIso (forwardRegularPairIso k G i) (forwardMiddlePairIso k G i)

private theorem forward_coevaluation_projection (i : V) :
    ((F).obj ((zigzagBraidComplex k G i).X (-1))).map
        ((zigzagBraidInverseComplex k G i).d 0 1) ≫
      ((F).map (zigzagBraidComplexXIso₀ k G i).hom).app
        ((zigzagBraidInverseComplex k G i).X 1) ≫
      ((F).obj (U i)).map (zigzagBraidInverseComplexXIso₁ k G i).hom ≫
      (zigzagBraidSelfTensorShiftRightIso k G i).hom ≫ biprod.snd =
        (forwardMinusPairIso k G i).hom := by
  rw [((F).map (zigzagBraidComplexXIso₀ k G i).hom).naturality_assoc
    ((zigzagBraidInverseComplex k G i).d 0 1)
    (((F).obj (U i)).map (zigzagBraidInverseComplexXIso₁ k G i).hom ≫
      (zigzagBraidSelfTensorShiftRightIso k G i).hom ≫ biprod.snd)]
  simp only [zigzagBraidInverseComplex_d, Functor.map_comp, Category.assoc,
    Iso.inv_hom_id_map_assoc (zigzagBraidInverseComplexXIso₁ k G i) ((F).obj (U i))]
  rw [zigzagBraidSelfTensorShiftRightIso_coevaluation_snd]
  rfl

private theorem forwardMiddlePair_coevaluation (i : V) :
    ((F).obj ((zigzagBraidComplex k G i).X (-1))).map
        ((zigzagBraidInverseComplex k G i).d 0 1) ≫
      (forwardMiddlePairIso k G i).hom ≫ biprod.snd =
        -(forwardMinusPairIso k G i).hom := by
  -- Expose the sign change in the middle summand before projecting to its volume copy.
  change ((F).obj ((zigzagBraidComplex k G i).X (-1))).map
      ((zigzagBraidInverseComplex k G i).d 0 1) ≫
    ((F).map (zigzagBraidComplexXIso₀ k G i).hom).app
      ((zigzagBraidInverseComplex k G i).X 1) ≫
    ((F).obj (U i)).map (zigzagBraidInverseComplexXIso₁ k G i).hom ≫
    (zigzagBraidSelfTensorShiftRightIso k G i).hom ≫ biprod.map (𝟙 _) (-𝟙 _) ≫ biprod.snd = _
  simp only [biprod.map_snd, Preadditive.comp_neg, Category.comp_id]
  exact congrArg Neg.neg (forward_coevaluation_projection k G i)

private theorem forward_d_snd_snd (i : V) :
    (T i).d (-1) 0 ≫ (forwardZeroIso k G i).hom ≫ biprod.snd ≫ biprod.snd =
      (zigzagBraidInverseTensorXMinusOneIso k G i).hom := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  -- Only the pair (-1,0) can contribute to total degree -1.
  rw [ComplexShape.π_eq_add] at hpq
  by_cases hp : p = -1
  · subst p
    obtain rfl : q = 0 := by omega
    rw [HomologicalComplex.mapBifunctor.d_eq]
    simp only [Preadditive.comp_add, Preadditive.add_comp,
      HomologicalComplex.mapBifunctor.ι_D₁_assoc,
      HomologicalComplex.mapBifunctor.ι_D₂_assoc]
    rw [HomologicalComplex.mapBifunctor.d₁_eq (zigzagBraidComplex k G i)
        (zigzagBraidInverseComplex k G i) F (ComplexShape.up ℤ)
        (by simp : (ComplexShape.up ℤ).Rel (-1) 0) 0 0 (by simp),
      HomologicalComplex.mapBifunctor.d₂_eq (zigzagBraidComplex k G i)
        (zigzagBraidInverseComplex k G i) F (ComplexShape.up ℤ) (-1)
        (by simp : (ComplexShape.up ℤ).Rel 0 1) 0 (by simp)]
    simp only [show ComplexShape.ε₁ (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) (-1, 0) = 1 from rfl,
      show ComplexShape.ε₂ (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) (-1, 0) = -1 from rfl,
      one_smul, Units.neg_smul, Preadditive.neg_comp, forwardZeroIso, Iso.trans_hom,
      biprod.mapIso_hom, Category.assoc,
      HomologicalComplex.ι_mapBifunctorTwoSummandIso_hom_left_assoc,
      HomologicalComplex.ι_mapBifunctorTwoSummandIso_hom_right_assoc, biprod.inl_map_assoc,
      biprod.inr_map_assoc, biprod.inl_snd_assoc, biprod.inr_snd_assoc, comp_zero, zero_comp,
      zero_add, ιMapBifunctor_zigzagBraidInverseTensorXMinusOneIso_hom]
    rw [forwardMiddlePair_coevaluation, neg_neg]
    rfl
  · exact (isZero_zigzagBraidInverseComplexTensor_pair k G i p q (by omega)).eq_of_src _ _

private theorem forward_evaluation_transport (i : V) :
    ((F).map ((zigzagBraidComplex k G i).d (-1) 0)).app
        ((zigzagBraidInverseComplex k G i).X 1) ≫ (forwardOnePairIso k G i).hom =
      ((F).map (zigzagBraidComplexXIso₀ k G i).hom).app
        ((zigzagBraidInverseComplex k G i).X 1) ≫
      ((F).obj (U i)).map (zigzagBraidInverseComplexXIso₁ k G i).hom ≫
      GradedModuleCat.bimoduleTensorMap Γ Γ Γ (zigzagBraidEvaluationHom k G i)
        (𝟙 ((U i).shiftObj (-2))) ≫
      (zigzagBimoduleLeftUnitor k G ((U i).shiftObj (-2))).hom := by
  -- Expand the component isomorphism to transport the actual evaluation differential.
  change ((F).map ((zigzagBraidComplex k G i).d (-1) 0)).app
      ((zigzagBraidInverseComplex k G i).X 1) ≫
    ((F).map (zigzagBraidComplexXIso₁ k G i).hom).app
      ((zigzagBraidInverseComplex k G i).X 1) ≫
    ((F).obj (zigzagGradedBimodule k G)).map (zigzagBraidInverseComplexXIso₁ k G i).hom ≫
    (zigzagBimoduleLeftUnitor k G ((U i).shiftObj (-2))).hom = _
  simp only [zigzagBraidComplex_d, Functor.map_comp, NatTrans.comp_app, Category.assoc,
    Iso.map_inv_hom_id_app_assoc]
  rw [← ((F).map (zigzagBraidEvaluationHom k G i)).naturality_assoc
    (zigzagBraidInverseComplexXIso₁ k G i).hom
    (zigzagBimoduleLeftUnitor k G ((U i).shiftObj (-2))).hom]
  rfl

private theorem forwardMiddlePair_evaluation (i : V) :
    (biprod.inl : (U i).shiftObj (-2) ⟶ (U i).shiftObj (-2) ⊞ U i) ≫
      (forwardMiddlePairIso k G i).inv ≫
      ((F).map ((zigzagBraidComplex k G i).d (-1) 0)).app
        ((zigzagBraidInverseComplex k G i).X 1) ≫ (forwardOnePairIso k G i).hom =
          𝟙 ((U i).shiftObj (-2)) := by
  rw [forward_evaluation_transport]
  -- Expand the inverse component identification so the two transported isomorphisms cancel.
  change biprod.inl ≫ biprod.map (𝟙 _) (-𝟙 _) ≫ (zigzagBraidSelfTensorShiftRightIso k G i).inv ≫
    ((F).obj (U i)).map (zigzagBraidInverseComplexXIso₁ k G i).inv ≫
    ((F).map (zigzagBraidComplexXIso₀ k G i).inv).app
      ((zigzagBraidInverseComplex k G i).X 1) ≫
    ((F).map (zigzagBraidComplexXIso₀ k G i).hom).app
      ((zigzagBraidInverseComplex k G i).X 1) ≫
    ((F).obj (U i)).map (zigzagBraidInverseComplexXIso₁ k G i).hom ≫
    GradedModuleCat.bimoduleTensorMap Γ Γ Γ (zigzagBraidEvaluationHom k G i)
      (𝟙 ((U i).shiftObj (-2))) ≫
    (zigzagBimoduleLeftUnitor k G ((U i).shiftObj (-2))).hom = _
  simp only [biprod.inl_map_assoc, Category.id_comp,
    Iso.map_inv_hom_id_app_assoc]
  -- Use the public tensor-map composition equation in the grading of the self-tensor isomorphism.
  change biprod.inl ≫ (zigzagBraidSelfTensorShiftRightIso k G i).inv ≫
    GradedModuleCat.bimoduleTensorMap Γ Γ Γ (𝟙 (U i))
      (zigzagBraidInverseComplexXIso₁ k G i).inv ≫
    GradedModuleCat.bimoduleTensorMap Γ Γ Γ (𝟙 (U i))
      (zigzagBraidInverseComplexXIso₁ k G i).hom ≫
    GradedModuleCat.bimoduleTensorMap Γ Γ Γ (zigzagBraidEvaluationHom k G i)
      (𝟙 ((U i).shiftObj (-2))) ≫
    (zigzagBimoduleLeftUnitor k G ((U i).shiftObj (-2))).hom = _
  have hc : GradedModuleCat.bimoduleTensorMap Γ Γ Γ (𝟙 (U i))
      (zigzagBraidInverseComplexXIso₁ k G i).inv ≫
    GradedModuleCat.bimoduleTensorMap Γ Γ Γ (𝟙 (U i))
      (zigzagBraidInverseComplexXIso₁ k G i).hom = 𝟙 _ := by
    rw [← GradedModuleCat.bimoduleTensorMap_comp, Category.id_comp,
      Iso.inv_hom_id, GradedModuleCat.bimoduleTensorMap_id]
  rw [← Category.assoc (GradedModuleCat.bimoduleTensorMap Γ Γ Γ (𝟙 (U i))
      (zigzagBraidInverseComplexXIso₁ k G i).inv), hc, Category.id_comp]
  rw [← Category.assoc biprod.inl (zigzagBraidSelfTensorShiftRightIso k G i).inv,
    zigzagBraidSelfTensorShiftRightIso_inl_inv]
  exact zigzagBraidSelfTensorShiftRightInl_evaluation k G i

private theorem forward_inl_inr_d (i : V) :
    (biprod.inl : (U i).shiftObj (-2) ⟶ (U i).shiftObj (-2) ⊞ U i) ≫
      biprod.inr ≫ (forwardZeroIso k G i).inv ≫
      (T i).d 0 1 ≫ (zigzagBraidInverseTensorXOneIso k G i).hom =
        𝟙 ((U i).shiftObj (-2)) := by
  simp only [forwardZeroIso, Iso.trans_inv, biprod.mapIso_inv,
    HomologicalComplex.mapBifunctorTwoSummandIso_inv, Category.assoc, biprod.inr_map_assoc,
    biprod.inr_desc_assoc]
  rw [HomologicalComplex.mapBifunctor.d_eq]
  simp only [Preadditive.comp_add, Preadditive.add_comp,
    HomologicalComplex.mapBifunctor.ι_D₁_assoc,
    HomologicalComplex.mapBifunctor.ι_D₂_assoc]
  rw [HomologicalComplex.mapBifunctor.d₁_eq (zigzagBraidComplex k G i)
      (zigzagBraidInverseComplex k G i) F (ComplexShape.up ℤ)
      (by simp : (ComplexShape.up ℤ).Rel (-1) 0) 1 1 (by simp),
    HomologicalComplex.mapBifunctor.d₂_eq (zigzagBraidComplex k G i)
      (zigzagBraidInverseComplex k G i) F (ComplexShape.up ℤ) (-1)
      (by simp : (ComplexShape.up ℤ).Rel 1 2) 1 (by simp),
    zigzagBraidInverseComplex_d_eq_zero₀ i 2 (by decide)]
  simp only [show ComplexShape.ε₁ (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) (-1, 1) = 1 from rfl,
    one_smul, Functor.map_zero, zero_comp, smul_zero, comp_zero, add_zero, Category.assoc,
    ιMapBifunctor_zigzagBraidInverseTensorXOneIso_hom]
  exact forwardMiddlePair_evaluation k G i

private def forwardCancellationData (i : V) :
    Contraction.ThreeTermCancellationData (T i) (U i)
      (zigzagGradedBimodule k G) ((U i).shiftObj (-2)) where
  minusIso := zigzagBraidInverseTensorXMinusOneIso k G i
  zeroIso := forwardZeroIso k G i
  oneIso := zigzagBraidInverseTensorXOneIso k G i
  vanish := isZero_forwardInverseProduct_X k G i
  d_snd_snd := forward_d_snd_snd k G i
  inl_inr_d := forward_inl_inr_d k G i

/-- The graded braid complex followed by its inverse is homotopy equivalent
to the regular graded zigzag bimodule in cochain degree zero. -/
def zigzagBraidComplexTensorInverseHomotopyEquiv (i : V) :
    HomotopyEquiv (zigzagBraidInverseComplexTensor k G i) (zigzagBraidUnitComplex k G) :=
  (Contraction.ThreeTermCancellationData.toContraction
    (forwardCancellationData k G i)).homotopyEquiv.symm

end TauCeti
