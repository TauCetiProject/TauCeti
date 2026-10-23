/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Zigzag.Braid.Inverse.Maps
public import TauCeti.Algebra.Homology.Contraction.ThreeTerm

/-!
# The inverse graded braid complex followed by the braid complex

The cochain tensor product `Bᵢ' ⊗ Bᵢ` has the same three graded terms as `Bᵢ ⊗ Bᵢ'`
(`TauCeti.zigzagBraidComplexTensorInverseHomotopyEquiv`). The second-factor differential
carries the cochain sign `(-1) ^ p`, which is `-1` on the block out of the `(1, -1)` summand,
so the Ui{−2} coordinate of the middle term is negated. The two differential blocks are then
identities, and the three-term cancellation criterion contracts the totalization to the regular
graded bimodule in degree zero: `TauCeti.zigzagBraidInverseTensorComplexHomotopyEquiv`. The
result includes arbitrary finite graphs and commutative coefficient rings, including isolated
vertices.

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

attribute [local instance] zigzagAlgebraIntegerGradedAlgebra

private abbrev reverseInverseProduct (i : V) :
    CochainComplex (GradedModuleCat.{max u w} (zigzagEnvelopingGrading k G).piece) ℤ :=
  HomologicalComplex.mapBifunctor (zigzagBraidInverseComplex k G i) (zigzagBraidComplex k G i)
    F (ComplexShape.up ℤ)

private theorem isZero_reverseInversePair_of_not_support (i : V) (p q : ℤ)
    (h : ¬ ((p = 0 ∨ p = 1) ∧ (q = -1 ∨ q = 0))) :
    IsZero (((F).obj ((zigzagBraidInverseComplex k G i).X p)).obj
      ((zigzagBraidComplex k G i).X q)) := by
  by_cases hp : p = 0 ∨ p = 1
  · exact ((F).obj ((zigzagBraidInverseComplex k G i).X p)).map_isZero
      (isZero_zigzagBraidComplex_X i (by omega) (by omega))
  · exact ((F).flip.obj ((zigzagBraidComplex k G i).X q)).map_isZero
      (isZero_zigzagBraidInverseComplex_X i (by omega) (by omega))

private theorem isZero_reverseInverseProduct_X (i : V) (n : ℤ)
    (h₀ : n ≠ -1) (h₁ : n ≠ 0) (h₂ : n ≠ 1) :
    IsZero ((reverseInverseProduct k G i).X n) := by
  apply (IsZero.iff_id_eq_zero _).2
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  rw [ComplexShape.π_eq_add] at hpq
  exact (isZero_reverseInversePair_of_not_support k G i p q (by omega)).eq_of_src _ _

private def reverseMinusPairIso (i : V) :
    ((F).obj ((zigzagBraidInverseComplex k G i).X 0)).obj
      ((zigzagBraidComplex k G i).X (-1)) ≅ U i :=
  ((F).flip.obj ((zigzagBraidComplex k G i).X (-1))).mapIso
      (zigzagBraidInverseComplexXIso₀ k G i) ≪≫
    ((F).obj (zigzagGradedBimodule k G)).mapIso (zigzagBraidComplexXIso₀ k G i) ≪≫
      zigzagBimoduleLeftUnitor k G (U i)

private def reverseOnePairIso (i : V) :
    ((F).obj ((zigzagBraidInverseComplex k G i).X 1)).obj
      ((zigzagBraidComplex k G i).X 0) ≅ (U i).shiftObj (-2) :=
  ((F).flip.obj ((zigzagBraidComplex k G i).X 0)).mapIso
      (zigzagBraidInverseComplexXIso₁ k G i) ≪≫
    ((F).obj ((U i).shiftObj (-2))).mapIso (zigzagBraidComplexXIso₁ k G i) ≪≫
      zigzagBimoduleRightUnitor k G ((U i).shiftObj (-2))

private def reverseMinusIso (i : V) : (reverseInverseProduct k G i).X (-1) ≅ U i :=
  HomologicalComplex.mapBifunctorSingleSummandIso (zigzagBraidInverseComplex k G i)
      (zigzagBraidComplex k G i) F (ComplexShape.up ℤ) 0 (-1) (-1) (by simp)
      (fun p q hpq _ ↦ isZero_reverseInversePair_of_not_support k G i p q (by
        rw [ComplexShape.π_eq_add] at hpq
        omega)) ≪≫
    reverseMinusPairIso k G i

private def reverseOneIso (i : V) : (reverseInverseProduct k G i).X 1 ≅ (U i).shiftObj (-2) :=
  HomologicalComplex.mapBifunctorSingleSummandIso (zigzagBraidInverseComplex k G i)
      (zigzagBraidComplex k G i) F (ComplexShape.up ℤ) 1 0 1 (by simp)
      (fun p q hpq _ ↦ isZero_reverseInversePair_of_not_support k G i p q (by
        rw [ComplexShape.π_eq_add] at hpq
        omega)) ≪≫
    reverseOnePairIso k G i

private def reverseRegularPairIso (i : V) :
    ((F).obj ((zigzagBraidInverseComplex k G i).X 0)).obj
      ((zigzagBraidComplex k G i).X 0) ≅ zigzagGradedBimodule k G :=
  ((F).flip.obj ((zigzagBraidComplex k G i).X 0)).mapIso
      (zigzagBraidInverseComplexXIso₀ k G i) ≪≫
    ((F).obj (zigzagGradedBimodule k G)).mapIso (zigzagBraidComplexXIso₁ k G i) ≪≫
      zigzagBimoduleRightUnitor k G (zigzagGradedBimodule k G)

private def reverseMiddlePairIso (i : V) :
    ((F).obj ((zigzagBraidInverseComplex k G i).X 1)).obj
      ((zigzagBraidComplex k G i).X (-1)) ≅ (U i).shiftObj (-2) ⊞ U i :=
  ((F).flip.obj ((zigzagBraidComplex k G i).X (-1))).mapIso
      (zigzagBraidInverseComplexXIso₁ k G i) ≪≫
    ((F).obj ((U i).shiftObj (-2))).mapIso (zigzagBraidComplexXIso₀ k G i) ≪≫
      zigzagBraidSelfTensorShiftLeftIso k G i ≪≫
        biprod.mapIso (-Iso.refl ((U i).shiftObj (-2))) (Iso.refl _)

private def reverseZeroIso (i : V) : (reverseInverseProduct k G i).X 0 ≅
    zigzagGradedBimodule k G ⊞ ((U i).shiftObj (-2) ⊞ U i) :=
  HomologicalComplex.mapBifunctorTwoSummandIso (zigzagBraidInverseComplex k G i)
      (zigzagBraidComplex k G i) F (ComplexShape.up ℤ) 0 0 1 (-1) 0 (by simp) (by simp) (by simp)
      (fun p q hpq _ ↦ isZero_reverseInversePair_of_not_support k G i p q (by
        rw [ComplexShape.π_eq_add] at hpq
        omega)) ≪≫
    biprod.mapIso (reverseRegularPairIso k G i) (reverseMiddlePairIso k G i)

private theorem reverse_coevaluation_projection (i : V) :
    ((F).map ((zigzagBraidInverseComplex k G i).d 0 1)).app
        ((zigzagBraidComplex k G i).X (-1)) ≫
      ((F).map (zigzagBraidInverseComplexXIso₁ k G i).hom).app
        ((zigzagBraidComplex k G i).X (-1)) ≫
      ((F).obj ((U i).shiftObj (-2))).map (zigzagBraidComplexXIso₀ k G i).hom ≫
      (zigzagBraidSelfTensorShiftLeftIso k G i).hom ≫ biprod.snd =
        (reverseMinusPairIso k G i).hom := by
  simp only [zigzagBraidInverseComplex_d, Functor.map_comp, NatTrans.comp_app,
    Category.assoc, Iso.map_inv_hom_id_app_assoc]
  have hn : GradedModuleCat.bimoduleTensorMap Γ Γ Γ (zigzagBraidCoevaluationHom k G i)
      (𝟙 ((zigzagBraidComplex k G i).X (-1))) ≫
    GradedModuleCat.bimoduleTensorMap Γ Γ Γ (𝟙 ((U i).shiftObj (-2)))
      (zigzagBraidComplexXIso₀ k G i).hom =
    GradedModuleCat.bimoduleTensorMap Γ Γ Γ (𝟙 (zigzagGradedBimodule k G))
      (zigzagBraidComplexXIso₀ k G i).hom ≫
    GradedModuleCat.bimoduleTensorMap Γ Γ Γ (zigzagBraidCoevaluationHom k G i) (𝟙 (U i)) := by
    rw [← GradedModuleCat.bimoduleTensorMap_comp, ← GradedModuleCat.bimoduleTensorMap_comp]
    simp only [Category.id_comp, Category.comp_id]
    congr 1
  -- Express both transported maps in the grading used by the first-factor self-tensor comparison.
  change GradedModuleCat.bimoduleTensorMap Γ Γ Γ (zigzagBraidInverseComplexXIso₀ k G i).hom
      (𝟙 ((zigzagBraidComplex k G i).X (-1))) ≫
    GradedModuleCat.bimoduleTensorMap Γ Γ Γ (zigzagBraidCoevaluationHom k G i)
      (𝟙 ((zigzagBraidComplex k G i).X (-1))) ≫
    GradedModuleCat.bimoduleTensorMap Γ Γ Γ (𝟙 ((U i).shiftObj (-2)))
      (zigzagBraidComplexXIso₀ k G i).hom ≫
    (zigzagBraidSelfTensorShiftLeftIso k G i).hom ≫ biprod.snd =
    GradedModuleCat.bimoduleTensorMap Γ Γ Γ (zigzagBraidInverseComplexXIso₀ k G i).hom
      (𝟙 ((zigzagBraidComplex k G i).X (-1))) ≫
    GradedModuleCat.bimoduleTensorMap Γ Γ Γ (𝟙 (zigzagGradedBimodule k G))
      (zigzagBraidComplexXIso₀ k G i).hom ≫ (zigzagBimoduleLeftUnitor k G (U i)).hom
  rw [← Category.assoc (GradedModuleCat.bimoduleTensorMap Γ Γ Γ
    (zigzagBraidCoevaluationHom k G i) (𝟙 ((zigzagBraidComplex k G i).X (-1)))), hn]
  simp only [Category.assoc, zigzagBraidSelfTensorShiftLeftIso_coevaluation_snd]

private theorem reverseMiddlePair_coevaluation (i : V) :
    ((F).map ((zigzagBraidInverseComplex k G i).d 0 1)).app
        ((zigzagBraidComplex k G i).X (-1)) ≫
      (reverseMiddlePairIso k G i).hom ≫ biprod.snd =
        (reverseMinusPairIso k G i).hom := by
  -- The middle identification changes the sign of its first summand, preserving the volume copy.
  change ((F).map ((zigzagBraidInverseComplex k G i).d 0 1)).app
      ((zigzagBraidComplex k G i).X (-1)) ≫
    ((F).map (zigzagBraidInverseComplexXIso₁ k G i).hom).app
      ((zigzagBraidComplex k G i).X (-1)) ≫
    ((F).obj ((U i).shiftObj (-2))).map (zigzagBraidComplexXIso₀ k G i).hom ≫
    (zigzagBraidSelfTensorShiftLeftIso k G i).hom ≫ biprod.map (-𝟙 _) (𝟙 _) ≫ biprod.snd = _
  simp only [biprod.map_snd, Category.comp_id]
  exact reverse_coevaluation_projection k G i

private theorem reverse_evaluation_transport (i : V) :
    ((F).obj ((zigzagBraidInverseComplex k G i).X 1)).map
        ((zigzagBraidComplex k G i).d (-1) 0) ≫ (reverseOnePairIso k G i).hom =
      ((F).map (zigzagBraidInverseComplexXIso₁ k G i).hom).app
        ((zigzagBraidComplex k G i).X (-1)) ≫
      ((F).obj ((U i).shiftObj (-2))).map (zigzagBraidComplexXIso₀ k G i).hom ≫
      GradedModuleCat.bimoduleTensorMap Γ Γ Γ (𝟙 ((U i).shiftObj (-2)))
        (zigzagBraidEvaluationHom k G i) ≫
      (zigzagBimoduleRightUnitor k G ((U i).shiftObj (-2))).hom := by
  -- Expand the degree-one component to transport the second-factor evaluation differential.
  change ((F).obj ((zigzagBraidInverseComplex k G i).X 1)).map
      ((zigzagBraidComplex k G i).d (-1) 0) ≫
    ((F).map (zigzagBraidInverseComplexXIso₁ k G i).hom).app
      ((zigzagBraidComplex k G i).X 0) ≫
    ((F).obj ((U i).shiftObj (-2))).map (zigzagBraidComplexXIso₁ k G i).hom ≫
    (zigzagBimoduleRightUnitor k G ((U i).shiftObj (-2))).hom = _
  rw [((F).map (zigzagBraidInverseComplexXIso₁ k G i).hom).naturality_assoc
    ((zigzagBraidComplex k G i).d (-1) 0)
    (((F).obj ((U i).shiftObj (-2))).map (zigzagBraidComplexXIso₁ k G i).hom ≫
      (zigzagBimoduleRightUnitor k G ((U i).shiftObj (-2))).hom)]
  simp only [zigzagBraidComplex_d, Functor.map_comp, Category.assoc,
    GradedModuleCat.shiftFunctor_obj,
    Iso.inv_hom_id_map_assoc (zigzagBraidComplexXIso₁ k G i) ((F).obj ((U i).shiftObj (-2)))
      (zigzagBimoduleRightUnitor k G ((U i).shiftObj (-2))).hom]
  rfl

private theorem reverseMiddlePair_evaluation (i : V) :
    (biprod.inl : (U i).shiftObj (-2) ⟶ (U i).shiftObj (-2) ⊞ U i) ≫
      (reverseMiddlePairIso k G i).inv ≫
      ((F).obj ((zigzagBraidInverseComplex k G i).X 1)).map
        ((zigzagBraidComplex k G i).d (-1) 0) ≫ (reverseOnePairIso k G i).hom =
          -𝟙 ((U i).shiftObj (-2)) := by
  rw [reverse_evaluation_transport]
  -- Expand the inverse component identification to expose its sign and cancel
  -- the transported isomorphisms.
  change biprod.inl ≫ biprod.map (-𝟙 _) (𝟙 _) ≫ (zigzagBraidSelfTensorShiftLeftIso k G i).inv ≫
    ((F).obj ((U i).shiftObj (-2))).map (zigzagBraidComplexXIso₀ k G i).inv ≫
    ((F).map (zigzagBraidInverseComplexXIso₁ k G i).inv).app
      ((zigzagBraidComplex k G i).X (-1)) ≫
    ((F).map (zigzagBraidInverseComplexXIso₁ k G i).hom).app
      ((zigzagBraidComplex k G i).X (-1)) ≫
    ((F).obj ((U i).shiftObj (-2))).map (zigzagBraidComplexXIso₀ k G i).hom ≫
    GradedModuleCat.bimoduleTensorMap Γ Γ Γ (𝟙 ((U i).shiftObj (-2)))
      (zigzagBraidEvaluationHom k G i) ≫
    (zigzagBimoduleRightUnitor k G ((U i).shiftObj (-2))).hom = _
  simp only [biprod.inl_map_assoc, Preadditive.neg_comp, Category.id_comp,
    Iso.map_inv_hom_id_app_assoc]
  apply congrArg Neg.neg
  -- Use tensor-map composition in the grading of the self-tensor isomorphism.
  change biprod.inl ≫ (zigzagBraidSelfTensorShiftLeftIso k G i).inv ≫
    GradedModuleCat.bimoduleTensorMap Γ Γ Γ (𝟙 ((U i).shiftObj (-2)))
      (zigzagBraidComplexXIso₀ k G i).inv ≫
    GradedModuleCat.bimoduleTensorMap Γ Γ Γ (𝟙 ((U i).shiftObj (-2)))
      (zigzagBraidComplexXIso₀ k G i).hom ≫
    GradedModuleCat.bimoduleTensorMap Γ Γ Γ (𝟙 ((U i).shiftObj (-2)))
      (zigzagBraidEvaluationHom k G i) ≫
    (zigzagBimoduleRightUnitor k G ((U i).shiftObj (-2))).hom = 𝟙 _
  have hc : GradedModuleCat.bimoduleTensorMap Γ Γ Γ (𝟙 ((U i).shiftObj (-2)))
      (zigzagBraidComplexXIso₀ k G i).inv ≫
    GradedModuleCat.bimoduleTensorMap Γ Γ Γ (𝟙 ((U i).shiftObj (-2)))
      (zigzagBraidComplexXIso₀ k G i).hom = 𝟙 _ := by
    rw [← GradedModuleCat.bimoduleTensorMap_comp, Category.id_comp,
      Iso.inv_hom_id, GradedModuleCat.bimoduleTensorMap_id]
  rw [← Category.assoc (GradedModuleCat.bimoduleTensorMap Γ Γ Γ (𝟙 ((U i).shiftObj (-2)))
      (zigzagBraidComplexXIso₀ k G i).inv), hc, Category.id_comp,
    ← Category.assoc biprod.inl (zigzagBraidSelfTensorShiftLeftIso k G i).inv,
    zigzagBraidSelfTensorShiftLeftIso_inl_inv]
  exact zigzagBraidSelfTensorShiftLeftInl_evaluation k G i

private theorem reverse_d_snd_snd (i : V) :
    (reverseInverseProduct k G i).d (-1) 0 ≫ (reverseZeroIso k G i).hom ≫
      biprod.snd ≫ biprod.snd = (reverseMinusIso k G i).hom := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  -- Only the pair (0,-1) can contribute to total degree -1.
  rw [ComplexShape.π_eq_add] at hpq
  by_cases hp : p = 0
  · subst p
    have hq : q = -1 := by omega
    subst q
    rw [HomologicalComplex.mapBifunctor.d_eq]
    simp only [Preadditive.comp_add, Preadditive.add_comp,
      HomologicalComplex.mapBifunctor.ι_D₁_assoc,
      HomologicalComplex.mapBifunctor.ι_D₂_assoc]
    rw [HomologicalComplex.mapBifunctor.d₁_eq (zigzagBraidInverseComplex k G i)
        (zigzagBraidComplex k G i) F (ComplexShape.up ℤ)
        (by simp : (ComplexShape.up ℤ).Rel 0 1) (-1) 0 (by simp),
      HomologicalComplex.mapBifunctor.d₂_eq (zigzagBraidInverseComplex k G i)
        (zigzagBraidComplex k G i) F (ComplexShape.up ℤ) 0
        (by simp : (ComplexShape.up ℤ).Rel (-1) 0) 0 (by simp)]
    simp only [show ComplexShape.ε₁ (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) (0, -1) = 1 from rfl,
      show ComplexShape.ε₂ (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) (0, -1) = 1 from rfl,
      one_smul, reverseZeroIso, reverseMinusIso, Iso.trans_hom, biprod.mapIso_hom,
      Category.assoc, HomologicalComplex.ι_mapBifunctorTwoSummandIso_hom_left_assoc,
      HomologicalComplex.ι_mapBifunctorTwoSummandIso_hom_right_assoc,
      HomologicalComplex.ι_mapBifunctorSingleSummandIso_hom_assoc, biprod.inl_map_assoc,
      biprod.inr_map_assoc, biprod.inl_snd_assoc, biprod.inr_snd_assoc, comp_zero, zero_comp,
      add_zero]
    exact reverseMiddlePair_coevaluation k G i
  · exact (isZero_reverseInversePair_of_not_support k G i p q (by omega)).eq_of_src _ _

private theorem reverse_inl_inr_d (i : V) :
    (biprod.inl : (U i).shiftObj (-2) ⟶ (U i).shiftObj (-2) ⊞ U i) ≫
      biprod.inr ≫ (reverseZeroIso k G i).inv ≫
      (reverseInverseProduct k G i).d 0 1 ≫ (reverseOneIso k G i).hom =
        𝟙 ((U i).shiftObj (-2)) := by
  simp only [reverseZeroIso, Iso.trans_inv, biprod.mapIso_inv,
    HomologicalComplex.mapBifunctorTwoSummandIso_inv, Category.assoc, biprod.inr_map_assoc,
    biprod.inr_desc_assoc]
  rw [HomologicalComplex.mapBifunctor.d_eq]
  simp only [Preadditive.comp_add, Preadditive.add_comp,
    HomologicalComplex.mapBifunctor.ι_D₁_assoc,
    HomologicalComplex.mapBifunctor.ι_D₂_assoc]
  rw [HomologicalComplex.mapBifunctor.d₁_eq (zigzagBraidInverseComplex k G i)
      (zigzagBraidComplex k G i) F (ComplexShape.up ℤ)
      (by simp : (ComplexShape.up ℤ).Rel 1 2) (-1) 1 (by simp),
    HomologicalComplex.mapBifunctor.d₂_eq (zigzagBraidInverseComplex k G i)
      (zigzagBraidComplex k G i) F (ComplexShape.up ℤ) 1
      (by simp : (ComplexShape.up ℤ).Rel (-1) 0) 1 (by simp),
    zigzagBraidInverseComplex_d_eq_zero₀ i 2 (by decide)]
  simp only [show ComplexShape.ε₂ (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) (1, -1) = -1 from rfl,
    Functor.map_zero, NatTrans.app_zero, zero_comp, smul_zero, comp_zero, zero_add,
    Units.neg_smul, Preadditive.comp_neg, Preadditive.neg_comp, one_smul,
    reverseOneIso, Iso.trans_hom, Category.assoc,
    HomologicalComplex.ι_mapBifunctorSingleSummandIso_hom_assoc]
  rw [reverseMiddlePair_evaluation, neg_neg]

private def reverseCancellationData (i : V) :
    Contraction.ThreeTermCancellationData (reverseInverseProduct k G i) (U i)
      (zigzagGradedBimodule k G) ((U i).shiftObj (-2)) where
  minusIso := reverseMinusIso k G i
  zeroIso := reverseZeroIso k G i
  oneIso := reverseOneIso k G i
  vanish := isZero_reverseInverseProduct_X k G i
  d_snd_snd := reverse_d_snd_snd k G i
  inl_inr_d := reverse_inl_inr_d k G i

/-- The inverse graded braid complex followed by the braid complex is homotopy
equivalent to the regular graded zigzag bimodule in cochain degree zero. -/
def zigzagBraidInverseTensorComplexHomotopyEquiv (i : V) :
    HomotopyEquiv
      (HomologicalComplex.mapBifunctor (zigzagBraidInverseComplex k G i) (zigzagBraidComplex k G i)
        F (ComplexShape.up ℤ))
      (zigzagBraidUnitComplex k G) :=
  (Contraction.ThreeTermCancellationData.toContraction
    (reverseCancellationData k G i)).homotopyEquiv.symm

end TauCeti
