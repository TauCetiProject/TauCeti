/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Zigzag.Braid.Inverse.Maps
public import TauCeti.Algebra.Homology.Contraction.ThreeTerm

/-!
# The graded braid complex followed by its inverse

The actual cochain totalization is supported in degrees −1, 0 and 1. Its terms are
Ui, Z ⊞ (Ui{−2} ⊞ Ui), and Ui{−2}. A sign change in the volume coordinate makes the
first differential's Ui block the identity; the second differential restricts to the
identity on Ui{−2}. The three-term cancellation criterion then contracts this complex
to the actual regular graded bimodule Z in degree zero. All component comparisons use
the existing braid complexes and the cochain totalization signs.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits MulOpposite
open scoped TensorProduct

universe u w

variable (k : Type w) [CommRing k] {V : Type u} (G : SimpleGraph V) [Finite V]

local notation "Z" => AlgCat.carrier (zigzagAlgebra k G)
local notation "E" => Z ⊗[k] Zᵐᵒᵖ
local notation "Γ" => zigzagAlgebraInternalGrading k G
local notation "U" => zigzagGradedBraidBimodule k G
local notation "F" => zigzagBimoduleTensor k G

attribute [local instance] zigzagAlgebraIntegerGradedAlgebra

private abbrev forwardInverseProduct (i : V) :
    CochainComplex (GradedModuleCat.{max u w} (zigzagEnvelopingGrading k G).piece) ℤ :=
  HomologicalComplex.mapBifunctor (zigzagBraidComplex k G i) (zigzagBraidInverseComplex k G i)
    F (ComplexShape.up ℤ)

private theorem isZero_forwardInversePair_of_not_support (i : V) (p q : ℤ)
    (h : ¬ ((p = -1 ∨ p = 0) ∧ (q = 0 ∨ q = 1))) :
    IsZero (((F).obj ((zigzagBraidComplex k G i).X p)).obj
      ((zigzagBraidInverseComplex k G i).X q)) := by
  by_cases hp : p = -1 ∨ p = 0
  · exact ((F).obj ((zigzagBraidComplex k G i).X p)).map_isZero
      (isZero_zigzagBraidInverseComplex_X i (by omega) (by omega))
  · exact ((F).flip.obj ((zigzagBraidInverseComplex k G i).X q)).map_isZero
      (isZero_zigzagBraidComplex_X i (by omega) (by omega))

private theorem isZero_forwardInverseProduct_X (i : V) (n : ℤ)
    (h₀ : n ≠ -1) (h₁ : n ≠ 0) (h₂ : n ≠ 1) :
    IsZero ((forwardInverseProduct k G i).X n) := by
  apply (IsZero.iff_id_eq_zero _).2
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  -- Cochain totalization assigns the tensor pair the sum of its two indices.
  change p + q = n at hpq
  exact (isZero_forwardInversePair_of_not_support k G i p q (by omega)).eq_of_src _ _

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

private def forwardMinusMap (i : V) (p q : ℤ) :
    ((F).obj ((zigzagBraidComplex k G i).X p)).obj
      ((zigzagBraidInverseComplex k G i).X q) ⟶ U i := by
  by_cases hp : p = (-1)
  · subst p
    by_cases hq : q = 0
    · subst q
      exact (forwardMinusPairIso k G i).hom
    · exact 0
  · exact 0

private def forwardMinusHom (i : V) : (forwardInverseProduct k G i).X (-1) ⟶ U i :=
  HomologicalComplex.mapBifunctorDesc (fun p q _ ↦ forwardMinusMap k G i p q)

private def forwardMinusInv (i : V) : U i ⟶ (forwardInverseProduct k G i).X (-1) :=
  (forwardMinusPairIso k G i).inv ≫ HomologicalComplex.ιMapBifunctor
    (zigzagBraidComplex k G i) (zigzagBraidInverseComplex k G i) F (ComplexShape.up ℤ)
    (-1) 0 (-1) (by simp)

private theorem forwardMinusMap_supported (i : V) :
    forwardMinusMap k G i (-1) 0 = (forwardMinusPairIso k G i).hom := by
  simp only [forwardMinusMap, dite_true]

private def forwardMinusIso (i : V) : (forwardInverseProduct k G i).X (-1) ≅ U i where
  hom := forwardMinusHom k G i
  inv := forwardMinusInv k G i
  hom_inv_id := by
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    -- The total degree is the sum of the pair of cochain indices.
    change p + q = (-1) at hpq
    by_cases hp : p = (-1)
    · subst p
      have hq : q = 0 := by omega
      subst q
      simp only [forwardMinusHom, forwardMinusInv,
        HomologicalComplex.ι_mapBifunctorDesc_assoc, forwardMinusMap_supported,
        Iso.hom_inv_id_assoc, Category.comp_id]
    · exact (isZero_forwardInversePair_of_not_support k G i p q (by omega)).eq_of_src _ _
  inv_hom_id := by
    simp only [forwardMinusHom, forwardMinusInv, Category.assoc,
      HomologicalComplex.ι_mapBifunctorDesc, forwardMinusMap_supported, Iso.inv_hom_id]

private def forwardOneMap (i : V) (p q : ℤ) :
    ((F).obj ((zigzagBraidComplex k G i).X p)).obj
      ((zigzagBraidInverseComplex k G i).X q) ⟶ (U i).shiftObj (-2) := by
  by_cases hp : p = 0
  · subst p
    by_cases hq : q = 1
    · subst q
      exact (forwardOnePairIso k G i).hom
    · exact 0
  · exact 0

private def forwardOneHom (i : V) : (forwardInverseProduct k G i).X 1 ⟶ (U i).shiftObj (-2) :=
  HomologicalComplex.mapBifunctorDesc (fun p q _ ↦ forwardOneMap k G i p q)

private def forwardOneInv (i : V) : (U i).shiftObj (-2) ⟶ (forwardInverseProduct k G i).X 1 :=
  (forwardOnePairIso k G i).inv ≫ HomologicalComplex.ιMapBifunctor
    (zigzagBraidComplex k G i) (zigzagBraidInverseComplex k G i) F (ComplexShape.up ℤ)
    0 1 1 (by simp)

private theorem forwardOneMap_supported (i : V) :
    forwardOneMap k G i 0 1 = (forwardOnePairIso k G i).hom := by
  simp only [forwardOneMap, dite_true]

private def forwardOneIso (i : V) : (forwardInverseProduct k G i).X 1 ≅ (U i).shiftObj (-2) where
  hom := forwardOneHom k G i
  inv := forwardOneInv k G i
  hom_inv_id := by
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    -- The total degree is the sum of the pair of cochain indices.
    change p + q = 1 at hpq
    by_cases hp : p = 0
    · subst p
      have hq : q = 1 := by omega
      subst q
      simp only [forwardOneHom, forwardOneInv,
        HomologicalComplex.ι_mapBifunctorDesc_assoc, forwardOneMap_supported,
        Iso.hom_inv_id_assoc, Category.comp_id]
    · exact (isZero_forwardInversePair_of_not_support k G i p q (by omega)).eq_of_src _ _
  inv_hom_id := by
    simp only [forwardOneHom, forwardOneInv, Category.assoc,
      HomologicalComplex.ι_mapBifunctorDesc, forwardOneMap_supported, Iso.inv_hom_id]

private def negativeVertexIso (i : V) : U i ≅ U i where
  hom := -𝟙 _
  inv := -𝟙 _
  hom_inv_id := by simp
  inv_hom_id := by simp

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
        biprod.mapIso (Iso.refl _) (negativeVertexIso k G i)

private def forwardZeroMap (i : V) (p q : ℤ) :
    ((F).obj ((zigzagBraidComplex k G i).X p)).obj
      ((zigzagBraidInverseComplex k G i).X q) ⟶
        zigzagGradedBimodule k G ⊞ ((U i).shiftObj (-2) ⊞ U i) := by
  by_cases hp : p = 0
  · subst p
    by_cases hq : q = 0
    · subst q
      exact (forwardRegularPairIso k G i).hom ≫ biprod.inl
    · exact 0
  · by_cases hp' : p = -1
    · subst p
      by_cases hq : q = 1
      · subst q
        exact (forwardMiddlePairIso k G i).hom ≫ biprod.inr
      · exact 0
    · exact 0

private def forwardZeroHom (i : V) : (forwardInverseProduct k G i).X 0 ⟶
    zigzagGradedBimodule k G ⊞ ((U i).shiftObj (-2) ⊞ U i) :=
  HomologicalComplex.mapBifunctorDesc (fun p q _ ↦ forwardZeroMap k G i p q)

private theorem forwardZeroMap_regular (i : V) :
    forwardZeroMap k G i 0 0 = (forwardRegularPairIso k G i).hom ≫ biprod.inl := by
  simp only [forwardZeroMap, dite_true]

private theorem forwardZeroMap_middle (i : V) :
    forwardZeroMap k G i (-1) 1 = (forwardMiddlePairIso k G i).hom ≫ biprod.inr := by
  simp only [forwardZeroMap, show (-1 : ℤ) ≠ 0 by decide, dite_false, dite_true]

private def forwardZeroInv (i : V) :
    zigzagGradedBimodule k G ⊞ ((U i).shiftObj (-2) ⊞ U i) ⟶
      (forwardInverseProduct k G i).X 0 :=
  biprod.desc
    ((forwardRegularPairIso k G i).inv ≫ HomologicalComplex.ιMapBifunctor
      (zigzagBraidComplex k G i) (zigzagBraidInverseComplex k G i) F (ComplexShape.up ℤ)
      0 0 0 (by simp))
    ((forwardMiddlePairIso k G i).inv ≫ HomologicalComplex.ιMapBifunctor
      (zigzagBraidComplex k G i) (zigzagBraidInverseComplex k G i) F (ComplexShape.up ℤ)
      (-1) 1 0 (by simp))

private def forwardZeroIso (i : V) : (forwardInverseProduct k G i).X 0 ≅
    zigzagGradedBimodule k G ⊞ ((U i).shiftObj (-2) ⊞ U i) where
  hom := forwardZeroHom k G i
  inv := forwardZeroInv k G i
  hom_inv_id := by
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    -- Degree zero has precisely the regular pair and the internally shifted middle pair.
    change p + q = 0 at hpq
    by_cases hp : p = 0
    · subst p
      have hq : q = 0 := by omega
      subst q
      simp only [forwardZeroHom, forwardZeroInv, Category.assoc,
        HomologicalComplex.ι_mapBifunctorDesc_assoc, forwardZeroMap_regular,
        biprod.inl_desc, Iso.hom_inv_id_assoc, Category.comp_id]
    · by_cases hp' : p = -1
      · subst p
        have hq : q = 1 := by omega
        subst q
        simp only [forwardZeroHom, forwardZeroInv, Category.assoc,
          HomologicalComplex.ι_mapBifunctorDesc_assoc, forwardZeroMap_middle,
          biprod.inr_desc, Iso.hom_inv_id_assoc, Category.comp_id]
      · exact (isZero_forwardInversePair_of_not_support k G i p q (by omega)).eq_of_src _ _
  inv_hom_id := by
    apply biprod.hom_ext'
    · simp only [forwardZeroHom, forwardZeroInv, Category.assoc, biprod.inl_desc_assoc,
        HomologicalComplex.ι_mapBifunctorDesc, forwardZeroMap_regular,
        Iso.inv_hom_id_assoc, Category.comp_id]
    · simp only [forwardZeroHom, forwardZeroInv, Category.assoc, biprod.inr_desc_assoc,
        HomologicalComplex.ι_mapBifunctorDesc, forwardZeroMap_middle,
        Iso.inv_hom_id_assoc, Category.comp_id]

private theorem forwardCoevaluationProjection (i : V) :
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
  exact congrArg Neg.neg (forwardCoevaluationProjection k G i)

private theorem forward_d_third (i : V) :
    (forwardInverseProduct k G i).d (-1) 0 ≫ (forwardZeroIso k G i).hom ≫
      biprod.snd ≫ biprod.snd = (forwardMinusIso k G i).hom := by
  -- The component isomorphisms use the totalization desc maps just constructed.
  change (forwardInverseProduct k G i).d (-1) 0 ≫ forwardZeroHom k G i ≫
    biprod.snd ≫ biprod.snd = forwardMinusHom k G i
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  -- Only the pair (-1,0) can contribute to total degree -1.
  change p + q = -1 at hpq
  by_cases hp : p = -1
  · subst p
    have hq : q = 0 := by omega
    subst q
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
      one_smul, Units.neg_smul, Preadditive.neg_comp, forwardZeroHom,
      forwardMinusHom, Category.assoc, HomologicalComplex.ι_mapBifunctorDesc,
      HomologicalComplex.ι_mapBifunctorDesc_assoc, forwardZeroMap_regular,
      forwardZeroMap_middle, forwardMinusMap_supported, biprod.inl_snd_assoc,
      biprod.inr_snd_assoc, comp_zero, zero_comp,
      zero_add]
    rw [forwardMiddlePair_coevaluation, neg_neg]
  · exact (isZero_forwardInversePair_of_not_support k G i p q (by omega)).eq_of_src _ _

private theorem forwardEvaluationTransport (i : V) :
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
  rw [forwardEvaluationTransport]
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

private theorem forward_d_middle (i : V) :
    (biprod.inl : (U i).shiftObj (-2) ⟶ (U i).shiftObj (-2) ⊞ U i) ≫
      biprod.inr ≫ (forwardZeroIso k G i).inv ≫
      (forwardInverseProduct k G i).d 0 1 ≫ (forwardOneIso k G i).hom =
        𝟙 ((U i).shiftObj (-2)) := by
  -- These components were defined as a binary desc and a totalization desc respectively.
  change biprod.inl ≫ biprod.inr ≫ forwardZeroInv k G i ≫
    (forwardInverseProduct k G i).d 0 1 ≫ forwardOneHom k G i = _
  simp only [forwardZeroInv, biprod.inr_desc_assoc]
  rw [HomologicalComplex.mapBifunctor.d_eq]
  simp only [Preadditive.comp_add, Preadditive.add_comp, Category.assoc,
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
    one_smul, Functor.map_zero, zero_comp, smul_zero, comp_zero, add_zero,
    forwardOneHom, Category.assoc, HomologicalComplex.ι_mapBifunctorDesc, forwardOneMap_supported]
  exact forwardMiddlePair_evaluation k G i

private def forwardCancellationData (i : V) :
    Contraction.ThreeTermCancellationData (forwardInverseProduct k G i) (U i)
      (zigzagGradedBimodule k G) ((U i).shiftObj (-2)) where
  minusIso := forwardMinusIso k G i
  zeroIso := forwardZeroIso k G i
  oneIso := forwardOneIso k G i
  vanish := isZero_forwardInverseProduct_X k G i
  d_snd_snd := forward_d_third k G i
  inl_inr_d := forward_d_middle k G i

/-- The actual graded braid complex followed by its inverse is homotopy equivalent
to the regular graded zigzag bimodule in cochain degree zero. -/
def zigzagBraidComplexTensorInverseHomotopyEquiv (i : V) :
    HomotopyEquiv
      (HomologicalComplex.mapBifunctor (zigzagBraidComplex k G i) (zigzagBraidInverseComplex k G i)
        F (ComplexShape.up ℤ))
      ((HomologicalComplex.single
        (GradedModuleCat.{max u w} (zigzagEnvelopingGrading k G).piece)
        (ComplexShape.up ℤ) 0).obj (zigzagGradedBimodule k G)) :=
  (Contraction.ThreeTermCancellationData.toContraction
    (forwardCancellationData k G i)).homotopyEquiv.symm

end TauCeti
