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

This tensor order has the same three graded terms as the forward product. Here the
second-factor differential has the negative cochain sign, so the Ui{−2} coordinate
of the middle term is negated. The actual two differential blocks are then identities,
and the three-term cancellation criterion contracts the totalization to the regular
graded bimodule in degree zero. The result includes arbitrary finite graphs and
commutative coefficient rings, including isolated vertices.
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
  -- Cochain totalization assigns the tensor pair the sum of its two indices.
  change p + q = n at hpq
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

private def reverseMinusMap (i : V) (p q : ℤ) :
    ((F).obj ((zigzagBraidInverseComplex k G i).X p)).obj
      ((zigzagBraidComplex k G i).X q) ⟶ U i := by
  by_cases hp : p = (0)
  · subst p
    by_cases hq : q = (-1)
    · subst q
      exact (reverseMinusPairIso k G i).hom
    · exact 0
  · exact 0

private def reverseMinusHom (i : V) : (reverseInverseProduct k G i).X (-1) ⟶ U i :=
  HomologicalComplex.mapBifunctorDesc (fun p q _ ↦ reverseMinusMap k G i p q)

private def reverseMinusInv (i : V) : U i ⟶ (reverseInverseProduct k G i).X (-1) :=
  (reverseMinusPairIso k G i).inv ≫ HomologicalComplex.ιMapBifunctor
    (zigzagBraidInverseComplex k G i) (zigzagBraidComplex k G i) F (ComplexShape.up ℤ)
    (0) (-1) (-1) (by simp)

private theorem reverseMinusMap_supported (i : V) :
    reverseMinusMap k G i (0) (-1) = (reverseMinusPairIso k G i).hom := by
  simp only [reverseMinusMap, dite_true]

private def reverseMinusIso (i : V) : (reverseInverseProduct k G i).X (-1) ≅ U i where
  hom := reverseMinusHom k G i
  inv := reverseMinusInv k G i
  hom_inv_id := by
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    -- The total degree is the sum of the pair of cochain indices.
    change p + q = (-1) at hpq
    by_cases hp : p = (0)
    · subst p
      have hq : q = (-1) := by omega
      subst q
      simp only [reverseMinusHom, reverseMinusInv,
        HomologicalComplex.ι_mapBifunctorDesc_assoc, reverseMinusMap_supported,
        Iso.hom_inv_id_assoc, Category.comp_id]
    · exact (isZero_reverseInversePair_of_not_support k G i p q (by omega)).eq_of_src _ _
  inv_hom_id := by
    simp only [reverseMinusHom, reverseMinusInv, Category.assoc,
      HomologicalComplex.ι_mapBifunctorDesc, reverseMinusMap_supported, Iso.inv_hom_id]

private def reverseOneMap (i : V) (p q : ℤ) :
    ((F).obj ((zigzagBraidInverseComplex k G i).X p)).obj
      ((zigzagBraidComplex k G i).X q) ⟶ (U i).shiftObj (-2) := by
  by_cases hp : p = (1)
  · subst p
    by_cases hq : q = (0)
    · subst q
      exact (reverseOnePairIso k G i).hom
    · exact 0
  · exact 0

private def reverseOneHom (i : V) : (reverseInverseProduct k G i).X (1) ⟶ (U i).shiftObj (-2) :=
  HomologicalComplex.mapBifunctorDesc (fun p q _ ↦ reverseOneMap k G i p q)

private def reverseOneInv (i : V) : (U i).shiftObj (-2) ⟶ (reverseInverseProduct k G i).X (1) :=
  (reverseOnePairIso k G i).inv ≫ HomologicalComplex.ιMapBifunctor
    (zigzagBraidInverseComplex k G i) (zigzagBraidComplex k G i) F (ComplexShape.up ℤ)
    (1) (0) (1) (by simp)

private theorem reverseOneMap_supported (i : V) :
    reverseOneMap k G i (1) (0) = (reverseOnePairIso k G i).hom := by
  simp only [reverseOneMap, dite_true]

private def reverseOneIso (i : V) : (reverseInverseProduct k G i).X (1) ≅ (U i).shiftObj (-2) where
  hom := reverseOneHom k G i
  inv := reverseOneInv k G i
  hom_inv_id := by
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    -- The total degree is the sum of the pair of cochain indices.
    change p + q = (1) at hpq
    by_cases hp : p = (1)
    · subst p
      have hq : q = (0) := by omega
      subst q
      simp only [reverseOneHom, reverseOneInv,
        HomologicalComplex.ι_mapBifunctorDesc_assoc, reverseOneMap_supported,
        Iso.hom_inv_id_assoc, Category.comp_id]
    · exact (isZero_reverseInversePair_of_not_support k G i p q (by omega)).eq_of_src _ _
  inv_hom_id := by
    simp only [reverseOneHom, reverseOneInv, Category.assoc,
      HomologicalComplex.ι_mapBifunctorDesc, reverseOneMap_supported, Iso.inv_hom_id]

private def negativeShiftIso (i : V) : (U i).shiftObj (-2) ≅ (U i).shiftObj (-2) where
  hom := -𝟙 _
  inv := -𝟙 _
  hom_inv_id := by simp
  inv_hom_id := by simp

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
      zigzagBraidSelfTensorShiftLeftIso k G i ≪≫ biprod.mapIso (negativeShiftIso k G i) (Iso.refl _)

private def reverseZeroMap (i : V) (p q : ℤ) :
    ((F).obj ((zigzagBraidInverseComplex k G i).X p)).obj
      ((zigzagBraidComplex k G i).X q) ⟶
        zigzagGradedBimodule k G ⊞ ((U i).shiftObj (-2) ⊞ U i) := by
  by_cases hp : p = 0
  · subst p
    by_cases hq : q = 0
    · subst q
      exact (reverseRegularPairIso k G i).hom ≫ biprod.inl
    · exact 0
  · by_cases hp' : p = 1
    · subst p
      by_cases hq : q = -1
      · subst q
        exact (reverseMiddlePairIso k G i).hom ≫ biprod.inr
      · exact 0
    · exact 0

private def reverseZeroHom (i : V) : (reverseInverseProduct k G i).X 0 ⟶
    zigzagGradedBimodule k G ⊞ ((U i).shiftObj (-2) ⊞ U i) :=
  HomologicalComplex.mapBifunctorDesc (fun p q _ ↦ reverseZeroMap k G i p q)

private theorem reverseZeroMap_regular (i : V) :
    reverseZeroMap k G i 0 0 = (reverseRegularPairIso k G i).hom ≫ biprod.inl := by
  simp only [reverseZeroMap, dite_true]

private theorem reverseZeroMap_middle (i : V) :
    reverseZeroMap k G i 1 (-1) = (reverseMiddlePairIso k G i).hom ≫ biprod.inr := by
  simp only [reverseZeroMap, show (1 : ℤ) ≠ 0 by decide, dite_false, dite_true]

private def reverseZeroInv (i : V) :
    zigzagGradedBimodule k G ⊞ ((U i).shiftObj (-2) ⊞ U i) ⟶
      (reverseInverseProduct k G i).X 0 :=
  biprod.desc
    ((reverseRegularPairIso k G i).inv ≫ HomologicalComplex.ιMapBifunctor
      (zigzagBraidInverseComplex k G i) (zigzagBraidComplex k G i) F (ComplexShape.up ℤ)
      0 0 0 (by simp))
    ((reverseMiddlePairIso k G i).inv ≫ HomologicalComplex.ιMapBifunctor
      (zigzagBraidInverseComplex k G i) (zigzagBraidComplex k G i) F (ComplexShape.up ℤ)
      1 (-1) 0 (by simp))

private def reverseZeroIso (i : V) : (reverseInverseProduct k G i).X 0 ≅
    zigzagGradedBimodule k G ⊞ ((U i).shiftObj (-2) ⊞ U i) where
  hom := reverseZeroHom k G i
  inv := reverseZeroInv k G i
  hom_inv_id := by
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    -- Degree zero has precisely the regular pair and the internally shifted middle pair.
    change p + q = 0 at hpq
    by_cases hp : p = 0
    · subst p
      have hq : q = 0 := by omega
      subst q
      simp only [reverseZeroHom, reverseZeroInv, Category.assoc,
        HomologicalComplex.ι_mapBifunctorDesc_assoc, reverseZeroMap_regular,
        biprod.inl_desc, Iso.hom_inv_id_assoc, Category.comp_id]
    · by_cases hp' : p = 1
      · subst p
        have hq : q = -1 := by omega
        subst q
        simp only [reverseZeroHom, reverseZeroInv, Category.assoc,
          HomologicalComplex.ι_mapBifunctorDesc_assoc, reverseZeroMap_middle,
          biprod.inr_desc, Iso.hom_inv_id_assoc, Category.comp_id]
      · exact (isZero_reverseInversePair_of_not_support k G i p q (by omega)).eq_of_src _ _
  inv_hom_id := by
    apply biprod.hom_ext'
    · simp only [reverseZeroHom, reverseZeroInv, Category.assoc, biprod.inl_desc_assoc,
        HomologicalComplex.ι_mapBifunctorDesc, reverseZeroMap_regular,
        Iso.inv_hom_id_assoc, Category.comp_id]
    · simp only [reverseZeroHom, reverseZeroInv, Category.assoc, biprod.inr_desc_assoc,
        HomologicalComplex.ι_mapBifunctorDesc, reverseZeroMap_middle,
        Iso.inv_hom_id_assoc, Category.comp_id]

private theorem reverseCoevaluationProjection (i : V) :
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
  exact reverseCoevaluationProjection k G i

private theorem reverseEvaluationTransport (i : V) :
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
  rw [reverseEvaluationTransport]
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

private theorem reverse_d_third (i : V) :
    (reverseInverseProduct k G i).d (-1) 0 ≫ (reverseZeroIso k G i).hom ≫
      biprod.snd ≫ biprod.snd = (reverseMinusIso k G i).hom := by
  -- The component isomorphisms use the totalization desc maps just constructed.
  change (reverseInverseProduct k G i).d (-1) 0 ≫ reverseZeroHom k G i ≫
    biprod.snd ≫ biprod.snd = reverseMinusHom k G i
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  -- Only the pair (0,-1) can contribute to total degree -1.
  change p + q = -1 at hpq
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
      one_smul, reverseZeroHom, reverseMinusHom, Category.assoc,
      HomologicalComplex.ι_mapBifunctorDesc, HomologicalComplex.ι_mapBifunctorDesc_assoc,
      reverseZeroMap_regular, reverseZeroMap_middle, reverseMinusMap_supported,
      biprod.inl_snd_assoc, biprod.inr_snd_assoc, comp_zero, zero_comp, add_zero]
    exact reverseMiddlePair_coevaluation k G i
  · exact (isZero_reverseInversePair_of_not_support k G i p q (by omega)).eq_of_src _ _

private theorem reverse_d_middle (i : V) :
    (biprod.inl : (U i).shiftObj (-2) ⟶ (U i).shiftObj (-2) ⊞ U i) ≫
      biprod.inr ≫ (reverseZeroIso k G i).inv ≫
      (reverseInverseProduct k G i).d 0 1 ≫ (reverseOneIso k G i).hom =
        𝟙 ((U i).shiftObj (-2)) := by
  -- The inverse components are defined by binary and totalization desc maps.
  change biprod.inl ≫ biprod.inr ≫ reverseZeroInv k G i ≫
    (reverseInverseProduct k G i).d 0 1 ≫ reverseOneHom k G i = _
  simp only [reverseZeroInv, biprod.inr_desc_assoc]
  rw [HomologicalComplex.mapBifunctor.d_eq]
  simp only [Preadditive.comp_add, Preadditive.add_comp, Category.assoc,
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
    reverseOneHom, Category.assoc, HomologicalComplex.ι_mapBifunctorDesc,
    reverseOneMap_supported]
  rw [reverseMiddlePair_evaluation, neg_neg]

private def reverseCancellationData (i : V) :
    Contraction.ThreeTermCancellationData (reverseInverseProduct k G i) (U i)
      (zigzagGradedBimodule k G) ((U i).shiftObj (-2)) where
  minusIso := reverseMinusIso k G i
  zeroIso := reverseZeroIso k G i
  oneIso := reverseOneIso k G i
  vanish := isZero_reverseInverseProduct_X k G i
  d_snd_snd := reverse_d_third k G i
  inl_inr_d := reverse_d_middle k G i

/-- The actual inverse graded braid complex followed by the braid complex is homotopy
equivalent to the regular graded zigzag bimodule in cochain degree zero. -/
def zigzagBraidInverseTensorComplexHomotopyEquiv (i : V) :
    HomotopyEquiv
      (HomologicalComplex.mapBifunctor (zigzagBraidInverseComplex k G i) (zigzagBraidComplex k G i)
        F (ComplexShape.up ℤ))
      ((HomologicalComplex.single
        (GradedModuleCat.{max u w} (zigzagEnvelopingGrading k G).piece)
        (ComplexShape.up ℤ) 0).obj (zigzagGradedBimodule k G)) :=
  (Contraction.ThreeTermCancellationData.toContraction
    (reverseCancellationData k G i)).homotopyEquiv.symm

end TauCeti
