/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Zigzag.Braid.TensorEvaluation
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone

/-!
# A common three-term complex for zigzag braid products

The pair of vertex tensor products maps to the two vertex bimodules by a signed
evaluation matrix, followed by the sum of the vertex evaluations to the regular
bimodule. The two composites of factor evaluations agree, so this is a complex.
For adjacent vertices `i` and `j`, the intended contraction target for
`B_i B_j B_i` and `B_j B_i B_j` is this common evaluation complex.
The swap isomorphism exchanges the two vertex orders in that common target.

It is constructed as Mathlib's mapping cone of a map from a two-term complex to
the regular bimodule in degree zero. The negated differential in that two-term
complex cancels the mapping-cone sign.
-/

public section
noncomputable section
namespace TauCeti
open CategoryTheory CategoryTheory.Limits MulOpposite
open scoped TensorProduct
universe u w
variable (k : Type w) [CommRing k] {V : Type u} (G : SimpleGraph V) [Finite V]
attribute [local instance] zigzagAlgebraIntegerGradedAlgebra
local notation "Γ" => zigzagAlgebraInternalGrading k G
local notation "Z" => zigzagGradedBimodule k G
local notation "U" => zigzagGradedBraidBimodule k G
local notation "T" => GradedModuleCat.bimoduleTensorObj Γ Γ Γ
local notation "E" => zigzagBraidEvaluationHom k G
local notation "c" => ComplexShape.up ℤ

/-- The signed evaluation matrix from the two ordered vertex tensor products. -/
def zigzagBraidNormalFirstDifferential (i j : V) :
    T (U i) (U j) ⊞ T (U j) (U i) ⟶ U i ⊞ U j :=
  Biprod.ofComponents (-zigzagBraidTensorEvaluationRight k G i j)
    (zigzagBraidTensorEvaluationLeft k G i j) (zigzagBraidTensorEvaluationLeft k G j i)
    (-zigzagBraidTensorEvaluationRight k G j i)

/-- The first-column first-row component of the signed evaluation matrix. -/
@[simp, reassoc]
theorem zigzagBraidNormalFirstDifferential_inl_fst (i j : V) :
    biprod.inl ≫ zigzagBraidNormalFirstDifferential k G i j ≫ biprod.fst =
      -zigzagBraidTensorEvaluationRight k G i j := by
  simp [zigzagBraidNormalFirstDifferential]

/-- The first-column second-row component of the signed evaluation matrix. -/
@[simp, reassoc]
theorem zigzagBraidNormalFirstDifferential_inl_snd (i j : V) :
    biprod.inl ≫ zigzagBraidNormalFirstDifferential k G i j ≫ biprod.snd =
      zigzagBraidTensorEvaluationLeft k G i j := by
  simp [zigzagBraidNormalFirstDifferential]

/-- The second-column first-row component of the signed evaluation matrix. -/
@[simp, reassoc]
theorem zigzagBraidNormalFirstDifferential_inr_fst (i j : V) :
    biprod.inr ≫ zigzagBraidNormalFirstDifferential k G i j ≫ biprod.fst =
      zigzagBraidTensorEvaluationLeft k G j i := by
  simp [zigzagBraidNormalFirstDifferential]

/-- The second-column second-row component of the signed evaluation matrix. -/
@[simp, reassoc]
theorem zigzagBraidNormalFirstDifferential_inr_snd (i j : V) :
    biprod.inr ≫ zigzagBraidNormalFirstDifferential k G i j ≫ biprod.snd =
      -zigzagBraidTensorEvaluationRight k G j i := by
  simp [zigzagBraidNormalFirstDifferential]

/-- The signed matrix is annihilated by the sum of the vertex evaluations. -/
@[reassoc]
theorem zigzagBraidNormalFirstDifferential_comp_evaluations (i j : V) :
    zigzagBraidNormalFirstDifferential k G i j ≫ biprod.desc (E i) (E j) = 0 := by
  apply biprod.hom_ext'
  · simp [zigzagBraidNormalFirstDifferential, ← Category.assoc]
    simp [Category.assoc, zigzagBraidTensorEvaluation_comm]
  · simp [zigzagBraidNormalFirstDifferential, ← Category.assoc]
    simp [Category.assoc, zigzagBraidTensorEvaluation_comm]

private abbrev normalDouble (i j : V) :
    CochainComplex (GradedModuleCat.{max u w} (zigzagEnvelopingGrading k G).piece) ℤ :=
  HomologicalComplex.double (-zigzagBraidNormalFirstDifferential k G i j)
    (i₀ := -1) (i₁ := 0) (by simp)

private def normalEvaluation (i j : V) :
    normalDouble k G i j ⟶
      (HomologicalComplex.single
        (GradedModuleCat.{max u w} (zigzagEnvelopingGrading k G).piece) c 0).obj Z :=
  HomologicalComplex.mkHomToSingle
    ((HomologicalComplex.doubleXIso₁ _ _ (by decide)).hom ≫ biprod.desc (E i) (E j)) (by
      intro p hp
      have hp' : p + 1 = 0 := hp
      have : p = -1 := by omega
      subst p
      -- Identify the source constructor before applying its differential formula.
      dsimp only [normalDouble]
      rw [HomologicalComplex.double_d _ _ (by decide)]
      simp only [Category.assoc, Iso.inv_hom_id_assoc, Preadditive.neg_comp,
        zigzagBraidNormalFirstDifferential_comp_evaluations, neg_zero, comp_zero])

/-- The common three-term graded complex of ordered pair and vertex evaluations. -/
def zigzagBraidNormalComplex (i j : V) :
    CochainComplex (GradedModuleCat.{max u w} (zigzagEnvelopingGrading k G).piece) ℤ :=
  CochainComplex.mappingCone (normalEvaluation k G i j)

/-- The degree-minus-two term is the sum of the two ordered vertex tensor products. -/
def zigzagBraidNormalComplexXMinusTwoIso (i j : V) :
    (zigzagBraidNormalComplex k G i j).X (-2) ≅
      T (U i) (U j) ⊞ T (U j) (U i) :=
  HomologicalComplex.homotopyCofiber.XIsoBiprod (normalEvaluation k G i j) (-2) (-1)
      (by simp) ≪≫
    (isoBiprodZero (HomologicalComplex.isZero_single_obj_X c 0 Z (-2) (by decide))).symm ≪≫
      HomologicalComplex.doubleXIso₀ _ _

/-- The degree-minus-one term is the sum of the two vertex bimodules. -/
def zigzagBraidNormalComplexXMinusOneIso (i j : V) :
    (zigzagBraidNormalComplex k G i j).X (-1) ≅ U i ⊞ U j :=
  HomologicalComplex.homotopyCofiber.XIsoBiprod (normalEvaluation k G i j) (-1) 0
      (by simp) ≪≫
    (isoBiprodZero (HomologicalComplex.isZero_single_obj_X c 0 Z (-1) (by decide))).symm ≪≫
      HomologicalComplex.doubleXIso₁ _ _ (by decide)

/-- The degree-zero term is the actual regular graded bimodule. -/
def zigzagBraidNormalComplexXZeroIso (i j : V) :
    (zigzagBraidNormalComplex k G i j).X 0 ≅ Z :=
  HomologicalComplex.homotopyCofiber.XIsoBiprod (normalEvaluation k G i j) 0 1 (by simp) ≪≫
    (isoZeroBiprod (HomologicalComplex.isZero_double_X _ _ 1 (by decide) (by decide))).symm ≪≫
      HomologicalComplex.singleObjXSelf c 0 Z

/-- The common evaluation complex is supported in cohomological degrees `-2`, `-1`, and `0`. -/
theorem isZero_zigzagBraidNormalComplex_X (i j : V) {n : ℤ}
    (h₂ : n ≠ -2) (h₁ : n ≠ -1) (h₀ : n ≠ 0) :
    IsZero ((zigzagBraidNormalComplex k G i j).X n) := by
  apply (CochainComplex.mappingCone.isZero_X_iff (normalEvaluation k G i j) n).2
  exact ⟨HomologicalComplex.isZero_double_X _ _ (n + 1) (by omega) (by omega),
    HomologicalComplex.isZero_single_obj_X c 0 Z n h₀⟩

private theorem normalXMinusTwoIso_inv (i j : V) :
    (zigzagBraidNormalComplexXMinusTwoIso k G i j).inv =
      (HomologicalComplex.doubleXIso₀ _ _).inv ≫
        HomologicalComplex.homotopyCofiber.inlX (normalEvaluation k G i j) (-1) (-2)
          (by simp) := by
  -- Compute the inverse of the cone term iso as its left inclusion.
  change (HomologicalComplex.doubleXIso₀ _ _).inv ≫
    (biprod.inl ≫ (HomologicalComplex.homotopyCofiber.XIsoBiprod
      (normalEvaluation k G i j) (-2) (-1) (by simp)).inv) = _
  rw [HomologicalComplex.homotopyCofiber.inl_XIsoBiprod_inv]

private theorem normalXMinusOneIso_inv (i j : V) :
    (zigzagBraidNormalComplexXMinusOneIso k G i j).inv =
      (HomologicalComplex.doubleXIso₁ _ _ (by decide)).inv ≫
        HomologicalComplex.homotopyCofiber.inlX (normalEvaluation k G i j) 0 (-1)
          (by simp) := by
  -- Compute the inverse of the cone term iso as its left inclusion.
  change (HomologicalComplex.doubleXIso₁ _ _ (by decide)).inv ≫
    (biprod.inl ≫ (HomologicalComplex.homotopyCofiber.XIsoBiprod
      (normalEvaluation k G i j) (-1) 0 (by simp)).inv) = _
  rw [HomologicalComplex.homotopyCofiber.inl_XIsoBiprod_inv]

private theorem normalInlXMinusOneIso_hom (i j : V) :
    HomologicalComplex.homotopyCofiber.inlX (normalEvaluation k G i j) 0 (-1) (by simp) ≫
        (zigzagBraidNormalComplexXMinusOneIso k G i j).hom =
      (HomologicalComplex.doubleXIso₁ _ _ (by decide)).hom := by
  -- Compute the cone term iso as its projection followed by the double term iso.
  change HomologicalComplex.homotopyCofiber.inlX (normalEvaluation k G i j) 0 (-1)
    (by simp) ≫ ((HomologicalComplex.homotopyCofiber.XIsoBiprod
      (normalEvaluation k G i j) (-1) 0 (by simp)).hom ≫ biprod.fst ≫
      (HomologicalComplex.doubleXIso₁ _ _ (by decide)).hom) = _
  simp only [HomologicalComplex.homotopyCofiber.inlX_XIsoBiprod_hom_assoc,
    biprod.inl_fst_assoc]

private theorem normalInrXZeroIso_hom (i j : V) :
    HomologicalComplex.homotopyCofiber.inrX (normalEvaluation k G i j) 0 ≫
        (zigzagBraidNormalComplexXZeroIso k G i j).hom =
      (HomologicalComplex.singleObjXSelf c 0 Z).hom := by
  -- Compute the cone term iso as its projection followed by the single term iso.
  change HomologicalComplex.homotopyCofiber.inrX (normalEvaluation k G i j) 0 ≫
    ((HomologicalComplex.homotopyCofiber.XIsoBiprod (normalEvaluation k G i j) 0 1
      (by simp)).hom ≫ biprod.snd ≫ (HomologicalComplex.singleObjXSelf c 0 Z).hom) = _
  simp only [HomologicalComplex.homotopyCofiber.inrX_XIsoBiprod_hom_assoc,
    biprod.inr_snd_assoc]

/-- The first differential is the signed pair-evaluation matrix. -/
@[simp, reassoc]
theorem zigzagBraidNormalComplex_d_minusTwo (i j : V) :
    (zigzagBraidNormalComplex k G i j).d (-2) (-1) ≫
        (zigzagBraidNormalComplexXMinusOneIso k G i j).hom =
      (zigzagBraidNormalComplexXMinusTwoIso k G i j).hom ≫
        zigzagBraidNormalFirstDifferential k G i j := by
  rw [← cancel_epi (zigzagBraidNormalComplexXMinusTwoIso k G i j).inv]
  simp only [Iso.inv_hom_id_assoc]
  rw [normalXMinusTwoIso_inv]
  -- Transport from the named complex to the cone before reassociating.
  dsimp only [zigzagBraidNormalComplex, CochainComplex.mappingCone]
  rw [Category.assoc]
  rw [HomologicalComplex.homotopyCofiber_d,
    HomologicalComplex.homotopyCofiber.inlX_d_assoc _ (-2) (-1) 0 (by simp) (by simp)]
  have hz : (normalEvaluation k G i j).f (-1) = 0 :=
    (HomologicalComplex.isZero_single_obj_X c 0 Z (-1) (by decide)).eq_of_tgt _ _
  simp only [hz, zero_comp, add_zero]
  dsimp only [normalDouble]
  rw [HomologicalComplex.double_d _ _ (by decide)]
  simp only [Category.assoc, Preadditive.neg_comp, Preadditive.comp_neg, neg_neg,
    Iso.inv_hom_id_assoc]
  exact congrArg (fun f ↦ zigzagBraidNormalFirstDifferential k G i j ≫
    (HomologicalComplex.doubleXIso₁ _ _ (by decide)).inv ≫ f)
      (normalInlXMinusOneIso_hom k G i j) |>.trans (by simp)

/-- The last differential is the sum of the two vertex evaluations. -/
@[simp, reassoc]
theorem zigzagBraidNormalComplex_d_minusOne (i j : V) :
    (zigzagBraidNormalComplex k G i j).d (-1) 0 ≫
        (zigzagBraidNormalComplexXZeroIso k G i j).hom =
      (zigzagBraidNormalComplexXMinusOneIso k G i j).hom ≫ biprod.desc (E i) (E j) := by
  rw [← cancel_epi (zigzagBraidNormalComplexXMinusOneIso k G i j).inv]
  simp only [Iso.inv_hom_id_assoc]
  rw [normalXMinusOneIso_inv]
  -- Transport from the named complex to the cone before reassociating.
  dsimp only [zigzagBraidNormalComplex, CochainComplex.mappingCone]
  rw [Category.assoc]
  rw [HomologicalComplex.homotopyCofiber_d,
    HomologicalComplex.homotopyCofiber.inlX_d_assoc _ (-1) 0 1 (by simp) (by simp)]
  have hz : (normalDouble k G i j).d 0 1 = 0 :=
    HomologicalComplex.double_d_eq_zero₀ _ _ 0 1 (by decide)
  simp only [hz, neg_zero, zero_comp, zero_add]
  -- Associate the concrete cone inclusions before transporting the named term iso.
  refine (congrArg
    (fun f ↦ (HomologicalComplex.doubleXIso₁ _ _ (by decide)).inv ≫ f)
    (Category.assoc ((normalEvaluation k G i j).f 0)
      (HomologicalComplex.homotopyCofiber.inrX (normalEvaluation k G i j) 0)
      (zigzagBraidNormalComplexXZeroIso k G i j).hom)).trans ?_
  refine (congrArg
    (fun f ↦ (HomologicalComplex.doubleXIso₁ _ _ (by decide)).inv ≫
      (normalEvaluation k G i j).f 0 ≫ f) (normalInrXZeroIso_hom k G i j)).trans ?_
  dsimp only [normalEvaluation]
  rw [HomologicalComplex.mkHomToSingle_f]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

/-- A differential with source outside the two nonzero differential degrees vanishes. -/
@[simp]
theorem zigzagBraidNormalComplex_d_eq_zero₀ (i j : V) {a : ℤ} (b : ℤ)
    (ha₂ : a ≠ -2) (ha₁ : a ≠ -1) :
    (zigzagBraidNormalComplex k G i j).d a b = 0 := by
  by_cases ha₀ : a = 0
  · subst a
    by_cases hb : b = 1
    · subst b
      exact (isZero_zigzagBraidNormalComplex_X k G i j
        (by decide) (by decide) (by decide)).eq_of_tgt _ _
    · apply HomologicalComplex.shape
      rw [ComplexShape.up_Rel]
      omega
  · exact (isZero_zigzagBraidNormalComplex_X k G i j ha₂ ha₁ ha₀).eq_of_src _ _

/-- A differential with target outside the two nonzero differential degrees vanishes. -/
@[simp]
theorem zigzagBraidNormalComplex_d_eq_zero₁ (i j : V) (a : ℤ) {b : ℤ}
    (hb₁ : b ≠ -1) (hb₀ : b ≠ 0) :
    (zigzagBraidNormalComplex k G i j).d a b = 0 := by
  by_cases hb₂ : b = -2
  · subst b
    by_cases ha : a = -3
    · subst a
      exact (isZero_zigzagBraidNormalComplex_X k G i j
        (by decide) (by decide) (by decide)).eq_of_src _ _
    · apply HomologicalComplex.shape
      rw [ComplexShape.up_Rel]
      omega
  · exact (isZero_zigzagBraidNormalComplex_X k G i j hb₂ hb₁ hb₀).eq_of_tgt _ _

/-- Swapping both pairs of summands preserves the signed evaluation matrix. -/
@[reassoc]
theorem zigzagBraidNormalFirstDifferential_swap (i j : V) :
    (biprod.braiding (T (U i) (U j))
      (T (U j) (U i))).hom ≫ zigzagBraidNormalFirstDifferential k G j i =
    zigzagBraidNormalFirstDifferential k G i j ≫ (biprod.braiding (U i) (U j)).hom := by
  apply biprod.hom_ext' <;> apply biprod.hom_ext <;>
    simp [zigzagBraidNormalFirstDifferential, biprod.braiding_hom]

private theorem normalSwap_evaluations (i j : V) :
    (biprod.braiding (U i) (U j)).hom ≫ biprod.desc (E j) (E i) =
      biprod.desc (E i) (E j) := by
  apply biprod.hom_ext' <;> simp [biprod.braiding_hom]

private theorem normal_d_minusTwo (i j : V) :
    (zigzagBraidNormalComplex k G i j).d (-2) (-1) =
      (zigzagBraidNormalComplexXMinusTwoIso k G i j).hom ≫
        zigzagBraidNormalFirstDifferential k G i j ≫
          (zigzagBraidNormalComplexXMinusOneIso k G i j).inv :=
  (Iso.eq_comp_inv _).2 (zigzagBraidNormalComplex_d_minusTwo k G i j)

private theorem normal_d_minusOne (i j : V) :
    (zigzagBraidNormalComplex k G i j).d (-1) 0 =
      (zigzagBraidNormalComplexXMinusOneIso k G i j).hom ≫ biprod.desc (E i) (E j) ≫
        (zigzagBraidNormalComplexXZeroIso k G i j).inv :=
  (Iso.eq_comp_inv _).2 (zigzagBraidNormalComplex_d_minusOne k G i j)

private def normalSwapComponentIso (i j : V) (p : ℤ) :
    (zigzagBraidNormalComplex k G i j).X p ≅ (zigzagBraidNormalComplex k G j i).X p := by
  by_cases h₂ : p = -2
  · subst p
    exact zigzagBraidNormalComplexXMinusTwoIso k G i j ≪≫
      biprod.braiding (T (U i) (U j)) (T (U j) (U i)) ≪≫
        (zigzagBraidNormalComplexXMinusTwoIso k G j i).symm
  · by_cases h₁ : p = -1
    · subst p
      exact zigzagBraidNormalComplexXMinusOneIso k G i j ≪≫ biprod.braiding (U i) (U j) ≪≫
        (zigzagBraidNormalComplexXMinusOneIso k G j i).symm
    · by_cases h₀ : p = 0
      · subst p
        exact zigzagBraidNormalComplexXZeroIso k G i j ≪≫
          (zigzagBraidNormalComplexXZeroIso k G j i).symm
      · exact (isZero_zigzagBraidNormalComplex_X k G i j h₂ h₁ h₀).iso
          (isZero_zigzagBraidNormalComplex_X k G j i h₂ h₁ h₀)

/-- Exchange the ordered pair and vertex summands of the common evaluation complex. -/
def zigzagBraidNormalSwapIso (i j : V) :
    zigzagBraidNormalComplex k G i j ≅ zigzagBraidNormalComplex k G j i :=
  HomologicalComplex.Hom.isoOfComponents (normalSwapComponentIso k G i j) (by
    intro p q hpq
    rw [ComplexShape.up_Rel] at hpq
    by_cases h₂ : p = -2
    · subst p
      have : q = -1 := by omega
      subst q
      -- Compute the two selected cone-term components before using their differential API.
      change ((zigzagBraidNormalComplexXMinusTwoIso k G i j).hom ≫
          (biprod.braiding (T (U i) (U j))
            (T (U j) (U i))).hom ≫
          (zigzagBraidNormalComplexXMinusTwoIso k G j i).inv) ≫
          (zigzagBraidNormalComplex k G j i).d (-2) (-1) =
        (zigzagBraidNormalComplex k G i j).d (-2) (-1) ≫
          (zigzagBraidNormalComplexXMinusOneIso k G i j).hom ≫
          (biprod.braiding (U i) (U j)).hom ≫
          (zigzagBraidNormalComplexXMinusOneIso k G j i).inv
      rw [normal_d_minusTwo, normal_d_minusTwo]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      exact congrArg (fun f ↦ (zigzagBraidNormalComplexXMinusTwoIso k G i j).hom ≫ f ≫
        (zigzagBraidNormalComplexXMinusOneIso k G j i).inv)
          (zigzagBraidNormalFirstDifferential_swap k G i j)
    · by_cases h₁ : p = -1
      · subst p
        have : q = 0 := by omega
        subst q
        -- Compute the vertex and regular-term components of the swap.
        change ((zigzagBraidNormalComplexXMinusOneIso k G i j).hom ≫
            (biprod.braiding (U i) (U j)).hom ≫
            (zigzagBraidNormalComplexXMinusOneIso k G j i).inv) ≫
            (zigzagBraidNormalComplex k G j i).d (-1) 0 =
          (zigzagBraidNormalComplex k G i j).d (-1) 0 ≫
            (zigzagBraidNormalComplexXZeroIso k G i j).hom ≫
            (zigzagBraidNormalComplexXZeroIso k G j i).inv
        rw [normal_d_minusOne, normal_d_minusOne]
        simp only [Category.assoc, Iso.inv_hom_id_assoc]
        exact congrArg (fun f ↦ (zigzagBraidNormalComplexXMinusOneIso k G i j).hom ≫ f ≫
          (zigzagBraidNormalComplexXZeroIso k G j i).inv) (normalSwap_evaluations k G i j)
      · by_cases h₀ : p = 0
        · exact (isZero_zigzagBraidNormalComplex_X k G j i
            (by omega) (by omega) (by omega)).eq_of_tgt _ _
        · exact (isZero_zigzagBraidNormalComplex_X k G i j h₂ h₁ h₀).eq_of_src _ _)

/-- In degree minus two the swap exchanges the two ordered tensor-product summands. -/
@[simp, reassoc]
theorem zigzagBraidNormalSwapIso_hom_f_minusTwo (i j : V) :
    (zigzagBraidNormalSwapIso k G i j).hom.f (-2) ≫
        (zigzagBraidNormalComplexXMinusTwoIso k G j i).hom =
      (zigzagBraidNormalComplexXMinusTwoIso k G i j).hom ≫
        (biprod.braiding (T (U i) (U j))
          (T (U j) (U i))).hom := by
  -- Compute the selected degree-minus-two component of isoOfComponents.
  change ((zigzagBraidNormalComplexXMinusTwoIso k G i j).hom ≫
    (biprod.braiding (T (U i) (U j)) (T (U j) (U i))).hom ≫
    (zigzagBraidNormalComplexXMinusTwoIso k G j i).inv) ≫
      (zigzagBraidNormalComplexXMinusTwoIso k G j i).hom = _
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- In degree minus one the swap exchanges the two vertex summands. -/
@[simp, reassoc]
theorem zigzagBraidNormalSwapIso_hom_f_minusOne (i j : V) :
    (zigzagBraidNormalSwapIso k G i j).hom.f (-1) ≫
        (zigzagBraidNormalComplexXMinusOneIso k G j i).hom =
      (zigzagBraidNormalComplexXMinusOneIso k G i j).hom ≫
        (biprod.braiding (U i) (U j)).hom := by
  -- Compute the selected degree-minus-one component of isoOfComponents.
  change ((zigzagBraidNormalComplexXMinusOneIso k G i j).hom ≫
    (biprod.braiding (U i) (U j)).hom ≫
    (zigzagBraidNormalComplexXMinusOneIso k G j i).inv) ≫
      (zigzagBraidNormalComplexXMinusOneIso k G j i).hom = _
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The swap acts as the identity on the regular bimodule in degree zero. -/
@[simp, reassoc]
theorem zigzagBraidNormalSwapIso_hom_f_zero (i j : V) :
    (zigzagBraidNormalSwapIso k G i j).hom.f 0 ≫
        (zigzagBraidNormalComplexXZeroIso k G j i).hom =
      (zigzagBraidNormalComplexXZeroIso k G i j).hom := by
  -- Compute the selected regular-term component of isoOfComponents.
  change ((zigzagBraidNormalComplexXZeroIso k G i j).hom ≫
    (zigzagBraidNormalComplexXZeroIso k G j i).inv) ≫
      (zigzagBraidNormalComplexXZeroIso k G j i).hom = _
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

end TauCeti
