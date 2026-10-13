/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Zigzag.Braid.Adjacent.Differentials
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Braid.Normal
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Braid.Triple.Differentials
public import TauCeti.Algebra.Homology.Contraction.FourTerm

/-!
# The adjacent braid product contracts to the common evaluation complex

The volume component of the lowest differential and the vertex component of the next
differential are negative identity blocks. Split the self-tensor and reorder the other
terms to cancel these blocks, with the corrected projection and inclusion supplied by
the four-term contraction criterion.

## References

* R. S. Huerfano and M. Khovanov, *A category for the adjoint representation*,
  [arXiv:math/0002060](https://arxiv.org/abs/math/0002060), Sections 3 and 4.6, Proposition 7.
* M. Khovanov and P. Seidel, *Quivers, Floer cohomology, and braid group actions*,
  [arXiv:math/0006056](https://arxiv.org/abs/math/0006056), Theorem 2.5 for the type-A relation.
-/

public section
noncomputable section
namespace TauCeti
open CategoryTheory CategoryTheory.Limits
universe u w
variable (k : Type w) [CommRing k] {V : Type u} (G : SimpleGraph V) [Finite V]
local notation "Γ" => zigzagAlgebraInternalGrading k G
local notation "U" => zigzagGradedBraidBimodule k G
local notation "T" => GradedModuleCat.bimoduleTensorObj Γ Γ Γ
local notation "M" => GradedModuleCat.bimoduleTensorMap Γ Γ Γ
local notation "K" => zigzagBraidComplexTriple k G
local notation "L" => zigzagBraidNormalComplex k G
local notation "E" => zigzagBraidEvaluationHom k G
local notation "R" => zigzagBraidTensorEvaluationRight k G
local notation "S" => zigzagBraidTensorEvaluationLeft k G
attribute [local instance] zigzagAlgebraIntegerGradedAlgebra

private abbrev pairTerms (i j : V) := T (U i) (U j) ⊞ T (U j) (U i)

private def pairSplitIso (i j : V) :
    T (U i) (U j) ⊞ (T (U i) (U i) ⊞ T (U j) (U i)) ≅
      pairTerms k G i j ⊞ ((U i) ⊞ (U i).shiftObj 2) :=
  biprod.mapIso (Iso.refl _) (biprod.braiding _ _) ≪≫
    (biprod.associator _ _ _).symm ≪≫
      biprod.mapIso (Iso.refl _) (zigzagBraidSelfTensorIso k G i)

private def vertexSplitIso (i j : V) : (U i ⊞ U j) ⊞ U i ≅ U i ⊞ (U i ⊞ U j) :=
  biprod.associator _ _ _ ≪≫ biprod.mapIso (Iso.refl _) (biprod.braiding _ _)

private def adjacentMinusThreeIso {i j : V} (h : G.Adj j i) :
    (K i j i).X (-3) ≅ (U i).shiftObj 2 :=
  zigzagBraidComplexTripleXMinusThreeIso k G i j i ≪≫ zigzagBraidAdjacentTripleIso k G h
private def adjacentMinusTwoIso (i j : V) :
    (K i j i).X (-2) ≅ pairTerms k G i j ⊞ (U i ⊞ (U i).shiftObj 2) :=
  zigzagBraidComplexTripleXMinusTwoIso k G i j i ≪≫ pairSplitIso k G i j
private def adjacentMinusOneIso (i j : V) : (K i j i).X (-1) ≅ U i ⊞ (U i ⊞ U j) :=
  zigzagBraidComplexTripleXMinusOneIso k G i j i ≪≫ vertexSplitIso k G i j

private def adjacentFirst {i j : V} (h : G.Adj j i) :
    (U i).shiftObj 2 ⟶ pairTerms k G i j ⊞ (U i ⊞ (U i).shiftObj 2) :=
  (zigzagBraidAdjacentTripleIso k G h).inv ≫ zigzagBraidTripleFirstDifferential k G i j i ≫
    (pairSplitIso k G i j).hom
private def alpha {i j : V} (h : G.Adj j i) : (U i).shiftObj 2 ⟶ pairTerms k G i j :=
  adjacentFirst k G h ≫ biprod.fst

private theorem adjacentFirst_eq {i j : V} (h : G.Adj j i) :
    adjacentFirst k G h = biprod.lift (alpha k G h) (biprod.lift 0 (-𝟙 _)) := by
  apply biprod.hom_ext
  · simp only [alpha, biprod.lift_fst]
  · apply biprod.hom_ext
    · simp [adjacentFirst, pairSplitIso, Category.assoc,
        zigzagBraidTripleFirstDifferential_snd_fst_assoc,
        zigzagBraidAdjacentTripleInsert_evaluateMiddle_assoc]
    · simp [adjacentFirst, pairSplitIso, Category.assoc,
        zigzagBraidTripleFirstDifferential_snd_fst_assoc,
        zigzagBraidAdjacentTripleInsert_evaluateMiddle_assoc]

private def adjacentSecond (i j : V) :
    pairTerms k G i j ⊞ (U i ⊞ (U i).shiftObj 2) ⟶ U i ⊞ (U i ⊞ U j) :=
  (pairSplitIso k G i j).inv ≫ zigzagBraidTripleSecondDifferential k G i j i ≫
    (vertexSplitIso k G i j).hom
private def first (i j : V) : pairTerms k G i j ⟶ U i := biprod.desc (-R i j) 0
private def second (i j : V) : pairTerms k G i j ⟶ U i ⊞ U j :=
  biprod.desc (biprod.lift 0 (S i j)) (biprod.lift (S j i) (-R j i))
private def delta (i j : V) : U i ⟶ U i ⊞ U j := biprod.inl
private def epsilon (i j : V) : U i ⊞ U j ⟶ zigzagGradedBimodule k G :=
  biprod.desc (E i) (E j)

private theorem adjacentSecond_inl (i j : V) :
    biprod.inl ≫ adjacentSecond k G i j = biprod.lift (first k G i j) (second k G i j) := by
  repeat' first | apply biprod.hom_ext | apply biprod.hom_ext'
  all_goals simp [adjacentSecond, pairSplitIso, vertexSplitIso, first, second,
    Category.assoc, biprod.lift_eq, Preadditive.comp_add,
    zigzagBraidTripleSecondDifferential_inl_assoc,
    zigzagBraidTripleSecondDifferential_inr_inr_assoc]
private theorem adjacentSecond_inl_inr (i j : V) :
    (biprod.inl : U i ⟶ U i ⊞ (U i).shiftObj 2) ≫ biprod.inr ≫
        adjacentSecond k G i j = biprod.lift (-𝟙 (U i)) (delta k G i j) := by
  repeat' first | apply biprod.hom_ext | apply biprod.hom_ext'
  all_goals simp [adjacentSecond, pairSplitIso, vertexSplitIso, delta,
    Category.assoc, biprod.lift_eq, Preadditive.comp_add,
    zigzagBraidTripleSecondDifferential_inl_inr_assoc]

private theorem transported_first {i j : V} (h : G.Adj j i) :
    (adjacentMinusThreeIso k G h).inv ≫ (K i j i).d (-3) (-2) ≫
      (adjacentMinusTwoIso k G i j).hom = adjacentFirst k G h := by
  simp only [adjacentMinusThreeIso, adjacentMinusTwoIso, Iso.trans_inv, Iso.trans_hom,
    Category.assoc, zigzagBraidComplexTriple_d_minusThree_assoc,
    Iso.inv_hom_id_assoc, adjacentFirst]
private theorem transported_second (i j : V) :
    (adjacentMinusTwoIso k G i j).inv ≫ (K i j i).d (-2) (-1) ≫
      (adjacentMinusOneIso k G i j).hom = adjacentSecond k G i j := by
  simp only [adjacentMinusTwoIso, adjacentMinusOneIso, Iso.trans_inv, Iso.trans_hom,
    Category.assoc, zigzagBraidComplexTriple_d_minusTwo_assoc,
    Iso.inv_hom_id_assoc, adjacentSecond]

private def qColumn (i j : V) : (U i).shiftObj 2 ⟶ U i ⊞ (U i ⊞ U j) :=
  biprod.inr ≫ biprod.inr ≫ adjacentSecond k G i j

private theorem adjacentSecond_eq (i j : V) :
    adjacentSecond k G i j = biprod.desc (biprod.lift (first k G i j) (second k G i j))
      (biprod.desc (biprod.lift (-𝟙 (U i)) (delta k G i j))
        (biprod.lift (qColumn k G i j ≫ biprod.fst) (qColumn k G i j ≫ biprod.snd))) := by
  apply biprod.hom_ext'
  · simp only [biprod.inl_desc, adjacentSecond_inl]
  · apply biprod.hom_ext'
    · simp only [biprod.inr_desc, biprod.inl_desc, adjacentSecond_inl_inr]
    · apply biprod.hom_ext <;> simp [qColumn, Category.assoc]

private theorem adjacentLast_eq (i j : V) :
    (vertexSplitIso k G i j).inv ≫ biprod.desc (biprod.desc (E i) (E j)) (E i) =
      biprod.desc (E i) (epsilon k G i j) := by
  repeat' first | apply biprod.hom_ext | apply biprod.hom_ext'
  all_goals simp [vertexSplitIso, epsilon, Category.assoc]

private theorem source_d_minusThree {i j : V} (h : G.Adj j i) :
    (K i j i).d (-3) (-2) ≫ (adjacentMinusTwoIso k G i j).hom =
      (adjacentMinusThreeIso k G h).hom ≫
        biprod.lift (alpha k G h) (biprod.lift 0 (-𝟙 _)) := by
  rw [← cancel_epi (adjacentMinusThreeIso k G h).inv]
  simp only [Iso.inv_hom_id_assoc, transported_first, adjacentFirst_eq]
private theorem source_d_minusTwo (i j : V) :
    (K i j i).d (-2) (-1) ≫ (adjacentMinusOneIso k G i j).hom =
      (adjacentMinusTwoIso k G i j).hom ≫
        biprod.desc (biprod.lift (first k G i j) (second k G i j))
          (biprod.desc (biprod.lift (-𝟙 (U i)) (delta k G i j))
            (biprod.lift (qColumn k G i j ≫ biprod.fst) (qColumn k G i j ≫ biprod.snd))) := by
  rw [← cancel_epi (adjacentMinusTwoIso k G i j).inv]
  simp only [Iso.inv_hom_id_assoc, transported_second, adjacentSecond_eq]
private theorem source_d_minusOne (i j : V) :
    (K i j i).d (-1) 0 ≫ (zigzagBraidComplexTripleXZeroIso k G i j i).hom =
      (adjacentMinusOneIso k G i j).hom ≫
        biprod.desc (E i) (epsilon k G i j) := by
  rw [← cancel_epi (adjacentMinusOneIso k G i j).inv]
  simp only [Iso.inv_hom_id_assoc]
  simpa only [adjacentMinusOneIso, Iso.trans_inv, Category.assoc,
    zigzagBraidComplexTriple_d_minusOne, Iso.inv_hom_id_assoc] using adjacentLast_eq k G i j

private theorem target_first (i j : V) : zigzagBraidNormalFirstDifferential k G i j =
    first k G i j ≫ delta k G i j + second k G i j := by
  repeat' first | apply biprod.hom_ext | apply biprod.hom_ext'
  all_goals simp [first, second, delta, Category.assoc]

private def adjacentCancellationData {i j : V} (h : G.Adj j i) :
    Contraction.FourTermCancellationData (K i j i) (L i j)
      (pairTerms k G i j) (U i) ((U i).shiftObj 2) (U i ⊞ U j) (zigzagGradedBimodule k G) where
  minusThreeIso := adjacentMinusThreeIso k G h
  minusTwoIso := adjacentMinusTwoIso k G i j
  minusOneIso := adjacentMinusOneIso k G i j
  zeroIso := zigzagBraidComplexTripleXZeroIso k G i j i
  targetMinusTwoIso := zigzagBraidNormalComplexXMinusTwoIso k G i j
  targetMinusOneIso := zigzagBraidNormalComplexXMinusOneIso k G i j
  targetZeroIso := zigzagBraidNormalComplexXZeroIso k G i j
  vanish n h₃ h₂ h₁ h₀ := isZero_zigzagBraidComplexTriple_X k G i j i n (by omega)
  targetVanish n h₂ h₁ h₀ := isZero_zigzagBraidNormalComplex_X k G i j h₂ h₁ h₀
  alpha := alpha k G h
  beta := 0
  first := first k G i j
  second := second k G i j
  qFirst := qColumn k G i j ≫ biprod.fst
  qSecond := qColumn k G i j ≫ biprod.snd
  delta := delta k G i j
  zFirst := E i
  epsilon := epsilon k G i j
  d_minusThree := source_d_minusThree k G h
  d_minusTwo := source_d_minusTwo k G i j
  d_minusOne := source_d_minusOne k G i j
  target_d_minusTwo := by
    simpa only [target_first] using zigzagBraidNormalComplex_d_minusTwo k G i j
  target_d_minusOne := by
    simpa only [epsilon] using zigzagBraidNormalComplex_d_minusOne k G i j

/-- Cancel the volume and repeated vertex blocks in the actual adjacent triple product. -/
def zigzagBraidAdjacentContraction {i j : V} (h : G.Adj j i) :
    Contraction (zigzagBraidComplexTriple k G i j i) (zigzagBraidNormalComplex k G i j) :=
  (adjacentCancellationData k G h).toContraction

/-- The actual graded braid complexes satisfy the adjacent three-generator braid relation. -/
def zigzagBraidComplexAdjacentHomotopyEquiv {i j : V} (h : G.Adj j i) :
    HomotopyEquiv (zigzagBraidComplexTriple k G i j i) (zigzagBraidComplexTriple k G j i j) :=
  (zigzagBraidAdjacentContraction k G h).homotopyEquiv.symm.trans
    ((HomotopyEquiv.ofIso (zigzagBraidNormalSwapIso k G i j)).trans
      (zigzagBraidAdjacentContraction k G h.symm).homotopyEquiv)

end TauCeti
