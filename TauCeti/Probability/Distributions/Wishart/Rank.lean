/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Wishart.Basic

import TauCeti.MeasureTheory.Measure.Matrix
import TauCeti.MeasureTheory.Measure.SymmetricMatrix.Rank
import TauCeti.LinearAlgebra.Matrix.Rank.Closed
import TauCeti.LinearAlgebra.Matrix.PosDef.Rank
import TauCeti.Probability.Distributions.MatrixNormal.PDF

/-!
# Almost-sure rank of Gaussian-Gram Wishart matrices

This file proves that the upper rank bound for the Gaussian-Gram Wishart family is sharp.  For a
positive-semidefinite scale matrix `S`, a Wishart matrix of degree `ν` has rank
`min ν S.rank` almost surely.

The proof writes the Gaussian sample matrix as `sqrt S * Z`.  An exact rank factorization of
`sqrt S` reduces this product to a matrix normal law with positive-definite row covariance.  That
law has a density, hence maximal rank almost surely; the full-column-rank factor preserves rank.

## Main results

* `TauCeti.Probability.wishartGramMeasure_setOf_rank_eq` — the exact-rank stratum has full
  measure.
* `TauCeti.Probability.ae_rank_eq_wishartGramMeasure` — the almost-sure exact-rank statement.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace Matrix MatrixOrder

namespace TauCeti.Probability

variable {p ν : ℕ} {S : Matrix (Fin p) (Fin p) ℝ}

/-- The matrix whose columns are the vectors in a Gaussian-Gram sample. -/
private def wishartSampleMatrix (X : Fin ν → EuclideanSpace ℝ (Fin p)) :
    Matrix (Fin p) (Fin ν) ℝ := fun i r => X r i

@[fun_prop]
private theorem measurable_wishartSampleMatrix :
    Measurable (wishartSampleMatrix :
      (Fin ν → EuclideanSpace ℝ (Fin p)) → Matrix (Fin p) (Fin ν) ℝ) := by
  change Measurable fun X : Fin ν → EuclideanSpace ℝ (Fin p) =>
    fun i : Fin p => fun r : Fin ν => X r i
  fun_prop

private theorem rank_coe_wishartGram_eq_sampleMatrix
    (X : Fin ν → EuclideanSpace ℝ (Fin p)) :
    (wishartGram X : Matrix (Fin p) (Fin p) ℝ).rank = (wishartSampleMatrix X).rank := by
  rw [coe_wishartGram_eq_gram,
    Matrix.gram_eq_conjTranspose_mul (EuclideanSpace.basisFun (Fin ν) ℝ),
    Matrix.rank_conjTranspose_mul_self]
  rw [← Matrix.rank_transpose]
  congr 1

private theorem rank_coe_symmetricCongruence_wishartGram_eq
    (M : Matrix (Fin p) (Fin p) ℝ) (X : Fin ν → EuclideanSpace ℝ (Fin p)) :
    ((Matrix.symmetricCongruenceLinearMap M (wishartGram X) :
        selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
        Matrix (Fin p) (Fin p) ℝ).rank = (M * wishartSampleMatrix X).rank := by
  rw [← wishartGram_toEuclideanLin M X, rank_coe_wishartGram_eq_sampleMatrix]
  congr 1

/-- Left multiplication by a full-column-rank matrix preserves matrix rank. -/
private theorem rank_mul_eq_right_of_full_column_rank {m r n : Type*}
    [Fintype r] [Fintype n] (L : Matrix m r ℝ) (B : Matrix r n ℝ)
    (hL : L.rank = Fintype.card r) : (L * B).rank = B.rank := by
  apply le_antisymm (Matrix.rank_mul_le_right L B)
  have h := Matrix.rank_add_rank_le_rank_mul_add_card L B
  omega

private theorem measurableSet_matrix_rank_eq {m n : Type*} [Finite m] [Fintype n]
    (k : ℕ) : MeasurableSet {A : Matrix m n ℝ | A.rank = k} := by
  classical
  let _ := Fintype.ofFinite m
  cases k with
  | zero =>
      simpa only [Nat.le_zero] using
        (Matrix.isClosed_setOfPred_rank_le (m := m) (n := n) (K := ℝ) 0).measurableSet
  | succ k =>
      have hle :=
        (Matrix.isClosed_setOfPred_rank_le (m := m) (n := n) (K := ℝ) (k + 1)).measurableSet
      have hlt :=
        (Matrix.isClosed_setOfPred_rank_le (m := m) (n := n) (K := ℝ) k).measurableSet
      have h := hle.inter hlt.compl
      convert h using 1
      ext A
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_compl_iff]
      omega

private theorem measurableSet_symmetricMatrix_rank_eq (k : ℕ) :
    MeasurableSet {A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) |
      (A : Matrix (Fin p) (Fin p) ℝ).rank = k} := by
  cases k with
  | zero =>
      simpa only [Nat.le_zero] using (measurableSet_setOfPred_rank_le (p := p) 0)
  | succ k =>
      have h := (measurableSet_setOfPred_rank_le (p := p) (k + 1)).inter
        (measurableSet_setOfPred_rank_le (p := p) k).compl
      convert h using 1
      ext A
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_compl_iff]
      omega

private theorem ae_rank_eq_min_of_absolutelyContinuous_matrix
    {m n : Type*} [Fintype m] [Fintype n] (μ : Measure (Matrix m n ℝ)) (hμ : μ ≪ volume) :
    ∀ᵐ X ∂μ, X.rank = min (Fintype.card m) (Fintype.card n) := by
  classical
  have hflat := Measure.ae_rank_eq_min
    (volume : Measure (m → n → ℝ)) Measure.AbsolutelyContinuous.rfl
  have hmatrix := ((Matrix.volume_preserving_ofMeasurableEquiv m n ℝ).symm
    (Matrix.ofMeasurableEquiv m n ℝ)).quasiMeasurePreserving.ae hflat
  refine hμ.ae_le (hmatrix.mono fun X hX => ?_)
  simpa only [Matrix.ofMeasurableEquiv_symm_apply, Equiv.apply_symm_apply] using hX

private theorem ae_rank_eq_min_matrixNormalMeasure_of_posDef
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    {U : Matrix m m ℝ} {V : Matrix n n ℝ} (hU : U.PosDef) (hV : V.PosDef) :
    ∀ᵐ X ∂matrixNormalMeasure (0 : Matrix m n ℝ) U V,
      X.rank = min (Fintype.card m) (Fintype.card n) := by
  have hac : matrixNormalMeasure (0 : Matrix m n ℝ) U V ≪ volume := by
    rw [matrixNormalMeasure_eq_withDensity 0 hU hV]
    exact withDensity_absolutelyContinuous volume (matrixNormalPDF 0 U V)
  exact ae_rank_eq_min_of_absolutelyContinuous_matrix _ hac

private theorem ae_rank_eq_min_matrixNormalMeasure_right_one
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    {U : Matrix m m ℝ} (hU : U.PosSemidef) :
    ∀ᵐ X ∂matrixNormalMeasure (0 : Matrix m n ℝ) U 1,
      X.rank = min U.rank (Fintype.card n) := by
  classical
  obtain ⟨L, R, hfac⟩ := (CFC.sqrt U).exists_eq_mul_fin_rank
  have hL : L.rank = Fintype.card (Fin (CFC.sqrt U).rank) :=
    Matrix.rank_left_factor_eq (by simp) hfac
  have hR : R.rank = Fintype.card (Fin (CFC.sqrt U).rank) := by
    apply le_antisymm R.rank_le_card_height
    calc
      Fintype.card (Fin (CFC.sqrt U).rank) = (CFC.sqrt U).rank := Fintype.card_fin _
      _ = (L * R).rank := congrArg Matrix.rank hfac
      _ ≤ R.rank := Matrix.rank_mul_le_right L R
  have hRR : (R * Rᵀ).PosDef := by
    simpa only [Matrix.mul_one] using
      ((Matrix.PosDef.one.mul_mul_transpose_same_iff_rank_eq_card R).2 hR)
  have hmax :
      ∀ᵐ X : Matrix (Fin (CFC.sqrt U).rank) n ℝ
        ∂matrixNormalMeasure 0 (R * Rᵀ) 1,
        X.rank = min (Fintype.card (Fin (CFC.sqrt U).rank)) (Fintype.card n) :=
    ae_rank_eq_min_matrixNormalMeasure_of_posDef hRR (Matrix.PosDef.one (n := n))
  have hmap := map_mul_mul_add_matrixNormalMeasure
    (0 : Matrix (Fin (CFC.sqrt U).rank) n ℝ) hRR.posSemidef Matrix.PosSemidef.one
    L (1 : Matrix n n ℝ) 0
  have hcov : L * (R * Rᵀ) * Lᵀ = U := by
    calc
      L * (R * Rᵀ) * Lᵀ = (L * R) * (L * R)ᵀ := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = CFC.sqrt U * (CFC.sqrt U)ᵀ := by rw [← hfac]
      _ = U := by
        rw [← Matrix.conjTranspose_eq_transpose_of_trivial,
          (Matrix.LE.le.posSemidef (CFC.sqrt_nonneg U)).isHermitian.eq]
        exact CFC.sqrt_mul_sqrt_self U hU.nonneg
  simp only [Matrix.mul_zero, add_zero, Matrix.mul_one, Matrix.transpose_one] at hmap
  rw [hcov] at hmap
  rw [← hmap]
  refine (ae_map_iff (by fun_prop) (measurableSet_matrix_rank_eq _)).2 ?_
  filter_upwards [hmax] with X hX
  rw [rank_mul_eq_right_of_full_column_rank L X hL, hX, hU.rank_sqrt]
  simp

private theorem map_wishartSampleMatrix_pi_one :
    (Measure.pi fun _ : Fin ν ↦
      multivariateGaussian 0 (1 : Matrix (Fin p) (Fin p) ℝ)).map wishartSampleMatrix =
      matrixNormalMeasure (0 : Matrix (Fin p) (Fin ν) ℝ) 1 1 := by
  classical
  simp_rw [multivariateGaussian_one_eq_map_pi]
  simp_rw [WithLp.ofLp_zero, Pi.zero_apply]
  rw [← Measure.pi_map_pi (fun _ : Fin ν ↦ (by fun_prop :
    AEMeasurable (WithLp.toLp 2) (Measure.pi fun _ : Fin p ↦ gaussianReal 0 1)))]
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  rw [matrixNormalMeasure_of_posSemidef 0 Matrix.PosSemidef.one Matrix.PosSemidef.one,
    Matrix.one_kronecker_one, Matrix.vec_zero, WithLp.toLp_zero, multivariateGaussian_zero_one,
    ← map_pi_eq_stdGaussian, Measure.map_map (MeasurableEquiv.measurable _) (by fun_prop)]
  have hc := TauCeti.measurePreserving_piCurry
    (fun _ : Fin ν ↦ fun _ : Fin p ↦ (gaussianReal 0 1 : Measure ℝ))
  let e : Fin ν × Fin p ≃ (Σ _ : Fin ν, Fin p) :=
    (Equiv.sigmaEquivProd (Fin ν) (Fin p)).symm
  have hp := measurePreserving_piCongrLeft
    (fun _ : (Σ _ : Fin ν, Fin p) ↦ (gaussianReal 0 1 : Measure ℝ)) e
  have hflat := hc.comp hp
  rw [← hflat.map_eq, Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext z
  ext i r
  simp only [Function.comp_apply, wishartSampleMatrix,
    MeasurableEquiv.coe_piCurry, Sigma.curry, MeasurableEquiv.coe_piCongrLeft,
    matrixVecMeasurableEquiv_symm_apply]
  change (Equiv.piCongrLeft (fun _ : (Σ _ : Fin ν, Fin p) ↦ ℝ) e z) (e (r, i)) = z (r, i)
  exact Equiv.piCongrLeft_apply_apply (P := fun _ : (Σ _ : Fin ν, Fin p) ↦ ℝ)
    (e := e) z (r, i)

/-- **A Gaussian-Gram Wishart matrix has the largest rank allowed by its degree and scale.** -/
theorem ae_rank_eq_wishartGramMeasure (ν : ℕ) {S : Matrix (Fin p) (Fin p) ℝ}
    (hS : S.PosSemidef) :
    ∀ᵐ A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ∂wishartGramMeasure ν S,
      (A : Matrix (Fin p) (Fin p) ℝ).rank = min ν S.rank := by
  classical
  have hcov : CFC.sqrt S * (CFC.sqrt S)ᵀ = S := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial,
      (Matrix.LE.le.posSemidef (CFC.sqrt_nonneg S)).isHermitian.eq]
    exact CFC.sqrt_mul_sqrt_self S hS.nonneg
  have hmap := map_mul_mul_add_matrixNormalMeasure
    (0 : Matrix (Fin p) (Fin ν) ℝ) Matrix.PosSemidef.one Matrix.PosSemidef.one
    (CFC.sqrt S) (1 : Matrix (Fin ν) (Fin ν) ℝ) 0
  simp only [Matrix.mul_zero, add_zero, Matrix.mul_one, Matrix.transpose_one] at hmap
  rw [hcov] at hmap
  have hmatrix := ae_rank_eq_min_matrixNormalMeasure_right_one
    (n := Fin ν) hS
  rw [← hmap] at hmatrix
  have hstandard := ae_of_ae_map (by fun_prop) hmatrix
  rw [← map_wishartSampleMatrix_pi_one] at hstandard
  have hsamples := ae_of_ae_map measurable_wishartSampleMatrix.aemeasurable hstandard
  rw [wishartGramMeasure_eq_map_sqrt ν hS, wishartGramMeasure_eq_map_pi,
    Measure.map_map (LinearMap.continuous_of_finiteDimensional _).measurable
      measurable_wishartGram]
  refine (ae_map_iff (by fun_prop) (measurableSet_symmetricMatrix_rank_eq _)).2 ?_
  filter_upwards [hsamples] with X hX
  simp only [Function.comp_apply]
  rw [rank_coe_symmetricCongruence_wishartGram_eq, hX, Fintype.card_fin, min_comm]

/-- **The Gaussian-Gram Wishart law is carried by its exact-rank stratum.** For a
positive-semidefinite scale `S`, the almost-sure rank is `min ν S.rank`; this includes singular
scales and the degree-zero law. -/
theorem wishartGramMeasure_setOf_rank_eq (ν : ℕ) {S : Matrix (Fin p) (Fin p) ℝ}
    (hS : S.PosSemidef) :
    wishartGramMeasure ν S
      {A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) |
        (A : Matrix (Fin p) (Fin p) ℝ).rank = min ν S.rank} = 1 := by
  exact (ae_iff_prob_eq_one (measurableSet_setOfPred.mp
    (measurableSet_symmetricMatrix_rank_eq _))).1
    (ae_rank_eq_wishartGramMeasure ν hS)

end TauCeti.Probability
