/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Wishart.Basic

import TauCeti.MeasureTheory.Measure.SymmetricMatrix.Rank
import TauCeti.Probability.Distributions.MatrixNormal.Rank

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
    Matrix (Fin p) (Fin ν) ℝ := Matrix.of fun i r ↦ X r i

@[fun_prop]
private theorem measurable_wishartSampleMatrix :
    Measurable (wishartSampleMatrix :
      (Fin ν → EuclideanSpace ℝ (Fin p)) → Matrix (Fin p) (Fin ν) ℝ) := by
  unfold wishartSampleMatrix
  fun_prop

private theorem basisFun_coordinates_eq_wishartSampleMatrix_transpose
    (X : Fin ν → EuclideanSpace ℝ (Fin p)) :
    (Matrix.of fun r i ↦ (EuclideanSpace.basisFun (Fin ν) ℝ).repr
      (WithLp.toLp 2 fun s ↦ X s i) r) = (wishartSampleMatrix X)ᵀ := by
  ext r i
  simp only [EuclideanSpace.basisFun_repr, wishartSampleMatrix, Matrix.transpose_apply,
    Matrix.of_apply]

private theorem wishartSampleMatrix_toEuclideanLin
    (M : Matrix (Fin p) (Fin p) ℝ) (X : Fin ν → EuclideanSpace ℝ (Fin p)) :
    wishartSampleMatrix (fun r ↦ M.toEuclideanLin (X r)) = M * wishartSampleMatrix X := by
  ext i r
  simp only [wishartSampleMatrix, Matrix.of_apply, Matrix.mul_apply, Matrix.toEuclideanLin,
    Matrix.toLpLin_apply, WithLp.ofLp_toLp, Matrix.mulVec, dotProduct]

private theorem rank_coe_wishartGram_eq_sampleMatrix
    (X : Fin ν → EuclideanSpace ℝ (Fin p)) :
    (wishartGram X : Matrix (Fin p) (Fin p) ℝ).rank = (wishartSampleMatrix X).rank := by
  rw [coe_wishartGram_eq_gram,
    Matrix.gram_eq_conjTranspose_mul (EuclideanSpace.basisFun (Fin ν) ℝ),
    Matrix.rank_conjTranspose_mul_self]
  rw [basisFun_coordinates_eq_wishartSampleMatrix_transpose, Matrix.rank_transpose]

private theorem rank_coe_symmetricCongruence_wishartGram_eq
    (M : Matrix (Fin p) (Fin p) ℝ) (X : Fin ν → EuclideanSpace ℝ (Fin p)) :
    ((Matrix.symmetricCongruenceLinearMap M (wishartGram X) :
        selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
        Matrix (Fin p) (Fin p) ℝ).rank = (M * wishartSampleMatrix X).rank := by
  rw [← wishartGram_toEuclideanLin M X, rank_coe_wishartGram_eq_sampleMatrix]
  exact congrArg Matrix.rank (wishartSampleMatrix_toEuclideanLin M X)

private theorem map_wishartSampleMatrix_pi_one :
    (Measure.pi fun _ : Fin ν ↦
      multivariateGaussian 0 (1 : Matrix (Fin p) (Fin p) ℝ)).map wishartSampleMatrix =
      matrixNormalMeasure (0 : Matrix (Fin p) (Fin ν) ℝ) 1 1 := by
  classical
  -- First express each standard multivariate Gaussian as a product of scalar Gaussians.
  simp_rw [multivariateGaussian_one_eq_map_pi]
  simp_rw [WithLp.ofLp_zero, Pi.zero_apply]
  rw [← Measure.pi_map_pi (fun _ : Fin ν ↦ (by fun_prop :
    AEMeasurable (WithLp.toLp 2) (Measure.pi fun _ : Fin p ↦ gaussianReal 0 1)))]
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  rw [matrixNormalMeasure_of_posSemidef 0 Matrix.PosSemidef.one Matrix.PosSemidef.one,
    Matrix.one_kronecker_one, Matrix.vec_zero, WithLp.toLp_zero, multivariateGaussian_zero_one,
    ← map_pi_eq_stdGaussian, Measure.map_map (MeasurableEquiv.measurable _) (by fun_prop)]
  -- Then regroup the product coordinates from vectors of samples into the sample matrix.
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
    Matrix.of_apply, MeasurableEquiv.coe_piCurry, Sigma.curry,
    matrixVecMeasurableEquiv_symm_apply]
  exact MeasurableEquiv.piCongrLeft_apply_apply
    (β := fun _ : (Σ _ : Fin ν, Fin p) ↦ ℝ) e z (r, i)

/-- **A Gaussian-Gram Wishart matrix almost surely has the largest rank allowed by its degree and
scale.** For a positive-semidefinite scale `S`, its rank is `min ν S.rank` almost everywhere. -/
theorem ae_rank_eq_wishartGramMeasure (ν : ℕ) {S : Matrix (Fin p) (Fin p) ℝ}
    (hS : S.PosSemidef) :
    ∀ᵐ A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ∂wishartGramMeasure ν S,
      (A : Matrix (Fin p) (Fin p) ℝ).rank = min ν S.rank := by
  classical
  have hcov : CFC.sqrt S * (CFC.sqrt S)ᵀ = S := hS.sqrt_mul_transpose_sqrt
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
  refine (ae_map_iff (by fun_prop) (measurableSet_setOfPred_rank_eq _)).2 ?_
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
    (measurableSet_setOfPred_rank_eq _))).1
    (ae_rank_eq_wishartGramMeasure ν hS)

end TauCeti.Probability
