/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Gaussian.Affine
public import Mathlib.Probability.Kernel.CondDistrib

import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence

/-!
# Conditional multivariate Gaussian distributions

This file constructs the Gaussian kernel obtained by conditioning one block of a jointly
Gaussian vector on the other.  For a positive-semidefinite covariance matrix with a
positive-definite observed block, the conditional mean is affine in the observed block and the
conditional covariance is its Schur complement.  The kernel is identified almost everywhere
with Mathlib's regular conditional distribution.

## Main definitions

* `TauCeti.gaussianCondMean` — the affine conditional mean;
* `TauCeti.gaussianCondCov` — the conditional covariance, as a Schur complement;
* `TauCeti.gaussianCondKernel` — the corresponding Markov kernel.

## Main results

* `TauCeti.condDistrib_multivariateGaussian` — the conditional-distribution formula.

## References

* T. W. Anderson, *An Introduction to Multivariate Statistical Analysis*, 3rd ed., Wiley, 2003.
* `TauCetiRoadmap/StandardDistributions/README.md`, Layer 5, item 4, and
  `TauCetiRoadmap/StandardDistributions/Suggested.lean`, which supplies the declaration skeleton
  and proof plan.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped MatrixOrder RealInnerProductSpace

namespace TauCeti

variable {ι κ : Type*}

/-- The affine conditional-mean formula for the `ι`-block given the `κ`-block.
Its interpretation as a conditional-law parameter requires a positive-semidefinite joint
covariance and a positive-definite observed covariance block, as in
`condDistrib_multivariateGaussian`. -/
noncomputable def gaussianCondMean [Fintype ι] [Fintype κ] [DecidableEq κ]
    (m : EuclideanSpace ℝ (ι ⊕ κ))
    (S : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (x₂ : EuclideanSpace ℝ κ) :
    EuclideanSpace ℝ ι :=
  let m₁ := (EuclideanSpace.sumEquivProd m).1
  let m₂ := (EuclideanSpace.sumEquivProd m).2
  let S₁₂ := S.submatrix Sum.inl Sum.inr
  let S₂₂ := S.submatrix Sum.inr Sum.inr
  m₁ + (S₁₂ * S₂₂⁻¹).toEuclideanLin (x₂ - m₂)

/-- The defining formula for the conditional Gaussian mean. -/
theorem gaussianCondMean_def [Fintype ι] [Fintype κ] [DecidableEq κ]
    (m : EuclideanSpace ℝ (ι ⊕ κ))
    (S : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (x₂ : EuclideanSpace ℝ κ) :
    gaussianCondMean m S x₂ =
      (EuclideanSpace.sumEquivProd m).1 +
        (S.submatrix Sum.inl Sum.inr * (S.submatrix Sum.inr Sum.inr)⁻¹).toEuclideanLin
          (x₂ - (EuclideanSpace.sumEquivProd m).2) :=
  (rfl)

/-- The Schur-complement formula for the conditional covariance of the `ι`-block.
Its interpretation as a conditional-law parameter requires a positive-semidefinite joint
covariance and a positive-definite observed covariance block, as in
`condDistrib_multivariateGaussian`. -/
noncomputable def gaussianCondCov [Fintype κ] [DecidableEq κ]
    (S : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) : Matrix ι ι ℝ :=
  S.submatrix Sum.inl Sum.inl -
    S.submatrix Sum.inl Sum.inr * (S.submatrix Sum.inr Sum.inr)⁻¹ *
      S.submatrix Sum.inr Sum.inl

/-- The defining formula for the conditional Gaussian covariance. -/
theorem gaussianCondCov_def [Fintype κ] [DecidableEq κ]
    (S : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) :
    gaussianCondCov S =
      S.submatrix Sum.inl Sum.inl -
        S.submatrix Sum.inl Sum.inr * (S.submatrix Sum.inr Sum.inr)⁻¹ *
          S.submatrix Sum.inr Sum.inl :=
  (rfl)

end TauCeti

variable {ι κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The conditional covariance of a positive-semidefinite block matrix is positive semidefinite
when the conditioned block is positive definite. -/
theorem Matrix.PosSemidef.gaussianCondCov [Finite ι] {S : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ}
    (hS : S.PosSemidef) (hS₂₂ : (S.submatrix Sum.inr Sum.inr).PosDef) :
    (TauCeti.gaussianCondCov S).PosSemidef := by
  classical
  let _ := Fintype.ofFinite ι
  let S₁₁ := S.submatrix Sum.inl Sum.inl
  let S₁₂ := S.submatrix Sum.inl Sum.inr
  let S₂₁ := S.submatrix Sum.inr Sum.inl
  let S₂₂ := S.submatrix Sum.inr Sum.inr
  let _ := hS₂₂.isUnit.invertible
  have hS₂₁ : S₂₁ = Matrix.conjTranspose S₁₂ := by
    ext i j
    simpa [S₂₁, S₁₂, Matrix.conjTranspose_apply] using
      (hS.isHermitian.apply (Sum.inr i) (Sum.inl j)).symm
  have hblocks : Matrix.fromBlocks S₁₁ S₁₂ (Matrix.conjTranspose S₁₂) S₂₂ = S := by
    rw [← hS₂₁]
    ext (i | i) (j | j) <;> rfl
  have hcond : (S₁₁ - S₁₂ * S₂₂⁻¹ * Matrix.conjTranspose S₁₂).PosSemidef :=
    (Matrix.PosDef.fromBlocks₂₂ S₁₁ S₁₂ hS₂₂).mp (hblocks ▸ hS)
  rw [← hS₂₁] at hcond
  simpa only [TauCeti.gaussianCondCov_def, S₁₁, S₁₂, S₂₁, S₂₂] using hcond

/-- The conditional covariance of a positive-definite block matrix is positive definite. -/
theorem Matrix.PosDef.gaussianCondCov [Finite ι] {S : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ}
    (hS : S.PosDef) :
    (TauCeti.gaussianCondCov S).PosDef := by
  classical
  let _ := Fintype.ofFinite ι
  let S₁₁ := S.submatrix Sum.inl Sum.inl
  let S₁₂ := S.submatrix Sum.inl Sum.inr
  let S₂₁ := S.submatrix Sum.inr Sum.inl
  let S₂₂ := S.submatrix Sum.inr Sum.inr
  have hS₂₂ : S₂₂.PosDef := hS.submatrix Sum.inr_injective
  let _ := hS₂₂.isUnit.invertible
  have hS₂₁ : S₂₁ = Matrix.conjTranspose S₁₂ := by
    ext i j
    simpa [S₂₁, S₁₂, Matrix.conjTranspose_apply] using
      (hS.isHermitian.apply (Sum.inr i) (Sum.inl j)).symm
  have hblocks' : Matrix.fromBlocks S₁₁ S₁₂ S₂₁ S₂₂ = S := by
    ext (i | i) (j | j) <;> rfl
  have hblocks : Matrix.fromBlocks S₁₁ S₁₂ (Matrix.conjTranspose S₁₂) S₂₂ = S := by
    rw [← hS₂₁]
    exact hblocks'
  have hpos : (S₁₁ - S₁₂ * S₂₂⁻¹ * Matrix.conjTranspose S₁₂).PosSemidef :=
    (Matrix.PosDef.fromBlocks₂₂ S₁₁ S₁₂ hS₂₂).mp (hblocks ▸ hS.posSemidef)
  let _ : Invertible S := hS.isUnit.invertible
  let _ : Invertible (Matrix.fromBlocks S₁₁ S₁₂ (Matrix.conjTranspose S₁₂) S₂₂) :=
    Invertible.copy ‹Invertible S› _ hblocks
  let _ : Invertible (S₁₁ - S₁₂ * ⅟S₂₂ * Matrix.conjTranspose S₁₂) :=
    Matrix.invertibleOfFromBlocks₂₂Invertible S₁₁ S₁₂ (Matrix.conjTranspose S₁₂) S₂₂
  have hunit : IsUnit (S₁₁ - S₁₂ * S₂₂⁻¹ * Matrix.conjTranspose S₁₂) := by
    simpa only [Matrix.invOf_eq_nonsing_inv] using
      (isUnit_of_invertible (S₁₁ - S₁₂ * ⅟S₂₂ * Matrix.conjTranspose S₁₂))
  rw [TauCeti.gaussianCondCov_def]
  -- Expose the named block matrices so the Schur-complement theorem applies directly.
  change (S₁₁ - S₁₂ * S₂₂⁻¹ * S₂₁).PosDef
  rw [hS₂₁]
  exact hpos.posDef_iff_isUnit.mpr hunit

namespace TauCeti

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- The Gaussian Markov kernel given by the conditional-law formula.
`condDistrib_multivariateGaussian` identifies it with the conditional distribution when the joint
covariance is positive semidefinite and the observed covariance block is positive definite. -/
noncomputable def gaussianCondKernel (m : EuclideanSpace ℝ (ι ⊕ κ))
    (S : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) :
    Kernel (EuclideanSpace ℝ κ) (EuclideanSpace ℝ ι) where
  toFun x₂ := multivariateGaussian (gaussianCondMean m S x₂) (gaussianCondCov S)
  measurable' := by
    have hparameters : Measurable fun x₂ => (gaussianCondMean m S x₂, gaussianCondCov S) := by
      apply Measurable.prodMk
      · rw [funext fun x₂ => gaussianCondMean_def m S x₂]
        fun_prop
      · exact measurable_const
    -- Present the kernel family as the uncurried measurable Gaussian parameter map.
    change Measurable
      (Function.uncurry multivariateGaussian ∘ fun x₂ =>
        (gaussianCondMean m S x₂, gaussianCondCov S))
    exact measurable_multivariateGaussian.comp hparameters

/-- The conditional Gaussian kernel evaluates to the Gaussian law with the displayed conditional
mean and covariance. -/
@[simp]
theorem gaussianCondKernel_apply (m : EuclideanSpace ℝ (ι ⊕ κ))
    (S : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (x₂ : EuclideanSpace ℝ κ) :
    gaussianCondKernel m S x₂ =
      multivariateGaussian (gaussianCondMean m S x₂) (gaussianCondCov S) :=
  (rfl)

instance isMarkovKernel_gaussianCondKernel (m : EuclideanSpace ℝ (ι ⊕ κ))
    (S : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) : IsMarkovKernel (gaussianCondKernel m S) where
  isProbabilityMeasure x := by
    rw [gaussianCondKernel_apply]
    infer_instance

private noncomputable def gaussianRegressionMatrix
    (S : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) : Matrix ι κ ℝ :=
  S.submatrix Sum.inl Sum.inr * (S.submatrix Sum.inr Sum.inr)⁻¹

private noncomputable def gaussianResidualMatrix
    (S : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) : Matrix ι (ι ⊕ κ) ℝ :=
  Matrix.fromCols 1 (-gaussianRegressionMatrix S)

private noncomputable def gaussianSndMatrix : Matrix κ (ι ⊕ κ) ℝ :=
  Matrix.fromCols 0 1

private theorem gaussianSndMatrix_mulVec (x : EuclideanSpace ℝ (ι ⊕ κ)) :
    (gaussianSndMatrix (ι := ι) (κ := κ)).toEuclideanLin x =
      (EuclideanSpace.sumEquivProd x).2 := by
  ext i
  have happly : ((gaussianSndMatrix (ι := ι) (κ := κ)).toEuclideanLin x).ofLp =
      Matrix.mulVec (gaussianSndMatrix (ι := ι) (κ := κ)) x.ofLp := by
    simpa only [Matrix.toLin'_apply] using
      Matrix.ofLp_toLpLin (p := 2) (q := 2) (gaussianSndMatrix (ι := ι) (κ := κ)) x
  -- Compare coordinates through the underlying unweighted function representation.
  change ((gaussianSndMatrix (ι := ι) (κ := κ)).toEuclideanLin x).ofLp i = _
  rw [happly, gaussianSndMatrix, Matrix.fromCols_mulVec]
  simp only [Matrix.zero_mulVec, Matrix.one_mulVec, zero_add]
  rfl

private theorem gaussianResidualMatrix_mulVec (S : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ)
    (x : EuclideanSpace ℝ (ι ⊕ κ)) :
    (gaussianResidualMatrix S).toEuclideanLin x =
      (EuclideanSpace.sumEquivProd x).1 -
        (gaussianRegressionMatrix S).toEuclideanLin (EuclideanSpace.sumEquivProd x).2 := by
  ext i
  have hleft : ((gaussianResidualMatrix S).toEuclideanLin x).ofLp =
      Matrix.mulVec (gaussianResidualMatrix S) x.ofLp := by
    simpa only [Matrix.toLin'_apply] using
      Matrix.ofLp_toLpLin (p := 2) (q := 2) (gaussianResidualMatrix S) x
  have hright : ((gaussianRegressionMatrix S).toEuclideanLin
      (EuclideanSpace.sumEquivProd x).2).ofLp =
      Matrix.mulVec (gaussianRegressionMatrix S) ((EuclideanSpace.sumEquivProd x).2).ofLp := by
    simpa only [Matrix.toLin'_apply] using
      Matrix.ofLp_toLpLin (p := 2) (q := 2) (gaussianRegressionMatrix S)
        (EuclideanSpace.sumEquivProd x).2
  -- Compare coordinates through the underlying unweighted function representation.
  change ((gaussianResidualMatrix S).toEuclideanLin x).ofLp i = _
  rw [hleft, WithLp.ofLp_sub, hright, gaussianResidualMatrix, Matrix.fromCols_mulVec]
  simp only [Matrix.one_mulVec, Matrix.neg_mulVec, Pi.sub_apply]
  rfl

omit [Fintype ι] [DecidableEq ι] in
private theorem gaussianRegressionMatrix_mul_block22 {S : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ}
    (hS₂₂ : (S.submatrix Sum.inr Sum.inr).PosDef) :
    gaussianRegressionMatrix S * S.submatrix Sum.inr Sum.inr =
      S.submatrix Sum.inl Sum.inr := by
  let _ := hS₂₂.isUnit.invertible
  simp [gaussianRegressionMatrix, Matrix.mul_assoc]

private theorem gaussianResidualMatrix_mul_cov_mul_transpose
    {S : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ}
    (hS₂₂ : (S.submatrix Sum.inr Sum.inr).PosDef) :
    gaussianResidualMatrix S * S * (gaussianResidualMatrix S).transpose = gaussianCondCov S := by
  let S₁₁ := S.submatrix Sum.inl Sum.inl
  let S₁₂ := S.submatrix Sum.inl Sum.inr
  let S₂₁ := S.submatrix Sum.inr Sum.inl
  let S₂₂ := S.submatrix Sum.inr Sum.inr
  let A := gaussianRegressionMatrix S
  have hblocks : Matrix.fromBlocks S₁₁ S₁₂ S₂₁ S₂₂ = S := by
    ext (i | i) (j | j) <;> rfl
  have hAS₂₂ : A * S₂₂ = S₁₂ := gaussianRegressionMatrix_mul_block22 hS₂₂
  -- Unfold the residual map to expose multiplication of partitioned matrices.
  change Matrix.fromCols 1 (-A) * S * (Matrix.fromCols 1 (-A)).transpose = gaussianCondCov S
  calc
    _ = Matrix.fromCols 1 (-A) * Matrix.fromBlocks S₁₁ S₁₂ S₂₁ S₂₂ *
        (Matrix.fromCols 1 (-A)).transpose := by rw [← hblocks]
    _ = (S₁₁ - A * S₂₁) * 1 + (S₁₂ - A * S₂₂) * (-A).transpose := by
      simp [Matrix.fromCols_mul_fromBlocks, Matrix.transpose_fromCols,
        Matrix.fromCols_mul_fromRows, sub_eq_add_neg]
    _ = S₁₁ - A * S₂₁ := by
      rw [hAS₂₂, sub_self]
      simp only [Matrix.mul_one, Matrix.zero_mul, add_zero]
    _ = gaussianCondCov S := by
      simp [gaussianCondCov_def, S₁₁, S₂₁, A, gaussianRegressionMatrix,
        Matrix.mul_assoc]

private theorem gaussianResidualMatrix_mul_cov_mul_snd_transpose
    {S : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ}
    (hS₂₂ : (S.submatrix Sum.inr Sum.inr).PosDef) :
    gaussianResidualMatrix S * S *
      (gaussianSndMatrix (ι := ι) (κ := κ)).transpose = (0 : Matrix ι κ ℝ) := by
  let S₁₁ := S.submatrix Sum.inl Sum.inl
  let S₁₂ := S.submatrix Sum.inl Sum.inr
  let S₂₁ := S.submatrix Sum.inr Sum.inl
  let S₂₂ := S.submatrix Sum.inr Sum.inr
  let A := gaussianRegressionMatrix S
  have hblocks : Matrix.fromBlocks S₁₁ S₁₂ S₂₁ S₂₂ = S := by
    ext (i | i) (j | j) <;> rfl
  have hAS₂₂ : A * S₂₂ = S₁₂ := gaussianRegressionMatrix_mul_block22 hS₂₂
  -- Unfold the two linear maps to expose multiplication of partitioned matrices.
  change Matrix.fromCols 1 (-A) * S *
    (Matrix.fromCols (0 : Matrix κ ι ℝ) (1 : Matrix κ κ ℝ)).transpose =
      (0 : Matrix ι κ ℝ)
  calc
    _ = Matrix.fromCols 1 (-A) * Matrix.fromBlocks S₁₁ S₁₂ S₂₁ S₂₂ *
        (Matrix.fromCols (0 : Matrix κ ι ℝ) (1 : Matrix κ κ ℝ)).transpose := by
      rw [← hblocks]
    _ = (S₁₁ - A * S₂₁) * (0 : Matrix ι κ ℝ) +
        (S₁₂ - A * S₂₂) * (1 : Matrix κ κ ℝ) := by
      simp [Matrix.fromCols_mul_fromBlocks, Matrix.transpose_fromCols,
        Matrix.fromCols_mul_fromRows, sub_eq_add_neg]
    _ = (0 : Matrix ι κ ℝ) := by rw [hAS₂₂, sub_self]; simp

private theorem gaussianResidual_hasLaw {S : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ}
    (m : EuclideanSpace ℝ (ι ⊕ κ)) (hS : S.PosSemidef)
    (hS₂₂ : (S.submatrix Sum.inr Sum.inr).PosDef) :
    HasLaw (fun x => (gaussianResidualMatrix S).toEuclideanLin x)
      (multivariateGaussian ((gaussianResidualMatrix S).toEuclideanLin m) (gaussianCondCov S))
      (multivariateGaussian m S) := by
  have h := HasLaw.comp
    (Y := fun x => (gaussianResidualMatrix S).toEuclideanLin x + 0)
    ⟨by fun_prop, map_affine_multivariateGaussian m hS (gaussianResidualMatrix S) 0⟩
    HasLaw.id
  rw [gaussianResidualMatrix_mul_cov_mul_transpose hS₂₂] at h
  simpa only [Function.comp_id, add_zero] using h

private theorem gaussianSnd_hasLaw {S : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ}
    (m : EuclideanSpace ℝ (ι ⊕ κ)) (hS : S.PosSemidef) :
    HasLaw (fun x => (EuclideanSpace.sumEquivProd x).2)
      (multivariateGaussian (EuclideanSpace.sumEquivProd m).2
        (S.submatrix Sum.inr Sum.inr)) (multivariateGaussian m S) := by
  let L : Matrix κ (ι ⊕ κ) ℝ := gaussianSndMatrix
  have hL (x : EuclideanSpace ℝ (ι ⊕ κ)) :
      L.toEuclideanLin x = (EuclideanSpace.sumEquivProd x).2 :=
    gaussianSndMatrix_mulVec x
  have hcov : L * S * L.transpose = S.submatrix Sum.inr Sum.inr := by
    let S₁₁ := S.submatrix Sum.inl Sum.inl
    let S₁₂ := S.submatrix Sum.inl Sum.inr
    let S₂₁ := S.submatrix Sum.inr Sum.inl
    let S₂₂ := S.submatrix Sum.inr Sum.inr
    have hblocks : Matrix.fromBlocks S₁₁ S₁₂ S₂₁ S₂₂ = S := by
      ext (i | i) (j | j) <;> rfl
    -- Unfold the second projection to expose multiplication of partitioned matrices.
    change Matrix.fromCols (0 : Matrix κ ι ℝ) (1 : Matrix κ κ ℝ) * S *
      (Matrix.fromCols (0 : Matrix κ ι ℝ) (1 : Matrix κ κ ℝ)).transpose = S₂₂
    calc
      _ = Matrix.fromCols (0 : Matrix κ ι ℝ) (1 : Matrix κ κ ℝ) *
          Matrix.fromBlocks S₁₁ S₁₂ S₂₁ S₂₂ *
          (Matrix.fromCols (0 : Matrix κ ι ℝ) (1 : Matrix κ κ ℝ)).transpose := by
        rw [← hblocks]
      _ = S₂₂ := by
        simp [Matrix.fromCols_mul_fromBlocks, Matrix.transpose_fromCols,
          Matrix.fromCols_mul_fromRows]
  have h := HasLaw.comp
    ⟨by fun_prop, map_affine_multivariateGaussian m hS L 0⟩ HasLaw.id
  rw [hcov] at h
  simpa only [hL, add_zero, Function.comp_id] using h

private theorem indepFun_gaussianSnd_gaussianResidual {S : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ}
    (m : EuclideanSpace ℝ (ι ⊕ κ)) (hS : S.PosSemidef)
    (hS₂₂ : (S.submatrix Sum.inr Sum.inr).PosDef) :
    IndepFun (fun x => (EuclideanSpace.sumEquivProd x).2)
      (fun x => (gaussianResidualMatrix S).toEuclideanLin x) (multivariateGaussian m S) := by
  let X₂ := fun x : EuclideanSpace ℝ (ι ⊕ κ) => (EuclideanSpace.sumEquivProd x).2
  let R := fun x : EuclideanSpace ℝ (ι ⊕ κ) => (gaussianResidualMatrix S).toEuclideanLin x
  have hXR : HasGaussianLaw (fun x => (X₂ x, R x)) (multivariateGaussian m S) := by
    let T : EuclideanSpace ℝ (ι ⊕ κ) →L[ℝ]
        EuclideanSpace ℝ κ × EuclideanSpace ℝ ι :=
      (gaussianSndMatrix (ι := ι) (κ := κ)).toEuclideanLin.toContinuousLinearMap.prod
        (gaussianResidualMatrix S).toEuclideanLin.toContinuousLinearMap
    refine ⟨by fun_prop, ?_⟩
    have hgaussian : IsGaussian ((multivariateGaussian m S).map T) :=
      isGaussian_map_of_measurable (by fun_prop)
    have hfun : (fun x => (X₂ x, R x)) = T := by
      funext x
      simp only [T, X₂, R, ContinuousLinearMap.prod_apply,
        LinearMap.coe_toContinuousLinearMap']
      rw [gaussianSndMatrix_mulVec]
    rwa [hfun]
  refine hXR.indepFun_of_covariance_inner fun x₂ r => ?_
  rw [covariance_comm]
  simp only [R, X₂]
  have hsnd : (fun z => ⟪x₂, (EuclideanSpace.sumEquivProd z).2⟫) =
      fun z => ⟪x₂, (gaussianSndMatrix (ι := ι) (κ := κ)).toEuclideanLin z⟫ := by
    funext z
    rw [gaussianSndMatrix_mulVec]
  rw [hsnd]
  rw [covariance_inner_matrix_multivariateGaussian m hS,
    gaussianResidualMatrix_mul_cov_mul_snd_transpose hS₂₂]
  simp

private theorem gaussianCondKernel_eq_map_residual {S : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ}
    (m : EuclideanSpace ℝ (ι ⊕ κ)) (hS : S.PosSemidef)
    (hS₂₂ : (S.submatrix Sum.inr Sum.inr).PosDef) (x₂ : EuclideanSpace ℝ κ) :
    gaussianCondKernel m S x₂ =
      (multivariateGaussian ((gaussianResidualMatrix S).toEuclideanLin m) (gaussianCondCov S)).map
        (fun r => r + (gaussianRegressionMatrix S).toEuclideanLin x₂) := by
  rw [gaussianCondKernel_apply]
  symm
  have hfun : (fun r : EuclideanSpace ℝ ι =>
      r + (gaussianRegressionMatrix S).toEuclideanLin x₂) =
      fun r => (1 : Matrix ι ι ℝ).toEuclideanLin r +
        (gaussianRegressionMatrix S).toEuclideanLin x₂ := by
    funext r
    simp
  rw [hfun]
  rw [map_affine_multivariateGaussian _ (Matrix.PosSemidef.gaussianCondCov hS hS₂₂) 1]
  congr 1
  · rw [gaussianCondMean_def, gaussianResidualMatrix_mulVec]
    simp only [Matrix.toLpLin_one, LinearMap.id_coe, id_eq]
    rw [map_sub]
    simp only [gaussianRegressionMatrix]
    abel
  · simp

private theorem compProd_gaussianCondKernel_eq_map_prod {S : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ}
    (m : EuclideanSpace ℝ (ι ⊕ κ)) (hS : S.PosSemidef)
    (hS₂₂ : (S.submatrix Sum.inr Sum.inr).PosDef) :
    multivariateGaussian (EuclideanSpace.sumEquivProd m).2 (S.submatrix Sum.inr Sum.inr) ⊗ₘ
        gaussianCondKernel m S =
      ((multivariateGaussian (EuclideanSpace.sumEquivProd m).2 (S.submatrix Sum.inr Sum.inr)).prod
          (multivariateGaussian ((gaussianResidualMatrix S).toEuclideanLin m)
            (gaussianCondCov S))).map
        (fun z => (z.1, z.2 + (gaussianRegressionMatrix S).toEuclideanLin z.1)) := by
  ext s hs
  rw [Measure.compProd_apply hs, Measure.map_apply (by fun_prop) hs,
    Measure.prod_apply (hs.preimage (by fun_prop))]
  congr with x₂
  rw [gaussianCondKernel_eq_map_residual m hS hS₂₂ x₂,
    Measure.map_apply (by fun_prop) (measurable_prodMk_left hs)]
  rfl

/-- For a jointly Gaussian vector with positive-semidefinite covariance and a positive-definite
observed covariance block, the regular conditional law of the first coordinate block given the
second is Gaussian with the Schur-complement covariance and the usual affine conditional mean. -/
theorem condDistrib_multivariateGaussian {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (X : Ω → EuclideanSpace ℝ (ι ⊕ κ))
    (m : EuclideanSpace ℝ (ι ⊕ κ)) {S : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ}
    (hX : HasLaw X (multivariateGaussian m S) P) (hS : S.PosSemidef)
    (hS₂₂ : (S.submatrix Sum.inr Sum.inr).PosDef) :
    condDistrib (fun ω => (EuclideanSpace.sumEquivProd (X ω)).1)
        (fun ω => (EuclideanSpace.sumEquivProd (X ω)).2) P =ᵐ[
      P.map (fun ω => (EuclideanSpace.sumEquivProd (X ω)).2)] gaussianCondKernel m S := by
  let X₁ := fun ω => (EuclideanSpace.sumEquivProd (X ω)).1
  let X₂ := fun ω => (EuclideanSpace.sumEquivProd (X ω)).2
  let R := fun x : EuclideanSpace ℝ (ι ⊕ κ) => (gaussianResidualMatrix S).toEuclideanLin x
  have hX₂ := (gaussianSnd_hasLaw m hS).comp hX
  have hprod := ((indepFun_gaussianSnd_gaussianResidual m hS hS₂₂).hasLaw_prod
    (gaussianSnd_hasLaw m hS) (gaussianResidual_hasLaw m hS hS₂₂)).comp hX
  refine condDistrib_ae_eq_of_measure_eq_compProd (by fun_prop) (by fun_prop) ?_
  have hX₂map : P.map X₂ =
      multivariateGaussian (EuclideanSpace.sumEquivProd m).2
        (S.submatrix Sum.inr Sum.inr) := by
    -- Match the compositional form used by `HasLaw.map_eq`.
    change P.map ((fun x => (EuclideanSpace.sumEquivProd x).2) ∘ X) = _
    exact hX₂.map_eq
  rw [hX₂map, compProd_gaussianCondKernel_eq_map_prod m hS hS₂₂, ← hprod.map_eq,
    AEMeasurable.map_map_of_aemeasurable (by fun_prop) (by fun_prop)]
  apply Measure.map_congr
  filter_upwards with ω
  dsimp only [X₁, X₂, R, Function.comp_apply]
  rw [gaussianResidualMatrix_mulVec]
  ext <;> simp

end TauCeti
