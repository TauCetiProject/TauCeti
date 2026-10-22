/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Vec
public import TauCeti.Probability.Distributions.Gaussian.Affine
public import TauCeti.Analysis.Matrix.MeasurableSpace

import Mathlib.Analysis.Matrix.Order

/-!
# Matrix normal laws

The matrix normal law `matrixNormalMeasure M U V` on real `ι × κ` matrices has mean `M`, row
covariance `U` and column covariance `V`. It is defined through the column-stacking
vectorization `Matrix.vec`, packaged as the measurable equivalence
`TauCeti.matrixVecMeasurableEquiv`: the vectorization of a matrix normal matrix is the multivariate
Gaussian with mean `vec M` and Kronecker covariance `V ⊗ₖ U`. Thus entries `(i, j)` and
`(k, l)` have covariance `U i k * V j l`, and rows and columns are multivariate Gaussian with
covariances proportional to `V` and `U`.

The covariance parameters are only required to be positive semidefinite, so singular laws are
included. If `U` or `V` is not positive semidefinite, the law is the point mass at `M`; this is
an explicit branch, because the Kronecker product of two negative definite matrices is positive
definite. Matrices with an empty row or column type also give the point mass.

## Main results

* `TauCeti.Probability.map_vec_matrixNormalMeasure`: the vectorized law is multivariate
  Gaussian with Kronecker covariance.
* `TauCeti.Probability.covariance_matrixNormalMeasure`: entries have covariance
  `U i k * V j l`.
* `TauCeti.Probability.map_mul_mul_add_matrixNormalMeasure`: the image under `X ↦ A * X * B + C`
  is matrix normal with parameters `A * M * B + C`, `A * U * Aᵀ` and `Bᵀ * V * B`.
* `TauCeti.Probability.map_row_matrixNormalMeasure`, `map_col_matrixNormalMeasure`: rows and
  columns are multivariate Gaussian.

## References

* A. K. Gupta and D. K. Nagar, *Matrix Variate Distributions*, Chapman & Hall/CRC, 2000,
  chapter 2.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped Kronecker Matrix NNReal

namespace TauCeti.Probability

variable {ι κ ι' κ' α : Type*} [Fintype ι] [Fintype κ] [Fintype ι'] [Fintype κ']
  [DecidableEq ι] [DecidableEq κ] [DecidableEq ι'] [DecidableEq κ']

open Classical in
/-- The matrix normal law on `ι × κ` real matrices with mean `M`, row covariance `U` and column
covariance `V`: its column-stacking vectorization is the multivariate Gaussian with mean `vec M`
and covariance `V ⊗ₖ U`. If `U` or `V` is not positive semidefinite, it is the point mass at
`M`. -/
def matrixNormalMeasure (M : Matrix ι κ ℝ) (U : Matrix ι ι ℝ) (V : Matrix κ κ ℝ) :
    Measure (Matrix ι κ ℝ) :=
  if U.PosSemidef ∧ V.PosSemidef then
    (multivariateGaussian (WithLp.toLp 2 M.vec) (V ⊗ₖ U)).map (matrixVecMeasurableEquiv 2).symm
  else Measure.dirac M

/-- For positive semidefinite covariances, the matrix normal law is the Gaussian law of its
vectorization, read back as a matrix. -/
theorem matrixNormalMeasure_of_posSemidef (M : Matrix ι κ ℝ) {U : Matrix ι ι ℝ}
    {V : Matrix κ κ ℝ} (hU : U.PosSemidef) (hV : V.PosSemidef) :
    matrixNormalMeasure M U V =
      (multivariateGaussian (WithLp.toLp 2 M.vec) (V ⊗ₖ U)).map (matrixVecMeasurableEquiv 2).symm :=
  ite_eq_left ⟨hU, hV⟩

/-- If one of the covariance parameters is not positive semidefinite, the matrix normal law is
the point mass at its mean. -/
theorem matrixNormalMeasure_of_not_posSemidef (M : Matrix ι κ ℝ) {U : Matrix ι ι ℝ}
    {V : Matrix κ κ ℝ} (h : ¬(U.PosSemidef ∧ V.PosSemidef)) :
    matrixNormalMeasure M U V = Measure.dirac M :=
  ite_eq_right h

/-- Every parameter gives a probability measure, including the point-mass fallback. -/
instance isProbabilityMeasure_matrixNormalMeasure (M : Matrix ι κ ℝ) (U : Matrix ι ι ℝ)
    (V : Matrix κ κ ℝ) : IsProbabilityMeasure (matrixNormalMeasure M U V) := by
  by_cases h : U.PosSemidef ∧ V.PosSemidef
  · rw [matrixNormalMeasure_of_posSemidef M h.1 h.2]
    infer_instance
  · rw [matrixNormalMeasure_of_not_posSemidef M h]
    infer_instance

/-- The column-stacking vectorization of a matrix normal matrix is multivariate Gaussian, with
the vectorized mean and the Kronecker product of the column and row covariances. -/
theorem map_vec_matrixNormalMeasure (M : Matrix ι κ ℝ) {U : Matrix ι ι ℝ} {V : Matrix κ κ ℝ}
    (hU : U.PosSemidef) (hV : V.PosSemidef) :
    (matrixNormalMeasure M U V).map (fun X => WithLp.toLp 2 X.vec) =
      multivariateGaussian (WithLp.toLp 2 M.vec) (V ⊗ₖ U) := by
  rw [matrixNormalMeasure_of_posSemidef M hU hV,
    show (fun X : Matrix ι κ ℝ => WithLp.toLp 2 X.vec) = matrixVecMeasurableEquiv 2 from
      funext fun X => (matrixVecMeasurableEquiv_apply 2 X).symm]
  exact MeasurableEquiv.map_map_symm _

/-- A zero row covariance gives the point mass at the mean. -/
@[simp]
theorem matrixNormalMeasure_zero_left (M : Matrix ι κ ℝ) (V : Matrix κ κ ℝ) :
    matrixNormalMeasure M 0 V = Measure.dirac M := by
  by_cases hV : V.PosSemidef
  · rw [matrixNormalMeasure_of_posSemidef M Matrix.PosSemidef.zero hV, Matrix.kronecker_zero,
      multivariateGaussian_zero_right, Measure.map_dirac' (MeasurableEquiv.measurable _)]
    rw [← matrixVecMeasurableEquiv_apply, MeasurableEquiv.symm_apply_apply]
  · exact matrixNormalMeasure_of_not_posSemidef M fun h => hV h.2

/-- A zero column covariance gives the point mass at the mean. -/
@[simp]
theorem matrixNormalMeasure_zero_right (M : Matrix ι κ ℝ) (U : Matrix ι ι ℝ) :
    matrixNormalMeasure M U 0 = Measure.dirac M := by
  by_cases hU : U.PosSemidef
  · rw [matrixNormalMeasure_of_posSemidef M hU Matrix.PosSemidef.zero, Matrix.zero_kronecker,
      multivariateGaussian_zero_right, Measure.map_dirac' (MeasurableEquiv.measurable _)]
    rw [← matrixVecMeasurableEquiv_apply, MeasurableEquiv.symm_apply_apply]
  · exact matrixNormalMeasure_of_not_posSemidef M fun h => hU h.1

/-- When there is only one matrix, as for an empty row or column type, the matrix normal law is
the point mass at it. -/
theorem matrixNormalMeasure_of_subsingleton [Subsingleton (Matrix ι κ ℝ)] (M : Matrix ι κ ℝ)
    (U : Matrix ι ι ℝ) (V : Matrix κ κ ℝ) : matrixNormalMeasure M U V = Measure.dirac M := by
  have h : (id : Matrix ι κ ℝ → Matrix ι κ ℝ) = fun _ => M :=
    funext fun X => Subsingleton.elim X M
  rw [← Measure.map_id (μ := matrixNormalMeasure M U V), h, Measure.map_const, measure_univ,
    one_smul]

/-- Reading the vectorized entries along any map of indices gives a multivariate Gaussian with the
reindexed mean and Kronecker covariance. -/
private theorem map_comp_vec_matrixNormalMeasure [Fintype α] [DecidableEq α] (M : Matrix ι κ ℝ)
    {U : Matrix ι ι ℝ} {V : Matrix κ κ ℝ} (hU : U.PosSemidef) (hV : V.PosSemidef) (f : α → κ × ι) :
    (matrixNormalMeasure M U V).map (fun X => WithLp.toLp 2 fun a => X.vec (f a)) =
      multivariateGaussian (WithLp.toLp 2 fun a => M.vec (f a)) ((V ⊗ₖ U).submatrix f f) := by
  have h := map_comp_multivariateGaussian (WithLp.toLp 2 M.vec) (hV.kronecker hU) f
  rw [← map_vec_matrixNormalMeasure M hU hV, Measure.map_map (by fun_prop) (by fun_prop)]
    at h
  simpa [Function.comp_def] using h

/-- Each entry of a matrix normal matrix is a real Gaussian, with variance the product of the
corresponding diagonal entries of the row and column covariances. -/
theorem map_apply_matrixNormalMeasure (M : Matrix ι κ ℝ) {U : Matrix ι ι ℝ} {V : Matrix κ κ ℝ}
    (hU : U.PosSemidef) (hV : V.PosSemidef) (i : ι) (j : κ) :
    (matrixNormalMeasure M U V).map (fun X => X i j) =
      gaussianReal (M i j) (U i i * V j j).toNNReal := by
  have h := (measurePreserving_eval_multivariateGaussian
    (μ := WithLp.toLp 2 M.vec) (hV.kronecker hU) (i := (j, i))).map_eq
  rw [← map_vec_matrixNormalMeasure M hU hV, Measure.map_map (by fun_prop) (by fun_prop)] at h
  simpa [Function.comp_def, mul_comm] using h

/-- The entries of a matrix normal matrix have every finite moment. This also holds for the
point-mass fallback. -/
theorem memLp_apply_matrixNormalMeasure (M : Matrix ι κ ℝ) (U : Matrix ι ι ℝ) (V : Matrix κ κ ℝ)
    (i : ι) (j : κ) (p : ℝ≥0) : MemLp (fun X => X i j) p (matrixNormalMeasure M U V) := by
  by_cases h : U.PosSemidef ∧ V.PosSemidef
  · have hp := memLp_id_gaussianReal (μ := M i j) (v := (U i i * V j j).toNNReal) p
    rw [← map_apply_matrixNormalMeasure M h.1 h.2] at hp
    exact (memLp_map_measure_iff hp.aestronglyMeasurable
      (Matrix.measurable_apply (i := i) (j := j)).aemeasurable).1 hp
  · rw [matrixNormalMeasure_of_not_posSemidef M h]
    exact memLp_dirac enorm_lt_top

/-- The mean of each entry is the corresponding entry of the mean parameter. This also holds for
the point-mass fallback. -/
@[simp]
theorem integral_apply_matrixNormalMeasure (M : Matrix ι κ ℝ) (U : Matrix ι ι ℝ)
    (V : Matrix κ κ ℝ) (i : ι) (j : κ) : ∫ X, X i j ∂matrixNormalMeasure M U V = M i j := by
  by_cases h : U.PosSemidef ∧ V.PosSemidef
  · rw [← integral_id_gaussianReal (μ := M i j) (v := (U i i * V j j).toNNReal),
      ← map_apply_matrixNormalMeasure M h.1 h.2,
      integral_map Matrix.measurable_apply.aemeasurable (by fun_prop)]
  · rw [matrixNormalMeasure_of_not_posSemidef M h, integral_dirac]

/-- Entries `(i, j)` and `(k, l)` of a matrix normal matrix have covariance `U i k * V j l`. -/
theorem covariance_matrixNormalMeasure (M : Matrix ι κ ℝ) {U : Matrix ι ι ℝ}
    {V : Matrix κ κ ℝ} (hU : U.PosSemidef) (hV : V.PosSemidef) (i k : ι) (j l : κ) :
    cov[fun X => X i j, fun X => X k l; matrixNormalMeasure M U V] = U i k * V j l := by
  have h := covariance_eval_multivariateGaussian (μ := WithLp.toLp 2 M.vec)
    (hV.kronecker hU) (j, i) (l, k)
  rw [← map_vec_matrixNormalMeasure M hU hV, covariance_map (by fun_prop) (by fun_prop)
    (by fun_prop)] at h
  simpa [Function.comp_def, mul_comm] using h

/-- The transpose of a matrix normal matrix is matrix normal, with the row and column
covariances exchanged. This holds for all parameters, including the point-mass fallback. -/
@[simp]
theorem map_transpose_matrixNormalMeasure (M : Matrix ι κ ℝ) (U : Matrix ι ι ℝ)
    (V : Matrix κ κ ℝ) :
    (matrixNormalMeasure M U V).map Matrix.transpose = matrixNormalMeasure Mᵀ V U := by
  by_cases h : U.PosSemidef ∧ V.PosSemidef
  · have hvec := map_comp_vec_matrixNormalMeasure M h.1 h.2 Prod.swap
    have hcov : (V ⊗ₖ U).submatrix Prod.swap Prod.swap = U ⊗ₖ V := by
      ext ⟨i, j⟩ ⟨k, l⟩
      simp [mul_comm]
    have hmean : (fun a : ι × κ => M.vec a.swap) = Mᵀ.vec := by
      ext
      simp
    rw [hcov, hmean] at hvec
    rw [matrixNormalMeasure_of_posSemidef Mᵀ h.2 h.1, ← hvec,
      Measure.map_map (by fun_prop) (by fun_prop)]
    refine congrArg (fun g => (matrixNormalMeasure M U V).map g) (funext fun X => ?_)
    ext j i
    simp
  · rw [matrixNormalMeasure_of_not_posSemidef M h,
      matrixNormalMeasure_of_not_posSemidef Mᵀ fun h' => h ⟨h'.2, h'.1⟩,
      Measure.map_dirac' (by fun_prop)]

/-- Each row of a matrix normal matrix is multivariate Gaussian, with covariance the column
covariance scaled by the corresponding diagonal entry of the row covariance. -/
theorem map_row_matrixNormalMeasure (M : Matrix ι κ ℝ) {U : Matrix ι ι ℝ} {V : Matrix κ κ ℝ}
    (hU : U.PosSemidef) (hV : V.PosSemidef) (i : ι) :
    (matrixNormalMeasure M U V).map (fun X => WithLp.toLp 2 (X i)) =
      multivariateGaussian (WithLp.toLp 2 (M i)) (U i i • V) := by
  have h := map_comp_vec_matrixNormalMeasure M hU hV fun j : κ => (j, i)
  have hcov : (V ⊗ₖ U).submatrix (fun j : κ => (j, i)) (fun j => (j, i)) = U i i • V := by
    ext j l
    simp [mul_comm]
  simpa [hcov] using h

/-- Each column of a matrix normal matrix is multivariate Gaussian, with covariance the row
covariance scaled by the corresponding diagonal entry of the column covariance. -/
theorem map_col_matrixNormalMeasure (M : Matrix ι κ ℝ) {U : Matrix ι ι ℝ} {V : Matrix κ κ ℝ}
    (hU : U.PosSemidef) (hV : V.PosSemidef) (j : κ) :
    (matrixNormalMeasure M U V).map (fun X => WithLp.toLp 2 fun i => X i j) =
      multivariateGaussian (WithLp.toLp 2 fun i => M i j) (V j j • U) := by
  have h := map_comp_vec_matrixNormalMeasure M hU hV fun i : ι => (j, i)
  have hcov : (V ⊗ₖ U).submatrix (fun i : ι => (j, i)) (fun i => (j, i)) = V j j • U := by
    ext i k
    simp
  simpa [hcov] using h

/-- **Affine transport of matrix normal laws.** The image of a matrix normal matrix `X` under
`X ↦ A * X * B + C` is matrix normal with mean `A * M * B + C`, row covariance `A * U * Aᵀ` and
column covariance `Bᵀ * V * B`. The matrices `A` and `B` may be rectangular and singular. -/
theorem map_mul_mul_add_matrixNormalMeasure (M : Matrix ι κ ℝ) {U : Matrix ι ι ℝ}
    {V : Matrix κ κ ℝ} (hU : U.PosSemidef) (hV : V.PosSemidef) (A : Matrix ι' ι ℝ)
    (B : Matrix κ κ' ℝ) (C : Matrix ι' κ' ℝ) :
    (matrixNormalMeasure M U V).map (fun X => A * X * B + C) =
      matrixNormalMeasure (A * M * B + C) (A * U * Aᵀ) (Bᵀ * V * B) := by
  have hAUA : (A * U * Aᵀ).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hU.mul_mul_conjTranspose_same A
  have hBVB : (Bᵀ * V * B).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hV.conjTranspose_mul_mul_same B
  -- Mathlib's `kronecker_mulVec_vec` produces `A * X * Bᵀ`, so it is applied at `Bᵀ`.
  have hK (X : Matrix ι κ ℝ) : (Bᵀ ⊗ₖ A) *ᵥ X.vec = (A * X * B).vec := by
    simpa using Matrix.kronecker_mulVec_vec A X Bᵀ
  have hL (X : Matrix ι κ ℝ) :
      matrixVecMeasurableEquiv 2 (A * X * B + C) =
        (Bᵀ ⊗ₖ A).toEuclideanLin (matrixVecMeasurableEquiv 2 X) + matrixVecMeasurableEquiv 2 C := by
    simp [hK]
  have hcov : (Bᵀ ⊗ₖ A) * (V ⊗ₖ U) * (Bᵀ ⊗ₖ A)ᵀ = (Bᵀ * V * B) ⊗ₖ (A * U * Aᵀ) := by
    rw [← Matrix.kroneckerMap_transpose, Matrix.transpose_transpose, ← Matrix.mul_kronecker_mul,
      ← Matrix.mul_kronecker_mul]
  have hmap := map_affine_multivariateGaussian (matrixVecMeasurableEquiv 2 M) (hV.kronecker hU)
    (Bᵀ ⊗ₖ A) (matrixVecMeasurableEquiv 2 C)
  rw [← hL M, hcov, matrixVecMeasurableEquiv_apply 2 M,
    matrixVecMeasurableEquiv_apply 2 (A * M * B + C)] at hmap
  -- Under vectorization, `X ↦ A * X * B + C` becomes the affine map of `hmap`.
  have hcomm : (fun X => A * X * B + C) ∘ (matrixVecMeasurableEquiv 2).symm =
      (matrixVecMeasurableEquiv 2).symm ∘
        fun x => (Bᵀ ⊗ₖ A).toEuclideanLin x + matrixVecMeasurableEquiv 2 C := by
    funext x
    apply (matrixVecMeasurableEquiv 2).injective
    rw [Function.comp_apply, Function.comp_apply, hL, MeasurableEquiv.apply_symm_apply,
      MeasurableEquiv.apply_symm_apply]
  have hmeas : Measurable fun X : Matrix ι κ ℝ => A * X * B + C :=
    (((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).add
      continuous_const).measurable
  rw [matrixNormalMeasure_of_posSemidef _ hAUA hBVB, matrixNormalMeasure_of_posSemidef M hU hV,
    Measure.map_map hmeas (MeasurableEquiv.measurable _), hcomm,
    ← Measure.map_map (MeasurableEquiv.measurable _) (by fun_prop)]
  exact congrArg (Measure.map _) hmap

end TauCeti.Probability
