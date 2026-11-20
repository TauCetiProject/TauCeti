/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Gaussian.Kernel

import TauCeti.Probability.Distributions.Gaussian.Conditional.Basic
import TauCeti.Probability.Distributions.Gaussian.Product
import TauCeti.Probability.Kernel.Randomization

/-!
# The isotropic Gaussian Bayes update

A linear observation of an isotropic Gaussian vector with independent isotropic Gaussian noise
has an isotropic Gaussian posterior. `TauCeti.compProd_gaussianKernel_eq_swap` gives the two
factorizations of the joint law, retaining the case of a point-mass prior. The update underlies
Gaussian denoising posteriors (Ho, Jain and Abbeel, *Denoising Diffusion Probabilistic Models*,
2020, equations (6)–(7)). The block conditional-law formula is
`EuclideanSpace.map_snd_fst_multivariateGaussian`.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Matrix TauCeti.Probability
open scoped MatrixOrder

namespace TauCeti

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local notation "E" => EuclideanSpace ℝ ι
local notation "E₂" => EuclideanSpace ℝ (ι ⊕ ι)
local notation "I" => (1 : Matrix ι ι ℝ)
local notation "split" => (EuclideanSpace.sumEquivProd : E₂ ≃L[ℝ] E × E)

omit [Fintype ι] in
private theorem posSemidef_independentCovariance {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (fromBlocks (u • I) 0 0 (v • I)).PosSemidef := by
  simp only [Matrix.smul_one_eq_diagonal, fromBlocks_diagonal, posSemidef_diagonal_iff]
  intro i
  cases i <;> simp [hu, hv]

private def observationMatrix (c : ℝ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ :=
  fromBlocks I 0 (c • I) I

private theorem split_observationMatrix (c : ℝ) (z : E₂) :
    split ((observationMatrix c).toEuclideanLin z) =
      ((split z).1, c • (split z).1 + (split z).2) := by
  apply Prod.ext <;> ext i <;>
    simp [observationMatrix, Matrix.toEuclideanLin, Matrix.toLpLin_apply, fromBlocks_mulVec,
      Matrix.smul_mulVec]

private theorem observationMatrix_covariance (c u v : ℝ) :
    observationMatrix c * fromBlocks (u • I) 0 0 (v • I) * (observationMatrix c).transpose =
      fromBlocks (u • I) ((c * u) • I) ((c * u) • I) ((c ^ 2 * u + v) • I) := by
  simp only [observationMatrix, fromBlocks_multiply, fromBlocks_transpose, transpose_smul,
    transpose_one, transpose_zero, Matrix.mul_one, Matrix.mul_zero,
    add_zero, zero_add, smul_zero, Matrix.mul_smul, smul_smul, ← add_smul]
  congr 2 <;> ring

private theorem compProd_gaussianKernel_eq_map_observation (m : E) {u v : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (c : ℝ) :
    multivariateGaussian m (u • I) ⊗ₘ gaussianKernel c v =
      (multivariateGaussian ((split).symm (m, c • m))
        (fromBlocks (u • I) ((c * u) • I) ((c * u) • I) ((c ^ 2 * u + v) • I))).map split := by
  have hv' : (v • I).PosSemidef := Matrix.PosSemidef.one.smul hv
  have hprod := (gaussianKernel (ι := ι) c v).map_prod_eq_compProd_of_map
    (μ := multivariateGaussian m (u • I)) (multivariateGaussian 0 (v • I))
    (fun x e ↦ c • x + e) (by fun_prop) (fun x ↦ by
      simpa only [one_pow, one_smul, smul_zero, add_zero, gaussianKernel_apply] using
        map_add_smul_multivariateGaussian 0 hv' (c • x) 1)
  have hmean : (observationMatrix c).toEuclideanLin ((split).symm (m, 0)) =
      (split).symm (m, c • m) := by
    apply (split).injective
    simp only [split_observationMatrix, ContinuousLinearEquiv.apply_symm_apply, add_zero]
  have hD := posSemidef_independentCovariance (ι := ι) hu hv
  have hblocks := map_sumEquivProd_multivariateGaussian_of_submatrix_eq_zero
    ((split).symm (m, 0)) hD (by rw [← toBlocks₁₂_eq_submatrix, toBlocks_fromBlocks₁₂])
  simp only [ContinuousLinearEquiv.apply_symm_apply, ← toBlocks₁₁_eq_submatrix,
    ← toBlocks₂₂_eq_submatrix, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₂₂] at hblocks
  have hmap := map_affine_multivariateGaussian ((split).symm (m, 0)) hD (observationMatrix c) 0
  simp only [add_zero, hmean, observationMatrix_covariance] at hmap
  rw [← hprod, ← hblocks, ← hmap,
    Measure.map_map (by fun_prop) (by fun_prop), Measure.map_map (by fun_prop) (by fun_prop)]
  simp_rw [Function.comp_def, split_observationMatrix]

private theorem gaussianCondKernel_observation_apply (m : E) {u v : ℝ} (c : ℝ)
    (hpos : 0 < c ^ 2 * u + v) (y : E) :
    let w := c ^ 2 * u + v
    ((split).symm (m, c • m)).gaussianCondKernel
        (fromBlocks (u • I) ((c * u) • I) ((c * u) • I) (w • I)) y =
      multivariateGaussian (m + (c * u / w) • (y - c • m)) ((u * v / w) • I) := by
  dsimp only
  set w := c ^ 2 * u + v with hw
  have hblock : ((fromBlocks (u • I) ((c * u) • I) ((c * u) • I) (w • I)).submatrix
      Sum.inr Sum.inr).PosDef := by
    rw [← toBlocks₂₂_eq_submatrix, toBlocks_fromBlocks₂₂]
    exact Matrix.PosDef.one.smul hpos
  have hinv : (w • I)⁻¹ = w⁻¹ • I := by
    apply Matrix.inv_eq_left_inv
    simp [smul_smul, hpos.ne']
  have hcov : u - c * u * (w⁻¹ * (c * u)) = u * v / w := by
    field_simp
    rw [hw]
    ring
  rw [EuclideanSpace.gaussianCondKernel_apply, EuclideanSpace.gaussianCondMean_of_posDef _ hblock,
    Matrix.gaussianCondCov_of_posDef hblock]
  simp only [ContinuousLinearEquiv.apply_symm_apply, ← toBlocks₁₁_eq_submatrix,
    ← toBlocks₁₂_eq_submatrix, ← toBlocks₂₁_eq_submatrix, ← toBlocks₂₂_eq_submatrix,
    toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂,
    hinv, Matrix.mul_smul, Matrix.mul_one, smul_smul, ← sub_smul, hcov]
  simp [div_eq_mul_inv, mul_comm w⁻¹ (c * u)]

/-- The joint law formed from an isotropic Gaussian prior with variance `u` and the Gaussian
observation kernel with noise variance `v` factors in the reverse order: the observation has
variance `w = c ^ 2 * u + v`, and the posterior has variance `u * v / w` and regression
coefficient `c * u / w`. The posterior formula also applies to a Dirac prior (`u = 0`). -/
theorem compProd_gaussianKernel_eq_swap (m : E) {u v : ℝ} (hu : 0 ≤ u) (hv : 0 < v) (c : ℝ) :
    let w := c ^ 2 * u + v
    multivariateGaussian m (u • I) ⊗ₘ gaussianKernel c v =
      (multivariateGaussian (c • m) (w • I) ⊗ₘ
        multivariateGaussianKernel (fun y ↦ m + (c * u / w) • (y - c • m))
          (fun _ ↦ (u * v / w) • I) (by fun_prop) measurable_const).map Prod.swap := by
  dsimp only
  let S := fromBlocks (u • I) ((c * u) • I) ((c * u) • I) ((c ^ 2 * u + v) • I)
  have hS : S.PosSemidef := by
    simpa only [S, Matrix.conjTranspose_eq_transpose_of_trivial, observationMatrix_covariance] using
      (posSemidef_independentCovariance (ι := ι) hu hv.le).mul_mul_conjTranspose_same
        (observationMatrix c)
  have hcond := ((split).symm (m, c • m)).map_snd_fst_multivariateGaussian hS
  have hpos : 0 < c ^ 2 * u + v := add_pos_of_nonneg_of_pos (mul_nonneg (sq_nonneg c) hu) hv
  have hk : ((split).symm (m, c • m)).gaussianCondKernel S = multivariateGaussianKernel
      (fun y ↦ m + (c * u / (c ^ 2 * u + v)) • (y - c • m))
      (fun _ ↦ (u * v / (c ^ 2 * u + v)) • I) (by fun_prop) measurable_const := by
    ext1 y
    rw [multivariateGaussianKernel_apply]
    exact gaussianCondKernel_observation_apply m c hpos y
  simp only [hk, ContinuousLinearEquiv.apply_symm_apply, S, ← toBlocks₂₂_eq_submatrix,
    toBlocks_fromBlocks₂₂] at hcond
  rw [compProd_gaussianKernel_eq_map_observation m hu hv.le c, ← hcond,
    Measure.map_map measurable_swap (by fun_prop)]
  rfl

end TauCeti
