/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Gaussian.Multivariate

import Mathlib.Probability.Distributions.Gaussian.CharFun
import Mathlib.Probability.Distributions.Gaussian.Fernique

/-!
# Affine images of multivariate Gaussian measures

This file proves that a multivariate Gaussian measure is carried by a rectangular affine map to
the multivariate Gaussian with the transformed mean and covariance.  Rectangular matrices are
allowed, so the result applies both to embeddings and to possibly singular projections.

## Main result

* `TauCeti.Probability.map_affine_multivariateGaussian`: the affine pushforward formula for a
  multivariate
  Gaussian measure.

## References

* M. L. Eaton, *Multivariate Statistics: A Vector Space Approach*.
* `TauCetiRoadmap/StandardDistributions/README.md`, Layer 5, item 3, **Affine maps of Gaussian
  laws**.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped MatrixOrder RealInnerProductSpace

namespace TauCeti.Probability

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- The covariance form of an affine image of a multivariate Gaussian is the one belonging to the
congruated matrix `L * S * Lᵀ`. The map `L` may be rectangular; no rank hypothesis is needed. -/
private theorem covarianceBilin_map_affine_multivariateGaussian (m : EuclideanSpace ℝ ι)
    {S : Matrix ι ι ℝ} (hS : S.PosSemidef) (L : Matrix κ ι ℝ) (c : EuclideanSpace ℝ κ) :
    covarianceBilin
        (((multivariateGaussian m S).map L.toEuclideanLin.toContinuousLinearMap).map
          fun y => y + c) =
      covarianceBilin
        (multivariateGaussian (L.toEuclideanLin m + c) (L * S * L.transpose)) := by
  simp_rw [add_comm _ c]
  rw [covarianceBilin_map_const_add]
  have hLS : (L * S * L.transpose).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hS.mul_mul_conjTranspose_same L
  ext x y
  rw [covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id,
    covariance_map (by fun_prop) (by fun_prop) (by fun_prop),
    covarianceBilin_multivariateGaussian hLS]
  exact covariance_inner_matrix_multivariateGaussian m hS L L x y

/-- The image of a multivariate Gaussian under a rectangular affine map is the multivariate
Gaussian with the corresponding transformed mean and covariance. -/
@[simp]
theorem map_affine_multivariateGaussian (m : EuclideanSpace ℝ ι) {S : Matrix ι ι ℝ}
    (hS : S.PosSemidef) (L : Matrix κ ι ℝ) (c : EuclideanSpace ℝ κ) :
    (multivariateGaussian m S).map (fun x => L.toEuclideanLin x + c) =
      multivariateGaussian (L.toEuclideanLin m + c) (L * S * L.transpose) := by
  let T : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ κ :=
    L.toEuclideanLin.toContinuousLinearMap
  -- Separate the linear image from the translation so that Mathlib's covariance rules apply.
  have h_map :
      (multivariateGaussian m S).map (fun x => L.toEuclideanLin x + c) =
        ((multivariateGaussian m S).map T).map (fun y => y + c) := by
    rw [Measure.map_map]
    · refine congrArg (fun f => (multivariateGaussian m S).map f) ?_
      funext x
      simp only [T, Function.comp_apply, LinearMap.coe_toContinuousLinearMap']
    · fun_prop
    · fun_prop
  rw [h_map]
  -- Gaussian measures are determined by their mean and covariance bilinear form.
  apply IsGaussian.ext
  · rw [integral_map]
    · simp only [id_eq]
      rw [integral_id_multivariateGaussian]
      calc
        ∫ x, x + c ∂(multivariateGaussian m S).map T =
            (∫ x, x ∂(multivariateGaussian m S).map T) +
              ∫ _x, c ∂(multivariateGaussian m S).map T :=
          integral_add IsGaussian.integrable_id (integrable_const c)
        _ = T m + c := by
          rw [T.integral_id_map IsGaussian.integrable_id, integral_id_multivariateGaussian,
            integral_const]
          simp
        _ = L.toEuclideanLin m + c := by
          simp only [T, LinearMap.coe_toContinuousLinearMap']
    · fun_prop
    · fun_prop
  · exact covarianceBilin_map_affine_multivariateGaussian m hS L c

end TauCeti.Probability
