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

## Main results

* `TauCeti.Probability.map_affine_multivariateGaussian`: the affine pushforward formula for a
  multivariate
  Gaussian measure.
* `TauCeti.Probability.map_comp_multivariateGaussian`: reindexing the coordinates along a map of
  index types.
* `TauCeti.Probability.multivariateGaussian_one_eq_map_pi`: the identity-covariance law as a
  product of its Gaussian coordinate laws.

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

/-- Reading the coordinates of a multivariate Gaussian vector along a map of index types gives the
multivariate Gaussian with the reindexed mean and covariance. The map need not be injective, so
coordinates may be repeated or omitted. -/
theorem map_comp_multivariateGaussian (m : EuclideanSpace ℝ ι) {S : Matrix ι ι ℝ}
    (hS : S.PosSemidef) (f : κ → ι) :
    (multivariateGaussian m S).map (fun x => WithLp.toLp 2 fun k => x (f k)) =
      multivariateGaussian (WithLp.toLp 2 fun k => m (f k)) (S.submatrix f f) := by
  let L : Matrix κ ι ℝ := (1 : Matrix ι ι ℝ).submatrix f id
  have hL (x : EuclideanSpace ℝ ι) : L.toEuclideanLin x = WithLp.toLp 2 fun k => x (f k) := by
    ext k
    simp [L, Matrix.mulVec, dotProduct, Matrix.one_apply]
  have hcov : L * S * L.transpose = S.submatrix f f := by
    ext
    simp [L, Matrix.mul_apply, Matrix.one_apply]
  simpa [hL, hcov] using map_affine_multivariateGaussian m hS L 0

/-- An identity-covariance Gaussian is the product of its unit-variance Gaussian coordinate
laws, transported to Euclidean space. -/
theorem multivariateGaussian_one_eq_map_pi (m : EuclideanSpace ℝ ι) :
    multivariateGaussian m (1 : Matrix ι ι ℝ) =
      (Measure.pi fun i ↦ gaussianReal (m i) 1).map (WithLp.toLp 2) := by
  have hshift : (Measure.pi fun _ : ι ↦ gaussianReal 0 1).map
      (fun x i ↦ m i + x i) = Measure.pi fun i ↦ gaussianReal (m i) 1 := by
    rw [Measure.pi_map_pi (fun _ ↦ by fun_prop)]
    simp only [gaussianReal_map_const_add, zero_add]
  have hmean : multivariateGaussian m (1 : Matrix ι ι ℝ) =
      (stdGaussian (EuclideanSpace ℝ ι)).map (fun x ↦ m + x) := by
    simpa [add_comm] using
      (map_affine_multivariateGaussian (0 : EuclideanSpace ℝ ι) Matrix.PosSemidef.one 1 m).symm
  rw [hmean, ← map_pi_eq_stdGaussian, ← hshift,
    Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)]
  apply congrArg (fun f ↦ (Measure.pi fun _ : ι ↦ gaussianReal 0 1).map f)
  funext x
  simpa only [Function.comp_apply, WithLp.toLp_ofLp, Pi.add_def] using
    (WithLp.toLp_add 2 m.ofLp x).symm

end TauCeti.Probability
