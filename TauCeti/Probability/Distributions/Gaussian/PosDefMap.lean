/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.GeometricMean
public import TauCeti.Probability.Distributions.Gaussian.Affine

import Mathlib.Probability.HasLaw

/-!
# The standard positive matrix between Gaussian laws

A Gaussian law of positive-definite covariance `S` and a Gaussian law of positive-semidefinite
covariance `T` are tied together by an affine map whose linear part is the unique nonnegative
matrix `A` solving `A * S * A = T` for the two covariance matrices.  That matrix is
`geometricMean S⁻¹ʳ T`, the geometric mean of the inverse of `S` and of `T`; it is Hermitian, so it
also solves the congruence `A * S * Aᵀ = T` by
`Matrix.PosDef.mul_mul_conjTranspose_geometricMean`, and the covariance of the image law is
therefore the target covariance.  The matrix itself is written out through square roots by
`Matrix.PosDef.geometricMean_ringInverse_eq_sqrt_mul_mul_sqrt`.

For two nondegenerate Gaussian laws this is the standard positive matrix formula for the Brenier
map between them.

## Main results

* `TauCeti.Probability.affineGeometricMean`,
  `TauCeti.Probability.affineGeometricMean_apply_m₁`,
  `TauCeti.Probability.affineGeometricMean_sub` and
  `TauCeti.Probability.measurable_affineGeometricMean`: the affine map in question, the mean it
  sends `m₁` to, its action on the difference `x - m₁`, and its measurability.
* `TauCeti.Probability.map_affineGeometricMean_multivariateGaussian`: that affine map sends the
  Gaussian law of mean `m₁` and covariance `S` to the Gaussian law of mean `m₂` and covariance
  `T`.
* `TauCeti.Probability.map_geometricMean_multivariateGaussian`: the linear version, between
  centred laws.
* `TauCeti.Probability.hasLaw_affineGeometricMean_multivariateGaussian`: the same statement for
  the law of a random variable.

## References

* M. L. Eaton, *Multivariate Statistics: A Vector Space Approach*.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Ring
open scoped MatrixOrder

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The affine map between two Gaussian laws.** This is the affine map whose linear part is the
positive matrix `geometricMean S⁻¹ʳ T`, and which sends the mean `m₁` to the mean `m₂`.  For a
positive-definite `S` and a positive-semidefinite `T` that linear part is the unique nonnegative
matrix `A` solving `A * S * A = T`; the definition itself needs no positivity hypothesis. -/
def affineGeometricMean (S T : Matrix ι ι ℝ) (m₁ m₂ : EuclideanSpace ℝ ι)
    (x : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι :=
  (geometricMean S⁻¹ʳ T).toEuclideanLin x + (m₂ - (geometricMean S⁻¹ʳ T).toEuclideanLin m₁)

/-- **The map sends the source mean to the target mean.** For any covariances `S` and `T`,
`affineGeometricMean S T m₁ m₂ m₁` is `m₂`. -/
@[simp]
theorem affineGeometricMean_apply_m₁ (S T : Matrix ι ι ℝ) (m₁ m₂ : EuclideanSpace ℝ ι) :
    affineGeometricMean S T m₁ m₂ m₁ = m₂ := by
  simp only [affineGeometricMean]
  rw [add_comm, sub_add_cancel]

/-- **The action on the difference from the source mean.** The linear part
`geometricMean S⁻¹ʳ T` acts on the difference `x - m₁`, and the result is translated by `m₂`. -/
@[simp]
theorem affineGeometricMean_sub (S T : Matrix ι ι ℝ) (m₁ m₂ x : EuclideanSpace ℝ ι) :
    affineGeometricMean S T m₁ m₂ x
      = (geometricMean S⁻¹ʳ T).toEuclideanLin (x - m₁) + m₂ := by
  have hA : (geometricMean S⁻¹ʳ T).toEuclideanLin (x - m₁)
      = (geometricMean S⁻¹ʳ T).toEuclideanLin x
        - (geometricMean S⁻¹ʳ T).toEuclideanLin m₁ := map_sub _ _ _
  simp only [affineGeometricMean]
  rw [hA]
  abel

/-- The affine map between two Gaussian laws is continuous, hence measurable. -/
@[fun_prop]
theorem measurable_affineGeometricMean (S T : Matrix ι ι ℝ) (m₁ m₂ : EuclideanSpace ℝ ι) :
    Measurable (affineGeometricMean S T m₁ m₂) := by
  unfold affineGeometricMean
  fun_prop

/-- **The standard positive matrix between two Gaussians.** For a positive-definite `S₁` and a
positive-semidefinite `S₂` the affine map `affineGeometricMean` carries a Gaussian law of mean
`m₁` and covariance `S₁` onto the Gaussian law of mean `m₂` and covariance `S₂`, because the
covariance of the image law is the congruence `A * S₁ * Aᵀ = S₂` solved by its linear part. -/
@[simp]
theorem map_affineGeometricMean_multivariateGaussian (m₁ m₂ : EuclideanSpace ℝ ι)
    {S₁ S₂ : Matrix ι ι ℝ} (hS₁ : S₁.PosDef) (hS₂ : S₂.PosSemidef) :
    (multivariateGaussian m₁ S₁).map (affineGeometricMean S₁ S₂ m₁ m₂) =
      multivariateGaussian m₂ S₂ := by
  unfold affineGeometricMean
  rw [map_affine_multivariateGaussian m₁ hS₁.posSemidef (geometricMean S₁⁻¹ʳ S₂),
    ← Matrix.conjTranspose_eq_transpose_of_trivial,
    Matrix.PosDef.mul_mul_conjTranspose_geometricMean hS₁ hS₂, add_comm, sub_add_cancel]

/-- **The linear version, between centred laws.** The linear map of the standard positive matrix
carries the centred Gaussian law of covariance `S` onto the centred Gaussian law of covariance
`T`.  This is the linear part of the Brenier map between two nondegenerate Gaussians. -/
@[simp]
theorem map_geometricMean_multivariateGaussian {S₁ S₂ : Matrix ι ι ℝ} (hS₁ : S₁.PosDef)
    (hS₂ : S₂.PosSemidef) :
    (multivariateGaussian 0 S₁).map (geometricMean S₁⁻¹ʳ S₂).toEuclideanLin =
      multivariateGaussian 0 S₂ := by
  have hmap : (fun x : EuclideanSpace ℝ ι => (geometricMean S₁⁻¹ʳ S₂).toEuclideanLin x + 0)
      = (geometricMean S₁⁻¹ʳ S₂).toEuclideanLin := funext fun _ => by rw [add_zero]
  rw [← hmap]
  have h := map_affineGeometricMean_multivariateGaussian 0 0 hS₁ hS₂
  unfold affineGeometricMean at h
  simpa only [map_zero, sub_zero] using h

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → EuclideanSpace ℝ ι}

/-- **The law of the image of a random variable.** A random variable with a Gaussian law of mean
`m₁` and positive-definite covariance `S`, mapped by `affineGeometricMean`, has a Gaussian law of
mean `m₂` and covariance `T`. -/
theorem hasLaw_affineGeometricMean_multivariateGaussian (m₁ m₂ : EuclideanSpace ℝ ι)
    {S₁ S₂ : Matrix ι ι ℝ} (hS₁ : S₁.PosDef) (hS₂ : S₂.PosSemidef)
    (hX : HasLaw X (multivariateGaussian m₁ S₁) P) :
    HasLaw (fun ω => affineGeometricMean S₁ S₂ m₁ m₂ (X ω)) (multivariateGaussian m₂ S₂) P := by
  have hY : HasLaw (affineGeometricMean S₁ S₂ m₁ m₂) (multivariateGaussian m₂ S₂)
      (multivariateGaussian m₁ S₁) := by
    have hmeas : AEMeasurable (affineGeometricMean S₁ S₂ m₁ m₂)
        (multivariateGaussian m₁ S₁) :=
      (measurable_affineGeometricMean S₁ S₂ m₁ m₂).aemeasurable
    have h := hasLaw_map hmeas
    rwa [map_affineGeometricMean_multivariateGaussian m₁ m₂ hS₁ hS₂] at h
  exact hY.fun_comp hX

end TauCeti.Probability
