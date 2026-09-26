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
# The standard positive matrix between two nondegenerate Gaussian laws

Two nondegenerate Gaussian laws are tied together by an affine map whose linear part is the
unique nonnegative matrix `A` solving `A * S * A = T` for the two covariance matrices.  That
matrix is the geometric mean of `S` and `T`; it is Hermitian, so it also solves the congruence
`A * S * Aᵀ = T` by `Matrix.PosDef.mul_mul_conjTranspose_geometricMean`, and the covariance of
the image law is therefore the target covariance.  The matrix itself is written out through
square roots by `Matrix.PosDef.geometricMean_ringInverse_eq_sqrt_mul_mul_sqrt`.

This is the standard positive matrix formula for the Brenier map between two Gaussians.

## Main results

* `TauCeti.Probability.affineGeometricMean` and
  `TauCeti.Probability.measurable_affineGeometricMean`: the affine map in question, and its
  measurability.
* `TauCeti.Probability.map_affineGeometricMean_multivariateGaussian`: that affine map sends the
  Gaussian law of mean `m₁` and covariance `S` to the Gaussian law of mean `m₂` and covariance
  `T`.
* `TauCeti.Probability.map_geometricMean_multivariateGaussian`: the linear version, between
  centred laws.
* `TauCeti.Probability.hasLaw_affineGeometricMean_multivariateGaussian`: the same statement for
  the law of a random variable.

## References

* M. L. Eaton, *Multivariate Statistics: A Vector Space Approach*.
* `TauCetiRoadmap/OptimalTransport/README.md`, Layer 5, item 3.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Ring
open scoped MatrixOrder

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The affine map between two nondegenerate Gaussian laws.** This is the affine map whose linear
part is the positive matrix `geometricMean S⁻¹ʳ T`, the unique nonnegative matrix `A` solving
`A * S * A = T`, and which sends the mean `m₁` to the mean `m₂`. -/
def affineGeometricMean (S T : Matrix ι ι ℝ) (m₁ m₂ : EuclideanSpace ℝ ι)
    (x : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι :=
  (geometricMean S⁻¹ʳ T).toEuclideanLin x + (m₂ - (geometricMean S⁻¹ʳ T).toEuclideanLin m₁)

/-- The affine map between two nondegenerate Gaussian laws is continuous, hence measurable. -/
@[fun_prop]
theorem measurable_affineGeometricMean (S T : Matrix ι ι ℝ) (m₁ m₂ : EuclideanSpace ℝ ι) :
    Measurable (affineGeometricMean S T m₁ m₂) := by
  change Measurable (fun x : EuclideanSpace ℝ ι =>
    (geometricMean S⁻¹ʳ T).toEuclideanLin x + (m₂ - (geometricMean S⁻¹ʳ T).toEuclideanLin m₁))
  fun_prop

/-- **The standard positive matrix between two nondegenerate Gaussians.** The affine map
`affineGeometricMean` carries a Gaussian law of covariance `S` onto the Gaussian law of
covariance `T`, because the covariance of the image law is the congruence `A * S * Aᵀ = T` solved
by its linear part. -/
theorem map_affineGeometricMean_multivariateGaussian (m₁ m₂ : EuclideanSpace ℝ ι)
    {S₁ S₂ : Matrix ι ι ℝ} (hS₁ : S₁.PosDef) (hS₂ : S₂.PosDef) :
    (multivariateGaussian m₁ S₁).map (affineGeometricMean S₁ S₂ m₁ m₂) =
      multivariateGaussian m₂ S₂ := by
  change (multivariateGaussian m₁ S₁).map
      (fun x : EuclideanSpace ℝ ι => (geometricMean S₁⁻¹ʳ S₂).toEuclideanLin x
        + (m₂ - (geometricMean S₁⁻¹ʳ S₂).toEuclideanLin m₁)) = _
  rw [map_affine_multivariateGaussian m₁ hS₁.posSemidef (geometricMean S₁⁻¹ʳ S₂),
    ← Matrix.conjTranspose_eq_transpose_of_trivial,
    Matrix.PosDef.mul_mul_conjTranspose_geometricMean hS₁ hS₂, add_comm, sub_add_cancel]

/-- **The linear version, between centred laws.** The linear map of the standard positive matrix
carries the centred Gaussian law of covariance `S` onto the centred Gaussian law of covariance
`T`.  This is the linear part of the Brenier map between two nondegenerate Gaussians. -/
theorem map_geometricMean_multivariateGaussian {S₁ S₂ : Matrix ι ι ℝ} (hS₁ : S₁.PosDef)
    (hS₂ : S₂.PosDef) :
    (multivariateGaussian 0 S₁).map (geometricMean S₁⁻¹ʳ S₂).toEuclideanLin =
      multivariateGaussian 0 S₂ := by
  have hmap : (fun x : EuclideanSpace ℝ ι => (geometricMean S₁⁻¹ʳ S₂).toEuclideanLin x + 0)
      = (geometricMean S₁⁻¹ʳ S₂).toEuclideanLin := funext fun _ => by rw [add_zero]
  rw [← hmap]
  have h := map_affineGeometricMean_multivariateGaussian 0 0 hS₁ hS₂
  change (multivariateGaussian 0 S₁).map
      (fun x : EuclideanSpace ℝ ι => (geometricMean S₁⁻¹ʳ S₂).toEuclideanLin x
        + (0 - (geometricMean S₁⁻¹ʳ S₂).toEuclideanLin 0)) = _ at h
  simpa only [map_zero, sub_zero] using h

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → EuclideanSpace ℝ ι}

/-- **The law of the image of a random variable.** A random variable with a nondegenerate Gaussian
law of mean `m₁` and covariance `S`, mapped by `affineGeometricMean`, has a nondegenerate
Gaussian law of mean `m₂` and covariance `T`. -/
theorem hasLaw_affineGeometricMean_multivariateGaussian (m₁ m₂ : EuclideanSpace ℝ ι)
    {S₁ S₂ : Matrix ι ι ℝ} (hS₁ : S₁.PosDef) (hS₂ : S₂.PosDef)
    (hX : HasLaw X (multivariateGaussian m₁ S₁) P) :
    HasLaw (fun ω => affineGeometricMean S₁ S₂ m₁ m₂ (X ω)) (multivariateGaussian m₂ S₂) P := by
  refine ⟨AEMeasurable.comp_aemeasurable'
      (measurable_affineGeometricMean S₁ S₂ m₁ m₂).aemeasurable hX.aemeasurable, ?_⟩
  calc P.map (fun ω => affineGeometricMean S₁ S₂ m₁ m₂ (X ω))
      = P.map (affineGeometricMean S₁ S₂ m₁ m₂ ∘ X) := rfl
    _ = (P.map X).map (affineGeometricMean S₁ S₂ m₁ m₂) :=
      (AEMeasurable.map_map_of_aemeasurable
        (measurable_affineGeometricMean S₁ S₂ m₁ m₂).aemeasurable hX.aemeasurable).symm
    _ = (multivariateGaussian m₁ S₁).map (affineGeometricMean S₁ S₂ m₁ m₂) := by rw [hX.map_eq]
    _ = multivariateGaussian m₂ S₂ :=
      map_affineGeometricMean_multivariateGaussian m₁ m₂ hS₁ hS₂

end TauCeti.Probability
