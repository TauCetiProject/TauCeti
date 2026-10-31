/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Gaussian.Conditional.Basic
import TauCeti.Topology.Instances.Matrix

/-!
# Measurability of conditional Gaussian parameters

The pseudoinverse regression mean, generalized Schur complement, and resulting conditional
Gaussian law depend measurably on the mean, covariance entries, and observed value. These
statements hold on the entire parameter space, so restricting to positive-semidefinite joint
covariances gives a measurable family of conditional probability laws even when rank changes.
The formula specifies a Gaussian kernel at observations outside the affine support as well.

The proofs combine `Matrix.measurable_covariancePseudoInverse` with polynomial matrix operations
and `ProbabilityTheory.measurable_multivariateGaussian`. Measurability does not assert continuity
at a change of covariance rank.
-/

public section

open MeasureTheory ProbabilityTheory

variable {ι κ : Type*} [Fintype κ] [DecidableEq κ]

namespace Matrix

/-- The generalized conditional covariance is measurable in the joint covariance entries. -/
@[fun_prop]
theorem measurable_gaussianCondCov [Finite ι] :
    Measurable (fun S : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ => S.gaussianCondCov) := by
  have hP : Measurable fun S : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ =>
      (S.submatrix Sum.inr Sum.inr).covariancePseudoInverse :=
    Matrix.measurable_covariancePseudoInverse.comp (continuous_id.matrix_submatrix _ _).measurable
  have hpoly : Continuous fun q : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ × Matrix κ κ ℝ =>
      q.1.submatrix Sum.inl Sum.inl - q.1.submatrix Sum.inl Sum.inr * q.2 *
        q.1.submatrix Sum.inr Sum.inl := by fun_prop
  simpa only [Matrix.gaussianCondCov_def, Function.comp_def, id_eq] using
    hpoly.measurable.comp (measurable_id.prodMk hP)

end Matrix

namespace EuclideanSpace

variable [Fintype ι]

/-- The regression mean is jointly measurable in mean, covariance, and observed value. -/
@[fun_prop]
theorem measurable_gaussianCondMean : Measurable fun q : (EuclideanSpace ℝ (ι ⊕ κ) ×
      Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) × EuclideanSpace ℝ κ =>
      q.1.1.gaussianCondMean q.1.2 q.2 := by
  have hP : Measurable fun q : (EuclideanSpace ℝ (ι ⊕ κ) ×
      Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) × EuclideanSpace ℝ κ =>
      (q.1.2.submatrix Sum.inr Sum.inr).covariancePseudoInverse :=
    Matrix.measurable_covariancePseudoInverse.comp
      (continuous_fst.snd.matrix_submatrix _ _).measurable
  have hpoly : Continuous fun q : ((EuclideanSpace ℝ (ι ⊕ κ) ×
      Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) × EuclideanSpace ℝ κ) × Matrix κ κ ℝ =>
      (EuclideanSpace.sumEquivProd q.1.1.1).1 +
        (q.1.1.2.submatrix Sum.inl Sum.inr * q.2).toEuclideanLin
          (q.1.2 - (EuclideanSpace.sumEquivProd q.1.1.1).2) := by
    simp only [Matrix.toLpLin_apply]
    fun_prop
  simpa only [gaussianCondMean_def, Function.comp_def, id_eq] using
    hpoly.measurable.comp (measurable_id.prodMk hP)

/-- The conditional Gaussian law is jointly measurable in mean, covariance entries, and
observed value, including singular covariance blocks. -/
@[fun_prop]
theorem measurable_gaussianCondKernel [DecidableEq ι] :
    Measurable fun q : (EuclideanSpace ℝ (ι ⊕ κ) × ((ι ⊕ κ) → (ι ⊕ κ) → ℝ)) ×
        EuclideanSpace ℝ κ => q.1.1.gaussianCondKernel (Matrix.of q.1.2) q.2 := by
  have hparameters : Measurable fun q : (EuclideanSpace ℝ (ι ⊕ κ) ×
      ((ι ⊕ κ) → (ι ⊕ κ) → ℝ)) × EuclideanSpace ℝ κ =>
      ((q.1.1, Matrix.of q.1.2), q.2) := by fun_prop
  have hmean := (measurable_gaussianCondMean (ι := ι) (κ := κ)).comp hparameters
  have hcov := (Matrix.measurable_gaussianCondCov (ι := ι) (κ := κ)).comp hparameters.fst.snd
  simpa only [gaussianCondKernel_apply, Function.comp_def, Function.uncurry_apply_pair] using
    measurable_multivariateGaussian.comp (hmean.prodMk hcov)

end EuclideanSpace
