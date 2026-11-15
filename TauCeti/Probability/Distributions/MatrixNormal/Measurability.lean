/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.MatrixNormal.Basic

import Mathlib.Analysis.Matrix.Order
import TauCeti.Topology.Instances.Matrix

/-!
# Parameter measurability of matrix normal laws

Matrix normal laws depend measurably on their mean and on every entry of their row and column
covariance parameters. The result covers the full totalized family: positive semidefinite
covariances give the Gaussian vectorization, while every invalid parameter gives the prescribed
Dirac fallback at the mean.

This measurability result allows matrix-valued parameter maps to define kernels without first
restricting their domain to the positive semidefinite cones.

## References

* A. K. Gupta and D. K. Nagar, *Matrix Variate Distributions*, Chapman & Hall/CRC, 2000,
  chapter 2, for the Gaussian vectorization of the matrix normal law.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped Kronecker

namespace TauCeti.Probability

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- The full totalized matrix normal family is jointly measurable in its mean and in the entries
of its row and column covariance parameters. No positivity or nonsingularity assumption is
needed. -/
@[fun_prop]
theorem measurable_matrixNormalMeasure :
    Measurable fun p : (ι → κ → ℝ) × (ι → ι → ℝ) × (κ → κ → ℝ) =>
      matrixNormalMeasure (Matrix.of p.1) (Matrix.of p.2.1) (Matrix.of p.2.2) := by
  classical
  have hmean : Measurable fun p : (ι → κ → ℝ) × (ι → ι → ℝ) × (κ → κ → ℝ) =>
      matrixVecMeasurableEquiv 2 (Matrix.of p.1) :=
    (matrixVecMeasurableEquiv 2).measurable.comp
      ((Matrix.measurable_of ι κ ℝ).comp measurable_fst)
  have hcov : Measurable fun p : (ι → κ → ℝ) × (ι → ι → ℝ) × (κ → κ → ℝ) =>
      Matrix.of p.2.2 ⊗ₖ Matrix.of p.2.1 := by
    fun_prop
  have hsource : Measurable fun p : (ι → κ → ℝ) × (ι → ι → ℝ) × (κ → κ → ℝ) =>
      multivariateGaussian (matrixVecMeasurableEquiv 2 (Matrix.of p.1))
        (Matrix.of p.2.2 ⊗ₖ Matrix.of p.2.1) :=
    measurable_multivariateGaussian.comp (hmean.prodMk hcov)
  have hgaussian : Measurable fun p : (ι → κ → ℝ) × (ι → ι → ℝ) × (κ → κ → ℝ) =>
      (multivariateGaussian (matrixVecMeasurableEquiv 2 (Matrix.of p.1))
        (Matrix.of p.2.2 ⊗ₖ Matrix.of p.2.1)).map (matrixVecMeasurableEquiv 2).symm :=
    (Measure.measurable_map _ (matrixVecMeasurableEquiv 2).symm.measurable).comp hsource
  have hvalid : MeasurableSet
      {p : (ι → κ → ℝ) × (ι → ι → ℝ) × (κ → κ → ℝ) |
        (Matrix.of p.2.1).PosSemidef ∧ (Matrix.of p.2.2).PosSemidef} :=
    ((_root_.isClosed_setOfPred_posSemidef (n := ι) (R := ℝ)).measurableSet.preimage
        ((Matrix.measurable_of ι ι ℝ).comp measurable_snd.fst)).inter
      ((_root_.isClosed_setOfPred_posSemidef (n := κ) (R := ℝ)).measurableSet.preimage
        ((Matrix.measurable_of κ κ ℝ).comp measurable_snd.snd))
  have hdirac : Measurable fun p : (ι → κ → ℝ) × (ι → ι → ℝ) × (κ → κ → ℝ) =>
      Measure.dirac (Matrix.of p.1) :=
    Measure.measurable_dirac.comp ((Matrix.measurable_of ι κ ℝ).comp measurable_fst)
  have hformula :
      (fun p : (ι → κ → ℝ) × (ι → ι → ℝ) × (κ → κ → ℝ) =>
        matrixNormalMeasure (Matrix.of p.1) (Matrix.of p.2.1) (Matrix.of p.2.2)) =
      fun p => if (Matrix.of p.2.1).PosSemidef ∧ (Matrix.of p.2.2).PosSemidef then
        (multivariateGaussian (matrixVecMeasurableEquiv 2 (Matrix.of p.1))
          (Matrix.of p.2.2 ⊗ₖ Matrix.of p.2.1)).map (matrixVecMeasurableEquiv 2).symm
      else Measure.dirac (Matrix.of p.1) := by
    funext p
    by_cases h : (Matrix.of p.2.1).PosSemidef ∧ (Matrix.of p.2.2).PosSemidef
    · rw [matrixNormalMeasure_of_posSemidef _ h.1 h.2, ite_eq_left h,
        matrixVecMeasurableEquiv_apply]
    · rw [matrixNormalMeasure_of_not_posSemidef _ h, ite_eq_right h]
  rw [hformula]
  exact Measurable.ite hvalid hgaussian hdirac

end TauCeti.Probability
