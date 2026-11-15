/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Gaussian.ProperComplex.PDF
public import TauCeti.Probability.Distributions.Gaussian.ProperComplex.Affine
import TauCeti.MeasureTheory.Measure.PiWithDensity

/-!
# Products of standard proper complex Gaussian laws

The identity-covariance proper complex Gaussian is the product of its scalar coordinate laws.
Consequently complex linear maps of independent standard coordinates have covariance `L * Lᴴ`.
This identifies independent-entry matrix models with the multivariate Gaussian model and supplies
their unitary invariance, including empty coordinate types and singular linear images.

## References

* D. Tse and P. Viswanath, *Fundamentals of Wireless Communication*, Cambridge University
  Press, 2005, appendix A.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ComplexOrder Matrix

namespace TauCeti.Probability

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- Independent standard proper complex Gaussian coordinates form the identity-covariance
proper complex Gaussian vector. -/
theorem properComplexGaussianMeasure_one_eq_pi :
    properComplexGaussianMeasure (0 : ι → ℂ) 1 =
      Measure.pi (fun _ : ι ↦ properComplexGaussianScalar) := by
  let f := fun z : ℂ ↦ ENNReal.ofReal (Real.exp (-‖z‖ ^ 2) / Real.pi)
  have hf : Measurable f := by fun_prop
  let _ : SigmaFinite (volume.withDensity f) := by
    rw [← properComplexGaussianScalar_eq_withDensity]
    infer_instance
  rw [properComplexGaussianMeasure_eq_withDensity _ Matrix.PosDef.one,
    properComplexGaussianScalar_eq_withDensity, pi_withDensity (fun _ : ι ↦ volume)
      (fun _ ↦ hf), ← volume_pi]
  apply withDensity_congr_ae
  filter_upwards [] with z
  rw [properComplexGaussianPDF_one]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i (_ : i ∈ Finset.univ) ↦
    (div_nonneg (Real.exp_pos (-‖z i‖ ^ 2)).le Real.pi_pos.le))]
  simp [Finset.prod_div_distrib, ← Real.exp_sum, ← Finset.sum_neg_distrib]

omit [DecidableEq ι] in
/-- A complex linear image of independent standard coordinates has covariance `L * Lᴴ`.
The target dimension may exceed the source dimension. -/
theorem map_mulVec_pi_properComplexGaussianScalar (L : Matrix κ ι ℂ) :
    (Measure.pi fun _ : ι ↦ properComplexGaussianScalar).map (fun z ↦ L *ᵥ z) =
      properComplexGaussianMeasure 0 (L * Lᴴ) := by
  classical
  rw [← properComplexGaussianMeasure_one_eq_pi]
  simpa only [Matrix.mul_one, Matrix.mulVec_zero, add_zero] using
    map_affine_properComplexGaussianMeasure (0 : ι → ℂ) Matrix.PosSemidef.one L 0

omit [DecidableEq ι] in
/-- A complex matrix with orthonormal rows sends standard proper Gaussian coordinates to
independent standard proper Gaussian coordinates. -/
theorem map_mulVec_pi_properComplexGaussianScalar_of_mul_conjTranspose_eq_one
    (L : Matrix κ ι ℂ) (hL : L * Lᴴ = 1) :
    (Measure.pi fun _ : ι ↦ properComplexGaussianScalar).map (fun z ↦ L *ᵥ z) =
      Measure.pi (fun _ : κ ↦ properComplexGaussianScalar) := by
  classical
  rw [map_mulVec_pi_properComplexGaussianScalar, hL,
    properComplexGaussianMeasure_one_eq_pi]

end TauCeti.Probability
