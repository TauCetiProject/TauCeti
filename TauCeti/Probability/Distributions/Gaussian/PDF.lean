/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Probability.Density
public import Mathlib.Probability.Distributions.Gaussian.Real
/-!
# Density API for the real Gaussian distribution

This file connects nondegenerate real Gaussian laws to `HasPDF` and identifies `pdf` at every
variance, including the singular zero-variance boundary. It also computes the logarithm of the
density and, for a nonzero variance, writes the real mass of a set as the integral of the density
over it (`measureReal_gaussianReal_eq_setIntegral`).
-/
public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real
namespace TauCeti.Probability
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}
/-- A variable with a nondegenerate Gaussian law has a density.

`v ≠ 0` is required, not merely convenient: `gaussianReal m 0` is `Measure.dirac m`, which is
singular with respect to `volume`. -/
theorem hasPDF_of_hasLaw_gaussianReal {m : ℝ} {v : ℝ≥0} (hv : v ≠ 0)
    (hX : HasLaw X (gaussianReal m v) P) : HasPDF X P :=
  hasPDF_of_hasLaw_withDensity (measurable_gaussianPDF m v).aemeasurable
    (by rwa [gaussianReal_of_var_ne_zero _ hv] at hX)
/-- The density of a Gaussian law is `gaussianPDF`, at **every** variance. -/
theorem pdf_eq_gaussianPDF_of_hasLaw_gaussianReal {m : ℝ} {v : ℝ≥0}
    (hX : HasLaw X (gaussianReal m v) P) : pdf X P =ᵐ[volume] gaussianPDF m v := by
  rw [pdf_def, hX.map_eq]
  exact rnDeriv_gaussianReal m v
/-- The logarithm of the Gaussian density is
`log (gaussianPDFReal m w y) = -log (2πw) / 2 - (y - m)² / (2w)`. At `w = 0` both sides are `0`,
since `Real.log 0 = 0` and division by `0` gives `0`. -/
theorem log_gaussianPDFReal (m : ℝ) (w : ℝ≥0) (y : ℝ) :
    Real.log (gaussianPDFReal m w y) = -Real.log (2 * π * w) / 2 - (y - m) ^ 2 / (2 * w) := by
  rcases eq_or_ne w 0 with rfl | hw
  · simp [gaussianPDFReal_zero_var]
  rw [gaussianPDFReal_def, Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_inv,
    Real.log_sqrt (by positivity), Real.log_exp]
  ring
/-- For a nonzero variance, the real mass of a set `s` under `gaussianReal m v` is the integral
of the Gaussian density over `s`. -/
theorem measureReal_gaussianReal_eq_setIntegral (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (s : Set ℝ) :
    (gaussianReal m v).real s = ∫ t in s, gaussianPDFReal m v t := by
  rw [measureReal_def, gaussianReal_apply_eq_integral m hv,
    ENNReal.toReal_ofReal (integral_nonneg fun t => gaussianPDFReal_nonneg m v t)]
end TauCeti.Probability
