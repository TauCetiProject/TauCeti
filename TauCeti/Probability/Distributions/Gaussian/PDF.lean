/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Probability.Density
public import Mathlib.Probability.Distributions.Gaussian.Real
/-! # Density API for the real Gaussian distribution -/
public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
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
end TauCeti.Probability
