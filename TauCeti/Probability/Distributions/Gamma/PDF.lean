/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Probability.Density
public import Mathlib.Probability.Distributions.Gamma

/-! # Density API for the Gamma distribution -/

public section
noncomputable section
open MeasureTheory ProbabilityTheory
namespace TauCeti.Probability

/-- The `ℝ≥0∞`-valued Gamma density is measurable. -/
theorem measurable_gammaPDF (a r : ℝ) : Measurable (gammaPDF a r) := by
  unfold gammaPDF
  exact (measurable_gammaPDFReal a r).ennreal_ofReal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}

/-- A variable with a Gamma law has a density. -/
theorem hasPDF_of_hasLaw_gammaMeasure {a r : ℝ} (hX : HasLaw X (gammaMeasure a r) P) :
    HasPDF X P :=
  hasPDF_of_hasLaw_withDensity (measurable_gammaPDF a r).aemeasurable
    (by simpa only [gammaMeasure] using hX)

/-- The density of a Gamma law is `gammaPDF`. -/
theorem pdf_eq_gammaPDF_of_hasLaw_gammaMeasure {a r : ℝ} (hX : HasLaw X (gammaMeasure a r) P) :
    pdf X P =ᵐ[volume] gammaPDF a r :=
  pdf_eq_of_hasLaw_withDensity (measurable_gammaPDF a r).aemeasurable
    (by simpa only [gammaMeasure] using hX)

/-- The Radon--Nikodym derivative of a Gamma law is `gammaPDF`. -/
theorem rnDeriv_gammaMeasure (a r : ℝ) :
    (gammaMeasure a r).rnDeriv volume =ᵐ[volume] gammaPDF a r := by
  unfold gammaMeasure
  exact Measure.rnDeriv_withDensity volume (measurable_gammaPDF a r)

end TauCeti.Probability
