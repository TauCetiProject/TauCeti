/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Probability.Density
public import Mathlib.Probability.Distributions.Beta
/-! # Density API for the Beta distribution -/
public section
noncomputable section
open MeasureTheory ProbabilityTheory
namespace TauCeti.Probability
/-- The `ℝ≥0∞`-valued Beta density is measurable. -/
theorem measurable_betaPDF (α β : ℝ) : Measurable (betaPDF α β) := by
  unfold betaPDF
  exact (measurable_betaPDFReal α β).ennreal_ofReal
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}
/-- A variable with a Beta law has a density. -/
theorem hasPDF_of_hasLaw_betaMeasure {α β : ℝ} (hX : HasLaw X (betaMeasure α β) P) :
    HasPDF X P :=
  hasPDF_of_hasLaw_withDensity (measurable_betaPDF α β).aemeasurable
    (by simpa only [betaMeasure] using hX)
/-- The density of a Beta law is `betaPDF`. -/
theorem pdf_eq_betaPDF_of_hasLaw_betaMeasure {α β : ℝ} (hX : HasLaw X (betaMeasure α β) P) :
    pdf X P =ᵐ[volume] betaPDF α β :=
  pdf_eq_of_hasLaw_withDensity (measurable_betaPDF α β).aemeasurable
    (by simpa only [betaMeasure] using hX)
/-- The Radon--Nikodym derivative of a Beta law is `betaPDF`. -/
theorem rnDeriv_betaMeasure (α β : ℝ) :
    (betaMeasure α β).rnDeriv volume =ᵐ[volume] betaPDF α β := by
  unfold betaMeasure
  exact Measure.rnDeriv_withDensity volume (measurable_betaPDF α β)
end TauCeti.Probability
