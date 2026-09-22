/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Probability.Density
public import Mathlib.Probability.Distributions.Pareto
/-! # Density API for the Pareto distribution -/
public section
noncomputable section
open MeasureTheory ProbabilityTheory
namespace TauCeti.Probability
/-- The `ℝ≥0∞`-valued Pareto density is measurable. -/
theorem measurable_paretoPDF (t r : ℝ) : Measurable (paretoPDF t r) := by
  unfold paretoPDF
  exact (measurable_paretoPDFReal t r).ennreal_ofReal
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}
/-- A variable with a Pareto law has a density. -/
theorem hasPDF_of_hasLaw_paretoMeasure {t r : ℝ} (hX : HasLaw X (paretoMeasure t r) P) :
    HasPDF X P :=
  hasPDF_of_hasLaw_withDensity (measurable_paretoPDF t r).aemeasurable
    (by simpa only [paretoMeasure] using hX)
/-- The density of a Pareto law is `paretoPDF`. -/
theorem pdf_eq_paretoPDF_of_hasLaw_paretoMeasure {t r : ℝ}
    (hX : HasLaw X (paretoMeasure t r) P) : pdf X P =ᵐ[volume] paretoPDF t r :=
  pdf_eq_of_hasLaw_withDensity (measurable_paretoPDF t r).aemeasurable
    (by simpa only [paretoMeasure] using hX)
/-- The Radon--Nikodym derivative of a Pareto law is `paretoPDF`. -/
theorem rnDeriv_paretoMeasure (t r : ℝ) :
    (paretoMeasure t r).rnDeriv volume =ᵐ[volume] paretoPDF t r := by
  unfold paretoMeasure
  exact Measure.rnDeriv_withDensity volume (measurable_paretoPDF t r)
end TauCeti.Probability
