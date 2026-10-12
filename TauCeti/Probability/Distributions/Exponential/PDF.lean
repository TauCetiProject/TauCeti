/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Probability.Density
public import Mathlib.Probability.Distributions.Exponential

import TauCeti.Probability.Distributions.Gamma.PDF

/-!
# Density API for the exponential distribution

This file connects Mathlib's exponential law to `MeasureTheory.HasPDF`, identifies its density,
and computes its Radon--Nikodym derivative with respect to Lebesgue measure.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}

/-- A variable with an exponential law has a density. -/
theorem hasPDF_of_hasLaw_expMeasure {r : ℝ} (hX : HasLaw X (expMeasure r) P) : HasPDF X P :=
  hasPDF_of_hasLaw_withDensity (measurable_gammaPDF 1 r).aemeasurable
    (by simpa only [expMeasure, gammaMeasure] using hX)

/-- The density of an exponential law is `exponentialPDF`. -/
theorem pdf_eq_exponentialPDF_of_hasLaw_expMeasure {r : ℝ} (hX : HasLaw X (expMeasure r) P) :
    pdf X P =ᵐ[volume] exponentialPDF r := by
  filter_upwards [pdf_eq_of_hasLaw_withDensity (measurable_gammaPDF 1 r).aemeasurable
    (by simpa only [expMeasure, gammaMeasure] using hX)] with x hx
  simpa only [exponentialPDF_eq, gammaPDF_eq, Real.rpow_one, Real.Gamma_one, div_one, sub_self,
    Real.rpow_zero, mul_one] using hx

/-- The Radon--Nikodym derivative of an exponential law is `exponentialPDF`, which is `gammaPDF 1`
by definition. -/
theorem rnDeriv_expMeasure (r : ℝ) :
    (expMeasure r).rnDeriv volume =ᵐ[volume] exponentialPDF r := by
  filter_upwards [rnDeriv_gammaMeasure 1 r] with x hx
  simpa only [expMeasure, exponentialPDF_eq, gammaPDF_eq, Real.rpow_one, Real.Gamma_one, div_one,
    sub_self, Real.rpow_zero, mul_one] using hx

end TauCeti.Probability
