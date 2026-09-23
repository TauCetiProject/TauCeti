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
  -- `exponentialPDF r` is definitionally `gammaPDF 1 r`, whose density theorem is available.
  change pdf X P =ᵐ[volume] gammaPDF 1 r
  exact pdf_eq_of_hasLaw_withDensity (measurable_gammaPDF 1 r).aemeasurable
    (by simpa only [expMeasure, gammaMeasure] using hX)

/-- The Radon--Nikodym derivative of an exponential law is `exponentialPDF`, which is `gammaPDF 1`
by definition. -/
theorem rnDeriv_expMeasure (r : ℝ) :
    (expMeasure r).rnDeriv volume =ᵐ[volume] exponentialPDF r := by
  -- `exponentialPDF r` is definitionally `gammaPDF 1 r`, whose derivative theorem is available.
  change (expMeasure r).rnDeriv volume =ᵐ[volume] gammaPDF 1 r
  unfold expMeasure
  exact rnDeriv_gammaMeasure 1 r

end TauCeti.Probability
