/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Probability.Distributions.Gamma.PDF
public import Mathlib.Probability.Distributions.Exponential

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

/-- `exponentialPDF` unfolds to `gammaPDF 1`.  Stated once, and `private`, so the two proofs in this
file that need it rewrite with a named equality rather than relying on a silent delta-reduction,
without adding a public wrapper for a definitional equality. -/
private theorem exponentialPDF_def (r : ℝ) : exponentialPDF r = gammaPDF 1 r := (rfl)

/-- The density of an exponential law is `exponentialPDF`.

`exponentialPDF` is *defined* as `gammaPDF 1`, so the two densities agree definitionally; the
private `exponentialPDF_def` names that equality rather than leaving it to elaboration. -/
theorem pdf_eq_exponentialPDF_of_hasLaw_expMeasure {r : ℝ} (hX : HasLaw X (expMeasure r) P) :
    pdf X P =ᵐ[volume] exponentialPDF r := by
  have h : pdf X P =ᵐ[volume] gammaPDF 1 r :=
    pdf_eq_of_hasLaw_withDensity (measurable_gammaPDF 1 r).aemeasurable
      (by simpa only [expMeasure, gammaMeasure] using hX)
  rw [exponentialPDF_def]
  exact h

/-- The Radon--Nikodym derivative of an exponential law is `exponentialPDF`, which is `gammaPDF 1`
by definition. -/
theorem rnDeriv_expMeasure (r : ℝ) :
    (expMeasure r).rnDeriv volume =ᵐ[volume] exponentialPDF r := by
  rw [exponentialPDF_def]
  unfold expMeasure
  exact rnDeriv_gammaMeasure 1 r

end TauCeti.Probability
