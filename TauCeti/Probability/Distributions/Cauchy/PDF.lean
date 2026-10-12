/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Probability.Density
public import Mathlib.Probability.Distributions.Cauchy
/-!
# Density API for the Cauchy distribution

This file connects nondegenerate Cauchy laws to `HasPDF` and identifies `pdf` and the
Radon--Nikodym derivative at every scale, including the singular zero-scale boundary.
-/
public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace TauCeti.Probability
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}
/-- A variable with a nondegenerate Cauchy law has a density.

`γ ≠ 0` is required. The zero-scale law is `Measure.dirac x₀`, which is singular with respect to
`volume`. -/
theorem hasPDF_of_hasLaw_cauchyMeasure {x₀ : ℝ} {γ : ℝ≥0} (hγ : γ ≠ 0)
    (hX : HasLaw X (cauchyMeasure x₀ γ) P) : HasPDF X P :=
  hasPDF_of_hasLaw_withDensity (measurable_cauchyPDF x₀ γ).aemeasurable
    (by rwa [cauchyMeasure_of_scale_ne_zero _ hγ] at hX)
/-- The Radon--Nikodym derivative of a Cauchy law is `cauchyPDF`, at **every** scale.

No nondegeneracy hypothesis is needed. At zero scale the law is `Measure.dirac x₀`, singular with
respect to `volume`, so the derivative vanishes almost everywhere, and `cauchyPDF x₀ 0` vanishes
too. -/
theorem rnDeriv_cauchyMeasure (x₀ : ℝ) (γ : ℝ≥0) :
    (cauchyMeasure x₀ γ).rnDeriv volume =ᵐ[volume] cauchyPDF x₀ γ := by
  by_cases hγ : γ = 0
  · subst hγ
    rw [cauchyMeasure_zero_scale, cauchyPDF_scale_zero]
    exact Measure.rnDeriv_eq_zero_of_mutuallySingular (mutuallySingular_dirac x₀ volume)
      Measure.AbsolutelyContinuous.rfl
  · rw [cauchyMeasure_of_scale_ne_zero _ hγ]
    exact Measure.rnDeriv_withDensity volume (measurable_cauchyPDF x₀ γ)
/-- **The singular boundary.** At zero scale the Cauchy law is `Measure.dirac x₀`, so its
Radon--Nikodym derivative with respect to `volume` vanishes almost everywhere. -/
theorem rnDeriv_cauchyMeasure_zero_scale (x₀ : ℝ) :
    (cauchyMeasure x₀ 0).rnDeriv volume =ᵐ[volume] 0 := by
  simpa using rnDeriv_cauchyMeasure x₀ 0
/-- The density of a Cauchy law is `cauchyPDF`, at **every** scale. -/
theorem pdf_eq_cauchyPDF_of_hasLaw_cauchyMeasure {x₀ : ℝ} {γ : ℝ≥0}
    (hX : HasLaw X (cauchyMeasure x₀ γ) P) : pdf X P =ᵐ[volume] cauchyPDF x₀ γ := by
  rw [pdf_def, hX.map_eq]
  exact rnDeriv_cauchyMeasure x₀ γ
end TauCeti.Probability
