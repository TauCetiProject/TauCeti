/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Integrals against a measure with a real density

This file treats a measure `μ.withDensity (fun x => ENNReal.ofReal (ρ x))` presented by a
real-valued density `ρ` that is nonnegative almost everywhere. Mathlib's integrability and integral
lemmas for `withDensity` are stated for an `ℝ≥0∞`- or `ℝ≥0`-valued density, so applying them to such
a measure needs the step `ENNReal.toReal (ENNReal.ofReal (ρ x)) = ρ x` each time. The lemmas here
take that step once.

## Main results

* `TauCeti.MeasureTheory.integrable_withDensity_ofReal_iff`: a function is integrable against the
  measure iff its scalar product with `ρ` is integrable against `μ`;
* `TauCeti.MeasureTheory.integrable_of_eq_withDensity`: if the measure is finite, `ρ` is integrable
  against `μ`;
* `TauCeti.MeasureTheory.integral_withDensity_ofReal`: integration against the measure is
  integration of the `ρ`-weighted integrand against `μ`;
* `TauCeti.MeasureTheory.measureReal_withDensity_ofReal`: the real mass of a null-measurable set is
  the integral of `ρ` over it.
-/

public section

open MeasureTheory

namespace TauCeti

namespace MeasureTheory

variable {α F : Type*} [MeasurableSpace α] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {μ : Measure α} {g : α → F} {ρ : α → ℝ} {s : Set α}

/-- For a measure presented by a real-valued density `ρ`, a function is integrable iff its scalar
product with `ρ` is integrable against the reference measure. The density need only be nonnegative
a.e.; the `ℝ≥0∞`-valued density used in the presentation is its `ENNReal.ofReal` lift. -/
theorem integrable_withDensity_ofReal_iff (hρ : AEMeasurable ρ μ) (hnn : 0 ≤ᵐ[μ] ρ) :
    Integrable g (μ.withDensity (fun x => ENNReal.ofReal (ρ x))) ↔
      Integrable (fun x => ρ x • g x) μ := by
  have hlt : ∀ᵐ x ∂μ, ENNReal.ofReal (ρ x) < ⊤ :=
    ae_of_all _ fun _ => ENNReal.ofReal_lt_top
  rw [integrable_withDensity_iff_integrable_smul₀' hρ.ennreal_ofReal hlt]
  refine integrable_congr ?_
  filter_upwards [hnn] with x hx
  rw [ENNReal.toReal_ofReal hx]

/-- A nonnegative real density presenting a finite measure is integrable against the
reference measure. -/
theorem integrable_of_eq_withDensity {ν : Measure α} [IsFiniteMeasure ν]
    (hν : ν = μ.withDensity fun x => ENNReal.ofReal (ρ x)) (hρ : AEMeasurable ρ μ)
    (hnn : 0 ≤ᵐ[μ] ρ) : Integrable ρ μ := by
  have h1 : Integrable (fun _ => (1 : ℝ)) ν := integrable_const 1
  rw [hν, integrable_withDensity_ofReal_iff hρ hnn] at h1
  simpa using h1

/-- For a measure presented by a real-valued density `ρ`, integration is integration of the
`ρ`-weighted integrand against the reference measure. This is the integral counterpart of
`TauCeti.MeasureTheory.integrable_withDensity_ofReal_iff`, and it needs no integrability
hypothesis: when the integrand is not integrable both sides are `0`.

It specializes Mathlib's `integral_withDensity_eq_integral_toReal_smul₀` to densities of the form
`ENNReal.ofReal ∘ ρ`, where the `toReal` of the density reduces to `ρ` itself. -/
theorem integral_withDensity_ofReal (hρ : AEMeasurable ρ μ) (hnn : 0 ≤ᵐ[μ] ρ) (g : α → F) :
    ∫ x, g x ∂(μ.withDensity fun x => ENNReal.ofReal (ρ x)) = ∫ x, ρ x • g x ∂μ := by
  rw [integral_withDensity_eq_integral_toReal_smul₀ hρ.ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae ?_
  filter_upwards [hnn] with x hx
  rw [ENNReal.toReal_ofReal hx]

/-- Integrating a density that is nonnegative and measurable on `s` computes the real mass of `s`
under the measure presented by that density. The set `s` need only be null-measurable for the
reference measure. The nonnegativity and measurability hypotheses are only local to `s`, and no
integrability is needed: when the integral is infinite both sides are `0`. -/
theorem measureReal_withDensity_ofReal (hnn : 0 ≤ᵐ[μ.restrict s] ρ)
    (hs : NullMeasurableSet s μ) (hρ : AEMeasurable ρ (μ.restrict s)) :
    (μ.withDensity (fun x => ENNReal.ofReal (ρ x))).real s = ∫ x in s, ρ x ∂μ := by
  rw [measureReal_def, withDensity_apply₀ _ hs,
    integral_eq_lintegral_of_nonneg_ae hnn hρ.aestronglyMeasurable]

end MeasureTheory

end TauCeti
