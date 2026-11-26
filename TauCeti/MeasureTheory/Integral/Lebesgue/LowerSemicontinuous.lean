/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.Topology.Semicontinuity.Basic

/-!
# Lower semicontinuity of Lebesgue integrals in a parameter

Fatou's lemma with a parameter: if `F x` is almost everywhere measurable for every `x` and
`F · p` is lower semicontinuous at `x₀` for almost every `p`, then `x ↦ ∫⁻ F x dρ` is lower
semicontinuous at `x₀`, provided the neighbourhood filter of `x₀` is countably generated.

## Main declarations

* `TauCeti.lowerSemicontinuousAt_lintegral`: Fatou's lemma with a parameter.

## Provenance

`TauCeti.lowerSemicontinuousAt_lintegral` is adapted from `New.lowerSemicontinuousAt_lintegral`
in `src/Lib/General/Measure/FibreMeasure.lean` of the Lean proof of the Riemann hypothesis by
Levent Alpöge with Claude, as published under Apache 2.0 at
https://github.com/leanprover-community/riemann-hypothesis (commit `5aa76fdf49d4`). There the
parameter space is first countable and the integrands are measurable; here only the
neighbourhood filter of the point is countably generated and the integrands are almost everywhere
measurable.
-/

public section

namespace TauCeti

open MeasureTheory Filter Topology
open scoped ENNReal

/-- **Fatou's lemma with a parameter.** If `F x` is almost everywhere measurable for every `x`
and `F · p` is lower semicontinuous at `x₀` for almost every `p`, then `x ↦ ∫⁻ F x dρ` is lower
semicontinuous at `x₀`, provided the neighbourhood filter of `x₀` is countably generated. -/
theorem lowerSemicontinuousAt_lintegral {X P : Type*} [TopologicalSpace X] [MeasurableSpace P]
    {ρ : Measure P} {F : X → P → ℝ≥0∞} {x₀ : X} [(𝓝 x₀).IsCountablyGenerated]
    (h_meas : ∀ x : X, AEMeasurable (F x) ρ)
    (h_lsc : ∀ᵐ p : P ∂ρ, LowerSemicontinuousAt (F · p) x₀) :
    LowerSemicontinuousAt (fun x : X ↦ ∫⁻ p : P, F x p ∂ρ) x₀ := by
  rw [lowerSemicontinuousAt_iff_le_liminf]
  calc ∫⁻ p, F x₀ p ∂ρ ≤ ∫⁻ p, liminf (F · p) (𝓝 x₀) ∂ρ :=
        lintegral_mono_ae (h_lsc.mono fun _ ↦ lowerSemicontinuousAt_iff_le_liminf.1)
    _ ≤ liminf (fun x ↦ ∫⁻ p, F x p ∂ρ) (𝓝 x₀) := lintegral_liminf_le' h_meas

end TauCeti
