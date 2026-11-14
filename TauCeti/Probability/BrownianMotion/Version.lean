/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.Probability.Process.Indistinguishable
import TauCeti.Probability.Process.Version

/-!
# Everywhere-continuous measurable versions of Brownian motion

Mathlib's `ProbabilityTheory.IsBrownianReal` requires only almost-everywhere measurable fixed-time
evaluations and almost-surely continuous sample paths, with `B 0 =ᵐ[P] 0`. Hitting-time and
optional-sampling arguments on raw measurable spaces need a process whose fixed-time evaluations
are strongly measurable everywhere, whose sample paths are continuous on every outcome, and which
starts at `0` on every outcome.

`ProbabilityTheory.IsBrownianReal.exists_stronglyMeasurable_continuous_indist` produces such an
indistinguishable Brownian version from
`TauCeti.Probability.exists_stronglyMeasurable_continuous_eval_eq_indist`, without completeness of
the ambient measurable space.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace ProbabilityTheory.IsBrownianReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B W : ℝ≥0 → Ω → ℝ}

/-- Indistinguishability preserves the Brownian property. -/
theorem congr_indist (hB : IsBrownianReal B P) (h : B ≡ᵐ[P] W) : IsBrownianReal W P where
  toIsPreBrownianReal := hB.toIsPreBrownianReal.congr h.ae_eq_eval
  cont := by
    filter_upwards [hB.cont, h] with ω hc hω
    exact hc.congr hω

/-- Every real Brownian motion has an indistinguishable Brownian version whose fixed-time
evaluations are strongly measurable everywhere, whose sample paths are continuous everywhere, and
which vanishes at time `0` on every outcome. -/
theorem exists_stronglyMeasurable_continuous_indist (hB : IsBrownianReal B P) :
    ∃ W : ℝ≥0 → Ω → ℝ, (∀ t, StronglyMeasurable (W t)) ∧ (∀ ω, Continuous (W · ω)) ∧
      (∀ ω, W 0 ω = 0) ∧ IsBrownianReal W P ∧ W ≡ᵐ[P] B := by
  obtain ⟨W, hWm, hWc, hW0, hWB⟩ :=
    TauCeti.Probability.exists_stronglyMeasurable_continuous_eval_eq_indist
      (fun t ↦ (hB.integrable_eval t).aestronglyMeasurable) hB.cont 0 0 hB.eval_zero_ae_eq_zero
  exact ⟨W, hWm, hWc, hW0, hB.congr_indist hWB.symm, hWB⟩

end ProbabilityTheory.IsBrownianReal
