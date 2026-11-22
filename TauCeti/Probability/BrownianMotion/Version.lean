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

`ProbabilityTheory.IsBrownianReal` assumes only almost-sure path continuity and `B 0 =ᵐ[P] 0`,
without coordinatewise `StronglyMeasurable (B t)` or completeness of the ambient measurable space.
To construct `MeasureTheory.Filtration.natural` and transfer raw-filtration stopping and pathwise
hitting-time results back to `B` (`ProbabilityTheory.IsBrownianReal.congr_indist`),
`ProbabilityTheory.IsBrownianReal.exists_stronglyMeasurable_continuous_indist` builds an
indistinguishable Brownian version that is strongly measurable at every time, continuous on every
outcome, and zero at time `0` on every outcome. Consequently the paths of `B` are jointly almost
everywhere strongly measurable in time and sample
(`ProbabilityTheory.IsBrownianReal.aestronglyMeasurable_uncurry`), as samplewise time integrals
of the paths require.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace ProbabilityTheory.IsBrownianReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B W : ℝ≥0 → Ω → ℝ}

/-- Indistinguishability preserves the Brownian property. -/
theorem congr_indist (hB : IsBrownianReal B P) (h : B ≡ᵐ[P] W) : IsBrownianReal W P where
  toIsPreBrownianReal := hB.toIsPreBrownianReal.congr h.ae_eq_eval
  cont := hB.cont.mp (h.mono fun _ hω hc ↦ hc.congr hω)

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

/-- The paths of a real Brownian motion, read along `Real.toNNReal`, are jointly almost
everywhere strongly measurable in time and sample, for every measure on time. -/
theorem aestronglyMeasurable_uncurry (hB : IsBrownianReal B P) (μ : Measure ℝ) :
    AEStronglyMeasurable (fun p : ℝ × Ω ↦ B p.1.toNNReal p.2) (μ.prod P) := by
  obtain ⟨W, hWm, hWc, -, -, hWB⟩ := hB.exists_stronglyMeasurable_continuous_indist
  have hm : StronglyMeasurable (Function.uncurry fun (u : ℝ) (ω : Ω) ↦ W u.toNNReal ω) :=
    stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable
      (fun ω ↦ (hWc ω).comp continuous_real_toNNReal) fun u ↦ hWm u.toNNReal
  refine hm.aestronglyMeasurable.congr ?_
  filter_upwards [(Measure.quasiMeasurePreserving_snd (μ := μ)).ae hWB] with p hp
  exact hp p.1.toNNReal

end ProbabilityTheory.IsBrownianReal
