/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Process.LocalProperty
import TauCeti.Probability.Process.Stopping

/-!
# Localizing sequences under filtration enlargement

Enlarging a filtration preserves its localizing sequences. The stopping-time property
transports to the larger filtration, while monotonicity and divergence are unchanged.
-/

public section

namespace ProbabilityTheory.IsLocalizingSequence

open MeasureTheory

/-- A localizing sequence for a filtration also localizes any larger filtration. -/
theorem mono_filtration {ι Ω : Type*} [Preorder ι] [TopologicalSpace ι] [OrderTopology ι]
    {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {ℱ 𝒢 : Filtration ι mΩ}
    {τ : ℕ → Ω → WithTop ι} (hτ : IsLocalizingSequence ℱ τ μ) (h : ℱ ≤ 𝒢) :
    IsLocalizingSequence 𝒢 τ μ where
  isStoppingTime n := (hτ.isStoppingTime n).mono_filtration h
  tendsto_top := hτ.tendsto_top
  mono := hτ.mono

end ProbabilityTheory.IsLocalizingSequence
