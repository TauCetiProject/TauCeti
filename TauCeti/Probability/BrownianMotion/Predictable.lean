/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Filtered
public import TauCeti.Probability.Process.Predictable

/-!
# Predictable versions of filtered Brownian motion

A Brownian motion adapted to a raw filtration need not itself be literally predictable:
its paths are only almost surely continuous. This file selects a predictable version agreeing
with the original process at every time outside one common null set. The version retains the
native Brownian law and increment independence from the past in the original filtration.
Neither completion nor right continuity of that filtration is needed.

The selection uses the lagged-step predictable approximation for adapted continuous processes.
It supplies a literally progressive process for stopped evaluations and stochastic integration;
it does not make all exceptional paths continuous or all null sets visible at time zero.

## References

* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, Springer, 1991,
  Chapters 1–2.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace TauCeti.Probability.IsFilteredPreBrownianReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {ℱ : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ}

/-- A filtered pre-Brownian motion with almost-surely continuous paths has a predictable
indistinguishable Brownian version on the same raw filtration. The selected version is still
adapted and has increments independent of the past, not merely the same marginal laws. -/
theorem exists_predictable_brownian_version (hB : IsFilteredPreBrownianReal ℱ B P)
    (hc : ∀ᵐ ω ∂P, Continuous (fun t => B t ω)) :
    ∃ W : ℝ≥0 → Ω → ℝ, IsStronglyPredictable ℱ W ∧ IsBrownianReal W P ∧
      IsFilteredPreBrownianReal ℱ W P ∧ ∀ᵐ ω ∂P, ∀ t, W t ω = B t ω := by
  obtain ⟨W, hW, heq⟩ := hB.adapted.stronglyAdapted.exists_isStronglyPredictable_of_ae_continuous hc
  have hFW := hB.congr hW.isStronglyProgressive.stronglyAdapted.adapted
    (fun t => heq.mono fun ω hω => (hω t).symm)
  refine ⟨W, hW, ⟨hFW.toIsPreBrownianReal, ?_⟩, hFW, heq⟩
  filter_upwards [hc, heq] with ω hω heqω
  exact hω.congr (fun t => (heqω t).symm)

end TauCeti.Probability.IsFilteredPreBrownianReal
