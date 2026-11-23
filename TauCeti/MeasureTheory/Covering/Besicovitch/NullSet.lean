/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Covering.Besicovitch

/-!
# A density criterion for null sets

In a metric space with the Besicovitch covering property, a set `Q` that fills at most a fixed
fraction `c < 1` of every small closed ball around every point is null for every locally finite
measure (`TauCeti.measure_eq_zero_of_forall_measure_inter_closedBall_le`): by Lebesgue's density
theorem `Besicovitch.ae_tendsto_measure_inter_div`, almost every point of `Q` has density one in
`Q`. No measurability of `Q` is assumed.
-/

public section

open Filter Metric MeasureTheory Set Topology
open scoped ENNReal

namespace TauCeti

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [SecondCountableTopology X]
  [BorelSpace X] [HasBesicovitchCovering X]

/-- **A density criterion for null sets.** A set filling at most a fraction `c < 1` of every small
closed ball around every point is null, by Lebesgue's density theorem. No measurability is
assumed. -/
theorem measure_eq_zero_of_forall_measure_inter_closedBall_le (ν : Measure X)
    [IsLocallyFiniteMeasure ν] (Q : Set X) {c : ℝ≥0∞} (hc : c < 1)
    (h : ∀ z, ∀ᶠ r in 𝓝[>] 0, ν (Q ∩ closedBall z r) ≤ c * ν (closedBall z r)) : ν Q = 0 := by
  by_contra hQ
  have : (ae (ν.restrict Q)).NeBot := ae_neBot.2 (by rwa [Ne, Measure.restrict_eq_zero])
  obtain ⟨z, hz⟩ := (Besicovitch.ae_tendsto_measure_inter_div ν Q).exists
  have h1 : ∀ᶠ r in 𝓝[>] (0 : ℝ), ν (Q ∩ closedBall z r) / ν (closedBall z r) ≤ c :=
    (h z).mono fun r hr => ENNReal.div_le_of_le_mul hr
  exact absurd (le_of_tendsto hz h1) (not_le.2 hc)

end TauCeti
