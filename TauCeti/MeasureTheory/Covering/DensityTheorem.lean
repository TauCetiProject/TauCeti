/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Covering.DensityTheorem

/-!
# Lebesgue points along concentric closed balls

Mathlib's `IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub` states the Lebesgue
differentiation theorem for a uniformly locally doubling measure along arbitrary families of
closed balls shrinking to a point. This file records its most common special case: almost every
point `x` is a Lebesgue point of a locally integrable function `f` in the sense that the mean
oscillation `⨍_{closedBall x r} ‖f - f x‖` tends to zero as `r → 0⁺`.
-/

public section

open Filter Metric MeasureTheory
open scoped Topology

namespace IsUnifLocDoublingMeasure

variable {α E : Type*} [PseudoMetricSpace α] [MeasurableSpace α] (μ : Measure α)
  [IsUnifLocDoublingMeasure μ] [SecondCountableTopology α] [BorelSpace α]
  [IsLocallyFiniteMeasure μ] [NormedAddCommGroup E]

/-- **Lebesgue differentiation theorem along concentric closed balls.** For a uniformly locally
doubling measure, almost every point `x` is a Lebesgue point of a locally integrable function `f`:
the mean oscillation `⨍_{closedBall x r} ‖f - f x‖` tends to zero as `r → 0⁺`. -/
theorem ae_tendsto_average_closedBall_norm_sub {f : α → E} (hf : LocallyIntegrable f μ) :
    ∀ᵐ x ∂μ, Tendsto (fun r => ⨍ y in closedBall x r, ‖f y - f x‖ ∂μ) (𝓝[>] 0) (𝓝 0) := by
  filter_upwards [ae_tendsto_average_norm_sub μ hf 1] with x hx
  exact hx (fun _ => x) id tendsto_id (eventually_mem_nhdsWithin.mono fun r hr =>
    mem_closedBall_self (by simpa using (le_of_lt hr)))

end IsUnifLocDoublingMeasure
