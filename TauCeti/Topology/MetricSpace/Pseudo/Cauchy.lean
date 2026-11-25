/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Tactic.Linarith

/-!
# A Cauchy criterion from vanishing objective gaps

A metric sequence is Cauchy when its pairwise distance penalty is bounded by average
objective gaps tending to zero, provided the penalty is bounded away from zero at every
positive distance from zero.

## Main results

* `TauCeti.cauchySeq_of_le_average_sub`: the Cauchy criterion for a general distance penalty.
-/

public section

open Filter Topology

namespace TauCeti

variable {X : Type*} [PseudoMetricSpace X]

/-- A sequence is Cauchy if a distance penalty bounded away from zero off every
neighborhood of zero is controlled by average objective gaps tending to zero. -/
theorem cauchySeq_of_le_average_sub {u : ℕ → X} {g : ℕ → ℝ} {a : ℝ} {ω : ℝ → ℝ}
    (hω : ∀ ε > 0, ∃ c > 0, ∀ r ≥ ε, c ≤ ω r)
    (hgap : ∀ n k, ω (dist (u n) (u k)) / 4 ≤ (g n + g k) / 2 - a)
    (hlim : Tendsto g atTop (𝓝 a)) : CauchySeq u := by
  refine Metric.cauchySeq_iff.2 fun ε hε ↦ ?_
  obtain ⟨c, hc, hωc⟩ := hω ε hε
  have hcut : a < a + c / 4 := by linarith
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hlim.eventually (gt_mem_nhds hcut))
  refine ⟨N, fun n hn k hk ↦ lt_of_not_ge fun hd ↦ ?_⟩
  linarith [hωc _ hd, hgap n k, hN n hn, hN k hk]

end TauCeti
