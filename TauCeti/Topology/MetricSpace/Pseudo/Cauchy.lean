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

A sequence is Cauchy when pairs separated by any fixed positive distance force a positive
objective gap, while the objective values converge to the reference value.

## Main results

* `TauCeti.cauchySeq_of_le_max_sub`: the Cauchy criterion for separated pairs.
-/

public section

open Filter Topology

namespace TauCeti

variable {X : Type*} [PseudoMetricSpace X]

/-- A sequence is Cauchy if, for every positive separation, the maximum of the two objective
values exceeds their limiting value by a fixed positive amount. -/
theorem cauchySeq_of_le_max_sub {u : ℕ → X} {g : ℕ → ℝ} {a : ℝ}
    (hgap : ∀ ε > 0, ∃ c > 0, ∀ n k, ε ≤ dist (u n) (u k) → c ≤ max (g n) (g k) - a)
    (hlim : Tendsto g atTop (𝓝 a)) : CauchySeq u := by
  refine Metric.cauchySeq_iff.2 fun ε hε ↦ ?_
  obtain ⟨c, hc, hgapc⟩ := hgap ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hlim.eventually (gt_mem_nhds (lt_add_of_pos_right a hc)))
  refine ⟨N, fun n hn k hk ↦ lt_of_not_ge fun hd ↦ ?_⟩
  have hmax : max (g n) (g k) < a + c := max_lt (hN n hn) (hN k hk)
  linarith [hgapc n k hd]

end TauCeti
