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

A sequence is Cauchy if its objective values converge to a reference value and, for every
`ε > 0`, a single positive gap above it works for all pairs at distance at least `ε`.

## Main results

* `TauCeti.cauchySeq_of_le_max_sub`: the Cauchy criterion for separated pairs.
-/

public section

open Filter Topology

namespace TauCeti

variable {X ι : Type*} [PseudoMetricSpace X] [Nonempty ι] [SemilatticeSup ι]

/-- Suppose the objective values converge to `a`. If, for each `ε > 0`, one positive gap
above `a` bounds the maximum objective from below for every pair at distance at least `ε`,
then the sequence is Cauchy. -/
theorem cauchySeq_of_le_max_sub {u : ι → X} {g : ι → ℝ} {a : ℝ}
    (hgap : ∀ ε > 0, ∃ c > 0, ∀ n k, ε ≤ dist (u n) (u k) → c ≤ max (g n) (g k) - a)
    (hlim : Tendsto g atTop (𝓝 a)) : CauchySeq u := by
  refine Metric.cauchySeq_iff.2 fun ε hε ↦ ?_
  obtain ⟨c, hc, hgapc⟩ := hgap ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hlim.eventually (gt_mem_nhds (lt_add_of_pos_right a hc)))
  refine ⟨N, fun n hn k hk ↦ lt_of_not_ge fun hd ↦ ?_⟩
  have hmax : max (g n) (g k) < a + c := max_lt (hN n hn) (hN k hk)
  linarith [hgapc n k hd]

end TauCeti
