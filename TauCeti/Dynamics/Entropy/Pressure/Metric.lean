/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Instances.EReal.Lemmas
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import TauCeti.Dynamics.Entropy.Pressure
import TauCeti.Topology.MetricSpace.Pseudo.Defs
import TauCeti.Topology.Order.Monotone.OneSidedLimit

/-!
# Metric forms of topological pressure

The topological pressure `TauCeti.topologicalPressure T φ` is a supremum over the entourages of the
uniformity; it is enough to take the supremum over a basis of the uniformity
(`TauCeti.topologicalPressure_eq_iSup_basis`). On a pseudometric space this gives the
Bowen–Dinaburg forms: the pressure at the entourages `{p | dist p.1 p.2 < ε}` and
`{p | dist p.1 p.2 ≤ ε}` (sums over `(n, ε)`-separated sets in the disjoint-Bowen-ball sense of
`Dynamics.IsDynNetIn`) tends to the topological pressure as `ε → 0⁺`. These are the pressure
analogues of `TauCeti.tendsto_netEntropyEntourage_dist_lt` and
`TauCeti.tendsto_netEntropyEntourage_dist_le`.

## Main results

* `TauCeti.tendsto_netPressureEntourage_dist_lt`, `TauCeti.tendsto_netPressureEntourage_dist_le`:
  the metric forms, for open and closed Bowen balls.

## References

* Peter Walters, *An Introduction to Ergodic Theory*, Graduate Texts in Mathematics 79, Springer,
  1982, Chapter 9: §9.1 defines the pressure through `(n, ε)`-separated sets and lets `ε → 0`.
-/

public section

namespace TauCeti

open Dynamics Filter Set Topology
open scoped Uniformity

variable {X : Type*} [PseudoMetricSpace X] (T : X → X) (φ : X → ℝ)

/-- **Metric form of pressure, open Bowen balls.** The pressure at the entourage
`{p | dist p.1 p.2 < ε}` tends to the topological pressure as `ε → 0⁺`. -/
theorem tendsto_netPressureEntourage_dist_lt :
    Tendsto (fun ε : ℝ ↦ netPressureEntourage T φ {p | dist p.1 p.2 < ε}) (𝓝[>] 0)
      (𝓝 (topologicalPressure T φ)) := by
  rw [topologicalPressure_eq_iSup_basis Metric.uniformity_basis_dist]
  exact ((netPressureEntourage_antitone T φ).comp_monotone
    Metric.monotone_ofPred_dist_lt).tendsto_nhdsGT_biSup 0

/-- **Metric form of pressure, closed Bowen balls.** The pressure at the entourage
`{p | dist p.1 p.2 ≤ ε}` tends to the topological pressure as `ε → 0⁺`. -/
theorem tendsto_netPressureEntourage_dist_le :
    Tendsto (fun ε : ℝ ↦ netPressureEntourage T φ {p | dist p.1 p.2 ≤ ε}) (𝓝[>] 0)
      (𝓝 (topologicalPressure T φ)) := by
  rw [topologicalPressure_eq_iSup_basis Metric.uniformity_basis_dist_le]
  exact ((netPressureEntourage_antitone T φ).comp_monotone
    Metric.monotone_ofPred_dist_le).tendsto_nhdsGT_biSup 0

end TauCeti
