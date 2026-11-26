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

* `TauCeti.topologicalPressure_eq_iSup_basis`: the supremum over a basis of the uniformity.
* `TauCeti.tendsto_netPressureEntourage_dist_lt`, `TauCeti.tendsto_netPressureEntourage_dist_le`:
  the metric forms, for open and closed Bowen balls.
-/

public section

namespace TauCeti

open Dynamics Filter Set Topology
open scoped Uniformity

variable {X : Type*}

/-- The topological pressure is the supremum of the pressure at the entourages of any basis of
the uniformity. -/
theorem topologicalPressure_eq_iSup_basis [UniformSpace X] {ι : Sort*} {p : ι → Prop}
    {s : ι → SetRel X X} (h : (𝓤 X).HasBasis p s) (T : X → X) (φ : X → ℝ) :
    topologicalPressure T φ = ⨆ (i : ι) (_ : p i), netPressureEntourage T φ (s i) := by
  refine (topologicalPressure_le_iff.2 fun U hU ↦ ?_).antisymm
    (iSup₂_le fun i hi ↦ netPressureEntourage_le_topologicalPressure (h.mem_of_mem hi))
  obtain ⟨i, hi, hsU⟩ := h.mem_iff.1 hU
  exact (netPressureEntourage_antitone T φ hsU).trans
    (le_iSup₂ (f := fun (i : ι) (_ : p i) ↦ netPressureEntourage T φ (s i)) i hi)

variable [PseudoMetricSpace X] (T : X → X) (φ : X → ℝ)

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
