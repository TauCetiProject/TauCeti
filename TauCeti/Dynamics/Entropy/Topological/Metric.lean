/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Dynamics.TopologicalEntropy.NetEntropy
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Instances.EReal.Lemmas
import TauCeti.Topology.MetricSpace.Pseudo.Defs
import TauCeti.Topology.Order.Monotone.OneSidedLimit

/-!
# Metric forms of topological entropy

On a pseudometric space, Mathlib's topological entropy `Dynamics.coverEntropy T F` is the limit as
`ε → 0⁺` of the Bowen–Dinaburg exponential growth rates of maximal `(n, ε)`-separated sets and of
minimal `(n, ε)`-spanning sets. We use the disjoint-Bowen-ball convention: an `(n, ε)`-separated
set is a dynamical net in Mathlib's sense (`Dynamics.IsDynNetIn`): a subset of `F` whose
`(n, ε)`-Bowen balls are pairwise disjoint. Disjointness of the open balls forces
`ε ≤ dist (T^[k] x) (T^[k] y)` for some `k < n` between distinct points, but it is a stronger
condition than this separation.
We prove the limits both for the entourage `{p | dist p.1 p.2 < ε}` (open Bowen balls) and for
`{p | dist p.1 p.2 ≤ ε}` (closed Bowen balls). In particular all these limits agree.

## Main results

* `TauCeti.tendsto_netEntropyEntourage_dist_lt`, `TauCeti.tendsto_netEntropyEntourage_dist_le`:
  the growth rates of maximal families with pairwise disjoint open (resp. closed) Bowen balls
  tend to the topological entropy as `ε → 0⁺`.
* `TauCeti.tendsto_coverEntropyEntourage_dist_lt`, `TauCeti.tendsto_coverEntropyEntourage_dist_le`:
  the same for spanning sets (open and closed Bowen balls).
* `TauCeti.tendsto_netEntropyInfEntourage_dist_lt` and its three siblings: the same for the
  `liminf` growth rates and `Dynamics.coverEntropyInf`.
-/

public section

namespace TauCeti

open Dynamics Filter Set Topology

variable {X : Type*} [PseudoMetricSpace X] (T : X → X) (F : Set X)

/-- The growth rates of maximal families of points of `F` with pairwise disjoint open Bowen
`(n, ε)`-balls (`(n, ε)`-separated sets in the disjoint-Bowen-ball sense) tend to the topological
entropy as `ε → 0⁺`. -/
theorem tendsto_netEntropyEntourage_dist_lt :
    Tendsto (fun ε : ℝ ↦ netEntropyEntourage T F {p | dist p.1 p.2 < ε}) (𝓝[>] 0)
      (𝓝 (coverEntropy T F)) := by
  rw [coverEntropy_eq_iSup_basis_netEntropyEntourage Metric.uniformity_basis_dist]
  exact ((netEntropyEntourage_antitone T F).comp_monotone
    Metric.monotone_ofPred_dist_lt).tendsto_nhdsGT_biSup 0

/-- The growth rates of maximal families of points of `F` with pairwise disjoint closed Bowen
`(n, ε)`-balls (`(n, ε)`-separated sets in the disjoint-Bowen-ball sense) tend to the topological
entropy as `ε → 0⁺`. -/
theorem tendsto_netEntropyEntourage_dist_le :
    Tendsto (fun ε : ℝ ↦ netEntropyEntourage T F {p | dist p.1 p.2 ≤ ε}) (𝓝[>] 0)
      (𝓝 (coverEntropy T F)) := by
  rw [coverEntropy_eq_iSup_basis_netEntropyEntourage Metric.uniformity_basis_dist_le]
  exact ((netEntropyEntourage_antitone T F).comp_monotone
    Metric.monotone_ofPred_dist_le).tendsto_nhdsGT_biSup 0

/-- The growth rates of minimal `(n, ε)`-spanning sets for open Bowen balls tend to the
topological entropy as `ε → 0⁺`. -/
theorem tendsto_coverEntropyEntourage_dist_lt :
    Tendsto (fun ε : ℝ ↦ coverEntropyEntourage T F {p | dist p.1 p.2 < ε}) (𝓝[>] 0)
      (𝓝 (coverEntropy T F)) := by
  rw [coverEntropy_eq_iSup_basis Metric.uniformity_basis_dist]
  exact ((coverEntropyEntourage_antitone T F).comp_monotone
    Metric.monotone_ofPred_dist_lt).tendsto_nhdsGT_biSup 0

/-- The growth rates of minimal `(n, ε)`-spanning sets for closed Bowen balls tend to the
topological entropy as `ε → 0⁺`. -/
theorem tendsto_coverEntropyEntourage_dist_le :
    Tendsto (fun ε : ℝ ↦ coverEntropyEntourage T F {p | dist p.1 p.2 ≤ ε}) (𝓝[>] 0)
      (𝓝 (coverEntropy T F)) := by
  rw [coverEntropy_eq_iSup_basis Metric.uniformity_basis_dist_le]
  exact ((coverEntropyEntourage_antitone T F).comp_monotone
    Metric.monotone_ofPred_dist_le).tendsto_nhdsGT_biSup 0

/-- The `liminf` growth rates of maximal families of points of `F` with pairwise disjoint open
Bowen `(n, ε)`-balls (`(n, ε)`-separated sets in the disjoint-Bowen-ball sense) tend to the
`liminf` topological entropy as `ε → 0⁺`. -/
theorem tendsto_netEntropyInfEntourage_dist_lt :
    Tendsto (fun ε : ℝ ↦ netEntropyInfEntourage T F {p | dist p.1 p.2 < ε}) (𝓝[>] 0)
      (𝓝 (coverEntropyInf T F)) := by
  rw [coverEntropyInf_eq_iSup_basis_netEntropyInfEntourage Metric.uniformity_basis_dist]
  exact ((netEntropyInfEntourage_antitone T F).comp_monotone
    Metric.monotone_ofPred_dist_lt).tendsto_nhdsGT_biSup 0

/-- The `liminf` growth rates of maximal families of points of `F` with pairwise disjoint closed
Bowen `(n, ε)`-balls (`(n, ε)`-separated sets in the disjoint-Bowen-ball sense) tend to the
`liminf` topological entropy as `ε → 0⁺`. -/
theorem tendsto_netEntropyInfEntourage_dist_le :
    Tendsto (fun ε : ℝ ↦ netEntropyInfEntourage T F {p | dist p.1 p.2 ≤ ε}) (𝓝[>] 0)
      (𝓝 (coverEntropyInf T F)) := by
  rw [coverEntropyInf_eq_iSup_basis_netEntropyInfEntourage Metric.uniformity_basis_dist_le]
  exact ((netEntropyInfEntourage_antitone T F).comp_monotone
    Metric.monotone_ofPred_dist_le).tendsto_nhdsGT_biSup 0

/-- The `liminf` growth rates of minimal `(n, ε)`-spanning sets for open Bowen balls tend to the
`liminf` topological entropy as `ε → 0⁺`. -/
theorem tendsto_coverEntropyInfEntourage_dist_lt :
    Tendsto (fun ε : ℝ ↦ coverEntropyInfEntourage T F {p | dist p.1 p.2 < ε}) (𝓝[>] 0)
      (𝓝 (coverEntropyInf T F)) := by
  rw [coverEntropyInf_eq_iSup_basis Metric.uniformity_basis_dist]
  exact ((coverEntropyInfEntourage_antitone T F).comp_monotone
    Metric.monotone_ofPred_dist_lt).tendsto_nhdsGT_biSup 0

/-- The `liminf` growth rates of minimal `(n, ε)`-spanning sets for closed Bowen balls tend to the
`liminf` topological entropy as `ε → 0⁺`. -/
theorem tendsto_coverEntropyInfEntourage_dist_le :
    Tendsto (fun ε : ℝ ↦ coverEntropyInfEntourage T F {p | dist p.1 p.2 ≤ ε}) (𝓝[>] 0)
      (𝓝 (coverEntropyInf T F)) := by
  rw [coverEntropyInf_eq_iSup_basis Metric.uniformity_basis_dist_le]
  exact ((coverEntropyInfEntourage_antitone T F).comp_monotone
    Metric.monotone_ofPred_dist_le).tendsto_nhdsGT_biSup 0

end TauCeti
