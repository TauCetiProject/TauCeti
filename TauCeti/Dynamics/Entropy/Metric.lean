/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Dynamics.TopologicalEntropy.NetEntropy
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Order.Monotone
public import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# Metric forms of topological entropy

On a pseudometric space, Mathlib's topological entropy `Dynamics.coverEntropy T F` is the limit as
`ε → 0⁺` of the Bowen–Dinaburg exponential growth rates of maximal `(n, ε)`-separated sets and of
minimal `(n, ε)`-spanning sets. We prove this for both conventions: separation `ε ≤ dist`
(entourage `{p | dist p.1 p.2 < ε}`, open Bowen balls) and separation `ε < dist` (entourage
`{p | dist p.1 p.2 ≤ ε}`, closed Bowen balls). In particular the four limits agree.

## Main results

* `TauCeti.tendsto_netEntropyEntourage_dist_lt`, `TauCeti.tendsto_netEntropyEntourage_dist_le`:
  the separated-set growth rates tend to the topological entropy as `ε → 0⁺`.
* `TauCeti.tendsto_coverEntropyEntourage_dist_lt`, `TauCeti.tendsto_coverEntropyEntourage_dist_le`:
  the same for spanning sets (open and closed Bowen balls).
* `TauCeti.tendsto_netEntropyInfEntourage_dist_lt` and its three siblings: the same for the
  `liminf` growth rates and `Dynamics.coverEntropyInf`.
-/

public section

namespace TauCeti

open Dynamics Filter Set Topology

variable {X : Type*} [PseudoMetricSpace X] (T : X → X) (F : Set X)

/-- The supremum over `ε > 0` of an antitone function `ℝ → EReal` is its limit as `ε → 0⁺`. -/
private lemma tendsto_iSup_of_antitone {f : ℝ → EReal} (hf : Antitone f) :
    Tendsto f (𝓝[>] 0) (𝓝 (⨆ ε > 0, f ε)) := by
  have h := hf.tendsto_nhdsGT 0
  rwa [sSup_image] at h

private lemma monotone_dist_lt :
    Monotone fun ε : ℝ ↦ ({p | dist p.1 p.2 < ε} : SetRel X X) :=
  fun _ _ h _ hp ↦ lt_of_lt_of_le hp h

private lemma monotone_dist_le :
    Monotone fun ε : ℝ ↦ ({p | dist p.1 p.2 ≤ ε} : SetRel X X) :=
  fun _ _ h _ hp ↦ le_trans hp h

/-- The growth rates of maximal `(n, ε)`-separated sets (separation `ε ≤ dist`) tend to the
topological entropy as `ε → 0⁺`. -/
theorem tendsto_netEntropyEntourage_dist_lt :
    Tendsto (fun ε : ℝ ↦ netEntropyEntourage T F {p | dist p.1 p.2 < ε}) (𝓝[>] 0)
      (𝓝 (coverEntropy T F)) := by
  rw [coverEntropy_eq_iSup_basis_netEntropyEntourage Metric.uniformity_basis_dist]
  exact tendsto_iSup_of_antitone fun _ _ h ↦
    netEntropyEntourage_antitone T F (monotone_dist_lt h)

/-- The growth rates of maximal `(n, ε)`-separated sets (separation `ε < dist`) tend to the
topological entropy as `ε → 0⁺`. -/
theorem tendsto_netEntropyEntourage_dist_le :
    Tendsto (fun ε : ℝ ↦ netEntropyEntourage T F {p | dist p.1 p.2 ≤ ε}) (𝓝[>] 0)
      (𝓝 (coverEntropy T F)) := by
  rw [coverEntropy_eq_iSup_basis_netEntropyEntourage Metric.uniformity_basis_dist_le]
  exact tendsto_iSup_of_antitone fun _ _ h ↦
    netEntropyEntourage_antitone T F (monotone_dist_le h)

/-- The growth rates of minimal `(n, ε)`-spanning sets for open Bowen balls tend to the
topological entropy as `ε → 0⁺`. -/
theorem tendsto_coverEntropyEntourage_dist_lt :
    Tendsto (fun ε : ℝ ↦ coverEntropyEntourage T F {p | dist p.1 p.2 < ε}) (𝓝[>] 0)
      (𝓝 (coverEntropy T F)) := by
  rw [coverEntropy_eq_iSup_basis Metric.uniformity_basis_dist]
  exact tendsto_iSup_of_antitone fun _ _ h ↦
    coverEntropyEntourage_antitone T F (monotone_dist_lt h)

/-- The growth rates of minimal `(n, ε)`-spanning sets for closed Bowen balls tend to the
topological entropy as `ε → 0⁺`. -/
theorem tendsto_coverEntropyEntourage_dist_le :
    Tendsto (fun ε : ℝ ↦ coverEntropyEntourage T F {p | dist p.1 p.2 ≤ ε}) (𝓝[>] 0)
      (𝓝 (coverEntropy T F)) := by
  rw [coverEntropy_eq_iSup_basis Metric.uniformity_basis_dist_le]
  exact tendsto_iSup_of_antitone fun _ _ h ↦
    coverEntropyEntourage_antitone T F (monotone_dist_le h)

/-- The `liminf` growth rates of maximal `(n, ε)`-separated sets (separation `ε ≤ dist`) tend to
the `liminf` topological entropy as `ε → 0⁺`. -/
theorem tendsto_netEntropyInfEntourage_dist_lt :
    Tendsto (fun ε : ℝ ↦ netEntropyInfEntourage T F {p | dist p.1 p.2 < ε}) (𝓝[>] 0)
      (𝓝 (coverEntropyInf T F)) := by
  rw [coverEntropyInf_eq_iSup_basis_netEntropyInfEntourage Metric.uniformity_basis_dist]
  exact tendsto_iSup_of_antitone fun _ _ h ↦
    netEntropyInfEntourage_antitone T F (monotone_dist_lt h)

/-- The `liminf` growth rates of maximal `(n, ε)`-separated sets (separation `ε < dist`) tend to
the `liminf` topological entropy as `ε → 0⁺`. -/
theorem tendsto_netEntropyInfEntourage_dist_le :
    Tendsto (fun ε : ℝ ↦ netEntropyInfEntourage T F {p | dist p.1 p.2 ≤ ε}) (𝓝[>] 0)
      (𝓝 (coverEntropyInf T F)) := by
  rw [coverEntropyInf_eq_iSup_basis_netEntropyInfEntourage Metric.uniformity_basis_dist_le]
  exact tendsto_iSup_of_antitone fun _ _ h ↦
    netEntropyInfEntourage_antitone T F (monotone_dist_le h)

/-- The `liminf` growth rates of minimal `(n, ε)`-spanning sets for open Bowen balls tend to the
`liminf` topological entropy as `ε → 0⁺`. -/
theorem tendsto_coverEntropyInfEntourage_dist_lt :
    Tendsto (fun ε : ℝ ↦ coverEntropyInfEntourage T F {p | dist p.1 p.2 < ε}) (𝓝[>] 0)
      (𝓝 (coverEntropyInf T F)) := by
  rw [coverEntropyInf_eq_iSup_basis Metric.uniformity_basis_dist]
  exact tendsto_iSup_of_antitone fun _ _ h ↦
    coverEntropyInfEntourage_antitone T F (monotone_dist_lt h)

/-- The `liminf` growth rates of minimal `(n, ε)`-spanning sets for closed Bowen balls tend to the
`liminf` topological entropy as `ε → 0⁺`. -/
theorem tendsto_coverEntropyInfEntourage_dist_le :
    Tendsto (fun ε : ℝ ↦ coverEntropyInfEntourage T F {p | dist p.1 p.2 ≤ ε}) (𝓝[>] 0)
      (𝓝 (coverEntropyInf T F)) := by
  rw [coverEntropyInf_eq_iSup_basis Metric.uniformity_basis_dist_le]
  exact tendsto_iSup_of_antitone fun _ _ h ↦
    coverEntropyInfEntourage_antitone T F (monotone_dist_le h)

end TauCeti
