/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import TauCeti.Dynamics.Expansive.FiniteWindow
public import TauCeti.Dynamics.TopologicalEntropy.Window

/-!
# Topological entropy of expansive maps

An expansive homeomorphism `T` of a compact metric space, with expansive constant `δ`, has finite
topological entropy, and its entropy is computed at any single scale `0 < ε ≤ δ`: it is the growth
rate of the largest dynamical nets for the closed entourage `{p | dist p.1 p.2 ≤ ε}` (sets whose
closed dynamical `ε`-balls are pairwise disjoint). The same holds for positively expansive
continuous maps.

The proof compares scales through the finite-window form of expansiveness
(`TauCeti.IsExpansive.exists_window`): for `η > 0` there is `N` such that points `ε`-close at all
times `|i| ≤ N` are `η`-close. Shifting a dynamical net for `{dist < η}` of length `n` back by
`T ^ N` gives a dynamical net for `{dist ≤ ε}` of length `n + 2 N`
(`TauCeti.netMaxcard_le_netMaxcard_add_of_window`), and such a comparison computes the entropy at
the scale `ε` (`TauCeti.coverEntropy_eq_netEntropyEntourage_of_window`).

## Main results

* `TauCeti.IsExpansive.coverEntropy_eq_netEntropyEntourage`: for an expansive homeomorphism and
  `0 < ε ≤ δ`, `coverEntropy T univ = netEntropyEntourage T univ {p | dist p.1 p.2 ≤ ε}`;
* `TauCeti.IsExpansive.coverEntropy_lt_top`: an expansive homeomorphism has finite entropy;
* `TauCeti.IsPositivelyExpansive.coverEntropy_eq_netEntropyEntourage`,
  `TauCeti.IsPositivelyExpansive.coverEntropy_lt_top`: the same for positively expansive maps.

## References

* R. Bowen, *Entropy-expansive maps*, Trans. Amer. Math. Soc. 164 (1972), 323–331, Theorem 2.4
  and Corollary 2.3, for the statement.
* P. Walters, *An Introduction to Ergodic Theory*, Graduate Texts in Mathematics 79, Springer,
  1982, Theorem 7.11 (with the window of Theorem 5.22), whose proof is followed here; the
  positively expansive theorems are its one-sided analogue.
-/

public section

namespace TauCeti

open Dynamics Set
open scoped Uniformity

variable {X : Type*} [PseudoMetricSpace X] [CompactSpace X]

/-- **Entropy of an expansive homeomorphism at a single scale.** If `T` is an expansive
homeomorphism of a compact metric space with constant `δ`, then for every `0 < ε ≤ δ` its
topological entropy is the growth rate of the largest dynamical nets for the closed entourage
`{p | dist p.1 p.2 ≤ ε}`. -/
theorem IsExpansive.coverEntropy_eq_netEntropyEntourage {T : Equiv.Perm X} {δ ε : ℝ}
    (h : IsExpansive T δ) (hT : Continuous T) (hT' : Continuous T.symm) (hε : 0 < ε)
    (hεδ : ε ≤ δ) :
    coverEntropy T univ = netEntropyEntourage T univ {p | dist p.1 p.2 ≤ ε} :=
  coverEntropy_eq_netEntropyEntourage_of_window Metric.uniformity_basis_dist
    (Metric.uniformity_basis_dist_le.mem_of_mem hε) fun _ hη ↦
      let ⟨N, hN⟩ := (h.mono hεδ).exists_window hT hT' hη
      ⟨2 * N, netMaxcard_le_netMaxcard_add_of_window T hN⟩

/-- **Expansive homeomorphisms have finite entropy.** An expansive homeomorphism of a compact
metric space with a positive expansive constant has finite topological entropy. -/
theorem IsExpansive.coverEntropy_lt_top {T : Equiv.Perm X} {δ : ℝ} (h : IsExpansive T δ)
    (hT : Continuous T) (hT' : Continuous T.symm) (hδ : 0 < δ) :
    coverEntropy T univ < ⊤ :=
  coverEntropy_lt_top_of_window Metric.uniformity_basis_dist
    (Metric.uniformity_basis_dist_le.mem_of_mem hδ)
    (fun _ hη ↦
      let ⟨N, hN⟩ := h.exists_window hT hT' hη
      ⟨2 * N, netMaxcard_le_netMaxcard_add_of_window T hN⟩)
    isCompact_univ (mapsTo_univ _ _)

/-- **Entropy of a positively expansive map at a single scale.** If a continuous map `T` of a
compact metric space is positively expansive with constant `δ`, then for every `0 < ε ≤ δ` its
topological entropy is the growth rate of the largest dynamical nets for the closed entourage
`{p | dist p.1 p.2 ≤ ε}`. -/
theorem IsPositivelyExpansive.coverEntropy_eq_netEntropyEntourage {T : X → X} {δ ε : ℝ}
    (h : IsPositivelyExpansive T δ) (hT : Continuous T) (hε : 0 < ε) (hεδ : ε ≤ δ) :
    coverEntropy T univ = netEntropyEntourage T univ {p | dist p.1 p.2 ≤ ε} :=
  coverEntropy_eq_netEntropyEntourage_of_window Metric.uniformity_basis_dist
    (Metric.uniformity_basis_dist_le.mem_of_mem hε) fun _ hη ↦
      let ⟨N, hN⟩ := (h.mono hεδ).exists_window hT hη
      ⟨N, netMaxcard_le_netMaxcard_add_of_forward_window T univ hN⟩

/-- **Positively expansive maps have finite entropy.** A continuous positively expansive map of a
compact metric space with a positive expansive constant has finite topological entropy. -/
theorem IsPositivelyExpansive.coverEntropy_lt_top {T : X → X} {δ : ℝ}
    (h : IsPositivelyExpansive T δ) (hT : Continuous T) (hδ : 0 < δ) :
    coverEntropy T univ < ⊤ :=
  coverEntropy_lt_top_of_window Metric.uniformity_basis_dist
    (Metric.uniformity_basis_dist_le.mem_of_mem hδ)
    (fun _ hη ↦
      let ⟨N, hN⟩ := h.exists_window hT hη
      ⟨N, netMaxcard_le_netMaxcard_add_of_forward_window T univ hN⟩)
    isCompact_univ (mapsTo_univ _ _)

end TauCeti
