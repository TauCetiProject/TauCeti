/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Weighted.Cluster.Interface
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import TauCeti.Analysis.BoundedVariation.Weighted.ZeroPerimeter

/-!
# The interface graph of a cluster

The **interface graph** of a cluster `Ω` (`TauCeti.Cluster.interfaceGraph`) has the indices of
the cells as vertices, with an edge `{i, j}` whenever `i ≠ j` and the interface area `A_ij` is
nonzero. For a `C¹` weight in dimension `n ≥ 2`, if every cell has positive measure the interface
graph is connected (`TauCeti.Cluster.interfaceGraph_connected`): the cells reachable from one
cell form a union `U` with `P_μ(U) = Σ_{i ∈ S, j ∉ S} A_ij = 0`, so `U` is null or conull
(`TauCeti.volume_eq_zero_or_volume_compl_eq_zero_of_weightedPerimeter_eq_zero`), which forces
every cell to be reachable. This route holds for every `C¹` weight; Milman and Neeman use the
Gaussian isoperimetric inequality instead.

## References

* E. Milman, J. Neeman, *The Gaussian double-bubble and multi-bubble conjectures*, Ann. of Math.
  (2022), Lemma 3.4.
-/

public section

noncomputable section

open MeasureTheory Set Module

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {W : E → ℝ} {q : ℕ}

namespace Cluster

/-- The **interface graph** of a cluster: the simple graph on the indices of the cells with an
edge `{i, j}` whenever `i ≠ j` and the interface area `A_ij` is nonzero. -/
def interfaceGraph (Ω : Cluster W q) : SimpleGraph (Fin q) :=
  SimpleGraph.fromRel fun i j => Ω.interfaceArea i j ≠ 0

theorem interfaceGraph_adj {Ω : Cluster W q} {i j : Fin q} :
    Ω.interfaceGraph.Adj i j ↔ i ≠ j ∧ Ω.interfaceArea i j ≠ 0 := by
  rw [interfaceGraph, SimpleGraph.fromRel_adj, Ω.interfaceArea_comm j i, or_self]

/-- **The interface graph is connected.** For a `C¹` weight in dimension `n ≥ 2`, if every cell
of a cluster has positive weighted measure, then its interface graph is connected. -/
theorem interfaceGraph_connected (hW : ContDiff ℝ 1 W) (hn : 2 ≤ finrank ℝ E) [NeZero q]
    (Ω : Cluster W q) (hpos : ∀ i, weightedMeasure W (Ω.cell i) ≠ 0) :
    Ω.interfaceGraph.Connected := by
  classical
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨0, fun j => ?_⟩
  by_contra hj
  set S : Finset (Fin q) := Finset.univ.filter fun k => Ω.interfaceGraph.Reachable 0 k with hS
  have hmem {k : Fin q} : k ∈ S ↔ Ω.interfaceGraph.Reachable 0 k := by simp [hS]
  -- No interface joins a cell of `S` to a cell outside `S`.
  have h0 : weightedPerimeter W ⊤ (⋃ i ∈ S, Ω.cell i) = 0 := by
    rw [Ω.weightedPerimeter_biUnion_cell_eq_sum_interfaceArea hW hn]
    refine Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun k hk => ?_
    by_contra hne
    rw [Finset.mem_compl, hmem] at hk
    have hik : i ≠ k := fun h => hk (h ▸ hmem.1 hi)
    exact hk ((hmem.1 hi).trans (interfaceGraph_adj.2 ⟨hik, hne⟩).reachable)
  have hvol (k : Fin q) (h : volume (Ω.cell k) = 0) : False :=
    hpos k (weightedMeasure_absolutelyContinuous h)
  rcases volume_eq_zero_or_volume_compl_eq_zero_of_weightedPerimeter_eq_zero hW
    (Ω.nullMeasurableSet_biUnion_cell S) h0 with h | h
  · exact hvol 0 (measure_mono_null (subset_biUnion_of_mem (u := Ω.cell)
      (hmem.2 (SimpleGraph.Reachable.refl 0))) h)
  · refine hvol j (measure_mono_null ?_ h)
    intro x hx hxU
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.1 hxU
    have hij : i ≠ j := fun h => hj (h ▸ hmem.1 hi)
    exact disjoint_left.1 (Ω.pairwise_disjoint hij) hxi hx

end Cluster

end TauCeti
