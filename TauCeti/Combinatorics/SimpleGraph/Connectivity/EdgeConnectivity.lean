/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.EdgeConnectivity
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import TauCeti.Data.ENat.Lattice

/-!
# The edge connectivity of a simple graph

Mathlib's `SimpleGraph.IsEdgeConnected G k` says that `G` stays preconnected after deleting any
set of fewer than `k` edges. This file introduces the numerical invariant
`G.edgeConnectivity : ℕ∞`, the supremum of the natural thresholds at which `G` is edge-connected,
and bounds it by vertex degrees. As for multigraphs, a graph on at most one vertex has edge
connectivity `⊤`.

The supremum definition and the degree bounds follow the proposal
[mathlib4#42494](https://github.com/leanprover-community/mathlib4/pull/42494), and the invariant
matches the multigraph `Graph.edgeConnectivity` on `Graph.ofSimpleGraph`.

## Main definitions

* `SimpleGraph.edgeConnectivity G`: the supremum in `ℕ∞` of the natural thresholds `k` at which
  `G` is `k`-edge-connected.

## Main results

* `SimpleGraph.isEdgeConnected_iff_le_edgeConnectivity`: the invariant records exactly the
  thresholds in `ℕ∞` at which `G` is edge-connected.
* `SimpleGraph.edgeConnectivity_le_degree`, `SimpleGraph.edgeConnectivity_le_minDegree`: on at
  least two vertices, edge connectivity is at most every degree, hence at most the minimum degree.
* `SimpleGraph.edgeConnectivity_eq_top_iff`: on a finite vertex type, edge connectivity is `⊤`
  exactly when there is at most one vertex.
-/

public section

namespace SimpleGraph

variable {V : Type*} {G H : SimpleGraph V} {k : ℕ∞}

variable (G) in
/-- The edge connectivity of a simple graph: the supremum in `ℕ∞` of the natural thresholds `k` at
which it is `k`-edge-connected. It is `⊤` when there is at most one vertex. -/
noncomputable def edgeConnectivity : ℕ∞ :=
  ⨆ (k : ℕ) (_ : G.IsEdgeConnected k), (k : ℕ∞)

/-- Edge connectivity records exactly the thresholds at which the graph is edge-connected. -/
theorem isEdgeConnected_iff_le_edgeConnectivity : G.IsEdgeConnected k ↔ k ≤ G.edgeConnectivity := by
  have hnat (n : ℕ) : G.IsEdgeConnected n ↔ n ≤ G.edgeConnectivity :=
    (Antitone.natCast_le_iSup_iff
      (fun _ _ hmn (h : G.IsEdgeConnected _) u v ↦ (h u v).anti (Nat.cast_le.2 hmn)) .zero).symm
  cases k with
  | top => simp [isEdgeConnected_top_iff_forall_nat, hnat, ENat.eq_top_iff_forall_ge]
  | coe n => exact hnat n

/-- Edge connectivity is monotone in the graph. -/
@[gcongr]
theorem edgeConnectivity_mono (hGH : G ≤ H) : G.edgeConnectivity ≤ H.edgeConnectivity :=
  iSup_mono fun _ ↦ iSup_mono' fun hk ↦ ⟨fun u v ↦ (hk u v).mono hGH, le_rfl⟩

/-- A graph on at most one vertex has edge connectivity `⊤`. -/
@[simp]
theorem edgeConnectivity_eq_top_of_subsingleton [Subsingleton V] : G.edgeConnectivity = ⊤ :=
  top_le_iff.1 (isEdgeConnected_iff_le_edgeConnectivity.1 .of_subsingleton)

/-! ### Degree bounds -/

/-- On at least two vertices, edge connectivity is at most the degree of every vertex of finite
degree. -/
theorem edgeConnectivity_le_degree [Nontrivial V] (u : V) [Fintype (G.neighborSet u)] :
    G.edgeConnectivity ≤ G.degree u :=
  (isEdgeConnected_iff_le_edgeConnectivity.2 le_rfl).le_degree

/-- On a finite vertex type with at least two vertices, a `k`-edge-connected graph has minimum
degree at least `k`. -/
theorem IsEdgeConnected.le_minDegree [Fintype V] [DecidableRel G.Adj] [Nontrivial V]
    (h : G.IsEdgeConnected k) : k ≤ G.minDegree := by
  obtain ⟨u, hu⟩ := G.exists_minimal_degree_vertex
  rw [hu]
  exact h.le_degree

/-- On a finite vertex type with at least two vertices, edge connectivity is at most the minimum
degree. -/
theorem edgeConnectivity_le_minDegree [Fintype V] [DecidableRel G.Adj] [Nontrivial V] :
    G.edgeConnectivity ≤ G.minDegree :=
  (isEdgeConnected_iff_le_edgeConnectivity.2 le_rfl).le_minDegree

/-- On a finite vertex type, edge connectivity is `⊤` exactly when there is at most one vertex. -/
theorem edgeConnectivity_eq_top_iff [Finite V] : G.edgeConnectivity = ⊤ ↔ Subsingleton V := by
  refine ⟨fun h ↦ ?_, fun _ ↦ edgeConnectivity_eq_top_of_subsingleton⟩
  by_contra hV
  rw [not_subsingleton_iff_nontrivial] at hV
  have := Fintype.ofFinite V
  classical
  obtain ⟨u⟩ := (inferInstance : Nonempty V)
  exact ENat.natCast_ne_top (G.degree u) (top_le_iff.1 (h ▸ G.edgeConnectivity_le_degree u))

end SimpleGraph
