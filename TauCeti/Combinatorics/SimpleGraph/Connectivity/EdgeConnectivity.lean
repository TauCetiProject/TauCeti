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
set of fewer than `k` edges. This file defines the numerical invariant
`SimpleGraph.edgeConnectivity G`, the supremum in `ℕ∞` of the natural thresholds at which `G` is
edge-connected, and proves that it records exactly those thresholds, also at `k = ⊤`. On at most
one vertex the edge connectivity is `⊤`; on a finite vertex type this characterizes the value `⊤`.

The edge connectivity of a graph on at least two vertices is at most every degree, hence at most
the minimum degree. This is one of **Whitney's inequalities**; the other, comparing vertex
connectivity with edge connectivity, is `SimpleGraph.vertexConnectivity_le_edgeConnectivity`.

The definition follows the proposal
[mathlib4#42494](https://github.com/leanprover-community/mathlib4/pull/42494), and agrees with
the multigraph invariant `Graph.edgeConnectivity` on `Graph.ofSimpleGraph G`. The inequalities
are those of H. Whitney, *Congruent graphs and the connectivity of graphs*, Amer. J. Math. 54
(1932), 150–168; see also R. Diestel, *Graph Theory*, 5th ed., Graduate Texts in Mathematics
173, Springer, 2017, Proposition 1.4.2.

## Main definitions

* `SimpleGraph.edgeConnectivity G`: the supremum in `ℕ∞` of the natural thresholds at which `G`
  is edge-connected.

## Main results

* `SimpleGraph.isEdgeConnected_iff_le_edgeConnectivity`: `G` is `k`-edge-connected exactly when
  `k ≤ G.edgeConnectivity`, for every `k : ℕ∞`.
* `SimpleGraph.edgeConnectivity_eq_top_iff`: on a finite vertex type, the edge connectivity is
  `⊤` exactly when there is at most one vertex.
* `SimpleGraph.IsEdgeConnected.le_minDegree`, `SimpleGraph.edgeConnectivity_le_minDegree`: on a
  finite type with at least two vertices, edge connectivity is at most the minimum degree.
-/

public section

namespace SimpleGraph

variable {V : Type*} {G H : SimpleGraph V} {k : ℕ∞}

variable (G) in
/-- The edge connectivity of a simple graph: the supremum in `ℕ∞` of the natural thresholds `k`
at which it is `k`-edge-connected. It is `⊤` when there is at most one vertex. -/
noncomputable def edgeConnectivity : ℕ∞ :=
  ⨆ (k : ℕ) (_ : G.IsEdgeConnected k), (k : ℕ∞)

/-- Edge connectivity records exactly the thresholds at which edge connectivity holds, including
the threshold `⊤`. -/
theorem isEdgeConnected_iff_le_edgeConnectivity : G.IsEdgeConnected k ↔ k ≤ G.edgeConnectivity := by
  have hnat (n : ℕ) : G.IsEdgeConnected n ↔ n ≤ G.edgeConnectivity :=
    (Antitone.natCast_le_iSup_iff (P := fun n : ℕ ↦ G.IsEdgeConnected n)
      (fun _ _ hmn h u v ↦ (h u v).anti (by gcongr)) IsEdgeConnected.zero).symm
  cases k with
  | top =>
    rw [isEdgeConnected_top_iff_forall_nat, top_le_iff, ENat.eq_top_iff_forall_ge]
    exact forall_congr' hnat
  | coe n => exact hnat n

/-- Edge connectivity is monotone in the graph. -/
@[gcongr]
theorem edgeConnectivity_mono (hGH : G ≤ H) : G.edgeConnectivity ≤ H.edgeConnectivity :=
  iSup₂_mono' fun k hk ↦ ⟨k, fun u v ↦ (hk u v).mono hGH, le_rfl⟩

@[simp]
theorem edgeConnectivity_of_subsingleton [Subsingleton V] : G.edgeConnectivity = ⊤ :=
  top_le_iff.mp <| isEdgeConnected_iff_le_edgeConnectivity.mp .of_subsingleton

/-- On at least two vertices, edge connectivity is at most the degree of every vertex. -/
theorem edgeConnectivity_le_degree [Nontrivial V] (u : V) [Fintype (G.neighborSet u)] :
    G.edgeConnectivity ≤ G.degree u :=
  IsEdgeConnected.le_degree (isEdgeConnected_iff_le_edgeConnectivity.mpr le_rfl)

/-- On a finite vertex type, the edge connectivity is `⊤` exactly when there is at most one
vertex. -/
theorem edgeConnectivity_eq_top_iff [Finite V] : G.edgeConnectivity = ⊤ ↔ Subsingleton V := by
  refine ⟨fun h ↦ ?_, fun _ ↦ edgeConnectivity_of_subsingleton⟩
  by_contra hV
  rw [not_subsingleton_iff_nontrivial] at hV
  obtain ⟨u⟩ := (inferInstance : Nonempty V)
  have := Fintype.ofFinite V
  classical
  exact ENat.natCast_ne_top _ (top_le_iff.mp (h ▸ G.edgeConnectivity_le_degree u))

/-- **Whitney's inequality** between edge connectivity and minimum degree, predicate form: a
`k`-edge-connected graph on a finite type with at least two vertices has minimum degree at least
`k`. -/
theorem IsEdgeConnected.le_minDegree [Fintype V] [DecidableRel G.Adj] [Nontrivial V]
    (h : G.IsEdgeConnected k) : k ≤ G.minDegree := by
  obtain ⟨u, hu⟩ := G.exists_minimal_degree_vertex
  exact hu ▸ h.le_degree

/-- **Whitney's inequality** between edge connectivity and minimum degree: on a finite type with
at least two vertices, the edge connectivity is at most the minimum degree. -/
theorem edgeConnectivity_le_minDegree [Fintype V] [DecidableRel G.Adj] [Nontrivial V] :
    G.edgeConnectivity ≤ G.minDegree :=
  IsEdgeConnected.le_minDegree (isEdgeConnected_iff_le_edgeConnectivity.mpr le_rfl)

end SimpleGraph
