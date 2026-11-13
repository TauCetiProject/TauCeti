/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Connectivity.Ear.EdgeConnected
public import TauCeti.Combinatorics.Graph.Connectivity.Ear.Extension
public import TauCeti.Combinatorics.Graph.Connectivity.Ear.VertexStart

import Mathlib.Data.Set.Card

/-!
# Ear characterization of two-edge-connected multigraphs

A multigraph with a nonempty actual vertex set and finitely many actual edges is
`2`-edge-connected exactly when it admits an ear decomposition (equivalently, a vertex-started ear
decomposition).  The forward direction iterates the finiteness-free single-ear extension theorem
from `Ear.Extension`: as long as a partial ear decomposition covers only a proper subgraph `H < G`,
`2`-edge-connectivity supplies an open or closed ear over `H` that strictly shrinks `E(G) \ E(H)`.
Finiteness of `E(G)` alone makes this iteration terminate (`Graph.EarDecomposition.extend`), while
preserving the starting partial decomposition as a prefix (`Graph.EarDecomposition.prefix_extend`).

In particular, starting from a prescribed actual vertex
(`Graph.IsEdgeConnected.earDecompositionOfVertex`) or cycle
(`Graph.IsEdgeConnected.earDecompositionOfCycle`) constructs a full ear decomposition beginning
there.  Combined with cycle-to-vertex start normalization in `Ear.VertexStart` and the
finiteness-free converse in `Ear.EdgeConnected`, this gives both the vertex-started and unrestricted
ear characterizations for multigraphs and, via `Graph.ofSimpleGraph`, for simple graphs.

The theorem goes back to H. E. Robbins (1939), *A theorem on graphs, with an application to a
problem of traffic control*, Amer. Math. Monthly 46, 281–283; the argument follows R. Diestel,
*Graph Theory*, Chapter 3, with edge identities retained for parallel edges and loops.

## Main results

* `Graph.EarDecomposition.extend`, `Graph.EarDecomposition.prefix_extend`: with finitely many
  actual edges, complete any partial ear decomposition to the whole graph while preserving it as a
  prefix.
* `Graph.IsEdgeConnected.earDecompositionOfVertex`,
  `Graph.IsEdgeConnected.earDecompositionOfCycle`: construct an ear decomposition starting at a
  chosen actual vertex or cycle.
* `Graph.isEdgeConnected_two_iff_exists_isVertexStart_earDecomposition`,
  `Graph.isEdgeConnected_two_iff_nonempty_earDecomposition`,
  `Graph.connected_and_forall_not_isBridge_iff_nonempty_earDecomposition`: ear characterizations of
  `2`-edge-connected multigraphs.
* `SimpleGraph.isEdgeConnected_two_iff_exists_isVertexStart_earDecomposition`,
  `SimpleGraph.isEdgeConnected_two_iff_nonempty_earDecomposition_ofSimpleGraph`: the corresponding
  simple-graph characterizations via `Graph.ofSimpleGraph`.
-/

public section

open Set

universe u v

namespace Graph

variable {α : Type u} {β : Type v} {G H : Graph α β}

namespace EarDecomposition

private theorem ncard_sdiff_add_lt [Finite E(G)] {H : Graph α β} (ear : G.Ear H) :
    (E(G) \ E(ear.add)).ncard < (E(G) \ E(H)).ncard :=
  Set.ncard_lt_ncard ear.sdiff_edgeSet_add_ssubset (Set.toFinite E(G)).sdiff

open Classical in
/-- Complete any partial ear decomposition in a `2`-edge-connected multigraph with finitely many
actual edges to an ear decomposition of the whole multigraph. -/
noncomputable def extend [Finite E(G)] (hG : G.IsEdgeConnected 2) {H : Graph α β}
    (d : G.EarDecomposition H) : G.EarDecomposition G :=
  if h : H = G then
    d.copy h
  else
    let ear : G.Ear H :=
      (d.vertexSet_nonempty.exists_ear_of_lt (lt_of_le_of_ne d.final_le h) hG).choose
    (d.snoc ear).extend hG
termination_by (E(G) \ E(H)).ncard
decreasing_by exact ncard_sdiff_add_lt _

private theorem extend_spec [Finite E(G)] (hG : G.IsEdgeConnected 2) {H : Graph α β}
    (d : G.EarDecomposition H) :
    ∃ hle : d.length ≤ (d.extend hG).length,
      (∀ i : Fin (d.length + 1),
        (d.extend hG).graphAfter (Fin.castLE (Nat.succ_le_succ hle) i) = d.graphAfter i) ∧
      (∀ i : Fin d.length,
        (d.extend hG).earAt (Fin.castLE hle i) = d.earAt i) ∧
      HEq (d.extend hG).start d.start := by
  fun_induction d.extend hG with
  | case1 d =>
      refine ⟨(d.length_copy rfl).ge, fun i ↦ ?_, fun i ↦ ?_, d.heq_start_copy rfl⟩
      · rw [d.graphAfter_copy]
        exact congrArg d.graphAfter (Fin.ext rfl)
      · rw [d.earAt_copy]
        exact congrArg d.earAt (Fin.ext rfl)
  | case2 _ d _ ear ih =>
      obtain ⟨hle', hgraph', hear', hstart'⟩ := ih
      have hle₀ : d.length ≤ (d.snoc ear).length :=
        (Nat.le_succ d.length).trans_eq (d.length_snoc ear).symm
      have hle : d.length ≤ ((d.snoc ear).extend hG).length := hle₀.trans hle'
      refine ⟨hle, fun i ↦ ?_, fun i ↦ ?_, hstart'.trans (d.heq_start_snoc ear)⟩
      · let i' : Fin ((d.snoc ear).length + 1) :=
          (Fin.cast (d.length_snoc ear).symm i).castSucc
        have hi : Fin.castLE (Nat.succ_le_succ hle) i =
            Fin.castLE (Nat.succ_le_succ hle') i' := Fin.ext (by simp [i'])
        rw [hi, hgraph' i']
        dsimp only [i']
        exact d.graphAfter_snoc_castSucc ear i
      · let i' : Fin (d.snoc ear).length :=
          Fin.cast (d.length_snoc ear).symm i.castSucc
        have hi : Fin.castLE hle i = Fin.castLE hle' i' := Fin.ext (by simp [i'])
        rw [hi, hear' i']
        dsimp only [i']
        exact d.earAt_snoc_castSucc ear i

/-- Completing a partial ear decomposition does not decrease its length. -/
theorem length_le_length_extend [Finite E(G)] (hG : G.IsEdgeConnected 2) {H : Graph α β}
    (d : G.EarDecomposition H) : d.length ≤ (d.extend hG).length :=
  let ⟨hle, _⟩ := d.extend_spec hG
  hle

/-- Completing a partial ear decomposition preserves all of its stage graphs. -/
@[simp]
theorem graphAfter_extend_castLE [Finite E(G)] (hG : G.IsEdgeConnected 2) {H : Graph α β}
    (d : G.EarDecomposition H) (i : Fin (d.length + 1)) :
    (d.extend hG).graphAfter
      (Fin.castLE (Nat.succ_le_succ (d.length_le_length_extend hG)) i) = d.graphAfter i :=
  let ⟨_, hgraph, _, _⟩ := d.extend_spec hG
  hgraph i

/-- Completing a partial ear decomposition preserves its initial graph. -/
theorem initial_extend [Finite E(G)] (hG : G.IsEdgeConnected 2) {H : Graph α β}
    (d : G.EarDecomposition H) : (d.extend hG).initial = d.initial := by
  simpa only [initial_eq_graphAfter, Fin.castLE_zero] using d.graphAfter_extend_castLE hG 0

/-- Completing a partial ear decomposition preserves all of its displayed ears. -/
@[simp]
theorem earAt_extend_castLE [Finite E(G)] (hG : G.IsEdgeConnected 2) {H : Graph α β}
    (d : G.EarDecomposition H) (i : Fin d.length) :
    (d.extend hG).earAt (Fin.castLE (d.length_le_length_extend hG) i) = d.earAt i :=
  let ⟨_, _, hear, _⟩ := d.extend_spec hG
  hear i

/-- Completing a partial ear decomposition preserves its initial stage data. -/
theorem heq_start_extend [Finite E(G)] (hG : G.IsEdgeConnected 2) {H : Graph α β}
    (d : G.EarDecomposition H) : HEq (d.extend hG).start d.start :=
  let ⟨_, _, _, hstart⟩ := d.extend_spec hG
  hstart

/-- Completing a partial ear decomposition preserves whether it starts from a cycle. -/
@[simp]
theorem start_isCycle_extend [Finite E(G)] (hG : G.IsEdgeConnected 2) {H : Graph α β}
    (d : G.EarDecomposition H) : (d.extend hG).start.IsCycle ↔ d.start.IsCycle :=
  EarStart.isCycle_iff_of_heq (by simpa using d.graphAfter_extend_castLE hG 0)
    (d.heq_start_extend hG)

/-- Completing a partial ear decomposition preserves whether it starts from a single vertex. -/
@[simp]
theorem isVertexStart_extend [Finite E(G)] (hG : G.IsEdgeConnected 2) {H : Graph α β}
    (d : G.EarDecomposition H) : (d.extend hG).IsVertexStart ↔ d.IsVertexStart := by
  simp only [isVertexStart_iff, d.initial_extend hG]

/-- Taking the prefix of `d.extend hG` of length `d.length` recovers `d`. -/
theorem prefix_extend [Finite E(G)] (hG : G.IsEdgeConnected 2) {H : Graph α β}
    (d : G.EarDecomposition H) :
    ((d.extend hG).prefix
      (Fin.castLE (Nat.succ_le_succ (d.length_le_length_extend hG)) (Fin.last d.length))).copy
      ((d.graphAfter_extend_castLE hG (Fin.last d.length)).trans d.graphAfter_last) = d := by
  let i₀ : Fin ((d.extend hG).length + 1) :=
    Fin.castLE (Nat.succ_le_succ (d.length_le_length_extend hG)) (Fin.last d.length)
  let hH : (d.extend hG).graphAfter i₀ = H :=
    (d.graphAfter_extend_castLE hG (Fin.last d.length)).trans d.graphAfter_last
  let p := ((d.extend hG).prefix i₀).copy hH
  have hi₀ : i₀.val = d.length := by simp [i₀]
  have hlen : p.length = d.length := by simp [p, hi₀]
  refine (ext d p hlen.symm
    ((Fin.heq_fun_iff (congrArg (· + 1) hlen.symm)).mpr fun j ↦ ?_)
    (((heq_start_copy _ hH).trans (heq_start_prefix (d.extend hG) i₀)).trans
      (d.heq_start_extend hG)).symm
    ((Fin.heq_fun_iff hlen.symm).mpr fun j ↦ ?_)).symm
  · let j' : Fin (i₀.val + 1) := Fin.cast (congrArg (· + 1) hi₀.symm) j
    have hj₁ : Fin.cast (congrArg (· + 1) (length_copy _ hH))
          (⟨j, congrArg (· + 1) hlen.symm ▸ j.2⟩ : Fin (p.length + 1)) =
        Fin.cast (congrArg (· + 1) (length_prefix (d.extend hG) i₀).symm) j' :=
      Fin.ext (by simp [j'])
    have hj₂ : Fin.castLE (Nat.succ_le_iff.mpr i₀.isLt) j' =
        Fin.castLE (Nat.succ_le_succ (d.length_le_length_extend hG)) j :=
      Fin.ext (by simp [j'])
    dsimp only [p]
    rw [graphAfter_copy, hj₁, graphAfter_prefix, hj₂, d.graphAfter_extend_castLE]
  · let j' : Fin i₀.val := Fin.cast hi₀.symm j
    have hj₁ : Fin.cast (length_copy _ hH) (⟨j, hlen.symm ▸ j.2⟩ : Fin p.length) =
        Fin.cast (length_prefix (d.extend hG) i₀).symm j' :=
      Fin.ext (by simp [j'])
    have hj₂ : Fin.castLE (Nat.le_of_lt_succ i₀.isLt) j' =
        Fin.castLE (d.length_le_length_extend hG) j :=
      Fin.ext (by simp [j'])
    dsimp only [p]
    rw [earAt_copy, hj₁, earAt_prefix, hj₂, d.earAt_extend_castLE]

end EarDecomposition

/-- An ear decomposition of a prefix subgraph of a `2`-edge-connected multigraph with finitely many
actual edges extends to an ear decomposition of the whole graph with the same initial graph. -/
theorem IsEdgeConnected.exists_earDecomposition_of_earDecomposition [Finite E(G)]
    (hG : G.IsEdgeConnected 2) (d₀ : G.EarDecomposition H) :
    ∃ d : G.EarDecomposition G, d.initial = d₀.initial :=
  ⟨d₀.extend hG, d₀.initial_extend hG⟩

/-- Build an ear decomposition of a `2`-edge-connected multigraph with finitely many actual edges
starting from a prescribed actual vertex. -/
noncomputable def IsEdgeConnected.earDecompositionOfVertex [Finite E(G)] (hG : G.IsEdgeConnected 2)
    (v : V(G)) : G.EarDecomposition G :=
  (EarDecomposition.vertex v).extend hG

/-- The ear decomposition built from a prescribed actual vertex has that vertex as initial graph. -/
theorem IsEdgeConnected.initial_earDecompositionOfVertex [Finite E(G)] (hG : G.IsEdgeConnected 2)
    (v : V(G)) : (hG.earDecompositionOfVertex v).initial = Graph.noEdge {v.1} β := by
  rw [earDecompositionOfVertex, EarDecomposition.initial_extend, EarDecomposition.initial_vertex]

@[simp]
theorem IsEdgeConnected.isVertexStart_earDecompositionOfVertex [Finite E(G)]
    (hG : G.IsEdgeConnected 2) (v : V(G)) :
    (hG.earDecompositionOfVertex v).IsVertexStart := by
  rw [earDecompositionOfVertex, EarDecomposition.isVertexStart_extend]
  exact EarDecomposition.isVertexStart_vertex v

@[simp]
theorem IsEdgeConnected.not_start_isCycle_earDecompositionOfVertex [Finite E(G)]
    (hG : G.IsEdgeConnected 2) (v : V(G)) :
    ¬ (hG.earDecompositionOfVertex v).start.IsCycle := by
  rw [earDecompositionOfVertex, EarDecomposition.start_isCycle_extend]
  exact EarDecomposition.not_start_isCycle_vertex v

/-- A `2`-edge-connected multigraph with finitely many actual edges has a vertex-starting ear
decomposition beginning at any chosen actual vertex. -/
theorem IsEdgeConnected.exists_earDecomposition [Finite E(G)] (hG : G.IsEdgeConnected 2)
    (v : V(G)) : ∃ d : G.EarDecomposition G, d.initial = Graph.noEdge {v.1} β :=
  ⟨hG.earDecompositionOfVertex v, hG.initial_earDecompositionOfVertex v⟩

/-- Build an ear decomposition of a `2`-edge-connected multigraph with finitely many actual edges
starting from a prescribed cycle. -/
noncomputable def IsEdgeConnected.earDecompositionOfCycle [Finite E(G)] (hG : G.IsEdgeConnected 2)
    {s : α} (walk : G.Walk s s) (isCycle : walk.IsCycle) : G.EarDecomposition G :=
  (EarDecomposition.cycle walk isCycle).extend hG

/-- The ear decomposition built from a prescribed cycle has its traced graph as initial graph. -/
theorem IsEdgeConnected.initial_earDecompositionOfCycle [Finite E(G)] (hG : G.IsEdgeConnected 2)
    {s : α} (walk : G.Walk s s) (isCycle : walk.IsCycle) :
    (hG.earDecompositionOfCycle walk isCycle).initial = G.walkGraph walk := by
  rw [earDecompositionOfCycle, EarDecomposition.initial_extend, EarDecomposition.initial_cycle]

@[simp]
theorem IsEdgeConnected.start_isCycle_earDecompositionOfCycle [Finite E(G)]
    (hG : G.IsEdgeConnected 2) {s : α} (walk : G.Walk s s) (isCycle : walk.IsCycle) :
    (hG.earDecompositionOfCycle walk isCycle).start.IsCycle := by
  rw [earDecompositionOfCycle, EarDecomposition.start_isCycle_extend]
  exact EarDecomposition.start_isCycle_cycle walk isCycle

/-- **Ear characterization of two-edge-connectivity** (vertex-started form). A multigraph with a
nonempty actual vertex set and finitely many actual edges is `2`-edge-connected exactly when it
admits an ear decomposition built from one vertex by adjoining open or closed ears. -/
theorem isEdgeConnected_two_iff_exists_isVertexStart_earDecomposition
    [Finite E(G)] [Nonempty V(G)] :
    G.IsEdgeConnected 2 ↔ ∃ d : G.EarDecomposition G, d.IsVertexStart :=
  ⟨fun hG ↦
    let v := Classical.arbitrary V(G)
    ⟨hG.earDecompositionOfVertex v, hG.isVertexStart_earDecompositionOfVertex v⟩,
   fun ⟨d, _⟩ ↦ d.isEdgeConnected_two⟩

/-- **Ear characterization of two-edge-connectivity**. A multigraph with a nonempty actual vertex
set and finitely many actual edges is `2`-edge-connected if and only if it admits an ear
decomposition. -/
theorem isEdgeConnected_two_iff_nonempty_earDecomposition [Finite E(G)] [Nonempty V(G)] :
    G.IsEdgeConnected 2 ↔ Nonempty (G.EarDecomposition G) := by
  rw [nonempty_earDecomposition_iff_exists_isVertexStart,
    isEdgeConnected_two_iff_exists_isVertexStart_earDecomposition]

/-- A multigraph with finitely many actual edges is connected and bridgeless if and only if it
admits an ear decomposition. Unlike `isEdgeConnected_two_iff_nonempty_earDecomposition`, no separate
vertex-nonemptiness assumption is needed because both sides imply `V(G).Nonempty`. -/
theorem connected_and_forall_not_isBridge_iff_nonempty_earDecomposition [Finite E(G)] :
    (G.Connected ∧ ∀ e, ¬ G.IsBridge e) ↔ Nonempty (G.EarDecomposition G) := by
  constructor
  · rintro ⟨hconn, hnb⟩
    have : Nonempty V(G) := hconn.nonempty.to_subtype
    exact isEdgeConnected_two_iff_nonempty_earDecomposition.mp
      ((isEdgeConnected_two_iff_connected_and_forall_not_isBridge hconn.nonempty).mpr ⟨hconn, hnb⟩)
  · rintro ⟨d⟩
    exact (isEdgeConnected_two_iff_connected_and_forall_not_isBridge d.vertexSet_nonempty).mp
      d.isEdgeConnected_two

end Graph

namespace SimpleGraph

variable {α : Type u}

/-- **Ear characterization of `2`-edge-connected simple graphs** (vertex-started form). A simple
graph on a nonempty vertex type with finitely many edges is `2`-edge-connected if and only if
`Graph.ofSimpleGraph H` admits an ear decomposition starting from a single vertex. -/
theorem isEdgeConnected_two_iff_exists_isVertexStart_earDecomposition (H : SimpleGraph α)
    [Finite H.edgeSet] [Nonempty α] :
    H.IsEdgeConnected 2 ↔
      ∃ d : (Graph.ofSimpleGraph H).EarDecomposition (Graph.ofSimpleGraph H),
        d.IsVertexStart := by
  have : Finite (Graph.ofSimpleGraph H).edgeSet := by
    rw [Graph.edgeSet_ofSimpleGraph]; infer_instance
  have : Nonempty (Graph.ofSimpleGraph H).vertexSet := by
    rw [Graph.vertexSet_ofSimpleGraph]; infer_instance
  rw [← Nat.cast_ofNat, ← Graph.isEdgeConnected_ofSimpleGraph_iff,
    Graph.isEdgeConnected_two_iff_exists_isVertexStart_earDecomposition]

/-- **Ear characterization of `2`-edge-connected simple graphs**. A simple graph on a nonempty
vertex type with finitely many edges is `2`-edge-connected if and only if `Graph.ofSimpleGraph H`
admits an ear decomposition. -/
theorem isEdgeConnected_two_iff_nonempty_earDecomposition_ofSimpleGraph (H : SimpleGraph α)
    [Finite H.edgeSet] [Nonempty α] :
    H.IsEdgeConnected 2 ↔
      Nonempty ((Graph.ofSimpleGraph H).EarDecomposition (Graph.ofSimpleGraph H)) := by
  have : Finite (Graph.ofSimpleGraph H).edgeSet := by
    rw [Graph.edgeSet_ofSimpleGraph]; infer_instance
  have : Nonempty (Graph.ofSimpleGraph H).vertexSet := by
    rw [Graph.vertexSet_ofSimpleGraph]; infer_instance
  rw [← Nat.cast_ofNat, ← Graph.isEdgeConnected_ofSimpleGraph_iff,
    Graph.isEdgeConnected_two_iff_nonempty_earDecomposition]

end SimpleGraph
