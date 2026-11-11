/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import TauCeti.Combinatorics.SimpleGraph.Connectivity.EdgeConnectivity

/-!
# Ear decompositions of simple graphs

An *open ear* over a subgraph `H : G.Subgraph` of a simple graph `G` is a path in `G` whose two
distinct endpoints lie in `H`, whose internal vertices lie outside `H`, and whose edges lie outside
`H` (in particular, a single unused edge between two vertices already in `H` is an open ear). A
*closed ear* over `H` is a cycle in `G` meeting `H` solely at its base vertex; in a simple graph,
the unused-edge property follows automatically because every edge of the cycle has at least one
endpoint different from the base vertex (`SimpleGraph.Ear.closed_edges_notMem_edgeSet`).

An *ear decomposition* `d : G.EarDecomposition H` is data recording an initial subgraph (either a
single vertex or a cycle), a finite sequence of open or closed ears, and the prefix subgraph after
each step, ending at `H`. An ear decomposition is *open* (`SimpleGraph.EarDecomposition.IsOpen`)
when it starts from a cycle and every ear is open.

This file defines ears, initial subgraphs, and ear decompositions of subgraphs of a simple graph,
establishes their extensionality, prefix, and induction API, shows that the initial subgraph and the
ears partition the edges of `H`, and proves without finiteness hypotheses that every ear
decomposition builds connected, `2`-edge-connected subgraphs (so a decomposition of `⊤` certifies
that `G` is connected and `2`-edge-connected). Preservation of `2`-vertex-connectivity by open ears
and Whitney's open ear characterization are proved in
`TauCeti.Combinatorics.SimpleGraph.Connectivity.Ear.Open`.

## Main definitions

* `SimpleGraph.EarKind`: whether an ear is `open` or `closed`.
* `SimpleGraph.Ear G H`: an open or closed ear in `G` over `H : G.Subgraph`.
* `SimpleGraph.EarStart G H`: witness that `H` is a singleton subgraph or traced by a cycle.
* `SimpleGraph.EarDecomposition G H`: a finite ear decomposition in `G` with final subgraph `H`.
* `SimpleGraph.EarDecomposition.IsOpen`: predicate that a decomposition starts from a cycle and
  adds only open ears.

## Main results

* `SimpleGraph.Ear.edges_notMem_edgeSet`: no edge of an open or closed ear belongs to `H.edgeSet`.
* `SimpleGraph.Ear.lt_adjoin`: adjoining an ear strictly enlarges the subgraph.
* `SimpleGraph.Ear.isEdgeConnected_two_adjoin`: adjoining an ear to a `2`-edge-connected subgraph
  preserves `2`-edge-connectivity.
* `SimpleGraph.EarDecomposition.ext`: an ear decomposition is determined by its length, initial
  subgraph and witness, and displayed ear walks.
* `SimpleGraph.EarDecomposition.subgraphAfter_strictMono`: prefix subgraphs grow strictly.
* `SimpleGraph.EarDecomposition.mem_edgeSet_initial_or_existsUnique_walkAt`: in an ear
  decomposition of `⊤`, every edge outside the initial subgraph belongs to a unique ear.
* `SimpleGraph.EarDecomposition.connected`, `SimpleGraph.EarDecomposition.isEdgeConnected_two`: a
  simple graph admitting an ear decomposition of `⊤` is connected and `2`-edge-connected, with no
  finiteness assumption.

## Implementation notes

All projection and predicate bodies (`Ear.kind`, `Ear.toWalk`, `Ear.toSubgraph`, `Ear.adjoin`,
`EarStart.IsCycle`, `EarDecomposition.initial`, `EarDecomposition.kindAt`,
`EarDecomposition.walkAt`, `EarDecomposition.IsOpen`) remain unexposed, with characteristic
`@[simp]` lemmas proved via `:= (rfl)` so downstream consumers do not rely on definitional
unfolding. Only the three length-transforming combinators `EarDecomposition.copy`,
`EarDecomposition.snoc`, and `EarDecomposition.prefix` carry `@[expose]` so dependent `Fin` indices
over `.length` compute in types.

## References

* H. Whitney, *Congruent graphs and the connectivity of graphs*, Amer. J. Math. 54 (1932),
  150–168.
* R. Diestel, *Graph Theory*, 5th ed., Graduate Texts in Mathematics 173, Springer, 2017,
  Section 3.1.
-/

public section

universe u

namespace SimpleGraph

variable {V : Type u} {G : SimpleGraph V} {H : G.Subgraph}

/-- Whether an ear is open (a path between two distinct vertices) or closed (a cycle at one base
vertex). -/
inductive EarKind
  | «open»
  | closed
  deriving DecidableEq

/-- An ear in `G` over a subgraph `H`: either an open ear (a path with distinct endpoints in `H`,
internal vertices outside `H`, and edges outside `H`) or a closed ear (a cycle meeting `H` only at
its base vertex). Single-edge open ears are permitted. -/
inductive Ear (G : SimpleGraph V) (H : G.Subgraph) : Type u
  | «open» {u v : V} (p : G.Walk u v) (hp : p.IsPath) (hu : u ∈ H.verts) (hv : v ∈ H.verts)
      (huv : u ≠ v) (hint : ∀ w ∈ p.support, w ≠ u → w ≠ v → w ∉ H.verts)
      (hedge : ∀ e ∈ p.edges, e ∉ H.edgeSet)
  | closed {u : V} (c : G.Walk u u) (hc : c.IsCycle) (hu : u ∈ H.verts)
      (hint : ∀ w ∈ c.support, w ≠ u → w ∉ H.verts)

namespace Ear

/-- Whether an ear is open or closed. -/
def kind : G.Ear H → EarKind
  | .«open» .. => .«open»
  | .closed .. => .closed

@[simp]
theorem kind_open {u v : V} (p : G.Walk u v) (hp : p.IsPath) (hu : u ∈ H.verts) (hv : v ∈ H.verts)
    (huv : u ≠ v) (hint : ∀ w ∈ p.support, w ≠ u → w ≠ v → w ∉ H.verts)
    (hedge : ∀ e ∈ p.edges, e ∉ H.edgeSet) :
    (Ear.«open» p hp hu hv huv hint hedge).kind = .«open» := (rfl)

@[simp]
theorem kind_closed {u : V} (c : G.Walk u u) (hc : c.IsCycle) (hu : u ∈ H.verts)
    (hint : ∀ w ∈ c.support, w ≠ u → w ∉ H.verts) :
    (Ear.closed c hc hu hint).kind = .closed := (rfl)

/-- The underlying walk of an ear, packaged with its endpoints. -/
def toWalk : G.Ear H → Σ u v : V, G.Walk u v
  | .«open» p .. => ⟨_, _, p⟩
  | .closed c .. => ⟨_, _, c⟩

@[simp]
theorem toWalk_open {u v : V} (p : G.Walk u v) (hp : p.IsPath) (hu : u ∈ H.verts)
    (hv : v ∈ H.verts) (huv : u ≠ v) (hint : ∀ w ∈ p.support, w ≠ u → w ≠ v → w ∉ H.verts)
    (hedge : ∀ e ∈ p.edges, e ∉ H.edgeSet) :
    (Ear.«open» p hp hu hv huv hint hedge).toWalk = ⟨u, v, p⟩ := (rfl)

@[simp]
theorem toWalk_closed {u : V} (c : G.Walk u u) (hc : c.IsCycle) (hu : u ∈ H.verts)
    (hint : ∀ w ∈ c.support, w ≠ u → w ∉ H.verts) :
    (Ear.closed c hc hu hint).toWalk = ⟨u, u, c⟩ := (rfl)

/-- Ears over `H` are determined by their underlying walk; distinctness vs. equality of the walk's
endpoints distinguishes open ears from closed ears. -/
@[ext]
theorem ext {e₁ e₂ : G.Ear H} (h : e₁.toWalk = e₂.toWalk) : e₁ = e₂ := by
  cases e₁ <;> cases e₂
  · injection h with hu h2
    subst hu
    injection h2 with hv hp
    subst hv
    cases eq_of_heq hp
    rfl
  · rename_i u v _ _ _ _ huv _ _ _ _ _ _ _
    injection h with hu h2
    subst hu
    injection h2 with hv _
    exact (huv hv.symm).elim
  · rename_i _ _ _ _ _ u v _ _ _ _ huv _ _
    injection h with hu h2
    subst hu
    injection h2 with hv _
    exact (huv hv).elim
  · injection h with hu h2
    subst hu
    injection h2 with _ hc
    subst hc
    rfl

/-- The subgraph traced by the vertices and edges of an ear. -/
def toSubgraph : G.Ear H → G.Subgraph
  | .«open» p .. => p.toSubgraph
  | .closed c .. => c.toSubgraph

@[simp]
theorem toSubgraph_open {u v : V} (p : G.Walk u v) (hp : p.IsPath) (hu : u ∈ H.verts)
    (hv : v ∈ H.verts) (huv : u ≠ v) (hint : ∀ w ∈ p.support, w ≠ u → w ≠ v → w ∉ H.verts)
    (hedge : ∀ e ∈ p.edges, e ∉ H.edgeSet) :
    (Ear.«open» p hp hu hv huv hint hedge).toSubgraph = p.toSubgraph := (rfl)

@[simp]
theorem toSubgraph_closed {u : V} (c : G.Walk u u) (hc : c.IsCycle) (hu : u ∈ H.verts)
    (hint : ∀ w ∈ c.support, w ≠ u → w ∉ H.verts) :
    (Ear.closed c hc hu hint).toSubgraph = c.toSubgraph := (rfl)

theorem toSubgraph_eq_toWalk (e : G.Ear H) : e.toSubgraph = e.toWalk.2.2.toSubgraph := by
  cases e <;> rfl

/-- The subgraph obtained by adjoining an ear `e` to `H`. -/
def adjoin (e : G.Ear H) : G.Subgraph := H ⊔ e.toSubgraph

theorem adjoin_def (e : G.Ear H) : e.adjoin = H ⊔ e.toSubgraph := (rfl)

@[simp]
theorem verts_adjoin (e : G.Ear H) : e.adjoin.verts = H.verts ∪ e.toSubgraph.verts :=
  Subgraph.verts_sup H e.toSubgraph

@[simp]
theorem edgeSet_adjoin (e : G.Ear H) : e.adjoin.edgeSet = H.edgeSet ∪ e.toSubgraph.edgeSet := by
  rw [adjoin_def, Subgraph.edgeSet_sup]

@[simp]
theorem adj_adjoin (e : G.Ear H) {u v : V} :
    e.adjoin.Adj u v ↔ H.Adj u v ∨ e.toSubgraph.Adj u v :=
  Subgraph.sup_adj

theorem le_adjoin (e : G.Ear H) : H ≤ e.adjoin := le_sup_left

theorem toSubgraph_le_adjoin (e : G.Ear H) : e.toSubgraph ≤ e.adjoin := le_sup_right

/-- Transport an ear along an equality of base subgraphs without altering its walk data. -/
def copy {H' : G.Subgraph} (e : G.Ear H) (h : H = H') : G.Ear H' :=
  match e with
  | .«open» p hp hu hv huv hint hedge =>
    .«open» p hp (h ▸ hu) (h ▸ hv) huv (h ▸ hint) (h ▸ hedge)
  | .closed c hc hu hint => .closed c hc (h ▸ hu) (h ▸ hint)

@[simp]
theorem copy_rfl (e : G.Ear H) : e.copy rfl = e := by cases e <;> rfl

@[simp]
theorem kind_copy {H' : G.Subgraph} (e : G.Ear H) (h : H = H') : (e.copy h).kind = e.kind := by
  cases e <;> rfl

@[simp]
theorem toWalk_copy {H' : G.Subgraph} (e : G.Ear H) (h : H = H') :
    (e.copy h).toWalk = e.toWalk := by cases e <;> rfl

@[simp]
theorem toSubgraph_copy {H' : G.Subgraph} (e : G.Ear H) (h : H = H') :
    (e.copy h).toSubgraph = e.toSubgraph := by cases e <;> rfl

@[simp]
theorem adjoin_copy {H' : G.Subgraph} (e : G.Ear H) (h : H = H') :
    (e.copy h).adjoin = H' ⊔ e.toSubgraph := by rw [adjoin_def, toSubgraph_copy]

/-- The starting vertex of an ear lies in `H`. -/
theorem fst_mem_verts (e : G.Ear H) : e.toWalk.1 ∈ H.verts := by
  cases e with
  | «open» _ _ hu => exact hu
  | closed _ _ hu => exact hu

/-- The ending vertex of an ear lies in `H`. -/
theorem snd_mem_verts (e : G.Ear H) : e.toWalk.2.1 ∈ H.verts := by
  cases e with
  | «open» _ _ _ hv => exact hv
  | closed _ _ hu => exact hu

/-- Every ear is a trail (its edges are pairwise distinct). -/
theorem isTrail (e : G.Ear H) : e.toWalk.2.2.IsTrail := by
  cases e with
  | «open» _ hp => exact hp.isTrail
  | closed _ hc => exact hc.isTrail

/-- Every ear has positive length (is not a trivial `nil` walk). -/
theorem not_nil (e : G.Ear H) : ¬e.toWalk.2.2.Nil := by
  cases e with
  | «open» _ _ _ _ huv => exact Walk.not_nil_of_ne huv
  | closed _ hc => exact hc.not_nil

theorem length_pos (e : G.Ear H) : 0 < e.toWalk.2.2.length :=
  Walk.not_nil_iff_lt_length.mp e.not_nil

theorem fst_ne_snd_of_kind_eq_open (e : G.Ear H) (he : e.kind = .«open») :
    e.toWalk.1 ≠ e.toWalk.2.1 := by
  cases e with
  | «open» _ _ _ _ huv => exact huv
  | closed => exact EarKind.noConfusion he

/-- **Closed-ear unused-edge property.** In a simple graph, a cycle meeting `H` only at its base
vertex uses no edge of `H`. -/
theorem closed_edges_notMem_edgeSet {u : V} {c : G.Walk u u}
    (hint : ∀ w ∈ c.support, w ≠ u → w ∉ H.verts) {x : Sym2 V} (hx : x ∈ c.edges) :
    x ∉ H.edgeSet := by
  induction x using Sym2.ind with
  | _ a b =>
    intro hab
    rw [Subgraph.mem_edgeSet] at hab
    have ha : a ∈ c.support := c.fst_mem_support_of_mem_edges hx
    have hb : b ∈ c.support := c.snd_mem_support_of_mem_edges hx
    by_cases hau : a = u
    · subst hau
      exact hint b hb hab.ne.symm (H.edge_vert hab.symm)
    · exact hint a ha hau (H.edge_vert hab)

/-- No edge of an open or closed ear belongs to `H.edgeSet`. -/
theorem edges_notMem_edgeSet (e : G.Ear H) {x : Sym2 V} (hx : x ∈ e.toWalk.2.2.edges) :
    x ∉ H.edgeSet := by
  cases e with
  | «open» _ _ _ _ _ _ hedge => exact hedge x hx
  | closed _ _ _ hint => exact closed_edges_notMem_edgeSet hint hx

theorem disjoint_edgeSet (e : G.Ear H) : Disjoint H.edgeSet e.toSubgraph.edgeSet := by
  rw [Set.disjoint_right, toSubgraph_eq_toWalk]
  intro x hx
  rw [Walk.edgeSet_toSubgraph, Walk.mem_edgeSet] at hx
  exact e.edges_notMem_edgeSet hx

/-- Adjoining an ear strictly enlarges `H`. -/
theorem lt_adjoin (e : G.Ear H) : H < e.adjoin := by
  refine lt_of_le_of_ne e.le_adjoin fun h ↦ ?_
  have hne : e.toWalk.2.2.edges ≠ [] := by
    intro hnil
    have hlen : e.toWalk.2.2.edges.length = 0 := by simp [hnil]
    rw [Walk.length_edges] at hlen
    exact e.length_pos.ne' hlen
  obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ hne
  have hx_mem : x ∈ e.adjoin.edgeSet := by
    rw [edgeSet_adjoin, toSubgraph_eq_toWalk]
    exact Or.inr ((Walk.mem_edges_toSubgraph _).mpr hx)
  exact e.edges_notMem_edgeSet hx (h.symm ▸ hx_mem)

/-- Adjoining any open or closed ear to a preconnected subgraph yields a connected subgraph. -/
theorem connected_adjoin (hH : H.Preconnected) (e : G.Ear H) : e.adjoin.Connected := by
  rw [adjoin_def, toSubgraph_eq_toWalk]
  exact Subgraph.connected_sup hH e.toWalk.2.2.toSubgraph_connected.preconnected
    ⟨e.toWalk.1, e.fst_mem_verts, e.toWalk.2.2.start_mem_verts_toSubgraph⟩

/-- Adjoining any open or closed ear to a `2`-edge-connected subgraph preserves
`2`-edge-connectivity, with no finiteness assumption. -/
theorem isEdgeConnected_two_adjoin (hH : H.coe.IsEdgeConnected 2) (e : G.Ear H) :
    e.adjoin.coe.IsEdgeConnected 2 := by
  rw [isEdgeConnected_two_iff_forall_preconnected]
  intro f
  have hadj_le : H ≤ e.adjoin := e.le_adjoin
  have hwalk_le : e.toWalk.2.2.toSubgraph ≤ e.adjoin :=
    e.toSubgraph_eq_toWalk ▸ e.toSubgraph_le_adjoin
  -- Every vertex in `H` reaches every other vertex in `H` inside `e.adjoin.coe - {f}`.
  have hH_reach : ∀ {a b : V} (ha : a ∈ H.verts) (hb : b ∈ H.verts),
      (e.adjoin.coe.deleteEdges {f}).Reachable ⟨a, hadj_le.1 ha⟩ ⟨b, hadj_le.1 hb⟩ := by
    intro a b ha hb
    induction f using Sym2.ind with
    | _ x y =>
      by_cases hxy : H.Adj x.1 y.1
      · let fH : Sym2 H.verts := s(⟨x.1, H.edge_vert hxy⟩, ⟨y.1, H.edge_vert hxy.symm⟩)
        have hr : (H.coe.deleteEdges {fH}).Reachable ⟨a, ha⟩ ⟨b, hb⟩ :=
          (isEdgeConnected_two_iff_forall_preconnected.mp hH) fH ⟨a, ha⟩ ⟨b, hb⟩
        let φ : H.coe.deleteEdges {fH} →g e.adjoin.coe.deleteEdges {s(x, y)} :=
          { toFun z := ⟨z.1, hadj_le.1 z.2⟩
            map_rel' {z₁ z₂} h := by
              rw [deleteEdges_adj, Set.mem_singleton_iff] at h ⊢
              refine ⟨(e.adjoin.coe_adj _ _).mpr (hadj_le.2 ((H.coe_adj _ _).mp h.1)),
                fun heq ↦ h.2 ?_⟩
              have hmap := congrArg (Sym2.map Subtype.val) heq
              exact Sym2.map.injective Subtype.val_injective hmap }
        exact hr.map φ
      · have : Nonempty H.verts := ⟨⟨a, ha⟩⟩
        obtain ⟨p, hp⟩ :=
          (Subgraph.connected_iff_forall_exists_walk_subgraph H).mp ⟨hH.connected (by decide)⟩
            |>.2 ha hb
        refine p.reachable_deleteEdges_coe (hp.trans hadj_le)
          (Set.forall_mem_singleton.mpr fun hmem ↦ hxy ?_)
        exact hp.2 (Subgraph.mem_edgeSet.mp ((Walk.mem_edges_toSubgraph p).mpr hmem))
  -- Every vertex of `e.adjoin` reaches a vertex of `H` inside `e.adjoin.coe - {f}`.
  have h_to_H : ∀ z : e.adjoin.verts, ∃ u : V, ∃ hu : u ∈ H.verts,
      (e.adjoin.coe.deleteEdges {f}).Reachable z ⟨u, hadj_le.1 hu⟩ := by
    rintro ⟨z, hz⟩
    rw [verts_adjoin, toSubgraph_eq_toWalk] at hz
    rcases hz with hzH | hze
    · exact ⟨z, hzH, .rfl⟩
    · rw [Walk.mem_verts_toSubgraph] at hze
      rcases e.isTrail.reachable_deleteEdges_coe_or_reachable_deleteEdges_coe hwalk_le f hze
        with h1 | h2
      · exact ⟨e.toWalk.1, e.fst_mem_verts, h1⟩
      · exact ⟨e.toWalk.2.1, e.snd_mem_verts, h2⟩
  intro a b
  obtain ⟨ua, hua, hra⟩ := h_to_H a
  obtain ⟨ub, hub, hrb⟩ := h_to_H b
  exact hra.trans ((hH_reach hua hub).trans hrb.symm)

end Ear

/-! ### Initial subgraphs -/

/-- Witness that an initial subgraph `H : G.Subgraph` of an ear decomposition is either a single
vertex or traced by a cycle. -/
inductive EarStart (G : SimpleGraph V) : G.Subgraph → Type u
  | vertex (v : V) : G.EarStart (G.singletonSubgraph v)
  | cycle {u : V} (c : G.Walk u u) (hc : c.IsCycle) : G.EarStart c.toSubgraph

namespace EarStart

/-- Whether the initial subgraph is a cycle rather than a single vertex. -/
def IsCycle : G.EarStart H → Prop
  | .vertex _ => False
  | .cycle _ _ => True

@[simp]
theorem isCycle_vertex (v : V) : (EarStart.vertex (G := G) v).IsCycle ↔ False := (Iff.rfl)

@[simp]
theorem isCycle_cycle {u : V} (c : G.Walk u u) (hc : c.IsCycle) :
    (EarStart.cycle c hc).IsCycle ↔ True := (Iff.rfl)

/-- Every valid initial subgraph is connected. -/
theorem connected : ∀ _ : G.EarStart H, H.Connected
  | .vertex _ => Subgraph.singletonSubgraph_connected
  | .cycle c _ => c.toSubgraph_connected

/-- Every valid initial subgraph of an ear decomposition is `2`-edge-connected. -/
theorem isEdgeConnected_two : ∀ _ : G.EarStart H, H.coe.IsEdgeConnected 2
  | .vertex _ => .of_subsingleton
  | .cycle _ hc => hc.isEdgeConnected_two_toSubgraph

end EarStart

/-! ### Ear decompositions -/

/-- A finite ear decomposition in `G` with final subgraph `H`, storing the prefix subgraphs, the
initial vertex or cycle witness, and the ear added at each step. -/
structure EarDecomposition (G : SimpleGraph V) (H : G.Subgraph) : Type u where
  /-- The number of ears added after the initial subgraph. -/
  length : ℕ
  /-- The subgraph built after each prefix; `0` is initial and `Fin.last length` is `H`. -/
  subgraphAfter : Fin (length + 1) → G.Subgraph
  /-- Witness that `subgraphAfter 0` is a singleton subgraph or traced by a cycle. -/
  start : G.EarStart (subgraphAfter 0)
  /-- The ear added at step `i` over `subgraphAfter i.castSucc`. -/
  earAt : (i : Fin length) → G.Ear (subgraphAfter i.castSucc)
  /-- Each successor prefix adjoins its displayed ear. -/
  subgraphAfter_succ : ∀ i : Fin length, subgraphAfter i.succ = (earAt i).adjoin
  /-- The last prefix equals the indexed target subgraph `H`. -/
  subgraphAfter_last : subgraphAfter (Fin.last length) = H

attribute [simp] EarDecomposition.subgraphAfter_last

namespace EarDecomposition

/-- The initial subgraph (`subgraphAfter 0`) of an ear decomposition. -/
def initial (d : G.EarDecomposition H) : G.Subgraph := d.subgraphAfter 0

@[simp]
theorem subgraphAfter_zero (d : G.EarDecomposition H) : d.subgraphAfter 0 = d.initial := (rfl)

/-- The kind (`open` or `closed`) of the `i`-th ear. -/
def kindAt (d : G.EarDecomposition H) (i : Fin d.length) : EarKind := (d.earAt i).kind

theorem kindAt_def (d : G.EarDecomposition H) (i : Fin d.length) :
    d.kindAt i = (d.earAt i).kind := (rfl)

/-- The underlying walk (with endpoints) of the `i`-th ear. -/
def walkAt (d : G.EarDecomposition H) (i : Fin d.length) : Σ u v : V, G.Walk u v :=
  (d.earAt i).toWalk

theorem walkAt_def (d : G.EarDecomposition H) (i : Fin d.length) :
    d.walkAt i = (d.earAt i).toWalk := (rfl)

/-- An ear decomposition is determined by its length, initial subgraph and witness, and displayed
ear walks; the intermediate prefix subgraphs and ear records are uniquely forced. -/
@[ext (iff := false)]
theorem ext {d₁ d₂ : G.EarDecomposition H} (hlen : d₁.length = d₂.length)
    (hinit : d₁.initial = d₂.initial) (hstart : HEq d₁.start d₂.start)
    (hwalk : ∀ i : Fin d₁.length, d₁.walkAt i = d₂.walkAt (i.cast hlen)) : d₁ = d₂ := by
  cases d₁ with
  | mk n₁ sub₁ start₁ ear₁ hsucc₁ hlast₁ =>
    cases d₂ with
    | mk n₂ sub₂ start₂ ear₂ hsucc₂ hlast₂ =>
      simp only at hlen
      subst hlen
      have hsub : sub₁ = sub₂ := by
        funext k
        refine Fin.induction hinit (fun i ih ↦ ?_) k
        rw [hsucc₁ i, hsucc₂ i, Ear.adjoin, Ear.adjoin,
          (ear₁ i).toSubgraph_eq_toWalk, (ear₂ i).toSubgraph_eq_toWalk]
        exact (congrArg (· ⊔ _) ih).trans
          (congrArg (fun w : Σ u v : V, G.Walk u v ↦ sub₂ i.castSucc ⊔ w.2.2.toSubgraph)
            (hwalk i))
      subst hsub
      cases eq_of_heq hstart
      have hear : ear₁ = ear₂ := funext fun i ↦ Ear.ext (hwalk i)
      subst hear
      rfl

theorem ext_iff {d₁ d₂ : G.EarDecomposition H} :
    d₁ = d₂ ↔ ∃ hlen : d₁.length = d₂.length,
      d₁.initial = d₂.initial ∧ HEq d₁.start d₂.start ∧
        ∀ i : Fin d₁.length, d₁.walkAt i = d₂.walkAt (i.cast hlen) :=
  ⟨fun h ↦ h ▸ ⟨rfl, rfl, .rfl, fun _ ↦ rfl⟩,
    fun ⟨hlen, hinit, hstart, hwalk⟩ ↦ ext hlen hinit hstart hwalk⟩

/-- An ear decomposition is *open* if it starts from a cycle and every added ear is open. -/
def IsOpen (d : G.EarDecomposition H) : Prop :=
  d.start.IsCycle ∧ ∀ i : Fin d.length, d.kindAt i = .«open»

theorem isOpen_iff (d : G.EarDecomposition H) :
    d.IsOpen ↔ d.start.IsCycle ∧ ∀ i : Fin d.length, d.kindAt i = .«open» := (Iff.rfl)

theorem IsOpen.start_isCycle {d : G.EarDecomposition H} (hd : d.IsOpen) : d.start.IsCycle := hd.1

theorem IsOpen.kindAt_eq_open {d : G.EarDecomposition H} (hd : d.IsOpen) (i : Fin d.length) :
    d.kindAt i = .«open» := hd.2 i

theorem IsOpen.earAt_kind_eq_open {d : G.EarDecomposition H} (hd : d.IsOpen) (i : Fin d.length) :
    (d.earAt i).kind = .«open» := hd.2 i

/-- Reindex the target subgraph of an ear decomposition along `H = H'` without changing any data
fields. -/
@[expose]
def copy {H' : G.Subgraph} (d : G.EarDecomposition H) (h : H = H') : G.EarDecomposition H' where
  length := d.length
  subgraphAfter := d.subgraphAfter
  start := d.start
  earAt := d.earAt
  subgraphAfter_succ := d.subgraphAfter_succ
  subgraphAfter_last := d.subgraphAfter_last.trans h

@[simp] theorem copy_rfl (d : G.EarDecomposition H) : d.copy rfl = d := rfl

@[simp]
theorem length_copy {H' : G.Subgraph} (d : G.EarDecomposition H) (h : H = H') :
    (d.copy h).length = d.length := rfl

@[simp]
theorem subgraphAfter_copy {H' : G.Subgraph} (d : G.EarDecomposition H) (h : H = H') :
    (d.copy h).subgraphAfter = d.subgraphAfter := rfl

@[simp]
theorem initial_copy {H' : G.Subgraph} (d : G.EarDecomposition H) (h : H = H') :
    (d.copy h).initial = d.initial := (rfl)

@[simp]
theorem start_copy {H' : G.Subgraph} (d : G.EarDecomposition H) (h : H = H') :
    (d.copy h).start = d.start := rfl

@[simp]
theorem earAt_copy {H' : G.Subgraph} (d : G.EarDecomposition H) (h : H = H') :
    (d.copy h).earAt = d.earAt := rfl

@[simp]
theorem walkAt_copy {H' : G.Subgraph} (d : G.EarDecomposition H) (h : H = H')
    (i : Fin d.length) : (d.copy h).walkAt i = d.walkAt i := (rfl)

@[simp]
theorem kindAt_copy {H' : G.Subgraph} (d : G.EarDecomposition H) (h : H = H')
    (i : Fin d.length) : (d.copy h).kindAt i = d.kindAt i := (rfl)

@[simp]
theorem isOpen_copy {H' : G.Subgraph} (d : G.EarDecomposition H) (h : H = H') :
    (d.copy h).IsOpen ↔ d.IsOpen := (Iff.rfl)

/-! ### Constructors: `vertex`, `cycle`, `snoc`, and `prefix` -/

/-- The zero-ear decomposition starting at a single vertex `v`. -/
def vertex (G : SimpleGraph V) (v : V) : G.EarDecomposition (G.singletonSubgraph v) where
  length := 0
  subgraphAfter _ := G.singletonSubgraph v
  start := .vertex v
  earAt i := i.elim0
  subgraphAfter_succ i := i.elim0
  subgraphAfter_last := rfl

@[simp] theorem length_vertex (v : V) : (vertex G v).length = 0 := (rfl)

@[simp]
theorem subgraphAfter_vertex (v : V) (k : Fin ((vertex G v).length + 1)) :
    (vertex G v).subgraphAfter k = G.singletonSubgraph v := (rfl)

@[simp] theorem initial_vertex (v : V) : (vertex G v).initial = G.singletonSubgraph v := (rfl)

@[simp]
theorem start_vertex (v : V) :
    (vertex G v).start =
      (subgraphAfter_vertex (G := G) v 0).symm.rec
        (motive := fun K _ ↦ G.EarStart K) (.vertex v) := (rfl)

@[simp] theorem not_isOpen_vertex (v : V) : ¬(vertex G v).IsOpen := fun h ↦ h.1

/-- The zero-ear decomposition starting at a cycle `c`. -/
def cycle {u : V} (c : G.Walk u u) (hc : c.IsCycle) : G.EarDecomposition c.toSubgraph where
  length := 0
  subgraphAfter _ := c.toSubgraph
  start := .cycle c hc
  earAt i := i.elim0
  subgraphAfter_succ i := i.elim0
  subgraphAfter_last := rfl

@[simp] theorem length_cycle {u : V} (c : G.Walk u u) (hc : c.IsCycle) : (cycle c hc).length = 0 :=
  (rfl)

@[simp]
theorem subgraphAfter_cycle {u : V} (c : G.Walk u u) (hc : c.IsCycle)
    (k : Fin ((cycle c hc).length + 1)) :
    (cycle c hc).subgraphAfter k = c.toSubgraph := (rfl)

@[simp]
theorem initial_cycle {u : V} (c : G.Walk u u) (hc : c.IsCycle) :
    (cycle c hc).initial = c.toSubgraph := (rfl)

@[simp]
theorem start_cycle {u : V} (c : G.Walk u u) (hc : c.IsCycle) :
    (cycle c hc).start =
      (subgraphAfter_cycle c hc 0).symm.rec
        (motive := fun K _ ↦ G.EarStart K) (.cycle c hc) := (rfl)

@[simp]
theorem isOpen_cycle {u : V} (c : G.Walk u u) (hc : c.IsCycle) : (cycle c hc).IsOpen :=
  ⟨trivial, fun i ↦ i.elim0⟩

/-- Append one ear `e : G.Ear H` to the end of an ear decomposition `d : G.EarDecomposition H`. -/
@[expose]
def snoc (d : G.EarDecomposition H) (e : G.Ear H) : G.EarDecomposition e.adjoin where
  length := d.length + 1
  subgraphAfter := Fin.lastCases e.adjoin d.subgraphAfter
  start := by
    rw [← Fin.castSucc_zero (n := d.length + 1), Fin.lastCases_castSucc]
    exact d.start
  earAt := Fin.lastCases
    (e.copy (by rw [Fin.lastCases_castSucc, d.subgraphAfter_last]))
    (fun i ↦ (d.earAt i).copy (by rw [Fin.lastCases_castSucc]))
  subgraphAfter_succ :=
    let earAt' : (j : Fin (d.length + 1)) →
        G.Ear (Fin.lastCases e.adjoin d.subgraphAfter j.castSucc) :=
      Fin.lastCases
        (e.copy (by rw [Fin.lastCases_castSucc, d.subgraphAfter_last]))
        (fun k ↦ (d.earAt k).copy (by rw [Fin.lastCases_castSucc]))
    Fin.lastCases
      (calc
        Fin.lastCases e.adjoin d.subgraphAfter (Fin.last d.length).succ
          = H ⊔ e.toSubgraph := by rw [Fin.succ_last, Fin.lastCases_last, Ear.adjoin_def]
        _ = Fin.lastCases e.adjoin d.subgraphAfter (Fin.last d.length).castSucc ⊔
              e.toSubgraph := by rw [Fin.lastCases_castSucc, d.subgraphAfter_last]
        _ = (earAt' (Fin.last d.length)).adjoin :=
            (congrArg (_ ⊔ ·)
              ((congrArg Ear.toSubgraph Fin.lastCases_last).trans
                (e.toSubgraph_copy _)).symm).trans (Ear.adjoin_def _).symm)
      (fun i ↦ calc
        Fin.lastCases e.adjoin d.subgraphAfter i.castSucc.succ
          = d.subgraphAfter i.castSucc ⊔ (d.earAt i).toSubgraph := by
            rw [Fin.succ_castSucc, Fin.lastCases_castSucc, d.subgraphAfter_succ i, Ear.adjoin_def]
        _ = Fin.lastCases e.adjoin d.subgraphAfter i.castSucc.castSucc ⊔
              (d.earAt i).toSubgraph := by rw [Fin.lastCases_castSucc]
        _ = (earAt' i.castSucc).adjoin :=
            (congrArg (_ ⊔ ·)
              ((congrArg Ear.toSubgraph (Fin.lastCases_castSucc i)).trans
                ((d.earAt i).toSubgraph_copy _)).symm).trans (Ear.adjoin_def _).symm)
  subgraphAfter_last := Fin.lastCases_last

@[simp]
theorem length_snoc (d : G.EarDecomposition H) (e : G.Ear H) :
    (d.snoc e).length = d.length + 1 := rfl

@[simp]
theorem subgraphAfter_snoc_castSucc (d : G.EarDecomposition H) (e : G.Ear H)
    (i : Fin (d.length + 1)) : (d.snoc e).subgraphAfter i.castSucc = d.subgraphAfter i := by
  simp [snoc]

@[simp]
theorem initial_snoc (d : G.EarDecomposition H) (e : G.Ear H) :
    (d.snoc e).initial = d.initial := by
  have h := d.subgraphAfter_snoc_castSucc e 0
  rwa [Fin.castSucc_zero] at h

@[simp]
theorem start_snoc (d : G.EarDecomposition H) (e : G.Ear H) :
    (d.snoc e).start =
      (d.subgraphAfter_zero.trans
        ((d.initial_snoc e).symm.trans (d.snoc e).subgraphAfter_zero.symm)).rec
        (motive := fun K _ ↦ G.EarStart K) d.start := by
  apply eq_of_heq
  rw [heq_eqRec_iff]
  dsimp only [snoc]
  have hrec : ∀ {α β : Type u} (h : α = β) (s : β), HEq (h.mpr s) s := by rintro _ _ rfl _; rfl
  exact (hrec _ _).trans (hrec _ _)

@[simp]
theorem walkAt_snoc_castSucc (d : G.EarDecomposition H) (e : G.Ear H) (i : Fin d.length) :
    (d.snoc e).walkAt i.castSucc = d.walkAt i := by simp [walkAt_def, snoc]

@[simp]
theorem walkAt_snoc_last (d : G.EarDecomposition H) (e : G.Ear H) :
    (d.snoc e).walkAt (Fin.last d.length) = e.toWalk := by simp [walkAt_def, snoc]

@[simp]
theorem kindAt_snoc_castSucc (d : G.EarDecomposition H) (e : G.Ear H) (i : Fin d.length) :
    (d.snoc e).kindAt i.castSucc = d.kindAt i := by simp [kindAt_def, snoc]

@[simp]
theorem kindAt_snoc_last (d : G.EarDecomposition H) (e : G.Ear H) :
    (d.snoc e).kindAt (Fin.last d.length) = e.kind := by simp [kindAt_def, snoc]

@[simp]
theorem isOpen_snoc (d : G.EarDecomposition H) (e : G.Ear H) :
    (d.snoc e).IsOpen ↔ d.IsOpen ∧ e.kind = .«open» := by
  have hstart : (d.snoc e).start.IsCycle ↔ d.start.IsCycle := by
    dsimp only [snoc]
    have hrec : ∀ {K L : G.Subgraph} (h : K = L) (s : G.EarStart L),
        (Eq.mpr (congrArg G.EarStart h) s).IsCycle ↔ s.IsCycle := by rintro _ _ rfl _; rfl
    exact hrec (d.initial_snoc e) d.start
  rw [isOpen_iff, isOpen_iff]
  refine ⟨fun ⟨hs, hk⟩ ↦ ⟨⟨hstart.mp hs, fun i ↦ ?_⟩, ?_⟩,
    fun ⟨⟨hs, hk⟩, he⟩ ↦ ⟨hstart.mpr hs, ?_⟩⟩
  · simpa only [kindAt_snoc_castSucc] using hk i.castSucc
  · simpa only [kindAt_snoc_last] using hk (Fin.last d.length)
  · exact Fin.lastCases (by simpa only [kindAt_snoc_last] using he)
      (fun i ↦ by simpa only [kindAt_snoc_castSucc] using hk i)

/-- The initial segment of `d` consisting of its first `k` ears, forming an ear decomposition of
`d.subgraphAfter k`. -/
@[expose]
def «prefix» (d : G.EarDecomposition H) (k : Fin (d.length + 1)) :
    G.EarDecomposition (d.subgraphAfter k) where
  length := k
  subgraphAfter j := d.subgraphAfter (j.castLE (Nat.succ_le_succ k.is_le))
  start := d.start
  earAt j := d.earAt (j.castLE k.is_le)
  subgraphAfter_succ j := d.subgraphAfter_succ (j.castLE k.is_le)
  subgraphAfter_last := rfl

@[simp]
theorem length_prefix (d : G.EarDecomposition H) (k : Fin (d.length + 1)) :
    (d.prefix k).length = k := rfl

@[simp]
theorem subgraphAfter_prefix (d : G.EarDecomposition H) (k : Fin (d.length + 1))
    (j : Fin ((k : ℕ) + 1)) :
    (d.prefix k).subgraphAfter j = d.subgraphAfter (j.castLE (Nat.succ_le_succ k.is_le)) := rfl

@[simp]
theorem initial_prefix (d : G.EarDecomposition H) (k : Fin (d.length + 1)) :
    (d.prefix k).initial = d.initial := (rfl)

@[simp]
theorem start_prefix (d : G.EarDecomposition H) (k : Fin (d.length + 1)) :
    (d.prefix k).start = d.start := rfl

@[simp]
theorem earAt_prefix (d : G.EarDecomposition H) (k : Fin (d.length + 1)) (j : Fin k) :
    (d.prefix k).earAt j = d.earAt (j.castLE k.is_le) := rfl

@[simp]
theorem walkAt_prefix (d : G.EarDecomposition H) (k : Fin (d.length + 1)) (j : Fin k) :
    (d.prefix k).walkAt j = d.walkAt (j.castLE k.is_le) := (rfl)

@[simp]
theorem kindAt_prefix (d : G.EarDecomposition H) (k : Fin (d.length + 1)) (j : Fin k) :
    (d.prefix k).kindAt j = d.kindAt (j.castLE k.is_le) := (rfl)

theorem IsOpen.prefix {d : G.EarDecomposition H} (hd : d.IsOpen) (k : Fin (d.length + 1)) :
    (d.prefix k).IsOpen :=
  ⟨hd.1, fun j ↦ hd.2 (j.castLE k.is_le)⟩

/-! ### Prefix monotonicity and induction -/

theorem subgraphAfter_castSucc_lt_succ (d : G.EarDecomposition H) (i : Fin d.length) :
    d.subgraphAfter i.castSucc < d.subgraphAfter i.succ := by
  rw [d.subgraphAfter_succ i]
  exact (d.earAt i).lt_adjoin

/-- Prefix subgraphs of an ear decomposition are strictly increasing. -/
theorem subgraphAfter_strictMono (d : G.EarDecomposition H) : StrictMono d.subgraphAfter :=
  Fin.strictMono_iff_lt_succ.mpr d.subgraphAfter_castSucc_lt_succ

/-- Prefix subgraphs of an ear decomposition are monotone. -/
theorem subgraphAfter_mono (d : G.EarDecomposition H) : Monotone d.subgraphAfter :=
  d.subgraphAfter_strictMono.monotone

theorem initial_le_subgraphAfter (d : G.EarDecomposition H) (k : Fin (d.length + 1)) :
    d.initial ≤ d.subgraphAfter k :=
  d.subgraphAfter_mono (Fin.zero_le k)

theorem subgraphAfter_le (d : G.EarDecomposition H) (k : Fin (d.length + 1)) :
    d.subgraphAfter k ≤ H :=
  calc
    d.subgraphAfter k ≤ d.subgraphAfter (Fin.last d.length) := d.subgraphAfter_mono (Fin.le_last k)
    _ = H := d.subgraphAfter_last

theorem initial_le (d : G.EarDecomposition H) : d.initial ≤ H := d.subgraphAfter_le 0

/-- Induction along the prefix subgraphs of an ear decomposition in construction order. -/
theorem subgraphAfter_induction (d : G.EarDecomposition H) {P : G.Subgraph → Prop}
    (h0 : P d.initial)
    (hstep : ∀ i : Fin d.length, P (d.subgraphAfter i.castSucc) → P (d.earAt i).adjoin)
    (k : Fin (d.length + 1)) : P (d.subgraphAfter k) := by
  refine Fin.induction h0 (fun i hi ↦ ?_) k
  rw [d.subgraphAfter_succ i]
  exact hstep i hi

/-- Induction in construction order proving a property of the final subgraph `H`. -/
theorem final_induction (d : G.EarDecomposition H) {P : G.Subgraph → Prop} (h0 : P d.initial)
    (hstep : ∀ i : Fin d.length, P (d.subgraphAfter i.castSucc) → P (d.earAt i).adjoin) : P H := by
  have h := d.subgraphAfter_induction h0 hstep (Fin.last d.length)
  rwa [d.subgraphAfter_last] at h

/-- Induction along the prefix ear decompositions `d.prefix k`. -/
theorem prefix_induction (d : G.EarDecomposition H)
    {P : ∀ ⦃K : G.Subgraph⦄, G.EarDecomposition K → Prop}
    (h0 : P (d.prefix 0))
    (hstep : ∀ i : Fin d.length, P (d.prefix i.castSucc) → P (d.prefix i.succ))
    (k : Fin (d.length + 1)) : P (d.prefix k) :=
  Fin.induction h0 hstep k

/-! ### Edge partition and coverage -/

theorem mem_edgeSet_subgraphAfter_iff (d : G.EarDecomposition H) (k : Fin (d.length + 1))
    {x : Sym2 V} :
    x ∈ (d.subgraphAfter k).edgeSet ↔
      x ∈ d.initial.edgeSet ∨ ∃ i : Fin d.length, i.castSucc < k ∧ x ∈ (d.walkAt i).2.2.edges := by
  refine Fin.induction ?_ (fun i ih ↦ ?_) k
  · simp [subgraphAfter_zero]
  · rw [d.subgraphAfter_succ i, Ear.edgeSet_adjoin, Set.mem_union, ih,
      (d.earAt i).toSubgraph_eq_toWalk, Walk.edgeSet_toSubgraph, Walk.mem_edgeSet, ← walkAt_def,
      or_assoc]
    refine or_congr_right ⟨?_, ?_⟩
    · rintro (⟨j, hj, hx⟩ | hx)
      · exact ⟨j, hj.trans Fin.castSucc_lt_succ, hx⟩
      · exact ⟨i, Fin.castSucc_lt_succ, hx⟩
    · rintro ⟨j, hj, hx⟩
      rcases lt_or_eq_of_le (Fin.castSucc_lt_succ_iff.mp hj) with hlt | rfl
      · exact Or.inl ⟨j, Fin.castSucc_lt_castSucc_iff.mpr hlt, hx⟩
      · exact Or.inr hx

/-- Every edge of `H` belongs either to `d.initial` or to one of the added ears. -/
theorem mem_edgeSet_iff (d : G.EarDecomposition H) {x : Sym2 V} :
    x ∈ H.edgeSet ↔ x ∈ d.initial.edgeSet ∨ ∃ i : Fin d.length, x ∈ (d.walkAt i).2.2.edges := by
  rw [← congrArg Subgraph.edgeSet d.subgraphAfter_last,
    d.mem_edgeSet_subgraphAfter_iff (Fin.last d.length)]
  simp [Fin.castSucc_lt_last]

/-- No edge of an added ear belongs to the initial subgraph. -/
theorem notMem_initial_of_mem_walkAt (d : G.EarDecomposition H) (i : Fin d.length) {x : Sym2 V}
    (hx : x ∈ (d.walkAt i).2.2.edges) : x ∉ d.initial.edgeSet :=
  fun hinit ↦ (d.earAt i).edges_notMem_edgeSet hx
    (Subgraph.edgeSet_mono (d.initial_le_subgraphAfter i.castSucc) hinit)

/-- Distinct ears of an ear decomposition share no edges. -/
theorem eq_of_mem_walkAt (d : G.EarDecomposition H) {i j : Fin d.length} {x : Sym2 V}
    (hi : x ∈ (d.walkAt i).2.2.edges) (hj : x ∈ (d.walkAt j).2.2.edges) : i = j := by
  rcases lt_trichotomy i j with hij | rfl | hji
  · exfalso
    have hx_sub : x ∈ (d.subgraphAfter j.castSucc).edgeSet := by
      rw [d.mem_edgeSet_subgraphAfter_iff]
      exact Or.inr ⟨i, Fin.castSucc_lt_castSucc_iff.mpr hij, hi⟩
    exact (d.earAt j).edges_notMem_edgeSet hj hx_sub
  · rfl
  · exfalso
    have hx_sub : x ∈ (d.subgraphAfter i.castSucc).edgeSet := by
      rw [d.mem_edgeSet_subgraphAfter_iff]
      exact Or.inr ⟨j, Fin.castSucc_lt_castSucc_iff.mpr hji, hj⟩
    exact (d.earAt i).edges_notMem_edgeSet hi hx_sub

/-- An ear decomposition of `⊤` covers every vertex of `G`. -/
theorem mem_verts_initial_or_walkAt (d : G.EarDecomposition (⊤ : G.Subgraph)) (v : V) :
    v ∈ d.initial.verts ∨ ∃ i : Fin d.length, v ∈ (d.walkAt i).2.2.support := by
  have hv : v ∈ (d.subgraphAfter (Fin.last d.length)).verts := by simp
  refine d.subgraphAfter_induction (P := fun K ↦ v ∈ K.verts →
      v ∈ d.initial.verts ∨ ∃ i : Fin d.length, v ∈ (d.walkAt i).2.2.support)
    (fun h ↦ Or.inl h) (fun i ih h ↦ ?_) (Fin.last d.length) hv
  rw [Ear.verts_adjoin, (d.earAt i).toSubgraph_eq_toWalk, Walk.verts_toSubgraph] at h
  rcases h with hprev | hwalk
  · exact ih hprev
  · exact Or.inr ⟨i, hwalk⟩

/-- An ear decomposition of `⊤` partitions every edge of `G` outside `d.initial` into a unique
added ear. -/
theorem mem_edgeSet_initial_or_existsUnique_walkAt (d : G.EarDecomposition (⊤ : G.Subgraph))
    {x : Sym2 V} (hx : x ∈ G.edgeSet) :
    x ∈ d.initial.edgeSet ∨ ∃! i : Fin d.length, x ∈ (d.walkAt i).2.2.edges := by
  have hx' : x ∈ (⊤ : G.Subgraph).edgeSet := by simpa using hx
  rcases d.mem_edgeSet_iff.mp hx' with hinit | ⟨i, hi⟩
  · exact Or.inl hinit
  · exact Or.inr ⟨i, hi, fun j hj ↦ d.eq_of_mem_walkAt hj hi⟩

/-! ### Preservation of connectedness and `2`-edge-connectivity -/

/-- Every prefix subgraph of an ear decomposition is connected. -/
theorem connected_subgraphAfter (d : G.EarDecomposition H) (k : Fin (d.length + 1)) :
    (d.subgraphAfter k).Connected :=
  d.subgraphAfter_induction (P := Subgraph.Connected) d.start.connected
    (fun i ih ↦ (d.earAt i).connected_adjoin ih.preconnected) k

/-- The final subgraph of an ear decomposition is connected. -/
theorem connected_final (d : G.EarDecomposition H) : H.Connected :=
  d.final_induction (P := Subgraph.Connected) d.start.connected
    fun i ih ↦ (d.earAt i).connected_adjoin ih.preconnected

/-- A simple graph with an ear decomposition of `⊤` is connected, with no finiteness assumption. -/
theorem connected (d : G.EarDecomposition (⊤ : G.Subgraph)) : G.Connected :=
  Subgraph.topIso.connected_iff.mp (Subgraph.connected_iff'.mp d.connected_final)

/-- Every prefix subgraph of an ear decomposition is `2`-edge-connected. -/
theorem isEdgeConnected_two_subgraphAfter (d : G.EarDecomposition H) (k : Fin (d.length + 1)) :
    (d.subgraphAfter k).coe.IsEdgeConnected 2 :=
  d.subgraphAfter_induction (P := fun K ↦ K.coe.IsEdgeConnected 2) d.start.isEdgeConnected_two
    (fun i ih ↦ (d.earAt i).isEdgeConnected_two_adjoin ih) k

/-- The final subgraph of an ear decomposition is `2`-edge-connected. -/
theorem isEdgeConnected_two_final (d : G.EarDecomposition H) : H.coe.IsEdgeConnected 2 :=
  d.final_induction (P := fun K ↦ K.coe.IsEdgeConnected 2) d.start.isEdgeConnected_two
    fun i ih ↦ (d.earAt i).isEdgeConnected_two_adjoin ih

/-- A simple graph with an ear decomposition of `⊤` is `2`-edge-connected, with no finiteness
assumption. -/
theorem isEdgeConnected_two (d : G.EarDecomposition (⊤ : G.Subgraph)) : G.IsEdgeConnected 2 := by
  rw [isEdgeConnected_two_iff_forall_preconnected]
  intro f u v
  let φ : (⊤ : G.Subgraph).coe ≃g G := Subgraph.topIso
  have hr := (isEdgeConnected_two_iff_forall_preconnected.mp d.isEdgeConnected_two_final)
    (f.map φ.symm) (φ.symm u) (φ.symm v)
  let ψ : (⊤ : G.Subgraph).coe.deleteEdges {f.map φ.symm} →g G.deleteEdges {f} :=
    { toFun x := φ x
      map_rel' {x y} h := by
        rw [deleteEdges_adj, Set.mem_singleton_iff] at h ⊢
        refine ⟨φ.map_rel_iff.mpr h.1, fun heq ↦ h.2 ?_⟩
        simp [← heq] }
  have hmap := hr.map ψ
  have hu : ψ (φ.symm u) = u := φ.apply_symm_apply u
  have hv : ψ (φ.symm v) = v := φ.apply_symm_apply v
  rwa [hu, hv] at hmap

end EarDecomposition

end SimpleGraph
