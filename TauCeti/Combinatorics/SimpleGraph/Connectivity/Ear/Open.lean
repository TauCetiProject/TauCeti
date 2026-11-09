/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.SimpleGraph.Connectivity.Ear.Basic
public import TauCeti.Combinatorics.SimpleGraph.Connectivity.VertexConnectivity

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Order.Preorder.Finite
import TauCeti.Combinatorics.SimpleGraph.Connectivity.Fan
import TauCeti.Combinatorics.SimpleGraph.Paths

/-!
# Open ear decompositions and `2`-vertex-connectivity

**Whitney's theorem** (1932) characterizes `2`-vertex-connected finite simple graphs as those
admitting an open ear decomposition: starting from a cycle, one repeatedly adjoins paths between
two distinct vertices already present whose internal vertices and edges are new.

This file proves both directions at their natural generality:

* **Soundness (no finiteness needed).** Combining cycle `2`-vertex-connectivity
  (`SimpleGraph.Walk.IsCycle.isVertexConnected_two_toSubgraph`) with preservation of
  `2`-vertex-connectivity when adjoining an open ear
  (`SimpleGraph.Ear.isVertexConnected_two_adjoin`), every open ear decomposition of `H` certifies
  `H.coe.IsVertexConnected 2` (`SimpleGraph.EarDecomposition.IsOpen.isVertexConnected_two_final`).
  In particular, any simple graph—finite or infinite—admitting an open ear decomposition of `⊤` is
  `2`-vertex-connected (`SimpleGraph.EarDecomposition.IsOpen.isVertexConnected_two`).
* **Completeness on finite vertex types.** In a `2`-vertex-connected simple graph on a finite vertex
  type, any proper subgraph `H ≠ ⊤` with at least two vertices admits an open ear
  (`SimpleGraph.IsVertexConnected.exists_open_ear`), constructed via the fan lemma
  `SimpleGraph.IsVertexConnected.exists_fan` when `H` misses a vertex and as a single missing edge
  when `H` is spanning. Well-founded induction on `G.Subgraph` shows that for any open ear
  decomposition of a subgraph there exists an open ear decomposition of `⊤` with the same initial
  subgraph (`SimpleGraph.IsVertexConnected.exists_isOpen_earDecomposition_of_earDecomposition`),
  yielding open ear decompositions starting from any prescribed cycle
  (`SimpleGraph.IsVertexConnected.exists_isOpen_earDecomposition_initial_eq`), from a cycle
  containing any prescribed edge
  (`SimpleGraph.IsVertexConnected.exists_isOpen_earDecomposition_mem_edgeSet_initial`), and the full
  equivalence `SimpleGraph.isVertexConnected_two_iff_exists_isOpen_earDecomposition` (which needs no
  separate `3 ≤ card V` hypothesis because both sides imply `3 ≤ ENat.card V`).

Because `Graph.IsVertexConnected G 2` is an `abbrev` for `G.toSimpleGraph.IsVertexConnected 2`, the
equivalence applies directly to the underlying simple graph of any multigraph with finitely many
actual vertices (`[Finite V(G)]`), regardless of loops or parallel edges.

## Main results

* `SimpleGraph.Ear.isVertexConnected_two_adjoin`: adjoining an open ear to a `2`-vertex-connected
  subgraph preserves `2`-vertex-connectivity.
* `SimpleGraph.EarDecomposition.IsOpen.isVertexConnected_two`: a simple graph with an open ear
  decomposition of `⊤` is `2`-vertex-connected.
* `SimpleGraph.IsVertexConnected.exists_open_ear`: every proper subgraph with at least two vertices
  in a finite `2`-vertex-connected graph admits an open ear.
* `SimpleGraph.IsVertexConnected.exists_isOpen_earDecomposition_of_earDecomposition`: if a subgraph
  of a finite `2`-vertex-connected graph has an open ear decomposition, then `⊤` has an open ear
  decomposition with the same initial subgraph.
* `SimpleGraph.IsVertexConnected.exists_isOpen_earDecomposition_initial_eq`: **Whitney's theorem
  with prescribed initial cycle**.
* `SimpleGraph.IsVertexConnected.exists_isOpen_earDecomposition_mem_edgeSet_initial`,
  `SimpleGraph.Adj.exists_isOpen_earDecomposition_adj_initial`: **prescribed-edge corollaries**.
* `SimpleGraph.isVertexConnected_two_iff_exists_isOpen_earDecomposition`: **Whitney's open ear
  characterization of `2`-vertex-connectivity**.

## Implementation notes

In the soundness direction, deleting a set `s` of fewer than two vertices leaves `s` having
`encard ≤ 1` (`Set.encard_le_one_iff`). On an open ear `p` from `u` to `v`, splitting `p` at any
undeleted internal vertex `w` yields two internally disjoint subwalks to `u` and `v`, at least one
of which avoids `s` and lifts via `SimpleGraph.Walk.reachable_induce_coe_of_mem_support`. In the
completeness direction, `Finite G.Subgraph` (from `[Finite V]`) gives `WellFoundedGT G.Subgraph`, so
producing an open ear decomposition of `⊤` with the same initial subgraph along `Ear.lt_adjoin`
requires no auxiliary edge-count measure or `[DecidableEq V]` assumption.

## References

* H. Whitney, *Congruent graphs and the connectivity of graphs*, Amer. J. Math. 54 (1932),
  150–168.
* R. Diestel, *Graph Theory*, 5th ed., Graduate Texts in Mathematics 173, Springer, 2017,
  Proposition 3.1.1.
-/

public section

open Finset

universe u

namespace SimpleGraph

variable {V : Type u} {G : SimpleGraph V} {H : G.Subgraph}

/-! ### Soundness: open ears preserve `2`-vertex-connectivity -/

/-- Adjoining an open ear to a `2`-vertex-connected subgraph preserves `2`-vertex-connectivity,
with no finiteness assumption. -/
theorem Ear.isVertexConnected_two_adjoin (hH : H.coe.IsVertexConnected 2) {e : G.Ear H}
    (he : e.kind = .«open») : e.adjoin.coe.IsVertexConnected 2 := by
  cases e with
  | closed => exact EarKind.noConfusion ((Ear.kind_closed ..).symm.trans he)
  | @«open» u v p hp hu hv huv hint hedge =>
    let e₀ : G.Ear H := Ear.«open» p hp hu hv huv hint hedge
    let K : G.Subgraph := e₀.adjoin
    have hHK : H ≤ K := e₀.le_adjoin
    have hpK : p.toSubgraph ≤ K :=
      (Ear.toSubgraph_open p hp hu hv huv hint hedge) ▸ e₀.toSubgraph_le_adjoin
    let ι : H.verts → K.verts := fun x ↦ ⟨x.1, hHK.1 x.2⟩
    have hι : Function.Injective ι :=
      fun _ _ h ↦ Subtype.ext (congrArg (Subtype.val : K.verts → V) h)
    refine isVertexConnected_iff.mpr ⟨?_, fun s hs ↦ ?_⟩
    · exact hH.add_one_le_card.trans (ENat.card_le_card_of_injective hι)
    · -- Restrict the deleted set `s` to `H` and connect remaining internal vertices along `p`.
      have hs1 : s.encard ≤ 1 := Order.le_of_lt_add_one hs
      let sH : Set H.verts := ι ⁻¹' s
      have hsH : sH.encard < 2 :=
        (Set.encard_le_encard_of_injOn (Set.mapsTo_preimage ι s) hι.injOn).trans_lt hs
      have hH_pre : (H.coe.induce sHᶜ).Preconnected :=
        (isVertexConnected_iff.mp hH).2 hsH
      let ψ : H.coe.induce sHᶜ →g K.coe.induce sᶜ :=
        { toFun z := ⟨ι z.1, z.2⟩
          map_rel' h := (K.coe_adj _ _).mpr (hHK.2 ((H.coe_adj _ _).mp h)) }
      -- Every vertex in `K` outside `s` reaches some vertex of `H` outside `s`.
      have h_to_H : ∀ w : ↑(sᶜ : Set K.verts), ∃ z : ↑(sHᶜ : Set H.verts),
          (K.coe.induce sᶜ).Reachable w (ψ z) := by
        intro w
        have hwK : w.1.1 ∈ H.verts ∪ p.toSubgraph.verts := by
          simpa [K, e₀] using w.1.2
        rcases hwK with hwH | hwp
        · exact ⟨⟨⟨w.1.1, hwH⟩, w.2⟩, .rfl⟩
        · obtain ⟨z, hz, hr⟩ := reachable_induce_compl_of_mem_verts_toSubgraph_of_encard_le_one
            hp hpK hu hv hHK hs1 w.2 hwp
          exact ⟨⟨z, hz⟩, hr⟩
      intro a b
      obtain ⟨za, hra⟩ := h_to_H a
      obtain ⟨zb, hrb⟩ := h_to_H b
      exact hra.trans (((hH_pre za zb).map ψ).trans hrb.symm)

/-- A cycle initial witness yields a `2`-vertex-connected initial subgraph. -/
theorem EarStart.IsCycle.isVertexConnected_two {s : G.EarStart H} (hs : s.IsCycle) :
    H.coe.IsVertexConnected 2 := by
  cases s with
  | vertex v => exact ((EarStart.isCycle_vertex v).mp hs).elim
  | cycle _ hc => exact hc.isVertexConnected_two_toSubgraph

namespace EarDecomposition

/-- The initial subgraph of an open ear decomposition is `2`-vertex-connected, with no finiteness
assumption. -/
theorem IsOpen.isVertexConnected_two_initial {d : G.EarDecomposition H} (hd : d.IsOpen) :
    d.initial.coe.IsVertexConnected 2 :=
  d.subgraphAfter_zero ▸ hd.start_isCycle.isVertexConnected_two

/-- Every prefix subgraph of an open ear decomposition is `2`-vertex-connected, with no finiteness
assumption. -/
theorem IsOpen.isVertexConnected_two_subgraphAfter {d : G.EarDecomposition H} (hd : d.IsOpen)
    (k : Fin (d.length + 1)) : (d.subgraphAfter k).coe.IsVertexConnected 2 :=
  d.subgraphAfter_induction (P := fun K ↦ K.coe.IsVertexConnected 2)
    hd.isVertexConnected_two_initial
    (fun i ih ↦ Ear.isVertexConnected_two_adjoin ih (hd.earAt_kind_eq_open i)) k

/-- The final subgraph of an open ear decomposition is `2`-vertex-connected, with no finiteness
assumption. -/
theorem IsOpen.isVertexConnected_two_final {d : G.EarDecomposition H} (hd : d.IsOpen) :
    H.coe.IsVertexConnected 2 :=
  d.final_induction (P := fun K ↦ K.coe.IsVertexConnected 2)
    hd.isVertexConnected_two_initial
    fun i ih ↦ Ear.isVertexConnected_two_adjoin ih (hd.earAt_kind_eq_open i)

/-- A simple graph admitting an open ear decomposition of `⊤` is `2`-vertex-connected, with no
finiteness assumption. -/
theorem IsOpen.isVertexConnected_two {d : G.EarDecomposition (⊤ : G.Subgraph)} (hd : d.IsOpen) :
    G.IsVertexConnected 2 :=
  Subgraph.topIso.isVertexConnected_iff.mpr hd.isVertexConnected_two_final

end EarDecomposition

/-! ### Completeness: constructing open ears and open ear decompositions -/

/-- A spanning proper subgraph admits an open ear: a single missing edge. -/
private theorem exists_open_ear_of_spanning {H : G.Subgraph} (hH : H ≠ ⊤)
    (hspan : ∀ x : V, x ∈ H.verts) : ∃ e : G.Ear H, e.kind = .«open» := by
  classical
  -- `H` is spanning and `H ≠ ⊤`, so some edge of `G` is missing from `H`.
  have hex : ∃ u v : V, G.Adj u v ∧ ¬H.Adj u v := by
    by_contra! hall
    apply hH
    ext x y
    · simp [hspan x]
    · exact ⟨fun h ↦ by simp [H.adj_sub h], fun h ↦ hall x y (by simpa using h)⟩
  obtain ⟨u, v, hadj, hnotH⟩ := hex
  refine ⟨Ear.«open» hadj.toWalk (Walk.IsPath.cons .nil (by simp [hadj.ne]))
    (hspan u) (hspan v) hadj.ne ?_ ?_, Ear.kind_open ..⟩
  · intro w hw hwu hwv
    simp only [Adj.toWalk, Walk.support_cons, Walk.support_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hw
    exact (hw.elim hwu hwv).elim
  · intro e he
    simp only [Adj.toWalk, Walk.edges_cons, Walk.edges_nil, List.mem_cons,
      List.not_mem_nil, or_false] at he
    subst he
    rwa [Subgraph.mem_edgeSet]

/-- A `2`-vertex-connected finite graph has an open ear on any subgraph with at least two
vertices that misses a vertex. -/
private theorem IsVertexConnected.exists_open_ear_of_not_mem_verts [Finite V]
    (hG : G.IsVertexConnected 2) {H : G.Subgraph} (hverts : H.verts.Nontrivial) {x : V}
    (hx : x ∉ H.verts) : ∃ e : G.Ear H, e.kind = .«open» := by
  classical
  cases nonempty_fintype V
  let U : Finset V := H.verts.toFinset
  have hxU : x ∉ U := by simpa [U] using hx
  have hU : 2 ≤ #U := by
    obtain ⟨a, ha, b, hb, hab⟩ := hverts
    exact Finset.one_lt_card.mpr ⟨a, Set.mem_toFinset.mpr ha, b, Set.mem_toFinset.mpr hb, hab⟩
  -- An open ear through `x` with its two ends in `H`; only the edge condition remains.
  obtain ⟨u₀, u₁, R, hu₀U, hu₁U, huv, hR, hxR, hint⟩ := hG.exists_open_ear_through hxU hU
  have hu₀ : u₀ ∈ H.verts := Set.mem_toFinset.mp hu₀U
  have hu₁ : u₁ ∈ H.verts := Set.mem_toFinset.mp hu₁U
  refine ⟨Ear.«open» R hR hu₀ hu₁ huv
    (fun w hw h0 h1 ↦ Set.mem_toFinset.not.mp (hint w hw h0 h1)) ?_, Ear.kind_open ..⟩
  -- An edge of `H` on `R` would join `u₀` to `u₁` along `R`, forcing `x` to be an end of `R`.
  intro e he heH
  induction e using Sym2.ind with
  | _ a b =>
    rw [Subgraph.mem_edgeSet] at heH
    have hends : ∀ z, z ∈ R.support → z ∈ U → z = u₀ ∨ z = u₁ := fun z hz hzU ↦ by
      by_contra! h
      exact hint z hz h.1 h.2 hzU
    have ha := hends a (R.fst_mem_support_of_mem_edges he)
      (Set.mem_toFinset.mpr (H.edge_vert heH))
    have hb := hends b (R.snd_mem_support_of_mem_edges he)
      (Set.mem_toFinset.mpr (H.edge_vert heH.symm))
    have hx₀ : x ≠ u₀ := fun h ↦ hxU (h ▸ hu₀U)
    have hx₁ : x ≠ u₁ := fun h ↦ hxU (h ▸ hu₁U)
    -- An edge joining `u₀` to `u₁` forces the path `R` to be that single edge.
    have key : s(u₀, u₁) ∈ R.edges → False := fun h ↦ by
      have hxs : x ∈ (R.adj_of_mem_edges h).toWalk.support := hR.eq_adj_toWalk_of_mem_edges h ▸ hxR
      simp only [Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil,
        or_false] at hxs
      exact hxs.elim hx₀ hx₁
    have hab := heH.ne
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact hab (ha.trans hb.symm)
    · rw [ha, hb] at he
      exact key he
    · rw [ha, hb, Sym2.eq_swap] at he
      exact key he
    · exact hab (ha.trans hb.symm)

/-- **Single-step open ear existence.** In a `2`-vertex-connected simple graph on a finite vertex
type, every proper subgraph `H ≠ ⊤` with at least two vertices admits an open ear. -/
theorem IsVertexConnected.exists_open_ear [Finite V] (hG : G.IsVertexConnected 2)
    {H : G.Subgraph} (hH : H ≠ ⊤) (hverts : H.verts.Nontrivial) :
    ∃ e : G.Ear H, e.kind = .«open» := by
  classical
  by_cases hspan : ∀ x : V, x ∈ H.verts
  · exact exists_open_ear_of_spanning hH hspan
  · push Not at hspan
    obtain ⟨x, hx⟩ := hspan
    exact hG.exists_open_ear_of_not_mem_verts hverts hx

/-- Given an open ear decomposition of a subgraph `H` in a finite `2`-vertex-connected simple
graph, there exists an open ear decomposition of `⊤` with the same initial subgraph. -/
theorem IsVertexConnected.exists_isOpen_earDecomposition_of_earDecomposition [Finite V]
    (hG : G.IsVertexConnected 2) {H : G.Subgraph} (d₀ : G.EarDecomposition H) (hd₀ : d₀.IsOpen) :
    ∃ d : G.EarDecomposition (⊤ : G.Subgraph), d.IsOpen ∧ d.initial = d₀.initial := by
  induction H using WellFoundedGT.induction with
  | ind H ih =>
    by_cases htop : H = ⊤
    · exact ⟨d₀.copy htop, (d₀.isOpen_copy htop).mpr hd₀, d₀.initial_copy htop⟩
    · have hcard : (1 : ℕ∞) < ENat.card H.verts :=
        lt_of_lt_of_le (by decide : (1 : ℕ∞) < 2 + 1)
          hd₀.isVertexConnected_two_final.add_one_le_card
      have hnt : Nontrivial H.verts := (ENat.one_lt_card_iff_nontrivial H.verts).mp hcard
      have hverts : H.verts.Nontrivial := Set.nontrivial_coe_sort.mp hnt
      obtain ⟨e, he⟩ := hG.exists_open_ear htop hverts
      obtain ⟨d, hd, hinit⟩ :=
        ih e.adjoin e.lt_adjoin (d₀.snoc e) ((d₀.isOpen_snoc e).mpr ⟨hd₀, he⟩)
      exact ⟨d, hd, hinit.trans (d₀.initial_snoc e)⟩

/-- **Whitney's theorem with prescribed initial cycle.** For any cycle `c` in a `2`-vertex-connected
simple graph on a finite vertex type, there is an open ear decomposition of `⊤` whose initial
subgraph is `c.toSubgraph`. -/
theorem IsVertexConnected.exists_isOpen_earDecomposition_initial_eq [Finite V]
    (hG : G.IsVertexConnected 2) {u : V} (c : G.Walk u u) (hc : c.IsCycle) :
    ∃ d : G.EarDecomposition (⊤ : G.Subgraph), d.IsOpen ∧ d.initial = c.toSubgraph := by
  obtain ⟨d, hd, hinit⟩ := hG.exists_isOpen_earDecomposition_of_earDecomposition
    (.cycle c hc) (EarDecomposition.isOpen_cycle c hc)
  exact ⟨d, hd, hinit.trans (EarDecomposition.initial_cycle c hc)⟩

/-- **Prescribed-edge open ear decomposition.** Every edge of a finite `2`-vertex-connected simple
graph belongs to the initial cycle of some open ear decomposition of `⊤`. -/
theorem IsVertexConnected.exists_isOpen_earDecomposition_mem_edgeSet_initial [Finite V]
    (hG : G.IsVertexConnected 2) {e : Sym2 V} (he : e ∈ G.edgeSet) :
    ∃ d : G.EarDecomposition (⊤ : G.Subgraph), d.IsOpen ∧ e ∈ d.initial.edgeSet := by
  have hnb : ¬G.IsBridge e :=
    isEdgeConnected_two_iff_forall_not_isBridge.mp hG.isEdgeConnected e
  have hcyc : ∃ (u : V) (c : G.Walk u u), c.IsCycle ∧ e ∈ c.edges := by
    by_contra! hall
    exact hnb ((G.isBridge_iff_forall_cycle_notMem he).mpr hall)
  obtain ⟨u, c, hc, hec⟩ := hcyc
  obtain ⟨d, hd, hinit⟩ := hG.exists_isOpen_earDecomposition_initial_eq c hc
  exact ⟨d, hd, hinit ▸ (Walk.mem_edges_toSubgraph c).mpr hec⟩

/-- Adjacency form of `IsVertexConnected.exists_isOpen_earDecomposition_mem_edgeSet_initial`. -/
theorem Adj.exists_isOpen_earDecomposition_adj_initial [Finite V] {s t : V} (hadj : G.Adj s t)
    (hG : G.IsVertexConnected 2) :
    ∃ d : G.EarDecomposition (⊤ : G.Subgraph), d.IsOpen ∧ d.initial.Adj s t := by
  obtain ⟨d, hd, hmem⟩ :=
    hG.exists_isOpen_earDecomposition_mem_edgeSet_initial (G.mem_edgeSet.mpr hadj)
  exact ⟨d, hd, Subgraph.mem_edgeSet.mp hmem⟩

/-- **Whitney's open ear characterization of `2`-vertex-connectivity.** A simple graph on a finite
vertex type is `2`-vertex-connected if and only if it admits an open ear decomposition of `⊤`.
No separate cardinality bound on `V` is required: both sides entail at least three vertices. -/
theorem isVertexConnected_two_iff_exists_isOpen_earDecomposition [Finite V] :
    G.IsVertexConnected 2 ↔ ∃ d : G.EarDecomposition (⊤ : G.Subgraph), d.IsOpen := by
  refine ⟨fun hG ↦ ?_, fun ⟨d, hd⟩ ↦ hd.isVertexConnected_two⟩
  have h1 : (1 : ℕ∞) < ENat.card V :=
    lt_of_lt_of_le (by decide : (1 : ℕ∞) < 2 + 1) hG.add_one_le_card
  have : Nontrivial V := (ENat.one_lt_card_iff_nontrivial V).mp h1
  obtain ⟨u, v, huv⟩ := exists_pair_ne V
  obtain ⟨c, hc⟩ :=
    exists_isCycle_of_two_le_isEdgeReachable huv le_rfl (hG.isEdgeConnected u v)
  obtain ⟨d, hd, -⟩ := hG.exists_isOpen_earDecomposition_initial_eq c hc
  exact ⟨d, hd⟩

end SimpleGraph
