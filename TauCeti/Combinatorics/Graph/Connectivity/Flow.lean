/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Connectivity.CutCapacity
public import TauCeti.Combinatorics.Graph.Connectivity.Walk.Bidirected
public import TauCeti.Combinatorics.Network.Acyclic
public import TauCeti.Combinatorics.Network.MinimumCut.Residual
public import TauCeti.Combinatorics.Network.ShortestAugmentation

/-!
# Flows of weighted multigraphs and undirected max-flow/min-cut

A weighted multigraph is a multigraph `G : Graph α β` with capacities `c : E(G) → K` on its actual
edges. Its flows are the flows of its *bidirected network*: the bidirected arrow family
`Graph.BidirectedHom G`, in which a nonloop edge gives one arrow in each direction and a loop gives
a single loop arrow, with every arrow carrying the capacity of its edge
(`Graph.bidirectedCapacity`). There is no separate type of undirected flows: an `s`–`t` flow of
`G` is a `TauCeti.Flow (G.bidirectedCapacity c) s t`, so the whole directed flow theory applies.

The bridge to undirected cuts is `Graph.arrowSum_bidirectedCapacity`: the arrows leaving a set `S`
of actual vertices correspond one-to-one to the edges crossing `S`, each such edge giving exactly
the arrow from its end in `S` to its end outside `S`. So the directed capacity of the cut is the
multigraph cut capacity `Graph.edgeCutCapacity c S`, in which parallel edges contribute separately
and loops not at all.

Acyclic flows are the natural normal form for undirected flows. A nonnegative acyclic assignment
vanishes on every loop arrow (`TauCeti.Assignment.IsAcyclic.apply_eq_zero_of_loop`) and on one of
the two opposite arrows of every nonloop edge
(`TauCeti.Assignment.IsAcyclic.apply_eq_zero_or_apply_eq_zero`), so it never sends flow along an
edge in both directions. By `TauCeti.Flow.exists_isAcyclic`, every flow can be replaced by an
acyclic flow of the same value that is arrowwise no larger.

## Main definitions

* `Graph.bidirectedCapacity`: the capacities of the bidirected network of a weighted multigraph.

## Main results

* `Graph.arrowSum_bidirectedCapacity`: the directed capacity of the arrows leaving a set of actual
  vertices is its multigraph cut capacity.
* `TauCeti.Flow.val_le_edgeCutCapacity`: **weak duality**, the value of an `s`–`t` flow of a
  weighted multigraph is at most the capacity of every cut separating `s` from `t`.
* `Graph.exists_flow_val_eq_edgeCutCapacity_mem`: the **undirected max-flow/min-cut theorem with
  integrality**. For nonnegative capacities in an additive subgroup `H` and distinct actual vertices
  `s` and `t`, some acyclic `s`–`t` flow with values in `H` has value equal to the capacity of some
  cut separating `s` from `t`. `Graph.exists_flow_val_eq_edgeCutCapacity` is the case without `H`.
* `TauCeti.Flow.IsMaximum.isMinimum_edgeCutCapacity_iff_val_eq`: for a maximum flow, the minimum
  cuts are the separating sets whose capacity is its value.
* `TauCeti.Flow.IsMaximum.val_eq_pairMinimumValue_edgeCutCapacity`: the value of a maximum flow is
  the minimum cut value `TauCeti.TerminalCut.pairMinimumValue (G.edgeCutCapacity c) s t` of the
  undirected cut function.

## References

* L. R. Ford, D. R. Fulkerson, *Maximal flow through a network*, Canad. J. Math. 8 (1956).
* A. Schrijver, *Combinatorial Optimization: Polyhedra and Efficiency*, Springer, 2003,
  Chapter 10.
-/

public section

open Finset TauCeti
open scoped Graph

universe u v w

namespace Graph

variable {α : Type u} {β : Type v} {K : Type w} {G : Graph α β}

/-- The capacities of the bidirected network of a weighted multigraph: every arrow of the
bidirected arrow family carries the capacity of its edge, so both arrows of a nonloop edge carry
that capacity. -/
def bidirectedCapacity (c : E(G) → K) : Assignment G.BidirectedHom K :=
  fun _ _ a ↦ c ⟨a.1, a.2.edge_mem⟩

/-- Every arrow of the bidirected network carries the capacity of its edge. -/
@[simp]
theorem bidirectedCapacity_apply (c : E(G) → K) {x y : V(G)} (a : G.BidirectedHom x y) :
    G.bidirectedCapacity c a = c ⟨a.1, a.2.edge_mem⟩ :=
  (rfl)

/-- Nonnegative edge capacities give nonnegative arrow capacities. -/
theorem bidirectedCapacity_nonneg [Zero K] [LE K] {c : E(G) → K} (hc : 0 ≤ c) :
    0 ≤ G.bidirectedCapacity c :=
  fun _ _ a ↦ hc ⟨a.1, a.2.edge_mem⟩

variable [Fintype V(G)] [DecidableEq V(G)] [Fintype E(G)] [∀ x y, Fintype (G.BidirectedHom x y)]

/-- The directed capacity of the arrows leaving a set `S` of actual vertices in the bidirected
network is the multigraph cut capacity of `S`. Each edge crossing `S` gives exactly one arrow
leaving `S`, from its end in `S` to its end outside `S`, and no other arrow leaves `S`. -/
@[simp]
theorem arrowSum_bidirectedCapacity [AddCommMonoid K] (c : E(G) → K) (S : Finset V(G)) :
    arrowSum (G.bidirectedCapacity c) S Sᶜ = G.edgeCutCapacity c S := by
  classical
  rw [edgeCutCapacity_def, ← sum_filter]
  have hsum : arrowSum (G.bidirectedCapacity c) S Sᶜ =
      ∑ a ∈ S.sigma fun x ↦ Sᶜ.sigma fun y ↦ (univ : Finset (G.BidirectedHom x y)),
        c ⟨a.2.2.1, a.2.2.2.edge_mem⟩ := by
    rw [arrowSum_def, sum_sigma]
    refine sum_congr rfl fun x _ ↦ ?_
    rw [sum_sigma]
    simp only [bidirectedCapacity_apply]
  rw [hsum]
  refine sum_nbij (fun a ↦ ⟨a.2.2.1, a.2.2.2.edge_mem⟩) ?_ ?_ ?_ fun _ _ ↦ rfl
  · -- An arrow leaving `S` comes from an edge crossing `S`.
    rintro ⟨x, y, e, hxy⟩ ha
    simp only [mem_sigma, mem_compl, mem_univ, and_true] at ha
    refine mem_filter.2 ⟨mem_univ _, mem_edgeCut_iff.2 ⟨x, y, hxy, ⟨x, ha.1, rfl⟩, ?_⟩⟩
    rintro ⟨z, hz, hzy⟩
    exact ha.2 (Subtype.ext hzy ▸ hz)
  · -- Different arrows leaving `S` come from different edges: the opposite arrow of an edge
    -- enters `S`.
    rintro a ha a' ha' he
    simp only [mem_coe, mem_sigma, mem_compl, mem_univ, and_true] at ha ha'
    exact bidirectedHom_edge_injOn_cut (G := G) (S : Set V(G)) ha ha'
      (congrArg Subtype.val he)
  · -- An edge crossing `S` gives the arrow from its end in `S` to its end outside `S`.
    rintro e he
    simp only [mem_coe, mem_filter, mem_univ, true_and, mem_edgeCut_iff] at he
    obtain ⟨x, y, hxy, ⟨x', hx', rfl⟩, hy⟩ := he
    refine ⟨⟨x', ⟨y, hxy.right_mem⟩, e.1, hxy⟩, ?_, rfl⟩
    simp only [mem_coe, mem_sigma, mem_compl, mem_univ, and_true]
    exact ⟨hx', fun hy' ↦ hy ⟨_, hy', rfl⟩⟩

end Graph

namespace TauCeti.Flow

variable {α : Type u} {β : Type v} {K : Type w} {G : Graph α β}
variable [Fintype V(G)] [Fintype E(G)] [∀ x y, Fintype (G.BidirectedHom x y)]
variable [AddCommGroup K] {c : E(G) → K} {s t : V(G)}

/-- **Weak duality for weighted multigraphs.** The value of an `s`–`t` flow of a weighted
multigraph is at most the capacity of every set of actual vertices containing `s` but not `t`. -/
theorem val_le_edgeCutCapacity [Preorder K] [AddLeftMono K] (f : Flow (G.bidirectedCapacity c) s t)
    {S : Finset V(G)} (hs : s ∈ S) (ht : t ∉ S) : f.val ≤ G.edgeCutCapacity c S := by
  classical
  exact Graph.arrowSum_bidirectedCapacity c S ▸ f.val_le_arrowSum hs ht

namespace IsMaximum

variable [LinearOrder K] [IsOrderedAddMonoid K] {f : Flow (G.bidirectedCapacity c) s t}

/-- For a maximum `s`–`t` flow `f` of a weighted multigraph, between distinct actual vertices, the
minimum cuts of the multigraph cut function are the sets of actual vertices containing `s` but not
`t` whose capacity is the value of `f`. -/
theorem isMinimum_edgeCutCapacity_iff_val_eq (hst : s ≠ t) (hf : f.IsMaximum)
    {S : Finset V(G)} :
    TerminalCut.IsMinimum (G.edgeCutCapacity c) {s} {t} S ↔
      s ∈ S ∧ t ∉ S ∧ f.val = G.edgeCutCapacity c S := by
  classical
  rw [← funext (Graph.arrowSum_bidirectedCapacity c), ← funext (cutBound_zero_left _)]
  exact ((isMaximum_toBoundedFlow f).2 hf).isMinimum_cutBound_iff_val_eq hst

/-- The value of a maximum `s`–`t` flow of a weighted multigraph, between distinct actual
vertices, is the minimum cut value between `s` and `t` of the multigraph cut function. -/
theorem val_eq_pairMinimumValue_edgeCutCapacity (hst : s ≠ t) (hf : f.IsMaximum) :
    f.val = TerminalCut.pairMinimumValue (G.edgeCutCapacity c) s t := by
  classical
  rw [← funext (Graph.arrowSum_bidirectedCapacity c), ← funext (cutBound_zero_left _)]
  exact ((isMaximum_toBoundedFlow f).2 hf).val_eq_pairMinimumValue hst

end IsMaximum

end TauCeti.Flow

namespace Graph

variable {α : Type u} {β : Type v} {K : Type w} {G : Graph α β}
variable [Fintype V(G)] [Fintype E(G)] [∀ x y, Fintype (G.BidirectedHom x y)]
variable [AddCommGroup K] [LinearOrder K] [IsOrderedAddMonoid K] {c : E(G) → K} {s t : V(G)}

/-- **Undirected max-flow/min-cut theorem with integrality.** For nonnegative capacities on the
edges of a multigraph, all lying in an additive subgroup `H`, and distinct actual vertices `s` and
`t`, some acyclic `s`–`t` flow with all values in `H` has value equal to the capacity of some set of
actual vertices containing `s` but not `t`. By `TauCeti.Flow.val_le_edgeCutCapacity` this flow is
maximum and this cut is minimum. Being acyclic, the flow vanishes on every loop arrow and on one of
the two arrows of every nonloop edge. -/
theorem exists_flow_val_eq_edgeCutCapacity_mem (hst : s ≠ t) (hc : 0 ≤ c) (H : AddSubgroup K)
    (hcH : ∀ e, c e ∈ H) :
    ∃ f : Flow (G.bidirectedCapacity c) s t, f.toFun.IsAcyclic ∧
      (∀ ⦃x y : V(G)⦄ (a : G.BidirectedHom x y), f.toFun a ∈ H) ∧
      ∃ S : Finset V(G), s ∈ S ∧ t ∉ S ∧ f.val = G.edgeCutCapacity c S := by
  classical
  obtain ⟨f, hf, hfH⟩ :=
    Flow.exists_isMaximum_mem (s := s) (t := t) (bidirectedCapacity_nonneg hc) H fun _ _ _ ↦ hcH _
  obtain ⟨S, hs, ht, hval⟩ := hf.exists_val_eq_arrowSum hst
  obtain ⟨g, hg, hgval, -, hgH⟩ := f.exists_isAcyclic_mem H hfH
  exact ⟨g, hg, hgH, S, hs, ht, by rw [hgval, hval, arrowSum_bidirectedCapacity]⟩

/-- **Undirected max-flow/min-cut theorem.** For nonnegative capacities on the edges of a
multigraph and distinct actual vertices `s` and `t`, some acyclic `s`–`t` flow has value equal to
the capacity of some set of actual vertices containing `s` but not `t`. By
`TauCeti.Flow.val_le_edgeCutCapacity` this flow is maximum and this cut is minimum. -/
theorem exists_flow_val_eq_edgeCutCapacity (hst : s ≠ t) (hc : 0 ≤ c) :
    ∃ f : Flow (G.bidirectedCapacity c) s t, f.toFun.IsAcyclic ∧
      ∃ S : Finset V(G), s ∈ S ∧ t ∉ S ∧ f.val = G.edgeCutCapacity c S :=
  let ⟨f, hf, _, hS⟩ :=
    exists_flow_val_eq_edgeCutCapacity_mem hst hc ⊤ fun _ ↦ AddSubgroup.mem_top _
  ⟨f, hf, hS⟩

end Graph
