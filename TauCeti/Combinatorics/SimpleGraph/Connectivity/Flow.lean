/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Connectivity.Flow

/-!
# Undirected flows on simple graphs

This file specializes the weighted-multigraph max-flow/min-cut theorem to simple graphs with
capacities indexed by unordered pairs of vertices.  The directed network is the bidirected arrow
family of `Graph.ofSimpleGraph G`; no separate undirected flow type is introduced.

The lower-layer bridge `SimpleGraph.edgeCutCapacity_eq_pairCutCapacity` identifies the multigraph
cut capacity with `TauCeti.pairCutCapacity` when capacities vanish away from the graph. It lets weak
duality, max-flow/min-cut, acyclic normalization, and additive-subgroup integrality be used directly
with pair capacities.

## Main results

* `SimpleGraph.edgeCutCapacity_eq_pairCutCapacity`: the two cut-capacity interfaces agree.
* `TauCeti.Flow.val_le_pairCutCapacity`: weak duality for simple-graph pair capacities.
* `SimpleGraph.exists_flow_val_eq_pairCutCapacity_mem`: max-flow/min-cut with
  additive-subgroup integrality.
* `SimpleGraph.exists_flow_val_eq_pairCutCapacity`: max-flow/min-cut without an integrality
  restriction.

The formulation follows the pair-capacity statement shape proposed in Mathlib PR #34028, while
reusing Tau Ceti's edge-indexed bidirected flow theory.
-/

public section

open Finset TauCeti
open scoped Graph

universe u w

namespace SimpleGraph

variable {V : Type u} (G : SimpleGraph V)

/-- The bidirected arrow types of the multigraph realization of a finite simple graph are
finite. -/
noncomputable instance instFintypeOfSimpleGraphBidirectedHom [Fintype V]
    (x y : (Graph.ofSimpleGraph G).vertexSet) :
    Fintype ((Graph.ofSimpleGraph G).BidirectedHom x y) :=
  Fintype.ofFinite _

end SimpleGraph

namespace TauCeti.Flow

variable {V : Type u} {K : Type w} {G : SimpleGraph V}
variable [Fintype V]
variable [AddCommGroup K] [Preorder K] [AddLeftMono K]
variable {c : Sym2 V → K} {s t : V}

/-- **Weak duality for simple-graph pair capacities.** The value of a flow on the bidirected
multigraph realization is at most the pair capacity of every cut separating its terminals.
Capacities away from graph edges may be nonzero on the diagonal, which never crosses a cut. -/
theorem val_le_pairCutCapacity
    (f : Flow ((Graph.ofSimpleGraph G).bidirectedCapacity (G.ofSimpleGraphCapacity c))
      (G.toOfSimpleGraphVertex s) (G.toOfSimpleGraphVertex t))
    (hsupport : ∀ p, ¬p.IsDiag → p ∉ G.edgeSet → c p = 0)
    {S : Finset V} (hs : s ∈ S) (ht : t ∉ S) :
    f.val ≤ pairCutCapacity c S := by
  classical
  rw [← G.edgeCutCapacity_eq_pairCutCapacity c hsupport S]
  exact f.val_le_edgeCutCapacity
    (G.mem_toOfSimpleGraphFinset.mpr hs)
    (fun ht' ↦ ht (G.mem_toOfSimpleGraphFinset.mp ht'))

end TauCeti.Flow

namespace SimpleGraph

variable {V : Type u} {K : Type w} (G : SimpleGraph V)

/-- **Undirected max-flow/min-cut for simple graphs, with integrality.** Let pair capacities be
nonnegative on the edges and vanish away from the edges of `G`, except possibly on the diagonal.
For distinct vertices, there is an acyclic flow on the bidirected multigraph realization whose
value equals the pair capacity of a separating cut. If all edge capacities lie in an
additive subgroup `A`, all arrow values of the flow can be chosen in `A` as well. -/
theorem exists_flow_val_eq_pairCutCapacity_mem [Fintype V]
    [AddCommGroup K] [LinearOrder K] [IsOrderedAddMonoid K]
    (c : Sym2 V → K) {s t : V} (hst : s ≠ t)
    (hc : ∀ p ∈ G.edgeSet, 0 ≤ c p)
    (hsupport : ∀ p, ¬p.IsDiag → p ∉ G.edgeSet → c p = 0)
    (A : AddSubgroup K) (hcA : ∀ p ∈ G.edgeSet, c p ∈ A) :
    ∃ f : Flow ((Graph.ofSimpleGraph G).bidirectedCapacity (G.ofSimpleGraphCapacity c))
        (G.toOfSimpleGraphVertex s) (G.toOfSimpleGraphVertex t),
      f.toFun.IsAcyclic ∧
      (∀ ⦃x y⦄ (a : (Graph.ofSimpleGraph G).BidirectedHom x y), f.toFun a ∈ A) ∧
      ∃ S : Finset V, s ∈ S ∧ t ∉ S ∧ f.val = pairCutCapacity c S := by
  classical
  have hst' : G.toOfSimpleGraphVertex s ≠ G.toOfSimpleGraphVertex t := by
    intro h
    exact hst (by simpa using congrArg Subtype.val h)
  have hcap : 0 ≤ G.ofSimpleGraphCapacity c := fun e ↦ by
    rw [G.ofSimpleGraphCapacity_apply]
    exact hc e.1 (by simpa using e.2)
  have hcapA : ∀ e, G.ofSimpleGraphCapacity c e ∈ A := fun e ↦ by
    rw [G.ofSimpleGraphCapacity_apply]
    exact hcA e.1 (by simpa using e.2)
  obtain ⟨f, hfacyc, hfA, T, hsT, htT, hval⟩ :=
    (Graph.ofSimpleGraph G).exists_flow_val_eq_edgeCutCapacity_mem hst' hcap A hcapA
  let S : Finset V := T.map ⟨Subtype.val, Subtype.val_injective⟩
  refine ⟨f, hfacyc, hfA, S, ?_, ?_, ?_⟩
  · exact Finset.mem_map.mpr ⟨G.toOfSimpleGraphVertex s, hsT, by simp⟩
  · intro htS
    obtain ⟨x, hxT, hxt⟩ := Finset.mem_map.mp htS
    apply htT
    have hx : x = G.toOfSimpleGraphVertex t := Subtype.ext (by simpa using hxt)
    exact hx ▸ hxT
  · have hcut := G.edgeCutCapacity_eq_pairCutCapacity c hsupport S
    rw [toOfSimpleGraphFinset_map_val] at hcut
    exact hval.trans hcut

/-- **Undirected max-flow/min-cut for simple graphs.** For pair capacities nonnegative on the
edges and supported off the diagonal on those edges, distinct vertices admit an acyclic flow and a
separating cut of equal value and pair capacity. -/
theorem exists_flow_val_eq_pairCutCapacity [Fintype V]
    [AddCommGroup K] [LinearOrder K] [IsOrderedAddMonoid K]
    (c : Sym2 V → K) {s t : V} (hst : s ≠ t)
    (hc : ∀ p ∈ G.edgeSet, 0 ≤ c p)
    (hsupport : ∀ p, ¬p.IsDiag → p ∉ G.edgeSet → c p = 0) :
    ∃ f : Flow ((Graph.ofSimpleGraph G).bidirectedCapacity (G.ofSimpleGraphCapacity c))
        (G.toOfSimpleGraphVertex s) (G.toOfSimpleGraphVertex t),
      f.toFun.IsAcyclic ∧
      ∃ S : Finset V, s ∈ S ∧ t ∉ S ∧ f.val = pairCutCapacity c S := by
  obtain ⟨f, hfacyc, -, hS⟩ :=
    G.exists_flow_val_eq_pairCutCapacity_mem c hst hc hsupport ⊤
      (fun _ _ ↦ AddSubgroup.mem_top _)
  exact ⟨f, hfacyc, hS⟩

end SimpleGraph
