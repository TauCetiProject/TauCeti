/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Graph.Lattice
public import Mathlib.Combinatorics.SimpleGraph.Subgraph
public import TauCeti.Combinatorics.Graph.Simple
public import TauCeti.Combinatorics.Graph.Union

/-!
# Order isomorphism and structural bridges for simple-graph subgraphs

`TauCeti.Combinatorics.Graph.Simple` associates to every bundled subgraph `S : H.Subgraph` of a
simple graph `H : SimpleGraph α` an edge-labelled multigraph `S.toGraph : Graph α (Sym2 α)` below
`Graph.ofSimpleGraph H`, with inverse `Graph.toSimpleGraphSubgraph`.

This file packages that correspondence as an order isomorphism
`SimpleGraph.subgraphOfSimpleGraphOrderIso : H.Subgraph ≃o Set.Iic (Graph.ofSimpleGraph H)`, records
its compatibility with intersections, compatible multigraph unions, spanning and induced subgraph
predicates, simplicity, and edge-set finiteness, and constructs the canonical isomorphisms
`S.toGraph.toSimpleGraph ≃g S.coe` and `Graph.Iso (Graph.ofSimpleGraph S.coe) S.toGraph`.

## Main definitions

* `SimpleGraph.Subgraph.toGraphToSimpleGraphIso`: canonical simple-graph isomorphism
  `S.toGraph.toSimpleGraph ≃g S.coe`.
* `SimpleGraph.Subgraph.ofSimpleGraphCoeIso`: canonical multigraph isomorphism
  `Graph.Iso (Graph.ofSimpleGraph S.coe) S.toGraph`.
* `SimpleGraph.subgraphOfSimpleGraphOrderIso`: the order isomorphism
  `H.Subgraph ≃o Set.Iic (Graph.ofSimpleGraph H)`.
-/

public section

open Set
open scoped Graph Sym2

universe u

namespace SimpleGraph.Subgraph

variable {α : Type u} {H : SimpleGraph α}

/-- The multigraph associated to any simple-graph subgraph is simple (loopless with no parallel
edges). -/
instance instSimpleToGraph (S : H.Subgraph) : S.toGraph.Simple where
  not_isLoopAt e x h := by rw [Graph.IsLoopAt, toGraph_isLink] at h; exact S.loopless.irrefl x h.2
  eq_of_isLink _ _ _ _ h₁ h₂ := by rw [toGraph_isLink] at h₁ h₂; exact h₁.1.trans h₂.1.symm

@[gcongr]
theorem toGraph_mono {S T : H.Subgraph} (h : S ≤ T) : S.toGraph ≤ T.toGraph :=
  (toGraph_le_toGraph S T).mpr h

theorem toGraph_injective : Function.Injective (toGraph (G := H)) :=
  fun _ _ ↦ toGraph_inj.mp

@[simp]
theorem toGraph_lt_toGraph (S T : H.Subgraph) : S.toGraph < T.toGraph ↔ S < T :=
  lt_iff_lt_of_le_iff_le' (toGraph_le_toGraph T S) (toGraph_le_toGraph S T)

@[simp]
theorem toGraph_inf (S T : H.Subgraph) : (S ⊓ T).toGraph = S.toGraph ⊓ T.toGraph :=
  Graph.ext (by simp) fun _ _ _ ↦ by simp [and_left_comm, and_assoc]

/-- Any two subgraphs of the same simple graph convert to compatible multigraphs. -/
theorem toGraph_compatible (S T : H.Subgraph) : S.toGraph.Compatible T.toGraph :=
  .of_le_le S.toGraph_le_ofSimpleGraph T.toGraph_le_ofSimpleGraph

/-- The supremum of two simple-graph subgraphs corresponds to the compatible multigraph union. -/
theorem toGraph_sup (S T : H.Subgraph) : (S ⊔ T).toGraph = (S.toGraph_compatible T).union :=
  Graph.ext (by simp) fun _ _ _ ↦ by simp [and_or_left]

/-- When `S.edgeSet` is finite, `S.toGraph` has finitely many actual edges. -/
instance instFiniteEdgeSetToGraph (S : H.Subgraph) [Finite S.edgeSet] : Finite E(S.toGraph) := by
  rw [S.edgeSet_toGraph]; infer_instance

@[simp]
theorem isSpanningSubgraph_toGraph_iff {S : H.Subgraph} :
    S.toGraph ≤s Graph.ofSimpleGraph H ↔ S.IsSpanning := by
  rw [Graph.isSpanningSubgraph_iff, Subgraph.isSpanning_iff]; simp [S.toGraph_le_ofSimpleGraph]

@[simp]
theorem isInducedSubgraph_toGraph_iff {S : H.Subgraph} :
    S.toGraph.IsInducedSubgraph (Graph.ofSimpleGraph H) ↔ S.IsInduced := by
  rw [Graph.isInducedSubgraph_iff]
  refine ⟨fun ⟨_, h⟩ x hx y hy hxy ↦ ?_, fun h ↦ ⟨S.toGraph_le_ofSimpleGraph, ?_⟩⟩
  · exact ((S.toGraph_isLink s(x, y) x y).mp
      (h (by simpa [Graph.ofSimpleGraph_isLink] using hxy)
        (S.vertexSet_toGraph.symm ▸ hx) (S.vertexSet_toGraph.symm ▸ hy))).2
  · rintro e x y he hx hy
    rw [Graph.ofSimpleGraph_isLink] at he; rcases he with ⟨rfl, he⟩
    exact (S.toGraph_isLink _ _ _).mpr
      ⟨rfl, h (S.vertexSet_toGraph ▸ hx) (S.vertexSet_toGraph ▸ hy) (H.mem_edgeSet.mp he)⟩

/-- The underlying simple graph of `S.toGraph` is canonically isomorphic to `S.coe`. -/
def toGraphToSimpleGraphIso (S : H.Subgraph) : S.toGraph.toSimpleGraph ≃g S.coe where
  toEquiv := Equiv.subtypeEquivRight fun _ ↦ by rw [S.vertexSet_toGraph]
  map_rel_iff' {x y} := by rw [S.toGraph.toSimpleGraph_adj_iff, S.toGraph_adj, S.coe_adj]; rfl

@[simp] theorem coe_toGraphToSimpleGraphIso_apply (S : H.Subgraph) (x : V(S.toGraph)) :
    (S.toGraphToSimpleGraphIso x : α) = x := (rfl)

@[simp] theorem coe_toGraphToSimpleGraphIso_symm_apply (S : H.Subgraph) (x : S.verts) :
    (S.toGraphToSimpleGraphIso.symm x : α) = x := (rfl)

/-- The multigraph built from the coerced simple graph `S.coe` is canonically isomorphic to
`S.toGraph`. -/
noncomputable def ofSimpleGraphCoeIso (S : H.Subgraph) :
    Graph.Iso (Graph.ofSimpleGraph S.coe) S.toGraph where
  vertexEquiv := (Equiv.Set.univ S.verts).trans
    (Equiv.subtypeEquivRight fun _ ↦ by rw [S.vertexSet_toGraph]).symm
  edgeEquiv := Equiv.ofBijective
    (fun e ↦ ⟨e.1.map Subtype.val, by
      have hm : e.1 ∈ S.coe.edgeSet := by simpa only [Graph.edgeSet_ofSimpleGraph] using e.2
      rw [S.edgeSet_toGraph]; rwa [S.edgeSet_coe] at hm⟩)
    ⟨fun _ _ h ↦ Subtype.ext (Sym2.map.injective Subtype.val_injective (Subtype.ext_iff.mp h)),
     fun ⟨f, hf⟩ ↦ by
      rw [S.edgeSet_toGraph, ← S.image_coe_edgeSet_coe] at hf
      obtain ⟨e, he, rfl⟩ := hf
      exact ⟨⟨e, by simpa only [Graph.edgeSet_ofSimpleGraph] using he⟩, rfl⟩⟩
  map_isLink_iff e x y := by
    simp only [toGraph_isLink, Graph.ofSimpleGraph_isLink]
    have hm : e.1 ∈ S.coe.edgeSet := by simpa only [Graph.edgeSet_ofSimpleGraph] using e.2
    refine ⟨fun ⟨he, _⟩ ↦ ⟨Sym2.map.injective Subtype.val_injective he, hm⟩,
      fun ⟨he, _⟩ ↦ ⟨congrArg (Sym2.map Subtype.val) he, ?_⟩⟩
    rwa [he, SimpleGraph.mem_edgeSet, S.coe_adj] at hm

@[simp] theorem coe_ofSimpleGraphCoeIso_vertexEquiv_apply (S : H.Subgraph)
    (x : V(Graph.ofSimpleGraph S.coe)) :
    (S.ofSimpleGraphCoeIso.vertexEquiv x : α) = (x.1 : α) := (rfl)

@[simp] theorem coe_ofSimpleGraphCoeIso_edgeEquiv_apply (S : H.Subgraph)
    (e : E(Graph.ofSimpleGraph S.coe)) :
    (S.ofSimpleGraphCoeIso.edgeEquiv e : Sym2 α) = e.1.map Subtype.val := (rfl)

end SimpleGraph.Subgraph

namespace Graph

variable {α : Type u} {H : SimpleGraph α}

/-- Converting the intersection of two subgraphs of `Graph.ofSimpleGraph H` to a simple subgraph
commutes with `⊓`. -/
theorem toSimpleGraphSubgraph_inf (K L : Graph α (Sym2 α))
    (hK : K ≤ Graph.ofSimpleGraph H) (hL : L ≤ Graph.ofSimpleGraph H) :
    (K ⊓ L).toSimpleGraphSubgraph (inf_le_left.trans hK) =
      K.toSimpleGraphSubgraph hK ⊓ L.toSimpleGraphSubgraph hL :=
  SimpleGraph.Subgraph.toGraph_injective (by simp)

/-- Converting the compatible union of two subgraphs of `Graph.ofSimpleGraph H` to a simple
subgraph commutes with `⊔`. -/
theorem toSimpleGraphSubgraph_union (K L : Graph α (Sym2 α))
    (hK : K ≤ Graph.ofSimpleGraph H) (hL : L ≤ Graph.ofSimpleGraph H) :
    (Compatible.of_le_le hK hL).union.toSimpleGraphSubgraph (IsSubgraph.union_le hK hL) =
      K.toSimpleGraphSubgraph hK ⊔ L.toSimpleGraphSubgraph hL := by
  apply SimpleGraph.Subgraph.toGraph_injective
  rw [toGraph_toSimpleGraphSubgraph, SimpleGraph.Subgraph.toGraph_sup]
  exact Graph.ext (by simp) fun _ _ _ ↦ by simp

/-- When `H.edgeSet` is finite, `Graph.ofSimpleGraph H` has finitely many actual edges. -/
instance instFiniteEdgeSetOfSimpleGraph (H : SimpleGraph α) [Finite H.edgeSet] :
    Finite E(Graph.ofSimpleGraph H) := by
  rw [Graph.edgeSet_ofSimpleGraph]; infer_instance

end Graph

namespace SimpleGraph

variable {α : Type u}

/-- Subgraphs `S : H.Subgraph` of a simple graph `H` are order-isomorphic to multigraph subgraphs
`K ≤ Graph.ofSimpleGraph H`. -/
def subgraphOfSimpleGraphOrderIso (H : SimpleGraph α) :
    H.Subgraph ≃o Set.Iic (Graph.ofSimpleGraph H) where
  toFun S := ⟨S.toGraph, S.toGraph_le_ofSimpleGraph⟩
  invFun K := K.1.toSimpleGraphSubgraph K.2
  left_inv S := S.toSimpleGraphSubgraph_toGraph _
  right_inv K := Subtype.ext (K.1.toGraph_toSimpleGraphSubgraph K.2)
  map_rel_iff' := Subgraph.toGraph_le_toGraph _ _

@[simp] theorem coe_subgraphOfSimpleGraphOrderIso_apply (H : SimpleGraph α) (S : H.Subgraph) :
    (H.subgraphOfSimpleGraphOrderIso S : Graph α (Sym2 α)) = S.toGraph := (rfl)

@[simp] theorem subgraphOfSimpleGraphOrderIso_symm_apply (H : SimpleGraph α)
    (K : Set.Iic (Graph.ofSimpleGraph H)) :
    H.subgraphOfSimpleGraphOrderIso.symm K = K.1.toSimpleGraphSubgraph K.2 := (rfl)

end SimpleGraph
