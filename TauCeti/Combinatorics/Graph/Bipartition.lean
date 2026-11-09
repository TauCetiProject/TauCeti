/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import TauCeti.Combinatorics.Graph.Incidence
public import TauCeti.Combinatorics.Graph.VertexCover

/-!
# Bipartitions of multigraphs

A *bipartition* of a multigraph `G : Graph α β` is a pair of disjoint finite sets `L` and `R` of
actual vertices, together covering `V(G)`, such that every edge joins a vertex of `L` to a vertex
of `R`. Parallel edges are allowed, isolated vertices may lie on either side, and either side may
be empty; loops are excluded, since the two ends of a loop coincide.

The sides are finite sets of actual vertices, so that sums of vertex capacities over a side, or
over a part of it, are finite sums; in particular a multigraph with a bipartition has finitely many
actual vertices. Since every actual edge has exactly one end in each side, summing over one side the
values of the edges incident with each vertex counts every actual edge exactly once, so the total
usage of either side by edge multiplicities equals their sum.

## Main definitions

* `Graph.IsBipartition G L R`: the finite sets `L` and `R` of actual vertices form a bipartition of
  `G`.

## Main results

* `Graph.isBipartition_comm`: a bipartition is symmetric in its two sides.
* `Graph.IsBipartition.loopless`: a multigraph with a bipartition has no loops.
* `Graph.IsBipartition.finite`: a multigraph with a bipartition has finitely many actual vertices.
* `Graph.IsBipartition.deleteEdges`: deleting edges preserves a displayed bipartition.
* `SimpleGraph.isBipartition_ofSimpleGraph_iff`: covering bipartitions of
  `Graph.ofSimpleGraph H` are precisely bipartitions of `H` whose two sides cover every vertex.
* `Graph.IsBipartition.isVertexCover_left`: the side `L` of a bipartition is a vertex cover, and
  similarly for `R`.
* `Graph.IsBipartition.sum_sum_incidentEdges_left`: summing over `L` the values of the edges
  incident with each vertex sums every actual edge once, and similarly for `R`.
-/

public section

open Finset
open scoped Graph

universe u v

namespace Graph

variable {α : Type u} {β : Type v} {G : Graph α β} {L R : Finset V(G)}

variable (G) in
/-- The finite sets `L` and `R` of actual vertices form a *bipartition* of the multigraph `G`: they
are disjoint, every actual vertex lies in one of them, and every edge joins a vertex of `L` to a
vertex of `R`. -/
structure IsBipartition (L R : Finset V(G)) : Prop where
  disjoint : Disjoint L R
  mem_or_mem (x : V(G)) : x ∈ L ∨ x ∈ R
  isLink {e : β} {x y : V(G)} : G.IsLink e x y → x ∈ L ∧ y ∈ R ∨ x ∈ R ∧ y ∈ L

namespace IsBipartition

/-- Exchanging the two sides of a bipartition gives a bipartition. -/
protected theorem symm (h : G.IsBipartition L R) : G.IsBipartition R L where
  disjoint := h.disjoint.symm
  mem_or_mem x := (h.mem_or_mem x).symm
  isLink he := (h.isLink he).symm

/-- An actual vertex outside `L` lies in `R`. -/
theorem notMem_left_iff (h : G.IsBipartition L R) {x : V(G)} : x ∉ L ↔ x ∈ R :=
  ⟨(h.mem_or_mem x).resolve_left, fun hx ↦ disjoint_right.1 h.disjoint hx⟩

/-- An actual vertex outside `R` lies in `L`. -/
theorem notMem_right_iff (h : G.IsBipartition L R) {x : V(G)} : x ∉ R ↔ x ∈ L :=
  h.symm.notMem_left_iff

/-- An edge with one end in `L` has its other end in `R`. -/
theorem mem_right_of_isLink (h : G.IsBipartition L R) {e : β} {x y : V(G)}
    (he : G.IsLink e x y) (hx : x ∈ L) : y ∈ R :=
  (h.isLink he).elim And.right fun hxy ↦ absurd hx (h.notMem_left_iff.2 hxy.1)

/-- An edge with one end in `R` has its other end in `L`. -/
theorem mem_left_of_isLink (h : G.IsBipartition L R) {e : β} {x y : V(G)}
    (he : G.IsLink e x y) (hx : x ∈ R) : y ∈ L :=
  h.symm.mem_right_of_isLink he hx

/-- A multigraph with a bipartition has no loops. -/
theorem loopless (h : G.IsBipartition L R) : G.Loopless where
  not_isLoopAt e x hx := by
    have hx' : x ∈ V(G) := hx.vertex_mem
    rcases h.isLink (x := ⟨x, hx'⟩) (y := ⟨x, hx'⟩) hx with ⟨hL, hR⟩ | ⟨hR, hL⟩ <;>
      exact disjoint_left.1 h.disjoint hL hR

/-- A multigraph with a bipartition has finitely many actual vertices. -/
theorem finite (h : G.IsBipartition L R) : Finite V(G) := by
  classical
  exact Set.finite_univ_iff.1 <| (L ∪ R).finite_toSet.subset fun x _ ↦ by
    simpa using h.mem_or_mem x

/-- Deleting any set of edges preserves a displayed bipartition. The actual vertex set, including
its isolated vertices, is unchanged. -/
theorem deleteEdges (h : G.IsBipartition L R) (F : Set β) :
    (G.deleteEdges F).IsBipartition L R where
  disjoint := h.disjoint
  mem_or_mem := h.mem_or_mem
  isLink he := h.isLink (he.mono Graph.deleteEdges_le)

/-- The side `L` of a bipartition is a vertex cover. -/
theorem isVertexCover_left (h : G.IsBipartition L R) : G.IsVertexCover (L : Set V(G)) :=
  isVertexCover_def.2 fun _ _ _ he ↦ (h.isLink he).imp And.left And.right

/-- The side `R` of a bipartition is a vertex cover. -/
theorem isVertexCover_right (h : G.IsBipartition L R) : G.IsVertexCover (R : Set V(G)) :=
  h.symm.isVertexCover_left

/-- Every actual edge has exactly one end in `L`. -/
theorem existsUnique_mem_left_inc (h : G.IsBipartition L R) (e : E(G)) :
    ∃! x : V(G), x ∈ L ∧ G.Inc e x := by
  obtain ⟨x, y, he⟩ := G.exists_isLink_of_mem_edgeSet e.2
  -- Orient the link so that its first end lies in `L`; the other end then lies in `R`.
  wlog hx : ∃ hx : x ∈ V(G), (⟨x, hx⟩ : V(G)) ∈ L generalizing x y
  · have hx' : x ∈ V(G) := he.left_mem
    have hy' : y ∈ V(G) := he.right_mem
    refine this y x he.symm ⟨hy', ?_⟩
    rcases h.isLink (x := ⟨x, hx'⟩) (y := ⟨y, hy'⟩) he with ⟨hxL, -⟩ | ⟨-, hyL⟩
    exacts [absurd ⟨hx', hxL⟩ hx, hyL]
  obtain ⟨hx, hxL⟩ := hx
  refine ⟨⟨x, hx⟩, ⟨hxL, he.inc_left⟩, fun z ⟨hzL, hz⟩ ↦ ?_⟩
  rcases hz.eq_or_eq_of_isLink he with hzx | hzy
  · exact Subtype.ext hzx
  · have hyR := h.mem_right_of_isLink (y := ⟨y, he.right_mem⟩) he hxL
    exact absurd hzL (h.notMem_left_iff.2 ((Subtype.ext hzy : z = ⟨y, he.right_mem⟩) ▸ hyR))

/-- Every actual edge has exactly one end in `R`. -/
theorem existsUnique_mem_right_inc (h : G.IsBipartition L R) (e : E(G)) :
    ∃! x : V(G), x ∈ R ∧ G.Inc e x :=
  h.symm.existsUnique_mem_left_inc e

variable [Fintype E(G)] {M : Type*} [AddCommMonoid M]

/-- Every actual edge has exactly one end in `L`, so summing over `L` the values of the edges
incident with each vertex sums every actual edge once. -/
theorem sum_sum_incidentEdges_left (h : G.IsBipartition L R) (f : E(G) → M) :
    ∑ x ∈ L, ∑ e ∈ G.incidentEdges {x}, f e = ∑ e, f e := by
  classical
  rw [sum_sum_incidentEdges_eq_sum_sum_filter_inc]
  refine sum_congr rfl fun e _ ↦ ?_
  obtain ⟨x, hx, hxu⟩ := h.existsUnique_mem_left_inc e
  rw [eq_singleton_iff_unique_mem.2 ⟨mem_filter.2 hx, fun y hy ↦ hxu y (mem_filter.1 hy)⟩,
    sum_singleton]

/-- Every actual edge has exactly one end in `R`, so summing over `R` the values of the edges
incident with each vertex sums every actual edge once. -/
theorem sum_sum_incidentEdges_right (h : G.IsBipartition L R) (f : E(G) → M) :
    ∑ x ∈ R, ∑ e ∈ G.incidentEdges {x}, f e = ∑ e, f e :=
  h.symm.sum_sum_incidentEdges_left f

end IsBipartition

/-- A bipartition is symmetric in its two sides. -/
theorem isBipartition_comm : G.IsBipartition L R ↔ G.IsBipartition R L :=
  ⟨IsBipartition.symm, IsBipartition.symm⟩

end Graph

namespace SimpleGraph

variable {α : Type u}

/-- Finite sets `L` and `R` form a covering bipartition of the multigraph associated to a simple
graph `H` exactly when they are bipartition classes of `H` and cover its entire vertex type.

The covering condition is separate because `SimpleGraph.IsBipartiteWith` permits isolated
vertices outside both displayed sets, whereas `Graph.IsBipartition` partitions all actual
vertices. -/
theorem isBipartition_ofSimpleGraph_iff (H : SimpleGraph α)
    (L R : Finset V(Graph.ofSimpleGraph H)) :
    (Graph.ofSimpleGraph H).IsBipartition L R ↔
      H.IsBipartiteWith (Subtype.val '' (L : Set V(Graph.ofSimpleGraph H)))
          (Subtype.val '' (R : Set V(Graph.ofSimpleGraph H))) ∧
        Subtype.val '' (L : Set V(Graph.ofSimpleGraph H)) ∪
          Subtype.val '' (R : Set V(Graph.ofSimpleGraph H)) = Set.univ := by
  constructor
  · intro h
    refine ⟨⟨?_, ?_⟩, Set.eq_univ_of_forall fun x ↦ ?_⟩
    · rw [Set.disjoint_left]
      rintro _ ⟨x, hxL, rfl⟩ ⟨y, hxR, hyx⟩
      have hxy : x = y := Subtype.ext hyx.symm
      exact Finset.disjoint_left.mp h.disjoint hxL (hxy ▸ hxR)
    · intro x y hxy
      obtain ⟨e, he⟩ : (Graph.ofSimpleGraph H).Adj x y :=
        (Graph.ofSimpleGraph_adj_iff x y).2 hxy
      rcases h.isLink (x := ⟨x, Set.mem_univ x⟩) (y := ⟨y, Set.mem_univ y⟩) he with
        hxy | hxy
      · exact Or.inl ⟨⟨_, hxy.1, rfl⟩, ⟨_, hxy.2, rfl⟩⟩
      · exact Or.inr ⟨⟨_, hxy.1, rfl⟩, ⟨_, hxy.2, rfl⟩⟩
    · rcases h.mem_or_mem ⟨x, Set.mem_univ x⟩ with hx | hx
      · exact Or.inl ⟨_, hx, rfl⟩
      · exact Or.inr ⟨_, hx, rfl⟩
  · rintro ⟨h, hcover⟩
    refine ⟨Finset.disjoint_left.mpr fun x hxL hxR ↦ ?_, fun x ↦ ?_, fun {e x y} he ↦ ?_⟩
    · exact Set.disjoint_left.mp h.disjoint ⟨x, hxL, rfl⟩ ⟨x, hxR, rfl⟩
    · have hx : x.1 ∈ Subtype.val '' (L : Set V(Graph.ofSimpleGraph H)) ∪
          Subtype.val '' (R : Set V(Graph.ofSimpleGraph H)) := by
        rw [hcover]
        exact Set.mem_univ x.1
      rcases hx with ⟨z, hz, hzx⟩ | ⟨z, hz, hzx⟩
      · exact Or.inl (Subtype.ext hzx ▸ hz)
      · exact Or.inr (Subtype.ext hzx ▸ hz)
    · have hxy : H.Adj x.1 y.1 :=
        (Graph.ofSimpleGraph_adj_iff x.1 y.1).1 ⟨_, he⟩
      rcases h.mem_of_adj hxy with hxy | hxy
      · obtain ⟨x', hx'L, hxx'⟩ := hxy.1
        obtain ⟨y', hy'R, hyy'⟩ := hxy.2
        exact Or.inl ⟨Subtype.ext hxx' ▸ hx'L, Subtype.ext hyy' ▸ hy'R⟩
      · obtain ⟨x', hx'R, hxx'⟩ := hxy.1
        obtain ⟨y', hy'L, hyy'⟩ := hxy.2
        exact Or.inr ⟨Subtype.ext hxx' ▸ hx'R, Subtype.ext hyy' ▸ hy'L⟩

end SimpleGraph
