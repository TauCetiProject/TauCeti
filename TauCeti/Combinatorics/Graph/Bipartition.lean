/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import TauCeti.Combinatorics.Graph.Incidence.Basic
public import TauCeti.Combinatorics.Graph.VertexCover.Basic

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
* `Graph.BipartiteHom G L`: one arrow for every actual edge, directed from `L` to its other end.
* `Graph.BipartiteHom.arrowEquiv`: the equivalence between all such arrows and actual edges.

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
* `Graph.BipartiteHom.sum_outgoing_eq_sum_incidentEdges` and
  `Graph.BipartiteHom.sum_incoming_eq_sum_incidentEdges`: sums over arrows at a vertex agree with
  sums over its incident edges.
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

/-! ### Bipartite arrow family -/

/-- The arrow family obtained by directing every actual edge of `G` from its end in `L` to its
other end. Under a bipartition by `L, R`, these are exactly the edges directed from `L` to `R`. -/
@[expose] def BipartiteHom (G : Graph α β) (L : Finset V(G)) (x y : V(G)) : Type v :=
  {e : E(G) // G.IsLink e x y ∧ x ∈ L}

instance [Finite E(G)] (L : Finset V(G)) (x y : V(G)) : Finite (G.BipartiteHom L x y) := by
  unfold BipartiteHom
  infer_instance

noncomputable instance [Fintype E(G)] (L : Finset V(G)) (x y : V(G)) :
    Fintype (G.BipartiteHom L x y) :=
  Fintype.ofFinite (G.BipartiteHom L x y)

namespace BipartiteHom

/-- The original edge underlying an arrow of the bipartite arrow family. -/
@[expose] def edge {L : Finset V(G)} {x y : V(G)} (e : G.BipartiteHom L x y) : E(G) := e.1

@[simp]
theorem edge_mk {L : Finset V(G)} {x y : V(G)} (e : E(G))
    (h : G.IsLink e x y ∧ x ∈ L) : edge (⟨e, h⟩ : G.BipartiteHom L x y) = e :=
  rfl

/-- The edge underlying a bipartite arrow links its source to its target. -/
theorem isLink {L : Finset V(G)} {x y : V(G)} (e : G.BipartiteHom L x y) :
    G.IsLink e.edge x y :=
  e.2.1

/-- Bipartite arrows are equal when their underlying edges are equal. -/
@[ext]
theorem ext {L : Finset V(G)} {x y : V(G)} {e e' : G.BipartiteHom L x y}
    (h : e.edge = e'.edge) : e = e' :=
  Subtype.ext h

/-- The source of every bipartite arrow belongs to `L`. -/
theorem source_mem {L : Finset V(G)} {x y : V(G)} (e : G.BipartiteHom L x y) : x ∈ L :=
  e.2.2

/-- The target of every bipartite arrow belongs to `R`. -/
theorem target_mem {L R : Finset V(G)} (hLR : G.IsBipartition L R) {x y : V(G)}
    (e : G.BipartiteHom L x y) : y ∈ R :=
  hLR.mem_right_of_isLink e.isLink e.source_mem

/-- The arrows leaving a vertex on the left side of a bipartition are in bijection with the
actual edges incident with that vertex. -/
noncomputable def outgoingEquiv {L : Finset V(G)} (x : V(G)) (hx : x ∈ L) :
    (Σ y, G.BipartiteHom L x y) ≃ {e : E(G) // G.Inc e x} :=
  Equiv.ofBijective (fun e ↦ ⟨e.2.edge, e.2.isLink.inc_left⟩) ⟨by
    rintro ⟨y, e⟩ ⟨z, f⟩ h
    have hef : e.edge = f.edge := congrArg Subtype.val h
    have hyz : y = z := Subtype.ext (e.isLink.right_unique (hef ▸ f.isLink))
    subst z
    exact congrArg (fun a : G.BipartiteHom L x y ↦
      (⟨y, a⟩ : Σ z, G.BipartiteHom L x z)) (BipartiteHom.ext hef), by
    intro e
    let y : V(G) := ⟨e.2.other, e.2.isLink_other.right_mem⟩
    refine ⟨⟨y, ⟨e.1, e.2.isLink_other, hx⟩⟩, ?_⟩
    apply Subtype.ext
    rfl⟩

@[simp]
theorem outgoingEquiv_apply {L : Finset V(G)} (x : V(G)) (hx : x ∈ L)
    (e : Σ y, G.BipartiteHom L x y) :
    outgoingEquiv x hx e = ⟨e.2.edge, e.2.isLink.inc_left⟩ :=
  (rfl)

/-- The arrows entering a vertex on the right side of a bipartition are in bijection with the
actual edges incident with that vertex. -/
noncomputable def incomingEquiv {L R : Finset V(G)} (hLR : G.IsBipartition L R)
    (x : V(G)) (hx : x ∈ R) :
    (Σ y, G.BipartiteHom L y x) ≃ {e : E(G) // G.Inc e x} :=
  Equiv.ofBijective (fun e ↦ ⟨e.2.edge, e.2.isLink.inc_right⟩) ⟨by
    rintro ⟨y, e⟩ ⟨z, f⟩ h
    have hef : e.edge = f.edge := congrArg Subtype.val h
    have hyz : y = z := Subtype.ext (e.isLink.left_unique (hef ▸ f.isLink))
    subst z
    exact congrArg (fun a : G.BipartiteHom L y x ↦
      (⟨y, a⟩ : Σ z, G.BipartiteHom L z x)) (BipartiteHom.ext hef), by
    intro e
    let y : V(G) := ⟨e.2.other, e.2.isLink_other.right_mem⟩
    refine ⟨⟨y, ⟨e.1, e.2.isLink_other.symm,
      hLR.mem_left_of_isLink e.2.isLink_other hx⟩⟩, ?_⟩
    apply Subtype.ext
    rfl⟩

@[simp]
theorem incomingEquiv_apply {L R : Finset V(G)} (hLR : G.IsBipartition L R)
    (x : V(G)) (hx : x ∈ R) (e : Σ y, G.BipartiteHom L y x) :
    incomingEquiv hLR x hx e = ⟨e.2.edge, e.2.isLink.inc_right⟩ :=
  (rfl)

/-- In a bipartite graph, directing an edge from the left side to the right side gives a
bijection from all bipartite arrows to the actual edges. -/
noncomputable def arrowEquiv {L R : Finset V(G)} (hLR : G.IsBipartition L R) :
    (Σ x, Σ y, G.BipartiteHom L x y) ≃ E(G) :=
  Equiv.ofBijective (fun e ↦ e.2.2.edge) ⟨by
    rintro ⟨x, y, e⟩ ⟨x', y', f⟩ h
    have hef : e.edge = f.edge := h
    rcases e.isLink.eq_and_eq_or_eq_and_eq (hef ▸ f.isLink) with hxy | hxy
    · rcases hxy with ⟨hxx, hyy⟩
      have hxx' : x = x' := Subtype.ext hxx
      have hyy' : y = y' := Subtype.ext hyy
      subst x' y'
      exact congrArg (fun a : G.BipartiteHom L x y ↦
        (⟨x, y, a⟩ : Σ x, Σ y, G.BipartiteHom L x y)) (BipartiteHom.ext hef)
    · have hxy' : x = y' := Subtype.ext hxy.1
      exact (disjoint_left.1 hLR.disjoint e.source_mem
        (hxy' ▸ f.target_mem hLR)).elim, by
    intro e
    obtain ⟨x, hxL, hx⟩ := (hLR.existsUnique_mem_left_inc e).exists
    let y : V(G) := ⟨hx.other, hx.isLink_other.right_mem⟩
    refine ⟨⟨x, y, ⟨e, hx.isLink_other, hxL⟩⟩, ?_⟩
    apply Subtype.ext
    rfl⟩

@[simp]
theorem arrowEquiv_apply {L R : Finset V(G)} (hLR : G.IsBipartition L R)
    (e : Σ x, Σ y, G.BipartiteHom L x y) : (arrowEquiv hLR e) = e.2.2.edge :=
  (rfl)

@[simp]
theorem arrowEquiv_symm_edge {L R : Finset V(G)} (hLR : G.IsBipartition L R)
    {x y : V(G)} (e : G.BipartiteHom L x y) :
    (arrowEquiv hLR).symm e.edge = ⟨x, y, e⟩ := by
  apply (arrowEquiv hLR).injective
  simp

/-- Summing an edge weight over the arrows leaving a left-side vertex is the sum over the
actual edges incident with that vertex. -/
theorem sum_outgoing_eq_sum_incidentEdges [Fintype V(G)] [Fintype E(G)]
    {M : Type*} [AddCommMonoid M] {L : Finset V(G)} (x : V(G)) (hx : x ∈ L)
    (f : E(G) → M) :
    ∑ y, ∑ e : G.BipartiteHom L x y, f e.edge = ∑ e ∈ G.incidentEdges {x}, f e := by
  classical
  rw [← Fintype.sum_sigma']
  refine (Fintype.sum_equiv (outgoingEquiv x hx)
    (fun e ↦ f e.2.edge) (fun e ↦ f e.1) fun e ↦ rfl).trans ?_
  exact (Finset.sum_subtype (G.incidentEdges {x}) (by simp [mem_incidentEdges]) f).symm

/-- Summing an edge weight over the arrows entering a right-side vertex is the sum over the
actual edges incident with that vertex. -/
theorem sum_incoming_eq_sum_incidentEdges [Fintype V(G)] [Fintype E(G)]
    {M : Type*} [AddCommMonoid M] {L R : Finset V(G)} (hLR : G.IsBipartition L R)
    (x : V(G)) (hx : x ∈ R) (f : E(G) → M) :
    ∑ y, ∑ e : G.BipartiteHom L y x, f e.edge = ∑ e ∈ G.incidentEdges {x}, f e := by
  classical
  rw [← Fintype.sum_sigma']
  refine (Fintype.sum_equiv (incomingEquiv hLR x hx)
    (fun e ↦ f e.2.edge) (fun e ↦ f e.1) fun e ↦ rfl).trans ?_
  exact (Finset.sum_subtype (G.incidentEdges {x}) (by simp [mem_incidentEdges]) f).symm

end BipartiteHom

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
