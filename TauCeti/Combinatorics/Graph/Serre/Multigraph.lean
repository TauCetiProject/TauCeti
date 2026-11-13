/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Basic
public import TauCeti.Combinatorics.Graph.Connectivity.Component

/-!
# The multigraph underlying a Serre graph

Reversal pairs of darts are the edges of the underlying undirected multigraph. This
construction retains loops and parallel edges, while its walks forget which direction of a
loop was chosen. Path reachability and connectedness agree with those of the multigraph.

When all darts are loops, for instance in the graph `noEdge V` without edges, distinct vertices
lie in distinct connected components and the component count `Graph.componentCount` is
`Nat.card` of the vertex type; for `noEdge V` the multigraph is `Graph.noEdge Set.univ _`. The
multigraph of the empty graph is not connected and has no component, and that of two isolated
vertices has two.

The directed paths remain necessary for the fundamental group of a graph: the two darts of a
loop represent inverse generators, even though they give the same one-edge undirected walk.

## References

* J.-P. Serre, *Trees*, Chapter I, §§2.1–2.2.
-/

public section

namespace TauCeti
namespace SerreGraph

variable (Γ : SerreGraph)

/-- Two darts represent the same undirected edge when they are equal or reverse one another. -/
def edgeSetoid : Setoid Γ.E where
  r e f := e = f ∨ e = Γ.rev f
  iseqv := ⟨fun _ => Or.inl rfl,
    by
      intro e f h
      rcases h with rfl | h
      · exact Or.inl rfl
      · exact Or.inr (by rw [h, Γ.rev_rev]),
    by
      intro e f g h k
      rcases h with rfl | h
      · exact k
      · rcases k with rfl | k
        · exact Or.inr h
        · exact Or.inl (by rw [h, k, Γ.rev_rev])⟩

/-- The undirected edge carried by a dart, identified with its reverse. -/
abbrev Edge : Type _ := Quotient Γ.edgeSetoid

/-- The reversal orbit of a dart. -/
def edge (e : Γ.E) : Γ.Edge := Quotient.mk Γ.edgeSetoid e

/-- Every undirected edge is represented by a dart. -/
theorem edge_surjective : Function.Surjective Γ.edge := Quotient.mk_surjective

/-- Induction on an undirected edge through a representing dart. -/
@[elab_as_elim] theorem Edge.ind {motive : Γ.Edge → Prop}
    (h : ∀ e : Γ.E, motive (Γ.edge e)) (q : Γ.Edge) : motive q := by
  obtain ⟨e, rfl⟩ := Γ.edge_surjective q
  exact h e

@[simp] theorem edge_rev (e : Γ.E) : Γ.edge (Γ.rev e) = Γ.edge e :=
  Quotient.sound (Or.inr rfl)

/-- Two darts determine the same edge exactly when they agree up to reversal. -/
theorem edge_eq_iff (e f : Γ.E) :
    Γ.edge e = Γ.edge f ↔ e = f ∨ e = Γ.rev f := Quotient.eq

/-- The ends of a reversal orbit, as an unordered pair. -/
def edgeEnds (q : Γ.Edge) : Sym2 Γ.V :=
  Quotient.liftOn q (fun e => s(Γ.src e, Γ.tgt e)) (by
    intro e f h
    rcases h with rfl | h
    · rfl
    · subst e
      simp only [Γ.src_rev, Γ.tgt_rev]
      exact Sym2.eq_swap)

@[simp] theorem edgeEnds_edge (e : Γ.E) :
    Γ.edgeEnds (Γ.edge e) = s(Γ.src e, Γ.tgt e) := by
  unfold edgeEnds edge
  rfl

/-- The undirected multigraph whose edges are reversal pairs of darts. -/
def toGraph : Graph Γ.V Γ.Edge where
  vertexSet := Set.univ
  edgeSet := Set.univ
  IsLink q x y := Γ.edgeEnds q = s(x, y)
  isLink_symm := by
    aesop (add simp symm_def)
  eq_or_eq_of_isLink_of_isLink := by
    intro q x y v w h k
    have h' : s(x, y) = s(v, w) := h.symm.trans k
    rcases Sym2.eq_iff.mp h' with h | h
    · exact Or.inl h.1
    · exact Or.inr h.1
  edge_mem_iff_exists_isLink := by
    intro q
    constructor
    · intro _
      obtain ⟨e, rfl⟩ := Γ.edge_surjective q
      exact ⟨Γ.src e, Γ.tgt e, rfl⟩
    · intro _
      trivial
  left_mem_of_isLink := by
    intro q x y _
    trivial

@[simp] theorem vertexSet_toGraph : (Γ.toGraph).vertexSet = Set.univ := by
  simp only [toGraph]

@[simp] theorem edgeSet_toGraph : (Γ.toGraph).edgeSet = Set.univ := by
  simp only [toGraph]

@[simp] theorem toGraph_isLink (q : Γ.Edge) (x y : Γ.V) :
    Γ.toGraph.IsLink q x y ↔ Γ.edgeEnds q = s(x, y) := Iff.rfl

/-- A Serre dart links its endpoints in the underlying multigraph. -/
theorem toGraph_isLink_edge {u v : Γ.V} (e : Quiver.Hom u v) :
    Γ.toGraph.IsLink (Γ.edge e.1) u v := by
  rw [toGraph_isLink, edgeEnds_edge]
  exact congrArg₂ (fun x y => s(x, y)) e.2.1 e.2.2

/-- Forget the directions of a Serre path, retaining its edge orbits. -/
def Path.toWalk {u v : Γ.V} (p : Γ.Path u v) : Γ.toGraph.Walk u v := by
  induction p with
  | nil => exact .nil
  | @cons a b _ e ih =>
    exact ih.append (Γ.toGraph_isLink_edge e).toWalk

@[simp] theorem Path.toWalk_nil (u : Γ.V) :
    Path.toWalk Γ (Quiver.Path.nil : Γ.Path u u) = .nil := (rfl)

@[simp] theorem Path.toWalk_cons {u v w : Γ.V} (p : Γ.Path u v)
    (e : Quiver.Hom v w) :
    Path.toWalk Γ (p.cons e) = (Path.toWalk Γ p).append
      (Γ.toGraph_isLink_edge e).toWalk := (rfl)

@[simp] theorem Path.toWalk_comp {u v w : Γ.V} (p : Γ.Path u v)
    (q : Γ.Path v w) :
    Path.toWalk Γ (p.comp q) = (Path.toWalk Γ p).append (Path.toWalk Γ q) := by
  induction q with
  | nil => simp
  | cons q e ih =>
    simp only [Quiver.Path.comp_cons, Path.toWalk_cons, ih, Graph.Walk.append_assoc]

@[simp] theorem Path.toWalk_toPath {u v : Γ.V} (e : Quiver.Hom u v) :
    Path.toWalk Γ e.toPath = (Γ.toGraph_isLink_edge e).toWalk := by
  simp [Quiver.Hom.toPath]

/-- Forgetting directions preserves the length of a path. -/
@[simp] theorem Path.length_toWalk {u v : Γ.V} (p : Γ.Path u v) :
    (p.toWalk Γ).length = p.length := by
  induction p with
  | nil => simp
  | cons p e ih => simp [ih]

/-- The final dart of a path contributes its undirected edge to the walk. -/
theorem Path.edges_toWalk_cons {u v w : Γ.V} (p : Γ.Path u v)
    (e : Quiver.Hom v w) :
    (Path.toWalk Γ (p.cons e)).edges = (Path.toWalk Γ p).edges ++ [Γ.edge e.1] := by
  simp [Graph.IsLink.edges_toWalk]

/-- A link in the underlying multigraph can be oriented as a Serre arrow. -/
theorem exists_hom_of_toGraph_isLink {u v : Γ.V} {q : Γ.Edge}
    (h : Γ.toGraph.IsLink q u v) :
    ∃ e : Quiver.Hom u v, Γ.edge e.1 = q := by
  obtain ⟨d, rfl⟩ := Γ.edge_surjective q
  rw [toGraph_isLink, edgeEnds_edge, Sym2.eq_iff] at h
  rcases h with ⟨hu, hv⟩ | ⟨hu, hv⟩
  · subst u
    subst v
    exact ⟨Γ.dart d, by simp⟩
  · subst u
    subst v
    exact ⟨Quiver.reverse (Γ.dart d), by simp⟩

/-- Every walk between vertices lifts to a directed Serre path. -/
theorem exists_path_toWalk {u v : Γ.V} (p : Γ.toGraph.Walk u v) :
    ∃ q : Γ.Path u v, q.toWalk = p := by
  induction p with
  | nil => exact ⟨.nil, rfl⟩
  | @cons u v w e h p ih =>
    obtain ⟨f, hf⟩ := Γ.exists_hom_of_toGraph_isLink h
    rcases ih with ⟨q, rfl⟩
    refine ⟨f.toPath.comp q, ?_⟩
    simp [Graph.IsLink.toWalk_eq_cons, hf]

/-- Serre path reachability agrees with reachability in the underlying multigraph. -/
theorem reachable_toGraph_iff (u v : Γ.V) :
    Γ.toGraph.Reachable u v ↔ Nonempty (Γ.Path u v) := by
  rw [Graph.reachable_def]
  simp only [vertexSet_toGraph, Set.mem_univ, true_and]
  constructor
  · rintro ⟨p⟩
    exact ⟨(Γ.exists_path_toWalk p).choose⟩
  · rintro ⟨p⟩
    exact ⟨p.toWalk⟩

/-- Connectedness agrees with that of the underlying multigraph, including the empty graph. -/
theorem connected_toGraph_iff : Γ.toGraph.Connected ↔ Γ.Connected := by
  rw [Graph.connected_iff_forall_reachable]
  simp only [vertexSet_toGraph, Set.mem_univ, true_implies]
  rw [Γ.connected_iff, Γ.preconnected_iff]
  constructor
  · intro h
    rcases h with ⟨⟨u, _⟩, hreach⟩
    exact ⟨⟨u⟩, fun x y => (Γ.reachable_toGraph_iff x y).mp
      (@hreach x y)⟩
  · intro h
    rcases h with ⟨⟨u⟩, hpath⟩
    exact ⟨⟨u, trivial⟩, fun x y => (Γ.reachable_toGraph_iff x y).mpr (hpath x y)⟩

/-- Two vertices lie in the same underlying multigraph component exactly when a Serre path
joins them. This also covers loops, parallel edges, and isolated vertices. -/
theorem toGraph_connectedComponentOf_eq_iff (u v : Γ.V) :
    Γ.toGraph.connectedComponentOf u (by simp) =
      Γ.toGraph.connectedComponentOf v (by simp) ↔ Nonempty (Γ.Path u v) := by
  rw [Graph.connectedComponentOf_eq_connectedComponentOf_iff]
  exact Γ.reachable_toGraph_iff u v

/-- Every connected component of the underlying multigraph is the component of a vertex. -/
theorem toGraph_connectedComponentOf_surjective :
    Function.Surjective fun v : Γ.V => Γ.toGraph.connectedComponentOf v (by simp) := by
  intro C
  obtain ⟨v, hv⟩ := C.property.nonempty
  exact ⟨v, (Graph.ConnectedComponent.eq_connectedComponentOf hv).symm⟩

/-- If all darts of `Γ` are loops, the underlying multigraph has `Nat.card Γ.V` connected
components; both sides are `0` when `Γ.V` is infinite. -/
theorem componentCount_toGraph_of_forall_src_eq_tgt (h : ∀ e, Γ.src e = Γ.tgt e) :
    Γ.toGraph.componentCount = Nat.card Γ.V := by
  rw [Graph.componentCount_def]
  refine (Nat.card_congr (Equiv.ofBijective _
    ⟨fun a b hab => ?_, Γ.toGraph_connectedComponentOf_surjective⟩)).symm
  exact (Γ.nonempty_path_iff_of_forall_src_eq_tgt h).mp
    ((Γ.toGraph_connectedComponentOf_eq_iff a b).mp hab)

/-- The multigraph underlying a Serre graph without darts has all vertices and no edges. -/
theorem toGraph_eq_noEdge_of_isEmpty_dart [IsEmpty Γ.E] :
    Γ.toGraph = Graph.noEdge Set.univ Γ.Edge :=
  Graph.ext (by simp) fun q _ _ => isEmptyElim (Γ.edge_surjective q).choose

/-- The multigraph underlying a Serre graph without vertices has no component. -/
theorem componentCount_toGraph_eq_zero_of_isEmpty [IsEmpty Γ.V] :
    Γ.toGraph.componentCount = 0 :=
  Graph.componentCount_def.trans Nat.card_of_isEmpty

/-- The multigraph underlying a Serre graph without vertices is not connected. -/
theorem not_connected_toGraph_of_isEmpty [IsEmpty Γ.V] : ¬Γ.toGraph.Connected :=
  fun h => Γ.not_connected_of_isEmpty ((connected_toGraph_iff Γ).mp h)

section NoEdge

universe u v

variable {V : Type u}

/-- The multigraph underlying a graph without edges has all vertices and no edges. -/
theorem toGraph_noEdge : (noEdge.{u, v} V).toGraph = Graph.noEdge Set.univ _ :=
  toGraph_eq_noEdge_of_isEmpty_dart _

/-- The multigraph underlying `noEdge V` has `Nat.card V` connected components; both sides are
`0` when `V` is infinite. -/
@[simp] theorem componentCount_toGraph_noEdge :
    (noEdge.{u, v} V).toGraph.componentCount = Nat.card V :=
  componentCount_toGraph_of_forall_src_eq_tgt _ isEmptyElim

/-- The multigraph underlying a graph of two or more isolated vertices is not connected. -/
theorem not_connected_toGraph_noEdge [Nontrivial V] : ¬(noEdge.{u, v} V).toGraph.Connected :=
  fun h => noEdge_not_connected ((connected_toGraph_iff _).mp h)

/-- The multigraph underlying the graph of two isolated vertices has two components. -/
example : (noEdge.{0, v} Bool).toGraph.componentCount = 2 := by
  simp

end NoEdge

end SerreGraph
end TauCeti
