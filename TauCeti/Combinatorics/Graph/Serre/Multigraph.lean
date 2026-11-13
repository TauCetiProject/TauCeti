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

A set `O` of darts is itself a multigraph on all the vertices, `SerreGraph.endpointGraph`: its
edges are the darts of `O`, each joining its source to its target, so loops and parallel darts
remain distinct edges. When `O` contains at least one dart of every reversal pair, in particular
when it is an orientation, this multigraph has the adjacency of the multigraph of reversal
pairs: the identity of the vertices is an isomorphism of the underlying simple graphs
(`SerreGraph.toSimpleGraphEndpointGraphIsoToGraph`). Hence two vertices are joined in it exactly
when a path of the Serre graph joins them, the two multigraphs have the same number of
components, and it is connected exactly when the Serre graph is.

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

/-- Two vertices are adjacent in the multigraph of reversal pairs exactly when some dart joins
them. -/
@[simp] theorem toGraph_adj (x y : Γ.V) :
    Γ.toGraph.Adj x y ↔ ∃ e, Γ.src e = x ∧ Γ.tgt e = y := by
  constructor
  · rintro ⟨q, hq⟩
    obtain ⟨e, -⟩ := Γ.exists_hom_of_toGraph_isLink hq
    exact ⟨e.1, e.2⟩
  · rintro ⟨e, rfl, rfl⟩
    exact ⟨Γ.edge e, by simp⟩

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

section EndpointGraph

variable (O : Set Γ.E)

/-- The multigraph on all vertices whose edges are the darts in `O`, each joining its source
and its target. Loops and parallel darts remain distinct edges. -/
def endpointGraph : Graph Γ.V Γ.E where
  vertexSet := Set.univ
  edgeSet := O
  IsLink e x y := e ∈ O ∧ s(Γ.src e, Γ.tgt e) = s(x, y)
  isLink_symm _ _ := ⟨fun _ _ h => ⟨h.1, h.2.trans Sym2.eq_swap⟩⟩
  eq_or_eq_of_isLink_of_isLink _ _ _ _ _ h k := by
    rcases Sym2.eq_iff.mp (h.2.symm.trans k.2) with h | h
    · exact Or.inl h.1
    · exact Or.inr h.1
  edge_mem_iff_exists_isLink e := ⟨fun he => ⟨_, _, he, rfl⟩, fun ⟨_, _, he, _⟩ => he⟩
  left_mem_of_isLink _ _ _ _ := Set.mem_univ _

@[simp, grind =] theorem vertexSet_endpointGraph :
    (Γ.endpointGraph O).vertexSet = Set.univ := (rfl)

@[simp, grind =] theorem edgeSet_endpointGraph : (Γ.endpointGraph O).edgeSet = O := (rfl)

@[simp, grind =] theorem endpointGraph_isLink (e : Γ.E) (x y : Γ.V) :
    (Γ.endpointGraph O).IsLink e x y ↔ e ∈ O ∧ s(Γ.src e, Γ.tgt e) = s(x, y) := Iff.rfl

variable {Γ O} in
/-- A chosen dart is an edge of the multigraph joining its source and its target. -/
theorem endpointGraph_isLink_src_tgt {e : Γ.E} (he : e ∈ O) :
    (Γ.endpointGraph O).IsLink e (Γ.src e) (Γ.tgt e) :=
  ⟨he, rfl⟩

/-- A dart is a loop at a vertex `x` of the multigraph exactly when it is chosen and both of its
ends equal `x`. -/
@[simp, grind =] theorem endpointGraph_isLoopAt_iff (e : Γ.E) (x : Γ.V) :
    (Γ.endpointGraph O).IsLoopAt e x ↔ e ∈ O ∧ Γ.src e = x ∧ Γ.tgt e = x := by
  simp [← Graph.isLink_self_iff]

/-- Two vertices are adjacent in the multigraph exactly when a chosen dart joins them, in
either direction. -/
@[simp, grind =] theorem endpointGraph_adj (x y : Γ.V) :
    (Γ.endpointGraph O).Adj x y ↔
      (∃ e ∈ O, Γ.src e = x ∧ Γ.tgt e = y) ∨ ∃ e ∈ O, Γ.src e = y ∧ Γ.tgt e = x := by
  simp only [Graph.Adj, endpointGraph_isLink, Sym2.eq_iff]
  grind

/-- A dart is incident to a vertex of the multigraph exactly when it is chosen and the vertex
is one of its ends. -/
@[simp, grind =] theorem endpointGraph_inc (e : Γ.E) (x : Γ.V) :
    (Γ.endpointGraph O).Inc e x ↔ e ∈ O ∧ (Γ.src e = x ∨ Γ.tgt e = x) := by
  simp only [Graph.Inc, endpointGraph_isLink, Sym2.eq_iff]
  grind

variable {Γ} in
/-- Enlarging the dart set enlarges the multigraph. -/
@[gcongr] theorem endpointGraph_mono {O O' : Set Γ.E} (h : O ⊆ O') :
    Γ.endpointGraph O ≤ Γ.endpointGraph O' :=
  ⟨subset_rfl, fun _ _ _ hl => ⟨h hl.1, hl.2⟩⟩

variable {Γ} in
/-- The multigraph of the darts in `O` is a subgraph of that of the darts in `O'` exactly when
`O ⊆ O'`. -/
@[simp, grind =] theorem endpointGraph_le_endpointGraph_iff {O O' : Set Γ.E} :
    Γ.endpointGraph O ≤ Γ.endpointGraph O' ↔ O ⊆ O' :=
  ⟨fun h => by simpa using h.edgeSet_mono, endpointGraph_mono⟩

variable {Γ} in
/-- Distinct dart sets give distinct multigraphs. -/
theorem endpointGraph_injective : Function.Injective Γ.endpointGraph :=
  fun _ _ h => by simpa using congrArg Graph.edgeSet h

variable {Γ} in
/-- Two dart sets give the same multigraph exactly when they are equal. -/
@[simp, grind =] theorem endpointGraph_inj {O O' : Set Γ.E} :
    Γ.endpointGraph O = Γ.endpointGraph O' ↔ O = O' :=
  endpointGraph_injective.eq_iff

/-- Without darts, the multigraph has no edges. -/
theorem endpointGraph_empty : Γ.endpointGraph ∅ = Graph.noEdge Set.univ Γ.E :=
  Graph.ext rfl fun _ _ _ => by simp

/-- Restricting the multigraph of the darts in `O` to a set `F` of edges gives the multigraph of
the darts in `O ∩ F`. -/
@[simp] theorem endpointGraph_restrict (F : Set Γ.E) :
    (Γ.endpointGraph O).restrict F = Γ.endpointGraph (O ∩ F) :=
  Graph.ext rfl fun _ _ _ => by simp [and_assoc, and_left_comm]

/-- Deleting a set `F` of edges from the multigraph of the darts in `O` gives the multigraph of
the darts in `O \ F`. -/
@[simp] theorem endpointGraph_deleteEdges (F : Set Γ.E) :
    (Γ.endpointGraph O).deleteEdges F = Γ.endpointGraph (O \ F) :=
  Graph.ext rfl fun _ _ _ => by simp [and_right_comm]

variable {Γ O}

/-- For a dart set containing at least one dart of every reversal pair, two vertices are
adjacent in the multigraph of its darts exactly when they are adjacent in the multigraph of
reversal pairs. -/
theorem endpointGraph_adj_iff_toGraph_adj (hO : ∀ e, e ∈ O ∨ Γ.rev e ∈ O) (x y : Γ.V) :
    (Γ.endpointGraph O).Adj x y ↔ Γ.toGraph.Adj x y := by
  rw [endpointGraph_adj, toGraph_adj]
  refine ⟨?_, fun ⟨e, h₁, h₂⟩ => ?_⟩
  · rintro (⟨e, -, h⟩ | ⟨e, -, h₁, h₂⟩)
    exacts [⟨e, h⟩, ⟨Γ.rev e, by simpa using h₂, by simpa using h₁⟩]
  · rcases hO e with he | he
    exacts [.inl ⟨e, he, h₁, h₂⟩, .inr ⟨Γ.rev e, he, by simpa using h₂, by simpa using h₁⟩]

/-- For an orientation, two vertices are adjacent in the multigraph of its darts exactly when
they are adjacent in the multigraph of reversal pairs. -/
theorem IsOrientation.endpointGraph_adj_iff_toGraph_adj (hO : Γ.IsOrientation O) (x y : Γ.V) :
    (Γ.endpointGraph O).Adj x y ↔ Γ.toGraph.Adj x y :=
  SerreGraph.endpointGraph_adj_iff_toGraph_adj hO.mem_or_rev_mem x y

/-- For a dart set containing at least one dart of every reversal pair, the identity of the
vertices is an isomorphism between the simple graphs underlying the multigraph of its darts and
the multigraph of reversal pairs. -/
def toSimpleGraphEndpointGraphIsoToGraph (hO : ∀ e, e ∈ O ∨ Γ.rev e ∈ O) :
    (Γ.endpointGraph O).toSimpleGraph ≃g Γ.toGraph.toSimpleGraph where
  toEquiv := Equiv.subtypeEquivRight fun x => by simp
  map_rel_iff' := by simp [Subtype.ext_iff, endpointGraph_adj_iff_toGraph_adj hO]

@[simp] theorem coe_toSimpleGraphEndpointGraphIsoToGraph_apply (hO : ∀ e, e ∈ O ∨ Γ.rev e ∈ O)
    (x : (Γ.endpointGraph O).vertexSet) :
    (toSimpleGraphEndpointGraphIsoToGraph hO x : Γ.V) = x := (rfl)

@[simp] theorem coe_toSimpleGraphEndpointGraphIsoToGraph_symm_apply
    (hO : ∀ e, e ∈ O ∨ Γ.rev e ∈ O) (x : Γ.toGraph.vertexSet) :
    ((toSimpleGraphEndpointGraphIsoToGraph hO).symm x : Γ.V) = x := (rfl)

/-- For a dart set containing at least one dart of every reversal pair, two vertices are joined
by a walk in the multigraph of its darts exactly when a path of the Serre graph joins them. -/
theorem reachable_endpointGraph_iff (hO : ∀ e, e ∈ O ∨ Γ.rev e ∈ O) (x y : Γ.V) :
    (Γ.endpointGraph O).Reachable x y ↔ Nonempty (Γ.Path x y) := by
  rw [← Graph.toSimpleGraph_reachable_iff (u := ⟨x, by simp⟩) (v := ⟨y, by simp⟩),
    ← (toSimpleGraphEndpointGraphIsoToGraph hO).reachable_iff, Graph.toSimpleGraph_reachable_iff,
    ← reachable_toGraph_iff]
  simp

/-- For an orientation, two vertices are joined by a walk in the multigraph of its darts exactly
when a path of the Serre graph joins them. -/
theorem IsOrientation.reachable_endpointGraph_iff (hO : Γ.IsOrientation O) (x y : Γ.V) :
    (Γ.endpointGraph O).Reachable x y ↔ Nonempty (Γ.Path x y) :=
  SerreGraph.reachable_endpointGraph_iff hO.mem_or_rev_mem x y

/-- For a dart set containing at least one dart of every reversal pair, the multigraph of its
darts and the multigraph of reversal pairs have the same number of components. -/
theorem componentCount_endpointGraph_eq_componentCount_toGraph
    (hO : ∀ e, e ∈ O ∨ Γ.rev e ∈ O) :
    (Γ.endpointGraph O).componentCount = Γ.toGraph.componentCount := by
  simp only [Graph.componentCount_eq_natCard_toSimpleGraph]
  exact Nat.card_congr (toSimpleGraphEndpointGraphIsoToGraph hO).connectedComponentEquiv

/-- For an orientation, the multigraph of its darts and the multigraph of reversal pairs have
the same number of components. -/
theorem IsOrientation.componentCount_endpointGraph_eq_componentCount_toGraph
    (hO : Γ.IsOrientation O) :
    (Γ.endpointGraph O).componentCount = Γ.toGraph.componentCount :=
  SerreGraph.componentCount_endpointGraph_eq_componentCount_toGraph hO.mem_or_rev_mem

/-- For a dart set containing at least one dart of every reversal pair, the multigraph of its
darts is connected exactly when the Serre graph is. -/
theorem connected_endpointGraph_iff (hO : ∀ e, e ∈ O ∨ Γ.rev e ∈ O) :
    (Γ.endpointGraph O).Connected ↔ Γ.Connected := by
  rw [Graph.connected_iff_toSimpleGraph_connected,
    (toSimpleGraphEndpointGraphIsoToGraph hO).connected_iff,
    ← Graph.connected_iff_toSimpleGraph_connected, connected_toGraph_iff]

/-- The multigraph of the darts of an orientation is connected exactly when the Serre graph
is. -/
theorem IsOrientation.connected_endpointGraph_iff (hO : Γ.IsOrientation O) :
    (Γ.endpointGraph O).Connected ↔ Γ.Connected :=
  SerreGraph.connected_endpointGraph_iff hO.mem_or_rev_mem

end EndpointGraph

end SerreGraph
end TauCeti
