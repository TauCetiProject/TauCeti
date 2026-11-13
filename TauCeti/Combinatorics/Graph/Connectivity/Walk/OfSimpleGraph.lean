/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Delete
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import TauCeti.Combinatorics.Graph.Connectivity.Walk.Maps

/-!
# Walks in graphs constructed from simple graphs

This file identifies Mathlib's vertex-based walks in a simple graph `H` with the edge-labelled
walks in `Graph.ofSimpleGraph H`.  In the latter graph, the edge joining `x` and `y` is the
unordered pair `s(x, y)`, so no edge choice is lost in either direction.

The two conversions preserve length, vertex support, edge lists, concatenation, reversal,
trails, paths, and cycles.  Their equivalence also identifies the two reachability predicates,
providing the basic bridge through which simple-graph connectivity results can be used for
multigraph walks.

In the other direction, reachability by edge-labelled walks in a multigraph `G` agrees with
reachability in its underlying simple graph `G.toSimpleGraph`. A walk in the underlying simple
graph can be lifted to the multigraph by choosing one actual edge for each adjacency; this lift
preserves the vertex sequence and hence the path predicate.
-/

public section

open scoped Sym2

universe u

namespace SimpleGraph

variable {α : Type u} {H : SimpleGraph α} {x y z : α}

namespace Walk

/-- Regard a simple-graph walk as an edge-labelled walk in `Graph.ofSimpleGraph H`. -/
def toGraph : {x y : α} → H.Walk x y → (Graph.ofSimpleGraph H).Walk x y
  | _, _, .nil => .nil
  | x, _, .cons (v := y) h p =>
      .cons s(x, y) (by simp [Graph.ofSimpleGraph_isLink, h]) p.toGraph

@[simp]
theorem toGraph_nil : (nil : H.Walk x x).toGraph = .nil := (rfl)

@[simp]
theorem toGraph_cons (h : H.Adj x y) (p : H.Walk y z) :
    (cons h p).toGraph = .cons s(x, y) (by simp [Graph.ofSimpleGraph_isLink, h]) p.toGraph :=
  (rfl)

@[simp]
theorem length_toGraph (p : H.Walk x y) : p.toGraph.length = p.length := by
  induction p <;> simp_all

@[simp]
theorem support_toGraph (p : H.Walk x y) : p.toGraph.support = p.support := by
  induction p <;> simp_all

@[simp]
theorem edges_toGraph (p : H.Walk x y) : p.toGraph.edges = p.edges := by
  induction p <;> simp_all

@[simp]
theorem toGraph_append (p : H.Walk x y) (q : H.Walk y z) :
    (p.append q).toGraph = p.toGraph.append q.toGraph := by
  induction p <;> simp_all

@[simp]
theorem toGraph_reverse (p : H.Walk x y) : p.reverse.toGraph = p.toGraph.reverse := by
  induction p with
  | nil => simp
  | cons h p ih => simp [ih, Graph.IsLink.toWalk_eq_cons, Sym2.eq_swap]

end Walk

end SimpleGraph

namespace Graph.Walk

variable {α : Type u} {H : SimpleGraph α} {x y z : α}

/-- Forget the redundant edge labels of a walk in `Graph.ofSimpleGraph H`. -/
def toSimpleGraph : {x y : α} → (Graph.ofSimpleGraph H).Walk x y → H.Walk x y
  | _, _, .nil => .nil
  | _, _, .cons e h p => .cons (by
      rw [Graph.ofSimpleGraph_isLink] at h
      exact H.mem_edgeSet.mp (h.1 ▸ h.2)) p.toSimpleGraph

@[simp]
theorem toSimpleGraph_nil :
    (nil : (Graph.ofSimpleGraph H).Walk x x).toSimpleGraph = .nil := (rfl)

@[simp]
theorem toSimpleGraph_cons {e : Sym2 α} (h : (Graph.ofSimpleGraph H).IsLink e x y)
    (p : (Graph.ofSimpleGraph H).Walk y z) :
    (cons e h p).toSimpleGraph =
      .cons ((Graph.ofSimpleGraph_adj_iff x y).mp ⟨e, h⟩) p.toSimpleGraph :=
  (rfl)

@[simp]
theorem length_toSimpleGraph (p : (Graph.ofSimpleGraph H).Walk x y) :
    p.toSimpleGraph.length = p.length := by
  induction p <;> simp_all

@[simp]
theorem support_toSimpleGraph (p : (Graph.ofSimpleGraph H).Walk x y) :
    p.toSimpleGraph.support = p.support := by
  induction p <;> simp_all

@[simp]
theorem edges_toSimpleGraph (p : (Graph.ofSimpleGraph H).Walk x y) :
    p.toSimpleGraph.edges = p.edges := by
  induction p with
  | nil => simp
  | cons e h p ih =>
      rw [Graph.ofSimpleGraph_isLink] at h
      simp only [toSimpleGraph_cons, SimpleGraph.Walk.edges_cons, Graph.Walk.edges_cons, ih]
      exact congrArg (· :: p.edges) h.1.symm

@[simp]
theorem toSimpleGraph_append (p : (Graph.ofSimpleGraph H).Walk x y)
    (q : (Graph.ofSimpleGraph H).Walk y z) :
    (p.append q).toSimpleGraph = p.toSimpleGraph.append q.toSimpleGraph := by
  induction p <;> simp_all

end Graph.Walk

namespace SimpleGraph.Walk

variable {α : Type u} {H : SimpleGraph α} {x y : α}

@[simp]
theorem toSimpleGraph_toGraph (p : H.Walk x y) : p.toGraph.toSimpleGraph = p := by
  induction p <;> simp_all

end SimpleGraph.Walk

namespace Graph.Walk

variable {α : Type u} {H : SimpleGraph α} {x y : α}

@[simp]
theorem toGraph_toSimpleGraph (p : (Graph.ofSimpleGraph H).Walk x y) :
    p.toSimpleGraph.toGraph = p := by
  induction p with
  | nil => simp
  | cons e h p ih =>
      rw [Graph.ofSimpleGraph_isLink] at h
      rcases h with ⟨rfl, _⟩
      simp [ih]

@[simp]
theorem toSimpleGraph_reverse (p : (Graph.ofSimpleGraph H).Walk x y) :
    p.reverse.toSimpleGraph = p.toSimpleGraph.reverse := by
  conv_lhs => rw [← toGraph_toSimpleGraph p, ← SimpleGraph.Walk.toGraph_reverse,
    SimpleGraph.Walk.toSimpleGraph_toGraph]

@[simp]
theorem nil_toSimpleGraph_iff (p : (Graph.ofSimpleGraph H).Walk x y) :
    p.toSimpleGraph.Nil ↔ p.Nil := by
  rw [← SimpleGraph.Walk.length_eq_zero_iff, ← Graph.Walk.length_eq_zero_iff,
    length_toSimpleGraph]

end Graph.Walk

namespace SimpleGraph

variable {α : Type u} {H : SimpleGraph α} {x y : α}

namespace Walk

@[simp]
theorem nil_toGraph_iff (p : H.Walk x y) : p.toGraph.Nil ↔ p.Nil := by
  rw [← Graph.Walk.length_eq_zero_iff, ← SimpleGraph.Walk.length_eq_zero_iff,
    length_toGraph]

end Walk

/-- Walks in a simple graph are equivalent to edge-labelled walks in its associated `Graph`. -/
def walkEquivOfSimpleGraph (H : SimpleGraph α) (x y : α) :
    H.Walk x y ≃ (Graph.ofSimpleGraph H).Walk x y where
  toFun := Walk.toGraph
  invFun := Graph.Walk.toSimpleGraph
  left_inv := Walk.toSimpleGraph_toGraph
  right_inv := Graph.Walk.toGraph_toSimpleGraph

@[simp]
theorem walkEquivOfSimpleGraph_apply (H : SimpleGraph α) (p : H.Walk x y) :
    H.walkEquivOfSimpleGraph x y p = p.toGraph := (rfl)

@[simp]
theorem walkEquivOfSimpleGraph_symm_apply (H : SimpleGraph α)
    (p : (Graph.ofSimpleGraph H).Walk x y) :
    (H.walkEquivOfSimpleGraph x y).symm p = p.toSimpleGraph := (rfl)

namespace Walk

@[simp]
theorem isTrail_toGraph_iff (p : H.Walk x y) : p.toGraph.IsTrail ↔ p.IsTrail := by
  rw [Graph.Walk.isTrail_def, SimpleGraph.Walk.isTrail_def, edges_toGraph]

@[simp]
theorem isPath_toGraph_iff (p : H.Walk x y) : p.toGraph.IsPath ↔ p.IsPath := by
  rw [Graph.Walk.isPath_def, SimpleGraph.Walk.isPath_def, support_toGraph]

/-- The walk equivalence identifies simple-graph cycles with edge-labelled multigraph cycles. -/
@[simp]
theorem isCycle_toGraph_iff (p : H.Walk x x) : p.toGraph.IsCycle ↔ p.IsCycle := by
  have hne : ¬ p.toGraph.Nil ↔ ¬ p.Nil := not_congr (nil_toGraph_iff p)
  simp only [Graph.Walk.isCycle_def, SimpleGraph.Walk.isCycle_def,
    SimpleGraph.Walk.isTrail_def, support_toGraph, edges_toGraph, ne_eq,
    Graph.Walk.eq_nil_iff_nil, SimpleGraph.Walk.eq_nil_iff_nil]
  rw [hne]
  tauto

end Walk

/-- Multigraph reachability in `Graph.ofSimpleGraph H` is simple-graph reachability in `H`. -/
@[simp]
theorem reachable_ofSimpleGraph_iff (H : SimpleGraph α) (x y : α) :
    (Graph.ofSimpleGraph H).Reachable x y ↔ H.Reachable x y := by
  rw [Graph.reachable_def, SimpleGraph.Reachable]
  constructor
  · rintro ⟨_, ⟨p⟩⟩
    exact ⟨p.toSimpleGraph⟩
  · rintro ⟨p⟩
    exact ⟨by simp, ⟨p.toGraph⟩⟩

end SimpleGraph

namespace Graph.Walk

variable {α : Type u} {H : SimpleGraph α} {x y : α}

@[simp]
theorem isTrail_toSimpleGraph_iff (p : (Graph.ofSimpleGraph H).Walk x y) :
    p.toSimpleGraph.IsTrail ↔ p.IsTrail := by
  rw [← SimpleGraph.Walk.isTrail_toGraph_iff, toGraph_toSimpleGraph]

@[simp]
theorem isPath_toSimpleGraph_iff (p : (Graph.ofSimpleGraph H).Walk x y) :
    p.toSimpleGraph.IsPath ↔ p.IsPath := by
  rw [← SimpleGraph.Walk.isPath_toGraph_iff, toGraph_toSimpleGraph]

@[simp]
theorem isCycle_toSimpleGraph_iff (p : (Graph.ofSimpleGraph H).Walk x x) :
    p.toSimpleGraph.IsCycle ↔ p.IsCycle := by
  rw [← SimpleGraph.Walk.isCycle_toGraph_iff, toGraph_toSimpleGraph]

end Graph.Walk

namespace SimpleGraph.Walk

variable {α : Type u} {β : Type*} {G : Graph α β} {x y z : G.vertexSet}

/-- Lift a walk in the underlying simple graph of a multigraph by choosing one actual edge for
each adjacency. The lift preserves the visited vertices but makes no canonical choice among
parallel edges. -/
noncomputable def liftToGraph {G : Graph α β} :
    {x y : G.vertexSet} → G.toSimpleGraph.Walk x y → G.Walk x y
  | _, _, .nil => .nil
  | _, _, .cons h p =>
      .cons (Classical.choose h.2) (Classical.choose_spec h.2) (liftToGraph p)

@[simp]
theorem liftToGraph_nil {G : Graph α β} (x : G.vertexSet) :
    (SimpleGraph.Walk.nil : G.toSimpleGraph.Walk x x).liftToGraph = .nil :=
  (rfl)

@[simp]
theorem liftToGraph_cons (h : G.toSimpleGraph.Adj x y) (p : G.toSimpleGraph.Walk y z) :
    (SimpleGraph.Walk.cons h p).liftToGraph =
      .cons (Classical.choose h.2) (Classical.choose_spec h.2) p.liftToGraph :=
  (rfl)

@[simp]
theorem liftToGraph_append (p : G.toSimpleGraph.Walk x y) (q : G.toSimpleGraph.Walk y z) :
    (p.append q).liftToGraph = p.liftToGraph.append q.liftToGraph := by
  induction p with
  | nil => rw [nil_append, liftToGraph_nil, Graph.Walk.nil_append]
  | cons h p ih =>
      rw [cons_append, liftToGraph_cons, liftToGraph_cons, ih, Graph.Walk.cons_append]

/-- Lifting a simplified walk preserves its vertex sequence, after forgetting the actual-vertex
membership proofs. -/
@[simp]
theorem support_liftToGraph (p : G.toSimpleGraph.Walk x y) :
    p.liftToGraph.support = p.support.map Subtype.val := by
  induction p with
  | nil => simp only [liftToGraph_nil, Graph.Walk.support_nil, support_nil, List.map_cons,
      List.map_nil]
  | cons h p ih =>
      rw [liftToGraph_cons, Graph.Walk.support_cons, ih, support_cons, List.map_cons]

/-- Lifting a simplified walk preserves its length. -/
@[simp]
theorem length_liftToGraph (p : G.toSimpleGraph.Walk x y) :
    p.liftToGraph.length = p.length := by
  induction p <;> simp_all

/-- A lifted walk is a path exactly when the simplified walk is a path. -/
@[simp]
theorem isPath_liftToGraph_iff (p : G.toSimpleGraph.Walk x y) :
    p.liftToGraph.IsPath ↔ p.IsPath := by
  rw [Graph.Walk.isPath_def, SimpleGraph.Walk.isPath_def, support_liftToGraph,
    List.nodup_map_iff Subtype.val_injective]

/-- Lifting is injective: a walk in a simple graph is determined by its vertex sequence, which
the lift preserves. Distinct simplified walks therefore lift to distinct multigraph walks, even
though the lift chooses arbitrarily among parallel edges. -/
theorem liftToGraph_injective :
    Function.Injective (liftToGraph : G.toSimpleGraph.Walk x y → G.Walk x y) := fun p q h ↦
  ext_support <| List.map_injective_iff.2 Subtype.val_injective <| by
    simpa only [support_liftToGraph] using congrArg Graph.Walk.support h

/-- Two simplified walks have the same lift exactly when they are equal. -/
@[simp]
theorem liftToGraph_inj {p q : G.toSimpleGraph.Walk x y} :
    p.liftToGraph = q.liftToGraph ↔ p = q :=
  liftToGraph_injective.eq_iff

end SimpleGraph.Walk

namespace Graph

variable {α β : Type*} {G H : Graph α β}

/-- A subgraph inclusion `H ≤ G` induces a homomorphism of underlying simple graphs, sending each
actual vertex of `H` to itself. -/
def toSimpleGraphHomOfLE (hHG : H ≤ G) : H.toSimpleGraph →g G.toSimpleGraph where
  toFun z := ⟨z, hHG.vertexSet_mono z.2⟩
  map_rel' hzw :=
    ⟨fun h ↦ hzw.1 (Subtype.ext (Subtype.mk.inj h)), hzw.2.mono hHG⟩

@[simp]
theorem coe_toSimpleGraphHomOfLE_apply (hHG : H ≤ G) (z : V(H)) :
    (toSimpleGraphHomOfLE hHG z : α) = z := (rfl)

/-- Reachability by an edge-labelled walk gives reachability in the underlying simple graph. -/
theorem Reachable.toSimpleGraph_reachable {x y : α} (h : G.Reachable x y) :
    G.toSimpleGraph.Reachable ⟨x, h.left_mem⟩ ⟨y, h.right_mem⟩ := by
  obtain ⟨-, ⟨p⟩⟩ := reachable_def.mp h
  suffices ∀ hx hy, G.toSimpleGraph.Reachable ⟨x, hx⟩ ⟨y, hy⟩ from this _ _
  clear h
  induction p with
  | nil => exact fun _ _ ↦ .rfl
  | @cons x y z e hxy p ih =>
      intro _ hz
      refine SimpleGraph.Reachable.trans ?_ (ih hxy.right_mem hz)
      by_cases hne : x = y
      · subst hne
        exact SimpleGraph.Reachable.rfl
      · exact SimpleGraph.Adj.reachable ⟨fun h ↦ hne (congrArg Subtype.val h), e, hxy⟩

/-- Reachability in the underlying simple graph is reachability by an edge-labelled walk. -/
@[simp]
theorem toSimpleGraph_reachable_iff {u v : V(G)} :
    G.toSimpleGraph.Reachable u v ↔ G.Reachable u v := by
  refine ⟨?_, fun h ↦ h.toSimpleGraph_reachable⟩
  rintro ⟨p⟩
  exact p.liftToGraph.reachable u.property

/-- Two actual vertices are reachable after deleting `S` exactly when some walk between them in
the underlying simple graph avoids `S`. -/
theorem toSimpleGraph_reachable_deleteVerts_iff_exists_walk {S : Set α} {x y : V(G)} :
    (G.deleteVerts S).Reachable x y ↔ ∃ p : G.toSimpleGraph.Walk x y, ∀ z ∈ p.support, ↑z ∉ S := by
  constructor
  · intro h
    obtain ⟨p⟩ := (toSimpleGraph_reachable_iff (G := G.deleteVerts S) (u := ⟨x, h.left_mem⟩)
      (v := ⟨y, h.right_mem⟩)).mpr h
    refine ⟨(p.map (toSimpleGraphHomOfLE deleteVerts_le)).copy
      (Subtype.ext (coe_toSimpleGraphHomOfLE_apply _ _))
      (Subtype.ext (coe_toSimpleGraphHomOfLE_apply _ _)), fun z hz ↦ ?_⟩
    rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map] at hz
    obtain ⟨z, -, rfl⟩ := List.mem_map.mp hz
    have hz : (z : α) ∈ V(G) ∧ (z : α) ∉ S := by
      simpa only [vertexSet_deleteVerts, Set.mem_sdiff] using z.property
    rw [coe_toSimpleGraphHomOfLE_apply]
    exact hz.2
  · rintro ⟨p, hp⟩
    refine reachable_deleteVerts_iff_exists_walk.mpr ⟨p.liftToGraph, x.property, fun z hz ↦ ?_⟩
    rw [SimpleGraph.Walk.support_liftToGraph] at hz
    obtain ⟨z, hz', rfl⟩ := List.mem_map.mp hz
    exact hp z hz'

/-- Deletion in a multigraph agrees with deletion in its simplification, retaining the original
endpoints. -/
theorem toSimpleGraph_reachable_induce_compl_iff {X : Set α} {s t : V(G)}
    (hs : (s : α) ∉ X) (ht : (t : α) ∉ X) :
    (G.toSimpleGraph.induce {v : V(G) | (v : α) ∉ X}).Reachable ⟨s, hs⟩ ⟨t, ht⟩ ↔
      (G.deleteVerts X).Reachable s t := by
  rw [← SimpleGraph.Iso.reachable_iff (φ := (G.toSimpleGraphDeleteVertsIso X).symm),
    toSimpleGraph_reachable_iff]
  simp

end Graph
