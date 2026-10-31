/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Connectivity.Walk.OfSimpleGraph

/-!
# Paths and simplification of multigraphs

A path in a multigraph projects to its underlying simple graph without changing its vertex
sequence. Conversely, a walk in the underlying simple graph lifts by choosing an actual edge
for each step. The lift preserves the vertex sequence and is a path exactly when the original
walk is a path. No finiteness or bound on edge multiplicities is needed.

These operations let vertex-disjoint path arguments in a simple graph return multigraph paths
with actual edge identities. Projection preserves internally vertex-disjoint families and their
distinctness between nonadjacent terminals. The nonadjacency condition matters: parallel direct
edges project to the same simple-graph path. Neither operation asserts preservation of
edge-disjointness under simplification.

The constructions extend the walk comparison in
`TauCeti.Combinatorics.Graph.Connectivity.Walk.OfSimpleGraph`.
-/

public section

open Graph

universe u v

namespace Graph.Walk

variable {α : Type u} {β : Type v} {G : Graph α β}

/-- Project a multigraph path to the underlying simple graph, retaining its vertex sequence.
The endpoint membership proofs also allow zero-length paths at actual vertices. -/
def toSimplification : {x y : α} → (p : G.Walk x y) → p.IsPath →
    (hx : x ∈ V(G)) → (hy : y ∈ V(G)) → G.toSimpleGraph.Walk ⟨x, hx⟩ ⟨y, hy⟩
  | _, _, .nil, _, _, _ => .nil
  | _, _, .cons e h p, hp, _, hy =>
      .cons (v := ⟨_, h.right_mem⟩) ((Graph.toSimpleGraph_adj ..).mpr
        ⟨fun heq ↦ (isPath_cons e h p |>.mp hp).2
        (by simpa only [Subtype.mk.inj heq] using p.start_mem_support), h.adj⟩)
        (p.toSimplification (isPath_cons e h p |>.mp hp).1 h.right_mem hy)

@[simp]
theorem toSimplification_nil {x : α} (hx : x ∈ V(G)) :
    (nil : G.Walk x x).toSimplification isPath_nil hx hx = .nil := (rfl)

@[simp]
theorem toSimplification_cons {x y z : α} (e : β) (h : G.IsLink e x y)
    (p : G.Walk y z) (hp : (cons e h p).IsPath) (hx : x ∈ V(G)) (hz : z ∈ V(G)) :
    (cons e h p).toSimplification hp hx hz =
      .cons (v := ⟨_, h.right_mem⟩) ((Graph.toSimpleGraph_adj ..).mpr
        ⟨fun heq ↦ (isPath_cons e h p |>.mp hp).2
        (by simpa only [Subtype.mk.inj heq] using p.start_mem_support), h.adj⟩)
        (p.toSimplification (isPath_cons e h p |>.mp hp).1 h.right_mem hz) := (rfl)

/-- Projection preserves the entire vertex sequence after forgetting subtype membership. -/
@[simp]
theorem support_toSimplification {x y : α} (p : G.Walk x y) (hp : p.IsPath)
    (hx : x ∈ V(G)) (hy : y ∈ V(G)) :
    (p.toSimplification hp hx hy).support.unattach = p.support := by
  induction p with
  | nil => simp
  | cons e h p ih =>
      simp only [toSimplification_cons, SimpleGraph.Walk.support_cons, List.unattach_cons,
        ih, support_cons]

@[simp]
theorem length_toSimplification {x y : α} (p : G.Walk x y) (hp : p.IsPath)
    (hx : x ∈ V(G)) (hy : y ∈ V(G)) :
    (p.toSimplification hp hx hy).length = p.length := by
  have := congrArg List.length (p.support_toSimplification hp hx hy)
  simpa only [List.length_unattach, SimpleGraph.Walk.length_support, length_support,
    Nat.add_right_cancel_iff] using this

/-- The projected walk is a path. -/
@[simp]
theorem isPath_toSimplification {x y : α} (p : G.Walk x y) (hp : p.IsPath)
    (hx : x ∈ V(G)) (hy : y ∈ V(G)) : (p.toSimplification hp hx hy).IsPath := by
  rw [SimpleGraph.Walk.isPath_def, ← List.nodup_map_iff Subtype.val_injective, ← List.unattach,
    support_toSimplification]
  exact hp.support_nodup

@[simp]
theorem mem_support_toSimplification {x y : α} (p : G.Walk x y) (hp : p.IsPath)
    (hx : x ∈ V(G)) (hy : y ∈ V(G)) (z : V(G)) :
    z ∈ (p.toSimplification hp hx hy).support ↔ (z : α) ∈ p.support := by
  rw [← support_toSimplification p hp hx hy]
  simp only [List.mem_unattach, Subtype.coe_eta, Subtype.coe_prop, exists_const]

end Graph.Walk

namespace SimpleGraph.Walk

variable {α : Type u} {β : Type v} {G : Graph α β}

/-- Lift a walk in the underlying simple graph by choosing actual multigraph edges.
Each step chooses an edge joining its endpoints; loops never occur in the lifted walk. -/
noncomputable def toMultigraph : {x y : V(G)} → G.toSimpleGraph.Walk x y → G.Walk x y
  | _, _, .nil => .nil
  | _, _, .cons h p =>
      .cons (Classical.choose ((Graph.toSimpleGraph_adj ..).mp h).2)
        (Classical.choose_spec ((Graph.toSimpleGraph_adj ..).mp h).2) p.toMultigraph

@[simp]
theorem toMultigraph_nil {x : V(G)} :
    (nil : G.toSimpleGraph.Walk x x).toMultigraph = .nil := (rfl)

@[simp]
theorem toMultigraph_cons {x y z : V(G)} (h : G.toSimpleGraph.Adj x y)
    (p : G.toSimpleGraph.Walk y z) :
    (cons h p).toMultigraph =
      .cons (Classical.choose ((Graph.toSimpleGraph_adj ..).mp h).2)
        (Classical.choose_spec ((Graph.toSimpleGraph_adj ..).mp h).2) p.toMultigraph := (rfl)

/-- Lifting preserves the entire vertex sequence. -/
@[simp]
theorem support_toMultigraph {x y : V(G)} (p : G.toSimpleGraph.Walk x y) :
    p.toMultigraph.support = p.support.map Subtype.val := by
  induction p <;> simp_all

@[simp]
theorem length_toMultigraph {x y : V(G)} (p : G.toSimpleGraph.Walk x y) :
    p.toMultigraph.length = p.length := by
  induction p <;> simp_all

/-- A lifted walk is a path exactly when the original walk is a path. -/
@[simp]
theorem isPath_toMultigraph_iff {x y : V(G)} (p : G.toSimpleGraph.Walk x y) :
    p.toMultigraph.IsPath ↔ p.IsPath := by
  rw [Graph.Walk.isPath_def, support_toMultigraph,
    List.nodup_map_iff Subtype.val_injective, isPath_def]

/-- Projecting a lifted path recovers the original path. The opposite round trip need not
recover the original choices of parallel edges. -/
@[simp]
theorem toSimplification_toMultigraph {x y : V(G)} (p : G.toSimpleGraph.Walk x y)
    (hp : p.toMultigraph.IsPath) :
    p.toMultigraph.toSimplification hp
      x.property y.property = p := by
  apply support_injective
  apply List.map_injective_iff.mpr Subtype.val_injective
  simp only [List.map_subtype, List.map_id_fun', id_eq,
    Graph.Walk.support_toSimplification, support_toMultigraph]

/-- Lifting walks is injective, even when the multigraph has parallel edges. -/
theorem toMultigraph_injective (x y : V(G)) :
    Function.Injective (toMultigraph : G.toSimpleGraph.Walk x y → G.Walk x y) := by
  intro p q hpq
  apply support_injective
  apply List.map_injective_iff.mpr Subtype.val_injective
  simpa only [support_toMultigraph] using congrArg Graph.Walk.support hpq

end SimpleGraph.Walk

namespace Graph.Walk

variable {α : Type u} {β : Type v} {G : Graph α β}

/-- Projection preserves and reflects vertex-disjointness, including endpoints. This allows
set-to-set path families, with varying endpoints and zero-length paths, to be transported. -/
@[simp]
theorem disjoint_support_toSimplification_iff {x y z w : V(G)}
    (p : G.Walk x y) (q : G.Walk z w) (hp : p.IsPath) (hq : q.IsPath) :
    (p.toSimplification hp x.property y.property).support.Disjoint
        (q.toSimplification hq z.property w.property).support ↔
      p.support.Disjoint q.support := by
  rw [← List.Disjoint.map_iff Subtype.val_injective]
  simp only [List.map_subtype, List.map_id_fun', id_eq, support_toSimplification]

/-- Projection preserves and reflects internal vertex-disjointness between fixed terminals. -/
theorem internally_disjoint_toSimplification_iff {x y : V(G)}
    (p q : G.Walk x y) (hp : p.IsPath) (hq : q.IsPath) :
    (∀ z ∈ (p.toSimplification hp x.property y.property).support,
      z ∈ (q.toSimplification hq x.property y.property).support → z = x ∨ z = y) ↔
    (∀ z ∈ p.support, z ∈ q.support → z = (x : α) ∨ z = (y : α)) := by
  constructor
  · intro h z hz hz'
    have hzg := p.support_subset_vertexSet x.property z hz
    rcases h ⟨z, hzg⟩
      ((p.mem_support_toSimplification hp x.property y.property _).mpr hz)
      ((q.mem_support_toSimplification hq x.property y.property _).mpr hz') with hzx | hzy
    · exact Or.inl (congrArg Subtype.val hzx)
    · exact Or.inr (congrArg Subtype.val hzy)
  · intro h z hz hz'
    rcases h z ((p.mem_support_toSimplification hp x.property y.property _).mp hz)
      ((q.mem_support_toSimplification hq x.property y.property _).mp hz') with hzx | hzy
    · exact Or.inl (Subtype.ext hzx)
    · exact Or.inr (Subtype.ext hzy)

/-- An internally vertex-disjoint family between distinct nonadjacent terminals stays distinct
under projection. Thus projection retains the cardinality of such finite path families. -/
theorem injective_toSimplification_of_pairwise {ι : Type*} {x y : V(G)}
    (p : ι → G.Walk x y) (hp : ∀ i, (p i).IsPath) (hxy : x ≠ y) (hAdj : ¬ G.Adj x y)
    (hdis : Pairwise fun i j ↦ ∀ z ∈ (p i).support,
      z ∈ (p j).support → z = (x : α) ∨ z = (y : α)) :
    Function.Injective (fun i ↦ (p i).toSimplification (hp i) x.property y.property) := by
  intro i j hij
  by_contra hne
  have hs : (p i).support = (p j).support := by
    simpa only [support_toSimplification] using
      congrArg (fun q ↦ q.support.unattach) hij
  obtain ⟨z, hz, hzx, hzy⟩ := (hp i).exists_mem_support_ne_endpoints
    (fun h ↦ hxy (Subtype.ext h)) hAdj
  exact (hdis hne z hz (hs ▸ hz)).elim hzx hzy

end Graph.Walk

namespace SimpleGraph.Walk

variable {α : Type u} {β : Type v} {G : Graph α β}

/-- Lifting preserves and reflects vertex-disjointness, including endpoints. -/
theorem disjoint_support_toMultigraph_iff {x y z w : V(G)}
    (p : G.toSimpleGraph.Walk x y) (q : G.toSimpleGraph.Walk z w) :
    p.toMultigraph.support.Disjoint q.toMultigraph.support ↔ p.support.Disjoint q.support := by
  rw [support_toMultigraph, support_toMultigraph, List.Disjoint.map_iff Subtype.val_injective]

/-- Lifting preserves and reflects internal vertex-disjointness between fixed terminals. -/
theorem internally_disjoint_toMultigraph_iff {x y : V(G)}
    (p q : G.toSimpleGraph.Walk x y) :
    (∀ z ∈ p.toMultigraph.support, z ∈ q.toMultigraph.support →
      z = (x : α) ∨ z = (y : α)) ↔
    (∀ z ∈ p.support, z ∈ q.support → z = x ∨ z = y) := by
  simp only [support_toMultigraph, List.mem_map, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, Subtype.coe_inj]
  constructor
  · intro h z hz hz'
    exact h z hz z hz' rfl
  · intro h z hz w hw heq
    subst w
    exact h z hz hw

end SimpleGraph.Walk

/-! ### Parallel edges and the nonadjacency hypothesis -/

/-- With infinitely many parallel edges, distinct one-edge paths can have the same projection.
Both ambient types are infinite, while the actual vertex set has only two elements. -/
example :
    let G := Graph.banana (0 : ℕ) 1 (Set.univ : Set ℕ)
    ∃ (p q : G.Walk 0 1) (hp : p.IsPath) (hq : q.IsPath), p ≠ q ∧
      p.toSimplification hp (by simp [G]) (by simp [G]) =
        q.toSimplification hq (by simp [G]) (by simp [G]) := by
  intro G
  have he (e : ℕ) : G.IsLink e 0 1 := by simp [G, Graph.banana_isLink]
  have hp (e : ℕ) : (he e).toWalk.IsPath := by simp
  refine ⟨(he 0).toWalk, (he 1).toWalk, hp 0, hp 1, ?_, ?_⟩
  · intro h
    have := congrArg Graph.Walk.edges h
    simp at this
  · apply SimpleGraph.Walk.support_injective
    apply List.map_injective_iff.mpr Subtype.val_injective
    simp only [List.map_subtype, List.map_id_fun', id_eq, Graph.Walk.support_toSimplification,
      Graph.IsLink.support_toWalk]
