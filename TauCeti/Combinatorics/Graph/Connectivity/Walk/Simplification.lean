/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Connectivity.Walk.OfSimpleGraph
public import TauCeti.Combinatorics.SimpleGraph.Paths

/-!
# Projecting multigraph paths to the underlying simple graph

A path in a multigraph traverses no loop, so forgetting its edge identities gives a path in
its underlying simple graph with exactly the same vertex sequence. On paths, projection is a left
inverse to `SimpleGraph.Walk.liftToGraph`, which chooses actual edges. It is not a right
inverse: parallel edges are forgotten.

Projection preserves and reflects internal vertex-disjointness and disjointness of whole
supports. For pairwise internally disjoint paths between distinct nonadjacent terminals,
projection also preserves distinctness, hence the cardinality of a finite family. Nonadjacency
is essential: distinct direct parallel edges project to the same one-edge path. Families with
pairwise disjoint whole supports retain distinctness even with varying endpoints and zero-length
members. Projection does not preserve edge-disjointness: distinct parallel edges are edge-disjoint
in the multigraph but project to the same simple-graph edge.
-/

public section

open scoped Graph

universe u v

namespace Graph.Walk

variable {α : Type u} {β : Type v} {G : Graph α β}

/-- A nonloop link gives adjacency in the underlying simple graph. -/
theorem _root_.Graph.IsLink.toSimpleGraph_adj {x y : α} {e : β} (h : G.IsLink e x y)
    (hxy : x ≠ y) : G.toSimpleGraph.Adj ⟨x, h.left_mem⟩ ⟨y, h.right_mem⟩ :=
  ⟨fun heq ↦ hxy (Subtype.mk.inj heq), h.adj⟩

/-- The first step of a path joins distinct vertices in the underlying simple graph. -/
theorem IsPath.toSimpleGraph_adj {x y z : α} {e : β} {h : G.IsLink e x y}
    {p : G.Walk y z} (hp : (cons e h p).IsPath) :
    G.toSimpleGraph.Adj ⟨x, h.left_mem⟩ ⟨y, h.right_mem⟩ :=
  h.toSimpleGraph_adj fun hxy ↦ ((isPath_cons e h p).1 hp).2
    (hxy.symm ▸ p.start_mem_support)

/-- Forget the edge identities of a multigraph path, retaining its vertex sequence as a walk
in the underlying simple graph. The endpoint membership proofs include the empty path case. -/
def toSimpleGraphWalk : {x y : α} → (p : G.Walk x y) → p.IsPath →
    (hx : x ∈ V(G)) → (hy : y ∈ V(G)) → G.toSimpleGraph.Walk ⟨x, hx⟩ ⟨y, hy⟩
  | _, _, .nil, _, _, _ => .nil
  | _, _, .cons e h p, hp, _, hy =>
      SimpleGraph.Walk.cons hp.toSimpleGraph_adj
        (p.toSimpleGraphWalk ((isPath_cons e h p).1 hp).1 h.right_mem hy)

/-- Projection preserves the empty path. -/
@[simp]
theorem toSimpleGraphWalk_nil {x : α} (hx : x ∈ V(G)) (hp : (nil : G.Walk x x).IsPath) :
    (nil : G.Walk x x).toSimpleGraphWalk hp hx hx = .nil :=
  (rfl)

/-- Projection replaces each traversed edge by the corresponding simple adjacency. -/
@[simp]
theorem toSimpleGraphWalk_cons {x y z : α} (e : β) (h : G.IsLink e x y) (p : G.Walk y z)
    (hp : (cons e h p).IsPath) (hx : x ∈ V(G)) (hz : z ∈ V(G)) :
    (cons e h p).toSimpleGraphWalk hp hx hz =
      SimpleGraph.Walk.cons hp.toSimpleGraph_adj
        (p.toSimpleGraphWalk ((isPath_cons e h p).1 hp).1 h.right_mem hz) :=
  (rfl)

/-- Projection retains the complete vertex sequence, including both endpoints. -/
@[simp]
theorem support_toSimpleGraphWalk {x y : α} (p : G.Walk x y) (hp : p.IsPath)
    (hx : x ∈ V(G)) (hy : y ∈ V(G)) :
    (p.toSimpleGraphWalk hp hx hy).support.unattach = p.support := by
  induction p with
  | nil => simp only [toSimpleGraphWalk_nil, SimpleGraph.Walk.support_nil, List.unattach_cons,
      List.unattach_nil, support_nil]
  | cons e h p ih =>
      simp only [toSimpleGraphWalk_cons, SimpleGraph.Walk.support_cons, List.unattach_cons,
        support_cons, ih]

/-- Projection preserves path length. -/
@[simp]
theorem length_toSimpleGraphWalk {x y : α} (p : G.Walk x y) (hp : p.IsPath)
    (hx : x ∈ V(G)) (hy : y ∈ V(G)) :
    (p.toSimpleGraphWalk hp hx hy).length = p.length := by
  have := congrArg List.length (p.support_toSimpleGraphWalk hp hx hy)
  simpa only [List.length_unattach, SimpleGraph.Walk.length_support, length_support,
    Nat.add_right_cancel_iff] using this

/-- Projection preserves and reflects being a zero-length walk. -/
@[simp]
theorem nil_toSimpleGraphWalk_iff {x y : α} (p : G.Walk x y) (hp : p.IsPath)
    (hx : x ∈ V(G)) (hy : y ∈ V(G)) :
    (p.toSimpleGraphWalk hp hx hy).Nil ↔ p.Nil := by
  rw [← SimpleGraph.Walk.length_eq_zero_iff, ← length_eq_zero_iff, length_toSimpleGraphWalk]

/-- Projection commutes with concatenation whenever the concatenated walk is a path. -/
@[simp]
theorem toSimpleGraphWalk_append {x y z : α} (p : G.Walk x y) (q : G.Walk y z)
    (hpq : (p.append q).IsPath) (hx : x ∈ V(G)) (hz : z ∈ V(G)) :
    (p.append q).toSimpleGraphWalk hpq hx hz =
      (p.toSimpleGraphWalk hpq.of_append_left hx
        (p.support_subset_vertexSet hx _ p.end_mem_support)).append
        (q.toSimpleGraphWalk hpq.of_append_right
          (p.support_subset_vertexSet hx _ p.end_mem_support) hz) := by
  apply SimpleGraph.Walk.ext_support
  apply List.map_injective_iff.2 Subtype.val_injective
  simp [SimpleGraph.Walk.support_append, List.map_tail]

/-- Projection sends a one-edge path to the corresponding simple-graph adjacency walk. -/
@[simp]
theorem _root_.Graph.IsLink.toSimpleGraphWalk_toWalk {x y : α} {e : β}
    (h : G.IsLink e x y) (hp : h.toWalk.IsPath) :
    h.toWalk.toSimpleGraphWalk hp h.left_mem h.right_mem =
      (h.toSimpleGraph_adj (h.isPath_toWalk_iff.1 hp)).toWalk := by
  simp only [h.toWalk_eq_cons, toSimpleGraphWalk_cons, toSimpleGraphWalk_nil,
    SimpleGraph.Adj.toWalk]

/-- The projected walk is a path. -/
@[simp]
theorem isPath_toSimpleGraphWalk {x y : α} (p : G.Walk x y) (hp : p.IsPath)
    (hx : x ∈ V(G)) (hy : y ∈ V(G)) :
    (p.toSimpleGraphWalk hp hx hy).IsPath := by
  apply SimpleGraph.Walk.IsPath.mk'
  apply (List.nodup_map_iff Subtype.val_injective).1
  rw [← List.unattach, support_toSimpleGraphWalk]
  exact hp.support_nodup

/-- A vertex occurs on the projected path exactly when its underlying vertex occurs on the
original path. -/
@[simp]
theorem mem_support_toSimpleGraphWalk {x y : α} (p : G.Walk x y) (hp : p.IsPath)
    (hx : x ∈ V(G)) (hy : y ∈ V(G)) (a : V(G)) :
    a ∈ (p.toSimpleGraphWalk hp hx hy).support ↔ (a : α) ∈ p.support := by
  rw [← support_toSimpleGraphWalk p hp hx hy, List.unattach]
  exact (List.mem_map_of_injective Subtype.val_injective).symm

/-- Projection forgets exactly the edge choices: projected paths are equal exactly when their
original vertex sequences agree. -/
@[simp]
theorem toSimpleGraphWalk_eq_iff {x y : α} (p q : G.Walk x y) (hp : p.IsPath) (hq : q.IsPath)
    (hx : x ∈ V(G)) (hy : y ∈ V(G)) :
    p.toSimpleGraphWalk hp hx hy = q.toSimpleGraphWalk hq hx hy ↔ p.support = q.support := by
  constructor
  · intro h
    simpa only [support_toSimpleGraphWalk] using
      congrArg (fun r ↦ r.support.unattach) h
  · intro h
    apply SimpleGraph.Walk.ext_support
    apply List.map_injective_iff.2 Subtype.val_injective
    simpa using h

/-- Reversal commutes with projection. -/
@[simp]
theorem toSimpleGraphWalk_reverse {x y : α} (p : G.Walk x y) (hp : p.reverse.IsPath)
    (hx : x ∈ V(G)) (hy : y ∈ V(G)) :
    p.reverse.toSimpleGraphWalk hp hy hx =
      (p.toSimpleGraphWalk ((isPath_reverse p).1 hp) hx hy).reverse := by
  apply SimpleGraph.Walk.ext_support
  apply List.map_injective_iff.2 Subtype.val_injective
  simp [SimpleGraph.Walk.support_reverse]

/-- Projection preserves and reflects internal vertex-disjointness. -/
@[simp]
theorem internallyDisjoint_toSimpleGraphWalk_iff {x y : α} (p q : G.Walk x y)
    (hp : p.IsPath) (hq : q.IsPath) (hx : x ∈ V(G)) (hy : y ∈ V(G)) :
    (p.toSimpleGraphWalk hp hx hy).InternallyDisjoint (q.toSimpleGraphWalk hq hx hy) ↔
      p.InternallyDisjoint q := by
  rw [SimpleGraph.Walk.internallyDisjoint_def, internallyDisjoint_def]
  constructor
  · intro h a hap haq
    have ha := p.support_subset_vertexSet hx a hap
    simpa only [Subtype.mk.injEq] using h ⟨a, ha⟩
      ((p.mem_support_toSimpleGraphWalk hp hx hy _).2 hap)
      ((q.mem_support_toSimpleGraphWalk hq hx hy _).2 haq)
  · intro h a hap haq
    simpa only [Subtype.ext_iff] using h a
      ((p.mem_support_toSimpleGraphWalk hp hx hy a).1 hap)
      ((q.mem_support_toSimpleGraphWalk hq hx hy a).1 haq)

/-- Projection preserves and reflects disjointness of whole supports, even for paths with
different endpoints. This is the disjointness used by set-to-set vertex path families. -/
@[simp]
theorem disjoint_support_toSimpleGraphWalk_iff {x y z w : α} (p : G.Walk x y) (q : G.Walk z w)
    (hp : p.IsPath) (hq : q.IsPath) (hx : x ∈ V(G)) (hy : y ∈ V(G))
    (hz : z ∈ V(G)) (hw : w ∈ V(G)) :
    (p.toSimpleGraphWalk hp hx hy).support.Disjoint (q.toSimpleGraphWalk hq hz hw).support ↔
      p.support.Disjoint q.support := by
  rw [← support_toSimpleGraphWalk p hp hx hy, ← support_toSimpleGraphWalk q hq hz hw]
  simp only [List.unattach]
  exact ⟨List.disjoint_map Subtype.val_injective, List.Disjoint.of_map⟩

/-- An internally disjoint family between distinct nonadjacent terminals remains a family of
distinct paths after projection. Neither the index type nor the graph needs to be finite. -/
theorem toSimpleGraphWalk_injective_of_pairwise_internallyDisjoint {ι : Type*} {s t : V(G)}
    {P : ι → G.Walk s t} (hP : ∀ i, (P i).IsPath)
    (hdisj : Pairwise fun i j ↦ (P i).InternallyDisjoint (P j))
    (hst : s ≠ t) (hadj : ¬G.toSimpleGraph.Adj s t) :
    Function.Injective (fun i ↦ (P i).toSimpleGraphWalk (hP i) s.2 t.2) :=
  SimpleGraph.Walk.injective_of_pairwise_internallyDisjoint
    (fun i j hij ↦ (internallyDisjoint_toSimpleGraphWalk_iff
      (P i) (P j) (hP i) (hP j) s.2 t.2).2 (hdisj hij)) hst hadj

/-- A finite internally disjoint family between distinct nonadjacent terminals has the same
number of distinct paths after projection. -/
theorem card_image_toSimpleGraphWalk_of_pairwise_internallyDisjoint {ι : Type*} [Fintype ι]
    {s t : V(G)} [DecidableEq (G.toSimpleGraph.Walk s t)]
    {P : ι → G.Walk s t} (hP : ∀ i, (P i).IsPath)
    (hdisj : Pairwise fun i j ↦ (P i).InternallyDisjoint (P j))
    (hst : s ≠ t) (hadj : ¬G.toSimpleGraph.Adj s t) :
    (Finset.univ.image (fun i ↦ (P i).toSimpleGraphWalk (hP i) s.2 t.2)).card =
      Fintype.card ι := by
  exact (Finset.card_image_of_injective _
    (toSimpleGraphWalk_injective_of_pairwise_internallyDisjoint hP hdisj hst hadj)).trans
    (Finset.card_univ)

/-- A family with pairwise disjoint whole supports remains a family of distinct paths after
projection, including when endpoints vary or a member has length zero. -/
theorem toSimpleGraphWalk_injective_of_pairwise_disjoint_support {ι : Type*} {s t : ι → V(G)}
    {P : ∀ i, G.Walk (s i) (t i)} (hP : ∀ i, (P i).IsPath)
    (hdisj : Pairwise fun i j ↦ (P i).support.Disjoint (P j).support) :
    Function.Injective (fun i ↦ (⟨s i, t i, (P i).toSimpleGraphWalk (hP i) (s i).2 (t i).2⟩ :
      Σ s t : V(G), G.toSimpleGraph.Walk s t)) := by
  intro i j hij
  by_contra hne
  have hsupp : (P i).support = (P j).support := by
    simpa only [support_toSimpleGraphWalk] using
      congrArg (fun r : Σ s t : V(G), G.toSimpleGraph.Walk s t ↦
        r.2.2.support.unattach) hij
  exact hdisj hne (P i).start_mem_support (hsupp ▸ (P i).start_mem_support)

end Graph.Walk

namespace SimpleGraph.Walk

variable {α : Type u} {β : Type v} {G : Graph α β} {s t : V(G)}

/-- Projecting a lifted simple path recovers the original path, regardless of the chosen
parallel edges in its lift. -/
@[simp]
theorem toSimpleGraphWalk_liftToGraph (p : G.toSimpleGraph.Walk s t)
    (hp : p.liftToGraph.IsPath) :
    p.liftToGraph.toSimpleGraphWalk hp s.2 t.2 = p := by
  apply ext_support
  apply List.map_injective_iff.2 Subtype.val_injective
  simp

/-- Lifting walks of the underlying simple graph preserves and reflects internal disjointness,
since the lift keeps every vertex sequence. -/
@[simp]
theorem internallyDisjoint_liftToGraph_iff {p q : G.toSimpleGraph.Walk s t} :
    p.liftToGraph.InternallyDisjoint q.liftToGraph ↔ p.InternallyDisjoint q := by
  simp only [Graph.Walk.internallyDisjoint_def, internallyDisjoint_def, support_liftToGraph,
    List.forall_mem_map, List.mem_map_of_injective Subtype.val_injective, Subtype.val_inj]

end SimpleGraph.Walk
