/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Connectivity.Walk.OfSimpleGraph
public import TauCeti.Combinatorics.SimpleGraph.Connectivity.Menger

/-!
# Projecting multigraph paths to the underlying simple graph

A path in a multigraph traverses no loop, so forgetting its edge identities gives a path in
its underlying simple graph with exactly the same vertex sequence. Projection is a left
inverse to `SimpleGraph.Walk.liftToGraph`, which chooses actual edges. It is not a right
inverse: parallel edges are forgotten.

Projection preserves and reflects internal vertex-disjointness and disjointness of whole
supports. For pairwise internally disjoint paths between distinct nonadjacent terminals,
projection also preserves distinctness, hence the cardinality of a finite family. Nonadjacency
is essential: distinct direct parallel edges project to the same one-edge path. Families with
pairwise disjoint whole supports retain distinctness even with varying endpoints and zero-length
members. No assertion about preservation of edge-disjointness is made.
-/

public section

open scoped Graph

universe u v

namespace Graph.Walk

variable {α : Type u} {β : Type v} {G : Graph α β}

/-- Forget the edge identities of a multigraph path, retaining its vertex sequence as a walk
in the underlying simple graph. The endpoint membership proofs include the empty path case. -/
def toSimplePath : {x y : α} → (p : G.Walk x y) → p.IsPath →
    (hx : x ∈ V(G)) → (hy : y ∈ V(G)) → G.toSimpleGraph.Walk ⟨x, hx⟩ ⟨y, hy⟩
  | _, _, .nil, _, _, _ => .nil
  | _, _, .cons e h p, hp, hx, hy =>
      SimpleGraph.Walk.cons (G := G.toSimpleGraph) (v := ⟨_, h.right_mem⟩)
        ((G.toSimpleGraph_adj _ _).mpr ⟨by
          intro hxy
          apply ((isPath_cons e h p).1 hp).2
          have heq := congrArg Subtype.val hxy
          dsimp only at heq
          rw [heq]
          exact p.start_mem_support, h.adj⟩)
        (p.toSimplePath ((isPath_cons e h p).1 hp).1 h.right_mem hy)

/-- Projection preserves the empty path. -/
@[simp]
theorem toSimplePath_nil {x : α} (hx : x ∈ V(G)) (hp : (nil : G.Walk x x).IsPath) :
    (nil : G.Walk x x).toSimplePath hp hx hx = .nil :=
  (rfl)

/-- Projection replaces each traversed edge by the corresponding simple adjacency. -/
@[simp]
theorem toSimplePath_cons {x y z : α} (e : β) (h : G.IsLink e x y) (p : G.Walk y z)
    (hp : (cons e h p).IsPath) (hx : x ∈ V(G)) (hz : z ∈ V(G)) :
    (cons e h p).toSimplePath hp hx hz =
      SimpleGraph.Walk.cons (G := G.toSimpleGraph) (v := ⟨y, h.right_mem⟩)
        ((G.toSimpleGraph_adj _ _).mpr ⟨by
          intro hxy
          apply ((isPath_cons e h p).1 hp).2
          have heq := congrArg Subtype.val hxy
          dsimp only at heq
          rw [heq]
          exact p.start_mem_support, h.adj⟩)
        (p.toSimplePath ((isPath_cons e h p).1 hp).1 h.right_mem hz) :=
  (rfl)

/-- Projection retains the complete vertex sequence, including both endpoints. -/
@[simp]
theorem support_toSimplePath {x y : α} (p : G.Walk x y) (hp : p.IsPath)
    (hx : x ∈ V(G)) (hy : y ∈ V(G)) :
    (p.toSimplePath hp hx hy).support.unattach = p.support := by
  induction p with
  | nil => simp only [toSimplePath_nil, SimpleGraph.Walk.support_nil, List.unattach_cons,
      List.unattach_nil, support_nil]
  | cons e h p ih =>
      simp only [toSimplePath_cons, SimpleGraph.Walk.support_cons, List.unattach_cons,
        support_cons, ih]

/-- Projection preserves path length. -/
@[simp]
theorem length_toSimplePath {x y : α} (p : G.Walk x y) (hp : p.IsPath)
    (hx : x ∈ V(G)) (hy : y ∈ V(G)) :
    (p.toSimplePath hp hx hy).length = p.length := by
  have := congrArg List.length (p.support_toSimplePath hp hx hy)
  simpa only [List.length_unattach, SimpleGraph.Walk.length_support, length_support,
    Nat.add_right_cancel_iff] using this

/-- The projected walk is a path. -/
@[simp]
theorem isPath_toSimplePath {x y : α} (p : G.Walk x y) (hp : p.IsPath)
    (hx : x ∈ V(G)) (hy : y ∈ V(G)) :
    (p.toSimplePath hp hx hy).IsPath := by
  apply SimpleGraph.Walk.IsPath.mk'
  apply (List.nodup_map_iff Subtype.val_injective).1
  rw [← List.unattach, support_toSimplePath]
  exact hp.support_nodup

/-- A vertex occurs on the projected path exactly when its underlying vertex occurs on the
original path. -/
@[simp]
theorem mem_support_toSimplePath {x y : α} (p : G.Walk x y) (hp : p.IsPath)
    (hx : x ∈ V(G)) (hy : y ∈ V(G)) (a : V(G)) :
    a ∈ (p.toSimplePath hp hx hy).support ↔ (a : α) ∈ p.support := by
  rw [← support_toSimplePath p hp hx hy, List.unattach]
  exact (List.mem_map_of_injective Subtype.val_injective).symm

/-- Projection forgets exactly the edge choices: projected paths are equal exactly when their
original vertex sequences agree. -/
@[simp]
theorem toSimplePath_eq_iff {x y : α} (p q : G.Walk x y) (hp : p.IsPath) (hq : q.IsPath)
    (hx : x ∈ V(G)) (hy : y ∈ V(G)) :
    p.toSimplePath hp hx hy = q.toSimplePath hq hx hy ↔ p.support = q.support := by
  constructor
  · intro h
    simpa only [support_toSimplePath] using
      congrArg (fun r ↦ r.support.unattach) h
  · intro h
    apply SimpleGraph.Walk.ext_support
    apply List.map_injective_iff.2 Subtype.val_injective
    simpa using h

/-- Reversal commutes with projection. -/
@[simp]
theorem toSimplePath_reverse {x y : α} (p : G.Walk x y) (hp : p.IsPath)
    (hx : x ∈ V(G)) (hy : y ∈ V(G)) :
    p.reverse.toSimplePath ((isPath_reverse p).2 hp) hy hx =
      (p.toSimplePath hp hx hy).reverse := by
  apply SimpleGraph.Walk.ext_support
  apply List.map_injective_iff.2 Subtype.val_injective
  simp [SimpleGraph.Walk.support_reverse]

/-- Projection preserves and reflects internal vertex-disjointness. -/
@[simp]
theorem internallyDisjoint_toSimplePath_iff {x y : α} (p q : G.Walk x y)
    (hp : p.IsPath) (hq : q.IsPath) (hx : x ∈ V(G)) (hy : y ∈ V(G)) :
    (p.toSimplePath hp hx hy).InternallyDisjoint (q.toSimplePath hq hx hy) ↔
      p.InternallyDisjoint q := by
  rw [SimpleGraph.Walk.internallyDisjoint_def, internallyDisjoint_def]
  constructor
  · intro h a hap haq
    have ha := p.support_subset_vertexSet hx a hap
    simpa only [Subtype.mk.injEq] using h ⟨a, ha⟩
      ((p.mem_support_toSimplePath hp hx hy _).2 hap)
      ((q.mem_support_toSimplePath hq hx hy _).2 haq)
  · intro h a hap haq
    simpa only [Subtype.ext_iff] using h a
      ((p.mem_support_toSimplePath hp hx hy a).1 hap)
      ((q.mem_support_toSimplePath hq hx hy a).1 haq)

/-- Projection preserves and reflects disjointness of whole supports, even for paths with
different endpoints. This is the disjointness used by set-to-set vertex path families. -/
@[simp]
theorem disjoint_support_toSimplePath_iff {x y z w : α} (p : G.Walk x y) (q : G.Walk z w)
    (hp : p.IsPath) (hq : q.IsPath) (hx : x ∈ V(G)) (hy : y ∈ V(G))
    (hz : z ∈ V(G)) (hw : w ∈ V(G)) :
    (p.toSimplePath hp hx hy).support.Disjoint (q.toSimplePath hq hz hw).support ↔
      p.support.Disjoint q.support := by
  rw [← support_toSimplePath p hp hx hy, ← support_toSimplePath q hq hz hw]
  simp only [List.unattach]
  exact ⟨List.disjoint_map Subtype.val_injective, List.Disjoint.of_map⟩

/-- An internally disjoint family between distinct nonadjacent terminals remains a family of
distinct paths after projection. Neither the index type nor the graph needs to be finite. -/
theorem toSimplePath_injective_of_pairwise_internallyDisjoint {ι : Type*} {s t : V(G)}
    {P : ι → G.Walk s t} (hP : ∀ i, (P i).IsPath)
    (hdisj : Pairwise fun i j ↦ (P i).InternallyDisjoint (P j))
    (hst : s ≠ t) (hadj : ¬G.toSimpleGraph.Adj s t) :
    Function.Injective (fun i ↦ (P i).toSimplePath (hP i) s.2 t.2) := by
  intro i j hij
  by_contra hne
  have hd := (internallyDisjoint_toSimplePath_iff (P i) (P j) (hP i) (hP j) s.2 t.2).2
    (hdisj hne)
  obtain ⟨a, ha, has, hat⟩ :=
    ((P i).toSimplePath (hP i) s.2 t.2).exists_mem_support_ne_ne hst hadj
  rcases SimpleGraph.Walk.internallyDisjoint_def.1 hd a ha
    (by simpa only [hij] using ha) with h | h
  · exact has h
  · exact hat h

open scoped Classical in
/-- A finite internally disjoint family between distinct nonadjacent terminals has the same
number of distinct paths after projection. -/
theorem card_image_toSimplePath {ι : Type*} [Fintype ι] {s t : V(G)}
    {P : ι → G.Walk s t} (hP : ∀ i, (P i).IsPath)
    (hdisj : Pairwise fun i j ↦ (P i).InternallyDisjoint (P j))
    (hst : s ≠ t) (hadj : ¬G.toSimpleGraph.Adj s t) :
    (Finset.univ.image (fun i ↦ (P i).toSimplePath (hP i) s.2 t.2)).card = Fintype.card ι := by
  classical
  exact (Finset.card_image_of_injective _
    (toSimplePath_injective_of_pairwise_internallyDisjoint hP hdisj hst hadj)).trans
    (Finset.card_univ)

/-- A family with pairwise disjoint whole supports remains a family of distinct paths after
projection, including when endpoints vary or a member has length zero. -/
theorem toSimplePath_injective_of_pairwise_disjoint_support {ι : Type*} {s t : ι → V(G)}
    {P : ∀ i, G.Walk (s i) (t i)} (hP : ∀ i, (P i).IsPath)
    (hdisj : Pairwise fun i j ↦ (P i).support.Disjoint (P j).support) :
    Function.Injective (fun i ↦ (⟨s i, t i, (P i).toSimplePath (hP i) (s i).2 (t i).2⟩ :
      Σ s t : V(G), G.toSimpleGraph.Walk s t)) := by
  intro i j hij
  by_contra hne
  have hsupp : (P i).support = (P j).support := by
    simpa only [support_toSimplePath] using
      congrArg (fun r : Σ s t : V(G), G.toSimpleGraph.Walk s t ↦
        r.2.2.support.unattach) hij
  exact hdisj hne (P i).start_mem_support (hsupp ▸ (P i).start_mem_support)

end Graph.Walk

namespace SimpleGraph.Walk

variable {α : Type u} {β : Type v} {G : Graph α β} {s t : V(G)}

/-- Projecting a lifted simple path recovers the original path, regardless of the chosen
parallel edges in its lift. -/
@[simp]
theorem toSimplePath_liftToGraph (p : G.toSimpleGraph.Walk s t) (hp : p.IsPath) :
    p.liftToGraph.toSimplePath ((isPath_liftToGraph_iff p).2 hp) s.2 t.2 = p := by
  apply ext_support
  apply List.map_injective_iff.2 Subtype.val_injective
  simp

end SimpleGraph.Walk
