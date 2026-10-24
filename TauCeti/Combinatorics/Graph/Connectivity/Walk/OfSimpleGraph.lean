/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Graph.Simple
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import TauCeti.Combinatorics.Graph.Connectivity.Walk.Basic

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
reachability in its underlying simple graph `G.toSimpleGraph`.
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

namespace Graph

variable {α β : Type*} {G : Graph α β}

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
theorem toSimpleGraph_reachable_iff {u v : V(G)} :
    G.toSimpleGraph.Reachable u v ↔ G.Reachable u v := by
  refine ⟨?_, fun h ↦ h.toSimpleGraph_reachable⟩
  rintro ⟨p⟩
  induction p with
  | nil => exact Reachable.refl (Subtype.property _)
  | cons huv _ ih =>
      obtain ⟨-, e, he⟩ := huv
      exact he.reachable.trans ih

end Graph
