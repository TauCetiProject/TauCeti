/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Data.Fintype.Card

/-!
# The two sides of an edge

For a simple graph `G` and vertices `u, v`, the side `G.edgeSide u v` is the finite set of
vertices still reachable from `u` after deleting the edge `s(u, v)`. Every vertex reachable from
`u` in `G` lies on the side of `u` or on the side of `v`, and the two sides are disjoint exactly
when `s(u, v)` is a bridge. In a tree, deleting an edge therefore splits the vertices into the two
sides of that edge: its fundamental partition.

In an acyclic graph the unique path between two vertices uses an edge exactly when that edge
separates them, so a path from a vertex on the side of `u` crosses `s(u, v)` exactly when it ends
off that side. These are the facts used to read off minimum cuts from weighted trees.
-/

public section

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {u v x : V}

namespace Walk

variable {s t : V}

/-- In an acyclic graph, a path uses an edge exactly when deleting that edge separates the
endpoints of the path. -/
theorem IsPath.mem_edges_iff_not_reachable_deleteEdges (hG : G.IsAcyclic) {p : G.Walk s t}
    (hp : p.IsPath) {e : Sym2 V} : e ∈ p.edges ↔ ¬(G.deleteEdges {e}).Reachable s t := by
  classical
  refine ⟨fun he ⟨q⟩ ↦ ?_, p.mem_edges_of_not_reachable_deleteEdges⟩
  -- A path avoiding `e` in the smaller graph is a second path from `s` to `t` in `G`.
  have hpq : p = q.toPath.val.mapLe (G.deleteEdges_le {e}) :=
    Subtype.ext_iff.mp ((hG.subsingleton_path s t).elim ⟨p, hp⟩ ⟨_, q.toPath.property.mapLe _⟩)
  rw [hpq, edges_mapLe_eq_edges] at he
  simpa using q.toPath.val.edges_subset_edgeSet he

end Walk

variable [Fintype V]

open scoped Classical in
/-- The side of `u` for the edge `s(u, v)`: the vertices still reachable from `u` after deleting
that edge. For a tree edge, `G.edgeSide u v` and `G.edgeSide v u` partition the vertices. -/
noncomputable def edgeSide (G : SimpleGraph V) (u v : V) : Finset V :=
  {x | (G.deleteEdges {s(u, v)}).Reachable u x}

/-- A vertex is on the side of `u` exactly when it is reachable from `u` without `s(u, v)`. -/
@[simp] theorem mem_edgeSide : x ∈ G.edgeSide u v ↔ (G.deleteEdges {s(u, v)}).Reachable u x := by
  simp [edgeSide]

/-- The side of `u` is the vertex set of the connected component of `u` after deleting
`s(u, v)`. -/
theorem coe_edgeSide :
    (G.edgeSide u v : Set V) = ((G.deleteEdges {s(u, v)}).connectedComponentMk u).supp := by
  ext x
  simp [ConnectedComponent.mem_supp_iff, ConnectedComponent.eq, reachable_comm]

/-- Each end of an edge lies on its own side. -/
theorem self_mem_edgeSide (G : SimpleGraph V) (u v : V) : u ∈ G.edgeSide u v :=
  mem_edgeSide.mpr .rfl

/-- A vertex whose only neighbour is `v` is alone on its side of the edge to `v`. -/
theorem edgeSide_eq_singleton (h : ∀ y, G.Adj u y → y = v) : G.edgeSide u v = {u} := by
  refine Finset.eq_singleton_iff_unique_mem.mpr ⟨self_mem_edgeSide G u v, fun x hx ↦ ?_⟩
  obtain ⟨p⟩ := mem_edgeSide.mp hx
  cases p with
  | nil => rfl
  | cons hadj _ =>
    obtain ⟨hadj, hne⟩ := deleteEdges_adj.mp hadj
    exact (hne (by rw [h _ hadj]; exact Set.mem_singleton _)).elim

/-- The far end of an edge is off the near side exactly when the edge is a bridge. -/
theorem notMem_edgeSide_iff : v ∉ G.edgeSide u v ↔ G.IsBridge s(u, v) := by
  rw [mem_edgeSide, isBridge_iff]

/-- The far end of a bridge is not on the near side. -/
theorem IsBridge.notMem_edgeSide (h : G.IsBridge s(u, v)) : v ∉ G.edgeSide u v :=
  notMem_edgeSide_iff.mpr h

/-- Two vertices on a common side of `s(u, v)` remain reachable after deleting it. -/
theorem reachable_deleteEdges_of_mem_edgeSide {y : V} (hx : x ∈ G.edgeSide u v)
    (hy : y ∈ G.edgeSide u v) : (G.deleteEdges {s(u, v)}).Reachable x y :=
  (mem_edgeSide.mp hx).symm.trans (mem_edgeSide.mp hy)

/-- The union of the two sides of `s(u, v)` is closed under adjacency: crossing any other edge
stays on the same side, and crossing `s(u, v)` itself lands on one of its ends. -/
private theorem Adj.mem_edgeSide_or_mem_edgeSide {y z : V} (hyz : G.Adj y z)
    (hy : y ∈ G.edgeSide u v ∨ y ∈ G.edgeSide v u) :
    z ∈ G.edgeSide u v ∨ z ∈ G.edgeSide v u := by
  by_cases he : s(y, z) = s(u, v)
  · rcases Sym2.eq_iff.mp he with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact .inr (self_mem_edgeSide G _ u)
    · exact .inl (self_mem_edgeSide G _ v)
  · have hadj : (G.deleteEdges {s(u, v)}).Adj y z := deleteEdges_adj.mpr ⟨hyz, he⟩
    have hadj' : (G.deleteEdges {s(v, u)}).Adj y z := by rwa [Sym2.eq_swap]
    exact hy.imp (fun hy ↦ mem_edgeSide.mpr ((mem_edgeSide.mp hy).trans hadj.reachable))
      (fun hy ↦ mem_edgeSide.mpr ((mem_edgeSide.mp hy).trans hadj'.reachable))

/-- Every vertex reachable from `u` lies on the side of `u` or the side of `v` for `s(u, v)`. -/
theorem Reachable.mem_edgeSide_or_mem_edgeSide (h : G.Reachable u x) :
    x ∈ G.edgeSide u v ∨ x ∈ G.edgeSide v u := by
  obtain ⟨p⟩ := h
  suffices key : ∀ {y z : V} (q : G.Walk y z), (y ∈ G.edgeSide u v ∨ y ∈ G.edgeSide v u) →
      z ∈ G.edgeSide u v ∨ z ∈ G.edgeSide v u from key p (.inl (self_mem_edgeSide G u v))
  intro y z q
  induction q with
  | nil => exact id
  | cons hyz _ ih => exact fun hy ↦ ih (Adj.mem_edgeSide_or_mem_edgeSide hyz hy)

/-- The two sides of a bridge are disjoint. -/
theorem IsBridge.disjoint_edgeSide (h : G.IsBridge s(u, v)) :
    Disjoint (G.edgeSide u v) (G.edgeSide v u) := by
  refine Finset.disjoint_left.mpr fun x hu hv ↦ h.notMem_edgeSide ?_
  rw [mem_edgeSide, Sym2.eq_swap] at hv
  exact mem_edgeSide.mpr ((mem_edgeSide.mp hu).trans hv.symm)

/-- In a preconnected graph, the side of `v` for a bridge `s(u, v)` is the complement of the side
of `u`. -/
theorem IsBridge.compl_edgeSide [DecidableEq V] (hG : G.Preconnected) (h : G.IsBridge s(u, v)) :
    (G.edgeSide u v)ᶜ = G.edgeSide v u := by
  ext x
  rw [Finset.mem_compl]
  refine ⟨fun hx ↦ ((hG u x).mem_edgeSide_or_mem_edgeSide).resolve_left hx, fun hx hu ↦ ?_⟩
  exact Finset.disjoint_left.mp h.disjoint_edgeSide hu hx

namespace Walk

variable {s t : V}

/-- In an acyclic graph, a path starting on the side of `u` uses the edge `s(u, v)` exactly when
it ends off that side. -/
theorem IsPath.mem_edges_iff_notMem_edgeSide (hG : G.IsAcyclic) {p : G.Walk s t} (hp : p.IsPath)
    (hs : s ∈ G.edgeSide u v) : s(u, v) ∈ p.edges ↔ t ∉ G.edgeSide u v := by
  rw [hp.mem_edges_iff_not_reachable_deleteEdges hG, mem_edgeSide]
  exact not_congr ⟨(mem_edgeSide.mp hs).trans, (mem_edgeSide.mp hs).symm.trans⟩

end Walk

end SimpleGraph
