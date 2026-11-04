/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Data.Fintype.Card
public import TauCeti.Data.Finset.Laminar
import TauCeti.Data.Sym.Sym2

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

The side of `u` can also be recognized without walks: in a preconnected graph it is the unique set
containing `u` but not `v` that no other edge leaves (`SimpleGraph.edgeSide_eq_of_forall_adj`).
This identifies the sides of a tree after local changes to its edges. In a tree, the bipartitions
given by the sides of two edges never cross (`SimpleGraph.IsTree.not_crosses_edgeSide`), so the
edges of a tree determine a non-crossing family of cuts.
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

/-- An edge other than `s(u, v)` has both of its ends on the side of `u`, or neither. -/
theorem Adj.mem_edgeSide_iff {y z : V} (h : G.Adj y z) (he : s(y, z) ≠ s(u, v)) :
    y ∈ G.edgeSide u v ↔ z ∈ G.edgeSide u v := by
  have hadj : (G.deleteEdges {s(u, v)}).Adj y z := deleteEdges_adj.mpr ⟨h, he⟩
  exact ⟨fun hy ↦ mem_edgeSide.mpr ((mem_edgeSide.mp hy).trans hadj.reachable),
    fun hz ↦ mem_edgeSide.mpr ((mem_edgeSide.mp hz).trans hadj.reachable.symm)⟩

/-- An edge whose ends both differ from `v` has both ends on the side of `u` for `s(u, v)`, or
neither. -/
theorem Adj.mem_edgeSide_iff_of_ne {y z : V} (h : G.Adj y z) (hy : y ≠ v) (hz : z ≠ v) :
    y ∈ G.edgeSide u v ↔ z ∈ G.edgeSide u v :=
  h.mem_edgeSide_iff <| (Sym2.ne_of_mem_notMem (Sym2.mem_mk_right u v) <| by
    simpa only [Sym2.mem_iff, not_or] using ⟨hy.symm, hz.symm⟩).symm

/-- The side of `u` for `s(u, v)` is contained in every set that contains `u` and that no edge
other than `s(u, v)` leaves. -/
theorem edgeSide_subset {S : Finset V} (hu : u ∈ S)
    (hS : ∀ ⦃y z : V⦄, G.Adj y z → s(y, z) ≠ s(u, v) → y ∈ S → z ∈ S) : G.edgeSide u v ⊆ S := by
  intro x hx
  have h := (reachable_iff_reflTransGen _ _).mp (mem_edgeSide.mp hx)
  clear hx
  induction h with
  | refl => exact hu
  | tail _ hyz ih =>
    obtain ⟨hyz, hne⟩ := deleteEdges_adj.mp hyz
    exact hS hyz hne ih

/-- In a preconnected graph, a set containing `u` but not `v`, such that no edge other than
`s(u, v)` has exactly one end in it, is the side of `u` for `s(u, v)`. -/
theorem edgeSide_eq_of_forall_adj (hG : G.Preconnected) {S : Finset V} (hu : u ∈ S) (hv : v ∉ S)
    (hS : ∀ ⦃y z : V⦄, G.Adj y z → s(y, z) ≠ s(u, v) → (y ∈ S ↔ z ∈ S)) :
    G.edgeSide u v = S := by
  classical
  refine (edgeSide_subset hu fun _ _ hyz hne ↦ (hS hyz hne).mp).antisymm fun x hx ↦ ?_
  refine ((hG u x).mem_edgeSide_or_mem_edgeSide (v := v)).resolve_right fun hxv ↦ ?_
  -- The side of `v` stays outside `S`, since only `s(u, v)` leaves `S`.
  have hsub : G.edgeSide v u ⊆ Sᶜ := by
    refine edgeSide_subset (by simpa using hv) fun y z hyz hne hy ↦ ?_
    rw [Sym2.eq_swap (a := v)] at hne
    exact Finset.mem_compl.mpr fun hz ↦ Finset.mem_compl.mp hy ((hS hyz hne).mpr hz)
  simpa [hx] using hsub hxv

/-- If `s(y, r)` is a bridge, every other neighbour of `r` lies off the side of `y`. -/
theorem IsBridge.notMem_edgeSide_of_adj {r y z : V} (h : G.IsBridge s(y, r)) (hz : G.Adj r z)
    (hzy : z ≠ y) : z ∉ G.edgeSide y r := by
  have hne : s(z, r) ≠ s(r, y) :=
    Sym2.ne_of_mem_notMem (Sym2.mem_mk_left z r) <| by
      simpa only [Sym2.mem_iff, not_or] using ⟨hz.ne.symm, hzy⟩
  exact fun hz' ↦ Finset.disjoint_left.mp h.disjoint_edgeSide hz'
    ((hz.symm.mem_edgeSide_iff hne).mpr (self_mem_edgeSide G r y))

/-- Every vertex `z ≠ r` reachable from `r` lies on the side of some neighbour `y` of `r` for the
edge `s(y, r)`. -/
theorem Reachable.exists_adj_mem_edgeSide {r z : V} (h : G.Reachable r z) (hz : z ≠ r) :
    ∃ y, G.Adj r y ∧ z ∈ G.edgeSide y r := by
  have hr := (reachable_iff_reflTransGen r z).mp h
  clear h
  induction hr with
  | refl => exact absurd rfl hz
  | @tail a b _ hab ih =>
    by_cases ha : a = r
    · exact ⟨b, ha ▸ hab, self_mem_edgeSide G b r⟩
    obtain ⟨y, hy, hay⟩ := ih ha
    exact ⟨y, hy, (hab.mem_edgeSide_iff_of_ne ha hz).mp hay⟩

/-- In a tree, the sides of two edges never cross: the bipartitions obtained by deleting tree
edges form a non-crossing family. -/
theorem IsTree.not_crosses_edgeSide (hG : G.IsTree) {a b c d : V} (hab : G.Adj a b)
    (hcd : G.Adj c d) : ¬(G.edgeSide a b).Crosses (G.edgeSide c d) := by
  classical
  have hbr := isAcyclic_iff_forall_adj_isBridge.mp hG.isAcyclic
  have hcompl {y z : V} (h : G.Adj y z) : (G.edgeSide y z)ᶜ = G.edgeSide z y :=
    (hbr h).compl_edgeSide hG.connected.preconnected
  -- If the second edge lies on the side of `a` and the first on the side of `c`, the two sides
  -- cover every vertex.
  have key {a b c d : V} (hab : G.Adj a b) (hcd : G.Adj c d) (hne : s(a, b) ≠ s(c, d))
      (hc : c ∈ G.edgeSide a b) (ha : a ∈ G.edgeSide c d) :
      ¬(G.edgeSide a b).Crosses (G.edgeSide c d) := by
    have hd : d ∈ G.edgeSide a b := (hcd.mem_edgeSide_iff hne.symm).mp hc
    have hb : b ∈ G.edgeSide c d := (hab.mem_edgeSide_iff hne).mp ha
    have hsub : G.edgeSide b a ⊆ G.edgeSide a b ∪ G.edgeSide c d := by
      refine edgeSide_subset (Finset.mem_union_right _ hb) fun y z hyz hne' hy ↦ ?_
      rw [Sym2.eq_swap (a := b)] at hne'
      rcases Finset.mem_union.mp hy with hy | hy
      · exact Finset.mem_union_left _ ((hyz.mem_edgeSide_iff hne').mp hy)
      · by_cases hyab : y ∈ G.edgeSide a b
        · exact Finset.mem_union_left _ ((hyz.mem_edgeSide_iff hne').mp hyab)
        · have hne'' : s(y, z) ≠ s(c, d) := by
            rintro h
            rcases Sym2.eq_iff.mp h with ⟨rfl, -⟩ | ⟨rfl, -⟩
            exacts [hyab hc, hyab hd]
          exact Finset.mem_union_right _ ((hyz.mem_edgeSide_iff hne'').mp hy)
    intro h
    obtain ⟨-, -, -, x, hxab, hxcd⟩ := Finset.crosses_def.mp h
    rcases (hG.connected.preconnected a x).mem_edgeSide_or_mem_edgeSide (v := b) with hx | hx
    · exact hxab hx
    · rcases Finset.mem_union.mp (hsub hx) with hx | hx
      exacts [hxab hx, hxcd hx]
  by_cases hsame : s(a, b) = s(c, d)
  · -- The two sides are equal or complementary.
    rcases Sym2.eq_iff.mp hsame with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · intro h
      obtain ⟨-, ⟨x, hx, hx'⟩, -⟩ := Finset.crosses_def.mp h
      exact hx' hx
    · intro h
      obtain ⟨⟨x, hx, hx'⟩, -⟩ := Finset.crosses_def.mp h
      exact Finset.disjoint_left.mp (hbr hab).disjoint_edgeSide hx hx'
  have hne₁ : s(a, b) ≠ s(d, c) := by rwa [Sym2.eq_swap (a := d)]
  have hne₂ : s(b, a) ≠ s(c, d) := by rwa [Sym2.eq_swap (a := b)]
  have hne₃ : s(b, a) ≠ s(d, c) := by rwa [Sym2.eq_swap (a := b), Sym2.eq_swap (a := d)]
  rcases (hG.connected.preconnected a c).mem_edgeSide_or_mem_edgeSide (v := b) with hc | hc <;>
    rcases (hG.connected.preconnected c a).mem_edgeSide_or_mem_edgeSide (v := d) with ha | ha
  · exact key hab hcd hsame hc ha
  · have hd : d ∈ G.edgeSide a b := (hcd.mem_edgeSide_iff (Ne.symm hsame)).mp hc
    rw [← Finset.crosses_compl_right, hcompl hcd]
    exact key hab hcd.symm hne₁ hd ha
  · have hb : b ∈ G.edgeSide c d := (hab.mem_edgeSide_iff hsame).mp ha
    rw [← Finset.crosses_compl_left, hcompl hab]
    exact key hab.symm hcd hne₂ hc hb
  · have hd : d ∈ G.edgeSide b a := (hcd.mem_edgeSide_iff (Ne.symm hne₂)).mp hc
    have hb : b ∈ G.edgeSide d c := (hab.mem_edgeSide_iff hne₁).mp ha
    rw [← Finset.crosses_compl_left, ← Finset.crosses_compl_right, hcompl hab, hcompl hcd]
    exact key hab.symm hcd.symm hne₃ hd hb

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
