/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Convex.Basic
public import TauCeti.Combinatorics.Graph.Serre.Dist

/-!
# Induced subgraphs of Serre graphs

The subgraph `Γ.induce C` induced on a set `C` of vertices of a Serre graph `Γ` is the subgraph
`Γ.subgraph C (Γ.inducedDarts C)`: it has the vertices of `C` and the darts of `Γ` with both
endpoints in `C`. Every reduced path between vertices of a convex set lifts to it. Hence the
subgraph induced on a convex set keeps the distances between its vertices, and it is preconnected
exactly when its vertices are pairwise joined in `Γ`. A subgraph induced in an acyclic graph is
acyclic, so the subgraph induced on a nonempty convex set of vertices of a tree is a tree: the
subtree spanned by the set.

## Main declarations

* `TauCeti.SerreGraph.induce`, `TauCeti.SerreGraph.induceInclusion`: the induced subgraph and its
  inclusion.
* `TauCeti.SerreGraph.IsConvex.exists_induce_path`: reduced paths between vertices of a convex
  set lift to the induced subgraph.
* `TauCeti.SerreGraph.IsConvex.preconnected_induce_iff`,
  `TauCeti.SerreGraph.IsConvex.dist_induce`: connectivity and distances of the subgraph induced
  on a convex set.
* `TauCeti.SerreGraph.IsTree.induce`: the subgraph induced on a nonempty convex set of vertices of
  a tree is a tree.

## References

* J.-P. Serre, *Trees*, Chapter I, §2.2.
-/

public section

universe u v

namespace TauCeti

namespace SerreGraph

variable (Γ : SerreGraph.{u, v})

/-- The subgraph induced on a set of vertices: its vertices are those of the set and its darts
are the darts of `Γ` with both endpoints in the set. -/
abbrev induce (C : Set Γ.V) : SerreGraph.{u, v} :=
  Γ.subgraph C (Γ.inducedDarts C) (fun _ he => (mem_inducedDarts_iff.1 he).1)
    fun _ => rev_mem_inducedDarts_iff.2

/-- The inclusion of an induced subgraph. -/
abbrev induceInclusion (C : Set Γ.V) : (Γ.induce C).Hom Γ :=
  Γ.subgraphInclusion _ _ _ _

variable {Γ} {C : Set Γ.V}

/-- A reduced path of `Γ` between vertices of a convex set `C` lifts to the subgraph induced
on `C`. -/
theorem IsConvex.exists_induce_path (hC : Γ.IsConvex C) {a b : (Γ.induce C).V} (p : Γ.Path a.1 b.1)
    (hp : Path.IsReduced Γ p) :
    ∃ q : (Γ.induce C).Path a b, (Γ.induceInclusion C).toPrefunctor.mapPath q = p :=
  Γ.exists_subgraph_path _ _ _ _ p
    (fun _ he => mem_inducedDarts_iff.2 ⟨hC.src_mem a.2 b.2 hp he, hC.tgt_mem a.2 b.2 hp he⟩)
    a.2 b.2

/-- A subgraph induced on a set of vertices of an acyclic graph is acyclic. -/
theorem IsAcyclic.induce (h : Γ.IsAcyclic) (C : Set Γ.V) : (Γ.induce C).IsAcyclic :=
  h.comap (Γ.induceInclusion C) fun _ _ _ he => Γ.subgraphInclusion_mapE_injective _ _ _ _ he

/-- The subgraph induced on a convex set of vertices is preconnected exactly when any two vertices
of the set are joined by a path of `Γ`. -/
theorem IsConvex.preconnected_induce_iff (hC : Γ.IsConvex C) :
    (Γ.induce C).Preconnected ↔ ∀ a ∈ C, ∀ b ∈ C, Nonempty (Γ.Path a b) := by
  refine ⟨fun h a ha b hb => ?_, fun h => (preconnected_iff _).2 fun a b => ?_⟩
  · obtain ⟨q⟩ := (preconnected_iff _).1 h ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨(Γ.induceInclusion C).toPrefunctor.mapPath q⟩
  · obtain ⟨p⟩ := h a.1 a.2 b.1 b.2
    exact ⟨(hC.exists_induce_path _ (Path.isReduced_reduce Γ p)).choose⟩

/-- The subgraph induced on a nonempty convex set of vertices of a tree is a tree. -/
theorem IsTree.induce (h : Γ.IsTree) (hC : Γ.IsConvex C) (hne : C.Nonempty) : (Γ.induce C).IsTree :=
  (isTree_iff _).2 ⟨(connected_iff _).2 ⟨hne.to_subtype,
    hC.preconnected_induce_iff.2 fun a _ b _ => h.nonempty_path a b⟩, h.isAcyclic.induce C⟩

/-- The distance between two vertices of a convex set in the subgraph it induces is their
distance in the ambient graph. -/
theorem IsConvex.dist_induce (hC : Γ.IsConvex C) (a b : (Γ.induce C).V) :
    (Γ.induce C).dist a b = Γ.dist a.1 b.1 := by
  rcases isEmpty_or_nonempty (Γ.Path a.1 b.1) with hab | hab
  · have : IsEmpty ((Γ.induce C).Path a b) :=
      ⟨fun q => hab.false ((Γ.induceInclusion C).toPrefunctor.mapPath q)⟩
    rw [dist_of_isEmpty hab, dist_of_isEmpty this]
  -- A shortest path is reduced after reduction, so it lifts to the induced subgraph.
  obtain ⟨p, hp⟩ := exists_length_eq_dist hab
  obtain ⟨q, hq⟩ := hC.exists_induce_path _ (Path.isReduced_reduce Γ p)
  refine le_antisymm ?_ ((Γ.induceInclusion C).dist_le ⟨q⟩)
  calc (Γ.induce C).dist a b ≤ q.length := dist_le_length q
    _ = (Path.reduce Γ p).length :=
      (Prefunctor.length_mapPath _ q).symm.trans (congrArg Quiver.Path.length hq)
    _ ≤ Γ.dist a.1 b.1 := hp ▸ Path.length_reduce_le Γ p

end SerreGraph

end TauCeti
