/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Connectivity.Component
public import TauCeti.Combinatorics.Graph.Connectivity.Walk.Maps
public import TauCeti.Combinatorics.SimpleGraph.Connectivity.VertexConnectivity

/-!
# Vertex connectivity of multigraphs

Vertex connectivity ignores loops and parallel edges. We use the vertex-connectivity predicates
and numerical invariant of `G.toSimpleGraph`, whose carrier consists of the actual vertices of
`G`, not its ambient vertex type. The deletion characterization relates these predicates to
native multigraph reachability after deleting ambient vertex sets. Thus witnesses and separators
can be expressed with the original vertices and edges even when the ambient types are infinite.

The numerical invariant records exactly the natural thresholds on a nonempty actual vertex set.
It is zero on empty and singleton actual vertex sets, and finite whenever the actual vertex set
is finite. The simple-graph comparison uses Mathlib's `Graph.toSimpleGraphOfSimpleGraphIso`.

The conventions follow R. Diestel, *Graph Theory*, 5th ed., Section 1.4, and the existing
`SimpleGraph.IsVertexConnected` and `SimpleGraph.vertexConnectivity` interfaces.
-/

public section

open Set

universe u v

namespace Graph

variable {α : Type u} {β : Type v} {G H : Graph α β} {k l : ℕ}

/-- Actual vertices are `k`-vertex-reachable when deletion of fewer than `k` other vertices
cannot separate them. Loops and parallel edges do not affect this predicate. -/
abbrev IsVertexReachable (G : Graph α β) (k : ℕ) (s t : V(G)) : Prop :=
  G.toSimpleGraph.IsVertexReachable k s t

/-- A multigraph is `k`-vertex-connected when its underlying simple graph is. In particular,
there must be more than `k` actual vertices. -/
abbrev IsVertexConnected (G : Graph α β) (k : ℕ) : Prop :=
  G.toSimpleGraph.IsVertexConnected k

/-- The vertex connectivity of a multigraph is that of its underlying simple graph. -/
noncomputable abbrev vertexConnectivity (G : Graph α β) : ℕ∞ :=
  G.toSimpleGraph.vertexConnectivity

/-- Vertex reachability can be tested by native vertex deletion. Deleted sets may contain
points outside the actual vertex set; those points cannot obstruct reachability. -/
theorem isVertexReachable_iff {s t : V(G)} : G.IsVertexReachable k s t ↔
    ∀ ⦃X : Set α⦄, X.encard < k → (s : α) ∉ X → (t : α) ∉ X →
      (G.deleteVerts X).Reachable s t := by
  rw [IsVertexReachable, SimpleGraph.isVertexReachable_def]
  refine ⟨fun h X hX hs ht ↦ ?_, fun h X hX hs ht ↦ ?_⟩
  · -- The bridge's set builder is definitionally the complement of the preimage of `X`;
    -- its subtype endpoints retain `s` and `t`.
    exact (toSimpleGraph_reachable_induce_compl_iff hs ht).mp
      (h ((encard_preimage_val_le_encard_right V(G) X).trans_lt hX)
        (by simpa using hs) (by simpa using ht))
  · have hs' : (s : α) ∉ Subtype.val '' X := by simpa using hs
    have ht' : (t : α) ∉ Subtype.val '' X := by simpa using ht
    have hr := (toSimpleGraph_reachable_induce_compl_iff hs' ht').mpr
      (h (by simpa [Subtype.val_injective.encard_image] using hX) hs' ht')
    have hsub : {v : V(G) | (v : α) ∉ Subtype.val '' X} ⊆ Xᶜ := by
      intro v hv
      simpa using hv
    -- The induced inclusion keeps the underlying vertices, so its endpoints are
    -- definitionally `⟨s, hs⟩` and `⟨t, ht⟩`; only their membership proofs change.
    exact hr.map (G.toSimpleGraph.induceHomOfLE hsub).toHom

/-- Every pair of actual vertices is `0`-vertex-reachable. -/
protected theorem IsVertexReachable.zero {s t : V(G)} : G.IsVertexReachable 0 s t := by
  simpa only [IsVertexReachable, Nat.cast_zero] using
    (SimpleGraph.IsVertexReachable.zero : G.toSimpleGraph.IsVertexReachable 0 s t)

/-- Vertex reachability is antitone in its threshold. -/
@[gcongr]
theorem IsVertexReachable.anti (hkl : k ≤ l) {s t : V(G)}
    (h : G.IsVertexReachable l s t) : G.IsVertexReachable k s t :=
  SimpleGraph.IsVertexReachable.anti (Nat.cast_le.mpr hkl) h

/-- The threshold `1` for vertex reachability is native multigraph reachability. -/
@[simp]
theorem isVertexReachable_one {s t : V(G)} :
    G.IsVertexReachable 1 s t ↔ G.Reachable s t :=
  SimpleGraph.isVertexReachable_one.trans toSimpleGraph_reachable_iff

/-- A positive vertex-reachability threshold implies native multigraph reachability. -/
theorem IsVertexReachable.reachable (hk : k ≠ 0) {s t : V(G)}
    (h : G.IsVertexReachable k s t) : G.Reachable s t :=
  isVertexReachable_one.mp (h.anti (Nat.one_le_iff_ne_zero.mpr hk))

@[simp]
theorem isVertexConnected_zero : G.IsVertexConnected 0 ↔ V(G).Nonempty :=
  SimpleGraph.isVertexConnected_zero.trans Set.nonempty_coe_sort

/-- A multigraph is `1`-vertex-connected exactly when it is connected and has at least two
actual vertices. In particular, a singleton with any number of loops is not 1-connected. -/
@[simp]
theorem isVertexConnected_one : G.IsVertexConnected 1 ↔ G.Connected ∧ V(G).Nontrivial := by
  rw [IsVertexConnected, Nat.cast_one, SimpleGraph.isVertexConnected_one,
    ← connected_iff_toSimpleGraph_connected, Set.nontrivial_coe_sort]

/-- A positive vertex-connectivity threshold implies native multigraph connectedness. -/
theorem IsVertexConnected.connected (hk : k ≠ 0) (h : G.IsVertexConnected k) :
    G.Connected :=
  (isVertexConnected_one.mp (SimpleGraph.IsVertexConnected.anti
    (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk) h)).1

/-- Vertex connectivity is antitone in its threshold. -/
@[gcongr]
theorem IsVertexConnected.anti (hkl : k ≤ l) (h : G.IsVertexConnected l) :
    G.IsVertexConnected k :=
  SimpleGraph.IsVertexConnected.anti (Nat.cast_le.mpr hkl) h

/-- Adding edges preserves local vertex reachability, with endpoints included into the larger
graph's actual vertex set. -/
theorem IsVertexReachable.mono (hGH : G ≤ H) {s t : V(G)}
    (h : G.IsVertexReachable k s t) :
    H.IsVertexReachable k ⟨s, hGH.vertexSet_mono s.property⟩
      ⟨t, hGH.vertexSet_mono t.property⟩ := by
  have hf (v : V(G)) : toSimpleGraphHomOfLE hGH v =
      ⟨v, hGH.vertexSet_mono v.property⟩ :=
    Subtype.ext (coe_toSimpleGraphHomOfLE_apply hGH v)
  simpa only [hf] using h.map (toSimpleGraphHomOfLE hGH) (fun _ _ he ↦
    Subtype.ext (by
      simpa only [coe_toSimpleGraphHomOfLE_apply] using congrArg Subtype.val he))

/-- Global vertex connectivity is monotone under graph inclusion with the same actual vertices.
Allowing additional isolated vertices would make this statement false. -/
theorem IsVertexConnected.mono (hGH : G ≤ H) (hV : V(G) = V(H))
    (h : G.IsVertexConnected k) : H.IsVertexConnected k := by
  rw [IsVertexConnected, SimpleGraph.isVertexConnected_def] at h ⊢
  refine ⟨?_, fun s t ↦ ?_⟩
  · simpa only [← hV] using h.1
  · have hs : (s : α) ∈ V(G) := hV.symm ▸ s.property
    have ht : (t : α) ∈ V(G) := hV.symm ▸ t.property
    exact IsVertexReachable.mono hGH (h.2 ⟨s, hs⟩ ⟨t, ht⟩)

/-- On a nonempty actual vertex set, the numerical invariant records exactly the thresholds at
which the multigraph is vertex-connected. No finiteness assumption is needed. -/
theorem isVertexConnected_iff_le_vertexConnectivity [Nonempty V(G)] (k : ℕ) :
    G.IsVertexConnected k ↔ k ≤ G.vertexConnectivity :=
  SimpleGraph.isVertexConnected_iff_le_vertexConnectivity k

/-- Vertex connectivity is monotone when edges are added without changing the actual vertices. -/
@[gcongr]
theorem vertexConnectivity_mono (hGH : G ≤ H) (hV : V(G) = V(H)) :
    G.vertexConnectivity ≤ H.vertexConnectivity := by
  rw [vertexConnectivity, vertexConnectivity, SimpleGraph.vertexConnectivity_def,
    SimpleGraph.vertexConnectivity_def]
  exact iSup_mono fun _ ↦ iSup_mono' fun hk ↦
    ⟨IsVertexConnected.mono hGH hV hk, le_rfl⟩

/-- A multigraph with finitely many actual vertices has finite vertex connectivity, even when
its ambient types or its actual edge set are infinite. -/
theorem vertexConnectivity_ne_top [Finite V(G)] : G.vertexConnectivity ≠ ⊤ :=
  SimpleGraph.vertexConnectivity_ne_top

/-- A multigraph on at most one actual vertex has vertex connectivity zero, independently of
its loops and edge multiplicities. -/
theorem vertexConnectivity_of_subsingleton [Subsingleton V(G)] : G.vertexConnectivity = 0 :=
  SimpleGraph.vertexConnectivity_of_subsingleton

/-- Local vertex reachability agrees with the simple-graph predicate on
`Graph.ofSimpleGraph`. -/
@[simp]
theorem isVertexReachable_ofSimpleGraph_iff (H : SimpleGraph α) (k : ℕ)
    (s t : V(Graph.ofSimpleGraph H)) :
    (Graph.ofSimpleGraph H).IsVertexReachable k s t ↔ H.IsVertexReachable k s t := by
  rw [isVertexReachable_iff, SimpleGraph.isVertexReachable_iff_exists_walk]
  constructor
  · intro h X hX hs ht
    obtain ⟨p, -, hp⟩ := reachable_deleteVerts_iff_exists_walk.mp (h hX hs ht)
    exact ⟨p.toSimpleGraph, by simpa only [Walk.support_toSimpleGraph] using hp⟩
  · intro h X hX hs ht
    obtain ⟨p, hp⟩ := h hX hs ht
    exact reachable_deleteVerts_iff_exists_walk.mpr
      ⟨p.toGraph, by simp, by simpa only [SimpleGraph.Walk.support_toGraph] using hp⟩

/-- The vertex-connectivity predicates agree with the simple-graph predicates on
`Graph.ofSimpleGraph`. -/
@[simp]
theorem isVertexConnected_ofSimpleGraph_iff (H : SimpleGraph α) (k : ℕ) :
    (Graph.ofSimpleGraph H).IsVertexConnected k ↔ H.IsVertexConnected k :=
  (toSimpleGraphOfSimpleGraphIso H).isVertexConnected_iff.symm

/-- Passing from a simple graph to a multigraph preserves numerical vertex connectivity,
including the empty graph. -/
@[simp]
theorem vertexConnectivity_ofSimpleGraph (H : SimpleGraph α) :
    (Graph.ofSimpleGraph H).vertexConnectivity = H.vertexConnectivity :=
  (toSimpleGraphOfSimpleGraphIso H).vertexConnectivity_eq.symm

end Graph
