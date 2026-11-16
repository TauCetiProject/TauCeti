/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Matching
public import TauCeti.Combinatorics.Graph.Matching.Basic

/-!
# Matchings under the simple-graph to multigraph conversion

This file identifies matchings of a simple graph in Mathlib's subgraph representation with sets
of matching edge identities in the corresponding multigraph `Graph.ofSimpleGraph H`.  The
canonical subgraph attached to an edge set has exactly the selected edges and their endpoints, so
it contains no artificial isolated vertices.  The identification preserves perfect matchings and
the cardinality of the selected edge set.

## Main declarations

* `SimpleGraph.matchingSubgraph`: the Mathlib subgraph traced by a set of edge identities of
  `Graph.ofSimpleGraph H`.
* `SimpleGraph.matchingEquiv`: the equivalence between multigraph edge-set matchings and Mathlib
  matching subgraphs.
* `SimpleGraph.matchingSubgraph_isPerfectMatching_iff`: the identification preserves perfect
  matchings.
-/

public section

open Set
open scoped Graph

universe u

namespace SimpleGraph

variable {V : Type u} {H : SimpleGraph V}

/-- The subgraph of `H` traced by a set of actual edges of `Graph.ofSimpleGraph H`.  Its vertices
are precisely the endpoints of the selected edges. -/
def matchingSubgraph (H : SimpleGraph V) (M : Set E(Graph.ofSimpleGraph H)) : H.Subgraph where
  verts := {x | ∃ e ∈ M, x ∈ (e : Sym2 V)}
  Adj x y := ∃ e ∈ M, (e : Sym2 V) = s(x, y)
  adj_sub := by
    rintro x y ⟨e, -, he⟩
    rw [← H.mem_edgeSet, ← he]
    exact e.2
  edge_vert := by
    rintro x y ⟨e, heM, he⟩
    exact ⟨e, heM, he.symm ▸ Sym2.mem_mk_left x y⟩
  symm := ⟨by
    rintro x y ⟨e, heM, he⟩
    exact ⟨e, heM, he.trans Sym2.eq_swap⟩⟩

/-- The vertices of the traced subgraph are exactly the endpoints of the selected edges. -/
@[simp]
theorem mem_matchingSubgraph_verts {M : Set E(Graph.ofSimpleGraph H)} {x : V} :
    x ∈ (H.matchingSubgraph M).verts ↔ ∃ e ∈ M, x ∈ (e : Sym2 V) :=
  Iff.rfl

/-- Adjacency in the traced subgraph means that the corresponding edge identity was selected. -/
@[simp]
theorem matchingSubgraph_adj {M : Set E(Graph.ofSimpleGraph H)} {x y : V} :
    (H.matchingSubgraph M).Adj x y ↔ ∃ e ∈ M, (e : Sym2 V) = s(x, y) :=
  Iff.rfl

/-- The edge set of the traced subgraph is the image of the selected actual edge set. -/
@[simp]
theorem edgeSet_matchingSubgraph (M : Set E(Graph.ofSimpleGraph H)) :
    (H.matchingSubgraph M).edgeSet = Subtype.val '' M := by
  ext p
  induction p using Sym2.inductionOn with
  | _ x y => simp [SimpleGraph.Subgraph.mem_edgeSet]

/-- Tracing selected edges does not change their cardinality. -/
theorem ncard_edgeSet_matchingSubgraph (M : Set E(Graph.ofSimpleGraph H)) :
    (H.matchingSubgraph M).edgeSet.ncard = M.ncard := by
  rw [edgeSet_matchingSubgraph, Set.ncard_image_of_injective _ Subtype.val_injective]

/-- The selected actual edges corresponding to the edges of a simple-graph subgraph. -/
def Subgraph.toGraphEdgeSet (S : H.Subgraph) : Set E(Graph.ofSimpleGraph H) :=
  Subtype.val ⁻¹' S.edgeSet

/-- Membership in the selected actual edge set is membership of the underlying unordered pair in
the subgraph edge set. -/
@[simp]
theorem Subgraph.mem_toGraphEdgeSet {S : H.Subgraph} {e : E(Graph.ofSimpleGraph H)} :
    e ∈ S.toGraphEdgeSet ↔ (e : Sym2 V) ∈ S.edgeSet :=
  Iff.rfl

/-- Converting the edges of a subgraph to multigraph edge identities and tracing them recovers its
edge set. -/
theorem Subgraph.edgeSet_matchingSubgraph_toGraphEdgeSet (S : H.Subgraph) :
    (H.matchingSubgraph S.toGraphEdgeSet).edgeSet = S.edgeSet := by
  rw [edgeSet_matchingSubgraph, Subgraph.toGraphEdgeSet, Subtype.image_preimage_coe]
  exact Set.inter_eq_right.mpr S.edgeSet_subset

/-- Converting selected multigraph edge identities to a subgraph and back recovers the selected
edge set. -/
@[simp]
theorem toGraphEdgeSet_matchingSubgraph (M : Set E(Graph.ofSimpleGraph H)) :
    (H.matchingSubgraph M).toGraphEdgeSet = M := by
  rw [Subgraph.toGraphEdgeSet, edgeSet_matchingSubgraph,
    Set.preimage_image_eq _ Subtype.val_injective]

/-- Converting a simple-graph subgraph's edges to multigraph edge identities preserves their
cardinality. -/
@[simp]
theorem Subgraph.ncard_toGraphEdgeSet (S : H.Subgraph) :
    S.toGraphEdgeSet.ncard = S.edgeSet.ncard := by
  rw [← S.edgeSet_matchingSubgraph_toGraphEdgeSet, ncard_edgeSet_matchingSubgraph]

/-- A selected edge set is a multigraph matching exactly when its traced Mathlib subgraph is a
matching. -/
@[simp]
theorem matchingSubgraph_isMatching_iff (M : Set E(Graph.ofSimpleGraph H)) :
    (H.matchingSubgraph M).IsMatching ↔ (Graph.ofSimpleGraph H).IsMatching M := by
  constructor
  · intro hM
    rw [Graph.isMatching_def]
    constructor
    · intro e _ x
      exact (Graph.ofSimpleGraph H).not_isLoopAt e x
    · intro e he f hf hef x hinc
      obtain ⟨y, hey⟩ := ((Graph.inc_ofSimpleGraph H).mp hinc.1).2
      obtain ⟨z, hfz⟩ := ((Graph.inc_ofSimpleGraph H).mp hinc.2).2
      have hexy : (H.matchingSubgraph M).Adj x y := ⟨e, he, hey⟩
      have hfxz : (H.matchingSubgraph M).Adj x z := ⟨f, hf, hfz⟩
      have hyz : y = z := (hM hexy.fst_mem).unique hexy hfxz
      exact hef (Subtype.ext (hey.trans (hyz ▸ hfz.symm)))
  · intro hM x hx
    obtain ⟨e, he, hxe⟩ := hx
    obtain ⟨y, hey⟩ := Sym2.mem_iff_exists.mp hxe
    refine ⟨y, ⟨e, he, hey⟩, ?_⟩
    intro z hz
    obtain ⟨f, hf, hfz⟩ := hz
    have hex : (Graph.ofSimpleGraph H).Inc e x :=
      (Graph.inc_ofSimpleGraph H).mpr ⟨e.2, hxe⟩
    have hfx : (Graph.ofSimpleGraph H).Inc f x :=
      (Graph.inc_ofSimpleGraph H).mpr ⟨f.2, hfz.symm ▸ Sym2.mem_mk_left x z⟩
    have hef : e = f := hM.eq_of_inc he hf hex hfx
    apply Sym2.congr_right.mp
    exact hfz.symm.trans ((congrArg Subtype.val hef).symm.trans hey)

/-- A matching subgraph is recovered by tracing its multigraph edge identities. -/
@[simp]
theorem Subgraph.matchingSubgraph_toGraphEdgeSet (S : H.Subgraph) (hS : S.IsMatching) :
    H.matchingSubgraph S.toGraphEdgeSet = S := by
  apply Subgraph.ext
  · rw [hS.verts_eq_biUnion_edgeSet]
    ext x
    rw [mem_matchingSubgraph_verts]
    constructor
    · rintro ⟨e, heS, hxe⟩
      exact Set.mem_iUnion₂.mpr ⟨e.1, heS, hxe⟩
    · intro hx
      obtain ⟨e, heS, hxe⟩ := Set.mem_iUnion₂.mp hx
      exact ⟨⟨e, S.edgeSet_subset heS⟩, heS, hxe⟩
  · exact (Sym2.fromRel_eq_fromRel_iff_eq _ _).mp S.edgeSet_matchingSubgraph_toGraphEdgeSet

/-- Matchings of `Graph.ofSimpleGraph H`, represented by selected edge identities, are equivalent
to matching subgraphs of `H` in Mathlib's canonical representation. -/
def matchingEquiv (H : SimpleGraph V) :
    {M : Set E(Graph.ofSimpleGraph H) // (Graph.ofSimpleGraph H).IsMatching M} ≃
      {S : H.Subgraph // S.IsMatching} where
  toFun M := ⟨H.matchingSubgraph M,
    (matchingSubgraph_isMatching_iff (H := H) M).2 M.2⟩
  invFun S := ⟨S.1.toGraphEdgeSet,
    (matchingSubgraph_isMatching_iff (H := H) _).1 <| by
      rw [Subgraph.matchingSubgraph_toGraphEdgeSet S.1 S.2]
      exact S.2⟩
  left_inv M := by
    apply Subtype.ext
    exact toGraphEdgeSet_matchingSubgraph M.1
  right_inv S := by
    apply Subtype.ext
    exact Subgraph.matchingSubgraph_toGraphEdgeSet S.1 S.2

/-- The matching equivalence sends a selected edge set to its traced subgraph. -/
@[simp]
theorem matchingEquiv_apply (M :
    {M : Set E(Graph.ofSimpleGraph H) // (Graph.ofSimpleGraph H).IsMatching M}) :
    (matchingEquiv H M : H.Subgraph) = H.matchingSubgraph M :=
  (rfl)

/-- The inverse matching equivalence selects precisely the edges of the Mathlib subgraph. -/
@[simp]
theorem matchingEquiv_symm_apply (S : {S : H.Subgraph // S.IsMatching}) :
    ((matchingEquiv H).symm S : Set E(Graph.ofSimpleGraph H)) = S.1.toGraphEdgeSet :=
  (rfl)

/-- The matching equivalence preserves the number of selected edges. -/
theorem ncard_edgeSet_matchingEquiv (M :
    {M : Set E(Graph.ofSimpleGraph H) // (Graph.ofSimpleGraph H).IsMatching M}) :
    (matchingEquiv H M).1.edgeSet.ncard = M.1.ncard :=
  by rw [matchingEquiv_apply, ncard_edgeSet_matchingSubgraph]

/-- The traced subgraph is a perfect matching exactly when the selected multigraph edge set is a
perfect matching. -/
@[simp]
theorem matchingSubgraph_isPerfectMatching_iff (M : Set E(Graph.ofSimpleGraph H)) :
    (H.matchingSubgraph M).IsPerfectMatching ↔
      (Graph.ofSimpleGraph H).IsPerfectMatching M := by
  rw [SimpleGraph.Subgraph.IsPerfectMatching, Graph.isPerfectMatching_def,
    matchingSubgraph_isMatching_iff]
  refine and_congr_right fun _ ↦ ⟨fun h x ↦ ?_, fun h x ↦ ?_⟩
  · obtain ⟨e, heM, hxe⟩ := h x
    exact ⟨e, heM, (Graph.inc_ofSimpleGraph H).mpr ⟨e.2, hxe⟩⟩
  · obtain ⟨e, heM, hex⟩ := h ⟨x, Set.mem_univ x⟩
    exact ⟨e, heM, ((Graph.inc_ofSimpleGraph H).mp hex).2⟩

/-- Under the matching equivalence, Mathlib perfect matchings are exactly perfect multigraph
edge-set matchings. -/
theorem matchingEquiv_isPerfectMatching_iff (M :
    {M : Set E(Graph.ofSimpleGraph H) // (Graph.ofSimpleGraph H).IsMatching M}) :
    (matchingEquiv H M).1.IsPerfectMatching ↔
      (Graph.ofSimpleGraph H).IsPerfectMatching M :=
  by rw [matchingEquiv_apply, matchingSubgraph_isPerfectMatching_iff]

end SimpleGraph
