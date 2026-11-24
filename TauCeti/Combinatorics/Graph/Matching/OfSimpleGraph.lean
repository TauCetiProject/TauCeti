/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Matching
public import TauCeti.Combinatorics.Graph.Matching.Basic
public import TauCeti.Combinatorics.Graph.Matching.Coloring

/-!
# Matchings under the simple-graph to multigraph conversion

This file identifies matchings of a simple graph in Mathlib's subgraph representation with sets
of matching edge identities in the corresponding multigraph `Graph.ofSimpleGraph H`.  The
canonical subgraph attached to an edge set has exactly the selected edges and their endpoints, so
it contains no artificial isolated vertices.  The identification preserves perfect matchings and
the cardinality of the selected edge set, and commutes with the edge-colouring equivalence
`SimpleGraph.edgeColoringEquivOfSimpleGraph` on colour classes and matching partitions.

## Main declarations

* `SimpleGraph.matchingSubgraph`: the Mathlib subgraph traced by a set of edge identities of
  `Graph.ofSimpleGraph H`.
* `SimpleGraph.matchingEquiv`: the equivalence between multigraph edge-set matchings and Mathlib
  matching subgraphs.
* `SimpleGraph.matchingSubgraph_isPerfectMatching_iff`: the identification preserves perfect
  matchings.
* `SimpleGraph.colorClass_edgeColoringEquivOfSimpleGraph`,
  `SimpleGraph.colorClassSubgraph_edgeColoringEquivOfSimpleGraph_symm`,
  `SimpleGraph.matchingEquiv_colorClass`, and
  `SimpleGraph.matchingEquiv_symm_colorClassSubgraph`: compatibility of colour classes with
  `SimpleGraph.matchingEquiv` across `SimpleGraph.edgeColoringEquivOfSimpleGraph`.
* `SimpleGraph.edgeColoringEquivOfSimpleGraph_ofMatchings` and
  `SimpleGraph.edgeColoringEquivOfSimpleGraph_symm_ofMatchings`: compatibility of
  `SimpleGraph.EdgeColoring.ofMatchings` and `Graph.EdgeColoring.ofMatchings` with
  `SimpleGraph.edgeColoringEquivOfSimpleGraph`.
-/

public section

open Set
open scoped Graph

universe u w

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
    exact e.property
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
      (Graph.inc_ofSimpleGraph H).mpr ⟨e.property, hxe⟩
    have hfx : (Graph.ofSimpleGraph H).Inc f x :=
      (Graph.inc_ofSimpleGraph H).mpr ⟨f.property, hfz.symm ▸ Sym2.mem_mk_left x z⟩
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
      exact Set.mem_iUnion₂.mpr ⟨e.val, heS, hxe⟩
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
    (matchingSubgraph_isMatching_iff (H := H) M).2 M.property⟩
  invFun S := ⟨S.val.toGraphEdgeSet,
    (matchingSubgraph_isMatching_iff (H := H) _).1 <| by
      rw [Subgraph.matchingSubgraph_toGraphEdgeSet S.val S.property]
      exact S.property⟩
  left_inv M := by
    apply Subtype.ext
    exact toGraphEdgeSet_matchingSubgraph M.val
  right_inv S := by
    apply Subtype.ext
    exact Subgraph.matchingSubgraph_toGraphEdgeSet S.val S.property

/-- The matching equivalence sends a selected edge set to its traced subgraph. -/
@[simp]
theorem matchingEquiv_apply (M :
    {M : Set E(Graph.ofSimpleGraph H) // (Graph.ofSimpleGraph H).IsMatching M}) :
    (matchingEquiv H M : H.Subgraph) = H.matchingSubgraph M :=
  (rfl)

/-- The inverse matching equivalence selects precisely the edges of the Mathlib subgraph. -/
@[simp]
theorem matchingEquiv_symm_apply (S : {S : H.Subgraph // S.IsMatching}) :
    ((matchingEquiv H).symm S : Set E(Graph.ofSimpleGraph H)) = S.val.toGraphEdgeSet :=
  (rfl)

/-- The matching equivalence preserves the number of selected edges. -/
theorem ncard_edgeSet_matchingEquiv (M :
    {M : Set E(Graph.ofSimpleGraph H) // (Graph.ofSimpleGraph H).IsMatching M}) :
    (matchingEquiv H M).val.edgeSet.ncard = M.val.ncard :=
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
    exact ⟨e, heM, (Graph.inc_ofSimpleGraph H).mpr ⟨e.property, hxe⟩⟩
  · obtain ⟨e, heM, hex⟩ := h ⟨x, Set.mem_univ x⟩
    exact ⟨e, heM, ((Graph.inc_ofSimpleGraph H).mp hex).2⟩

/-- Under the matching equivalence, Mathlib perfect matchings are exactly perfect multigraph
edge-set matchings. -/
theorem matchingEquiv_isPerfectMatching_iff (M :
    {M : Set E(Graph.ofSimpleGraph H) // (Graph.ofSimpleGraph H).IsMatching M}) :
    (matchingEquiv H M).val.IsPerfectMatching ↔
      (Graph.ofSimpleGraph H).IsPerfectMatching M :=
  by rw [matchingEquiv_apply, matchingSubgraph_isPerfectMatching_iff]

/-! ### Compatibility with edge-colourings -/

variable {C : Type w}

/-- The `i`-th colour class of `H.edgeColoringEquivOfSimpleGraph C c` is the set of actual edges
selected by `c.colorClassSubgraph i`. -/
@[simp]
theorem colorClass_edgeColoringEquivOfSimpleGraph (c : H.EdgeColoring C) (i : C) :
    (H.edgeColoringEquivOfSimpleGraph C c).colorClass i =
      (c.colorClassSubgraph i).toGraphEdgeSet := by
  ext e
  rw [Subgraph.mem_toGraphEdgeSet, EdgeColoring.edgeSet_colorClassSubgraph]
  simp only [Coloring.colorClass, mem_ofPred_eq, edgeColoringEquivOfSimpleGraph_apply]
  constructor
  · intro he
    exact ⟨Graph.lineGraphOfSimpleGraphIso H e, he, Graph.coe_lineGraphOfSimpleGraphIso_apply H e⟩
  · rintro ⟨e', he', hee'⟩
    have heq : Graph.lineGraphOfSimpleGraphIso H e = e' :=
      Subtype.ext ((Graph.coe_lineGraphOfSimpleGraphIso_apply H e).trans hee'.symm)
    exact (congrArg c heq).trans he'

/-- Transporting a multigraph edge-colouring of `Graph.ofSimpleGraph H` back to `H` sends its
`i`-th colour class to `H.matchingSubgraph (c.colorClass i)`. -/
@[simp]
theorem colorClassSubgraph_edgeColoringEquivOfSimpleGraph_symm
    (c : (Graph.ofSimpleGraph H).EdgeColoring C) (i : C) :
    ((H.edgeColoringEquivOfSimpleGraph C).symm c).colorClassSubgraph i =
      H.matchingSubgraph (c.colorClass i) := by
  refine Subgraph.IsMatching.injOn_edgeSet
    (((H.edgeColoringEquivOfSimpleGraph C).symm c).isMatching_colorClassSubgraph i)
    ((H.matchingSubgraph_isMatching_iff (c.colorClass i)).2 (c.isMatching_colorClass i)) ?_
  ext p
  rw [EdgeColoring.edgeSet_colorClassSubgraph, edgeSet_matchingSubgraph]
  constructor
  · rintro ⟨e, he, rfl⟩
    simp only [Coloring.colorClass, mem_ofPred_eq, edgeColoringEquivOfSimpleGraph_symm_apply] at he
    exact ⟨(Graph.lineGraphOfSimpleGraphIso H).symm e, he,
      Graph.coe_lineGraphOfSimpleGraphIso_symm_apply H e⟩
  · rintro ⟨e, he, rfl⟩
    refine ⟨Graph.lineGraphOfSimpleGraphIso H e, ?_, Graph.coe_lineGraphOfSimpleGraphIso_apply H e⟩
    simp only [Coloring.colorClass, mem_ofPred_eq, edgeColoringEquivOfSimpleGraph_symm_apply,
      RelIso.symm_apply_apply]
    exact he

/-- Under `SimpleGraph.matchingEquiv`, the `i`-th colour class of a multigraph edge-colouring `c`
maps to the `i`-th colour-class subgraph of `(H.edgeColoringEquivOfSimpleGraph C).symm c`. -/
theorem matchingEquiv_colorClass (c : (Graph.ofSimpleGraph H).EdgeColoring C) (i : C) :
    H.matchingEquiv ⟨c.colorClass i, c.isMatching_colorClass i⟩ =
      ⟨((H.edgeColoringEquivOfSimpleGraph C).symm c).colorClassSubgraph i,
        ((H.edgeColoringEquivOfSimpleGraph C).symm c).isMatching_colorClassSubgraph i⟩ :=
  Subtype.ext ((H.matchingEquiv_apply _).trans
    (colorClassSubgraph_edgeColoringEquivOfSimpleGraph_symm c i).symm)

/-- Under `(SimpleGraph.matchingEquiv H).symm`, the `i`-th colour-class subgraph of a simple-graph
edge-colouring `c` maps to the `i`-th colour class of `H.edgeColoringEquivOfSimpleGraph C c`. -/
theorem matchingEquiv_symm_colorClassSubgraph (c : H.EdgeColoring C) (i : C) :
    (H.matchingEquiv).symm ⟨c.colorClassSubgraph i, c.isMatching_colorClassSubgraph i⟩ =
      ⟨(H.edgeColoringEquivOfSimpleGraph C c).colorClass i,
        (H.edgeColoringEquivOfSimpleGraph C c).isMatching_colorClass i⟩ :=
  Subtype.ext ((H.matchingEquiv_symm_apply _).trans
    (colorClass_edgeColoringEquivOfSimpleGraph c i).symm)

/-- Transporting `SimpleGraph.EdgeColoring.ofMatchings` along
`SimpleGraph.edgeColoringEquivOfSimpleGraph` agrees with `Graph.EdgeColoring.ofMatchings` on the
selected actual edge sets. -/
theorem edgeColoringEquivOfSimpleGraph_ofMatchings
    (M : C → H.Subgraph) (hM : ∀ i, (M i).IsMatching)
    (hpart : ∀ e : H.edgeSet, ∃! i, (e : Sym2 V) ∈ (M i).edgeSet)
    (hpart' : ∀ e : E(Graph.ofSimpleGraph H), ∃! i, e ∈ (M i).toGraphEdgeSet) :
    H.edgeColoringEquivOfSimpleGraph C (EdgeColoring.ofMatchings M hM hpart) =
      Graph.EdgeColoring.ofMatchings (fun i ↦ (M i).toGraphEdgeSet)
        (fun i ↦ by
          rw [← H.matchingSubgraph_isMatching_iff, (M i).matchingSubgraph_toGraphEdgeSet (hM i)]
          exact hM i) hpart' := by
  ext e
  symm
  rw [Graph.EdgeColoring.ofMatchings_apply_eq_iff, edgeColoringEquivOfSimpleGraph_apply,
    Subgraph.mem_toGraphEdgeSet, ← Graph.coe_lineGraphOfSimpleGraphIso_apply H e]
  exact (EdgeColoring.ofMatchings_apply_eq_iff M hM hpart _ _).1 rfl

/-- Transporting `Graph.EdgeColoring.ofMatchings` along
`(SimpleGraph.edgeColoringEquivOfSimpleGraph H C).symm` agrees with
`SimpleGraph.EdgeColoring.ofMatchings` on the traced matching subgraphs. -/
theorem edgeColoringEquivOfSimpleGraph_symm_ofMatchings
    (M : C → Set E(Graph.ofSimpleGraph H))
    (hM : ∀ i, (Graph.ofSimpleGraph H).IsMatching (M i))
    (hpart : ∀ e, ∃! i, e ∈ M i)
    (hpart' : ∀ e : H.edgeSet, ∃! i, (e : Sym2 V) ∈ (H.matchingSubgraph (M i)).edgeSet) :
    (H.edgeColoringEquivOfSimpleGraph C).symm (Graph.EdgeColoring.ofMatchings M hM hpart) =
      EdgeColoring.ofMatchings (fun i ↦ H.matchingSubgraph (M i))
        (fun i ↦ (H.matchingSubgraph_isMatching_iff (M i)).2 (hM i)) hpart' := by
  ext e
  symm
  rw [EdgeColoring.ofMatchings_apply_eq_iff, edgeColoringEquivOfSimpleGraph_symm_apply,
    edgeSet_matchingSubgraph]
  exact ⟨(Graph.lineGraphOfSimpleGraphIso H).symm e,
    (Graph.EdgeColoring.ofMatchings_apply_eq_iff M hM hpart _ _).1 rfl,
    Graph.coe_lineGraphOfSimpleGraphIso_symm_apply H e⟩

end SimpleGraph
