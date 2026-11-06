/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Incidence

/-!
# Matchings in multigraphs

A matching in a multigraph is a set of actual edge identities with no loops and no two distinct
members incident to a common vertex.  Thus parallel edges remain distinct choices, but at most one
of them can belong to a matching.  A perfect matching is incident to every actual vertex.

The graph `Graph.matchingSubgraph G M` has exactly the edges selected by `M` and exactly their
endpoints as vertices.  It has no isolated vertices, and `Graph.IsMatching` is equivalent to this
subgraph being loopless with exactly one incident edge at every one of its vertices.  Perfectness
is equivalently the assertion that this canonical subgraph is spanning.  This connects the
edge-set representation, convenient for deleting and partitioning multigraph edges, with the
subgraph viewpoint used by Mathlib for simple-graph matchings.

## Main definitions

* `Graph.IsMatching G M`: the actual edges in `M` form a matching.
* `Graph.IsPerfectMatching G M`: `M` is a matching incident to every actual vertex.
* `Graph.matchingSubgraph G M`: the subgraph containing precisely the selected edges and their
  endpoints.
-/

public section

open Set
open scoped Graph

universe u v

namespace Graph

variable {α : Type u} {β : Type v} {G : Graph α β} {M N : Set E(G)}

/-- A set of actual multigraph edges is a matching when it contains no loop and no two distinct
edges in it have a common incident vertex. -/
def IsMatching (G : Graph α β) (M : Set E(G)) : Prop :=
  (∀ e ∈ M, ∀ x, ¬G.IsLoopAt e x) ∧
    ∀ e ∈ M, ∀ f ∈ M, e ≠ f → ∀ x, ¬(G.Inc e x ∧ G.Inc f x)

/-- A perfect matching is a matching incident to every actual vertex. -/
def IsPerfectMatching (G : Graph α β) (M : Set E(G)) : Prop :=
  G.IsMatching M ∧ ∀ x : V(G), ∃ e ∈ M, G.Inc e x

theorem isMatching_def :
    G.IsMatching M ↔
      (∀ e ∈ M, ∀ x, ¬G.IsLoopAt e x) ∧
        ∀ e ∈ M, ∀ f ∈ M, e ≠ f → ∀ x, ¬(G.Inc e x ∧ G.Inc f x) :=
  Iff.rfl

theorem isPerfectMatching_def :
    G.IsPerfectMatching M ↔ G.IsMatching M ∧ ∀ x : V(G), ∃ e ∈ M, G.Inc e x :=
  Iff.rfl

/-- The empty set of edges is a matching. -/
@[simp]
theorem isMatching_empty (G : Graph α β) : G.IsMatching ∅ := by
  simp [IsMatching]

/-- A subset of a matching is a matching. -/
theorem IsMatching.mono (hM : G.IsMatching M) (hNM : N ⊆ M) : G.IsMatching N := by
  refine ⟨fun e he ↦ hM.1 e (hNM he), fun e he f hf ↦ ?_⟩
  exact hM.2 e (hNM he) f (hNM hf)

/-- Every edge in a matching is a nonloop edge. -/
theorem IsMatching.not_isLoopAt (hM : G.IsMatching M) {e : E(G)} (he : e ∈ M) (x : α) :
    ¬G.IsLoopAt e x :=
  hM.1 e he x

/-- Two edges of a matching incident to the same vertex are equal. -/
theorem IsMatching.eq_of_inc (hM : G.IsMatching M) {e f : E(G)} (he : e ∈ M) (hf : f ∈ M)
    {x : α} (hex : G.Inc e x) (hfx : G.Inc f x) : e = f := by
  by_contra hef
  exact hM.2 e he f hf hef x ⟨hex, hfx⟩

/-- At most one edge of a matching is incident to any given vertex. -/
theorem IsMatching.existsUnique_of_exists_inc (hM : G.IsMatching M) {x : α}
    (h : ∃ e ∈ M, G.Inc e x) : ∃! e, e ∈ M ∧ G.Inc e x := by
  obtain ⟨e, he, hex⟩ := h
  exact ⟨e, ⟨he, hex⟩, fun f hf ↦ hM.eq_of_inc hf.1 he hf.2 hex⟩

/-- In a perfect matching, every actual vertex is incident to a unique selected edge. -/
theorem IsPerfectMatching.existsUnique_inc (hM : G.IsPerfectMatching M) (x : V(G)) :
    ∃! e, e ∈ M ∧ G.Inc e x :=
  hM.1.existsUnique_of_exists_inc (hM.2 x)

/-- A matching is perfect exactly when every actual vertex is incident to a unique selected edge. -/
theorem IsMatching.isPerfectMatching_iff (hM : G.IsMatching M) :
    G.IsPerfectMatching M ↔ ∀ x : V(G), ∃! e, e ∈ M ∧ G.Inc e x := by
  refine ⟨fun h x ↦ h.existsUnique_inc x, fun h ↦ ⟨hM, fun x ↦ ?_⟩⟩
  obtain ⟨e, he, -⟩ := h x
  exact ⟨e, he.1, he.2⟩

/-- The vertices incident to a selected set of actual edges. -/
def matchingSupport (G : Graph α β) (M : Set E(G)) : Set α :=
  {x | ∃ e ∈ M, G.Inc e x}

@[simp]
theorem mem_matchingSupport {x : α} : x ∈ G.matchingSupport M ↔ ∃ e ∈ M, G.Inc e x :=
  Iff.rfl

/-- Every endpoint of a selected actual edge is an actual vertex. -/
theorem matchingSupport_subset_vertexSet : G.matchingSupport M ⊆ V(G) := by
  rintro x ⟨e, -, hex⟩
  exact hex.vertex_mem

/-- Enlarging the selected edge set enlarges its vertex support. -/
theorem matchingSupport_mono (hMN : M ⊆ N) : G.matchingSupport M ⊆ G.matchingSupport N := by
  rintro x ⟨e, he, hex⟩
  exact ⟨e, hMN he, hex⟩

/-- The empty edge set has empty vertex support. -/
@[simp]
theorem matchingSupport_empty (G : Graph α β) : G.matchingSupport ∅ = ∅ := by
  ext x
  simp

/-- The subgraph whose edges are exactly `M` and whose vertices are exactly their endpoints. -/
def matchingSubgraph (G : Graph α β) (M : Set E(G)) : Graph α β where
  vertexSet := G.matchingSupport M
  edgeSet := Subtype.val '' M
  IsLink e x y := ∃ he : e ∈ E(G), (⟨e, he⟩ : E(G)) ∈ M ∧ G.IsLink e x y
  isLink_symm e he := ⟨by
    rintro x y ⟨heG, heM, hxy⟩
    exact ⟨heG, heM, hxy.symm⟩⟩
  eq_or_eq_of_isLink_of_isLink _ _ _ _ _ h h' := h.2.2.left_eq_or_eq h'.2.2
  edge_mem_iff_exists_isLink e := by
    constructor
    · rintro ⟨f, hfM, rfl⟩
      obtain ⟨x, y, hxy⟩ := G.exists_isLink_of_mem_edgeSet f.2
      exact ⟨x, y, f.2, hfM, hxy⟩
    · rintro ⟨x, y, heG, heM, -⟩
      exact ⟨⟨e, heG⟩, heM, rfl⟩
  left_mem_of_isLink := by
    rintro e x y ⟨heG, heM, hxy⟩
    exact ⟨⟨e, heG⟩, heM, hxy.inc_left⟩

@[simp]
theorem vertexSet_matchingSubgraph : V(G.matchingSubgraph M) = G.matchingSupport M :=
  by simp only [matchingSubgraph]

@[simp]
theorem edgeSet_matchingSubgraph : E(G.matchingSubgraph M) = Subtype.val '' M :=
  by simp only [matchingSubgraph]

@[simp]
theorem matchingSubgraph_isLink {e : β} {x y : α} :
    (G.matchingSubgraph M).IsLink e x y ↔
      ∃ he : e ∈ E(G), (⟨e, he⟩ : E(G)) ∈ M ∧ G.IsLink e x y :=
  by simp only [matchingSubgraph]

/-- Incidence in the canonical subgraph is incidence in `G` by a selected edge. -/
@[simp]
theorem matchingSubgraph_inc {e : β} {x : α} :
    (G.matchingSubgraph M).Inc e x ↔
      ∃ he : e ∈ E(G), (⟨e, he⟩ : E(G)) ∈ M ∧ G.Inc e x := by
  constructor
  · rintro ⟨y, heG, heM, hxy⟩
    exact ⟨heG, heM, hxy.inc_left⟩
  · rintro ⟨heG, heM, y, hxy⟩
    exact ⟨y, heG, heM, hxy⟩

/-- A loop of the canonical subgraph is precisely a selected loop of `G`. -/
@[simp]
theorem matchingSubgraph_isLoopAt {e : β} {x : α} :
    (G.matchingSubgraph M).IsLoopAt e x ↔
      ∃ he : e ∈ E(G), (⟨e, he⟩ : E(G)) ∈ M ∧ G.IsLoopAt e x :=
  matchingSubgraph_isLink

/-- The canonical subgraph construction remembers the selected set of actual edges. -/
theorem matchingSubgraph_injective (G : Graph α β) :
    Function.Injective (G.matchingSubgraph : Set E(G) → Graph α β) := by
  intro M N h
  apply Subtype.val_injective.image_injective
  simpa only [edgeSet_matchingSubgraph] using congrArg Graph.edgeSet h

/-- The canonical graph of selected edges is a subgraph of the original graph. -/
theorem matchingSubgraph_le (G : Graph α β) (M : Set E(G)) : G.matchingSubgraph M ≤ G := by
  refine ⟨fun x hx ↦ ?_, fun e x y h ↦ h.2.2⟩
  obtain ⟨e, -, hex⟩ := hx
  exact hex.vertex_mem

/-- Enlarging the selected edge set enlarges its canonical subgraph. -/
theorem matchingSubgraph_mono (hMN : M ⊆ N) : G.matchingSubgraph M ≤ G.matchingSubgraph N := by
  refine ⟨matchingSupport_mono hMN, fun e x y h ↦ ?_⟩
  obtain ⟨heG, heM, hxy⟩ := h
  exact ⟨heG, hMN heM, hxy⟩

/-- Selecting no edges gives the empty graph. -/
@[simp]
theorem matchingSubgraph_empty (G : Graph α β) : G.matchingSubgraph ∅ = ⊥ := by
  apply Graph.ext
  · simp
  · simp

/-- Every vertex of the canonical graph of selected edges is incident to one of its edges. -/
theorem matchingSubgraph_exists_inc {x : α} (hx : x ∈ V(G.matchingSubgraph M)) :
    ∃ e, (G.matchingSubgraph M).Inc e x := by
  obtain ⟨e, heM, hex⟩ := hx
  obtain ⟨y, hxy⟩ := hex
  exact ⟨e, y, ⟨e.2, heM, hxy⟩⟩

/-- A matching gives a loopless canonical subgraph. -/
theorem IsMatching.matchingSubgraph_loopless (hM : G.IsMatching M) :
    (G.matchingSubgraph M).Loopless where
  not_isLoopAt e x h := by
    obtain ⟨heG, heM, hG⟩ := h
    exact hM.not_isLoopAt heM x hG

/-- In the canonical subgraph of a matching, every vertex has a unique incident edge. -/
theorem IsMatching.matchingSubgraph_existsUnique_inc (hM : G.IsMatching M) {x : α}
    (hx : x ∈ V(G.matchingSubgraph M)) :
    ∃! e, (G.matchingSubgraph M).Inc e x := by
  obtain ⟨e, hex⟩ := matchingSubgraph_exists_inc hx
  refine ⟨e, hex, fun f hfx ↦ ?_⟩
  obtain ⟨y, heG, heM, hey⟩ := hex
  obtain ⟨z, hfG, hfM, hfz⟩ := hfx
  exact (congrArg Subtype.val <|
    hM.eq_of_inc heM hfM hey.inc_left hfz.inc_left).symm

/-- The edge-set definition of a matching is equivalent to saying that its canonical subgraph is
loopless and has exactly one incident edge at every vertex. -/
theorem isMatching_iff_matchingSubgraph :
    G.IsMatching M ↔
      (G.matchingSubgraph M).Loopless ∧
        ∀ x, x ∈ V(G.matchingSubgraph M) → ∃! e, (G.matchingSubgraph M).Inc e x := by
  constructor
  · intro hM
    exact ⟨hM.matchingSubgraph_loopless, fun _ ↦ hM.matchingSubgraph_existsUnique_inc⟩
  · rintro ⟨hloopless, hunique⟩
    constructor
    · intro e he x hex
      exact hloopless.not_isLoopAt e x ⟨e.2, he, hex⟩
    · intro e he f hf hef x hinc
      obtain ⟨y, hey⟩ := hinc.1
      obtain ⟨z, hfz⟩ := hinc.2
      have he' : (G.matchingSubgraph M).Inc e x := ⟨y, e.2, he, hey⟩
      have hf' : (G.matchingSubgraph M).Inc f x := ⟨z, f.2, hf, hfz⟩
      have hx : x ∈ V(G.matchingSubgraph M) := he'.vertex_mem
      exact hef (Subtype.ext ((hunique x hx).unique he' hf'))

/-- A matching is perfect exactly when its canonical subgraph is spanning. -/
theorem IsMatching.isPerfectMatching_iff_matchingSubgraph_spanning (hM : G.IsMatching M) :
    G.IsPerfectMatching M ↔ G.matchingSubgraph M ≤s G := by
  refine ⟨fun h ↦ ⟨matchingSubgraph_le G M, Set.Subset.antisymm
      (matchingSubgraph_le G M).vertexSet_mono ?_⟩, fun h ↦ ⟨hM, fun x ↦ ?_⟩⟩
  · intro x hx
    obtain ⟨e, heM, hex⟩ := h.2 ⟨x, hx⟩
    exact ⟨e, heM, hex⟩
  · have hx : (x : α) ∈ V(G.matchingSubgraph M) := h.vertexSet_eq.symm ▸ x.2
    exact hx

/-- The empty matching is perfect exactly when the graph has no actual vertices. -/
@[simp]
theorem isPerfectMatching_empty_iff : G.IsPerfectMatching ∅ ↔ V(G) = ∅ := by
  constructor
  · intro h
    apply Set.eq_empty_iff_forall_notMem.2
    intro x hx
    obtain ⟨e, he, -⟩ := h.2 ⟨x, hx⟩
    exact he
  · intro h
    refine ⟨isMatching_empty G, fun x ↦ ?_⟩
    have : False := by simpa only [h, mem_empty_iff_false] using x.2
    exact this.elim

/-- The unique edge of a two-vertex single-edge multigraph is a perfect matching. -/
theorem isPerfectMatching_univ_banana_singleton {u v : α} {e : β} (huv : u ≠ v) :
    (banana u v {e}).IsPerfectMatching Set.univ := by
  constructor
  · constructor
    · intro f _ x hloop
      exact huv (banana_isLoopAt.mp hloop).2.2
    · intro f _ g _ hfg x
      have : f = g := Subtype.ext <| by simpa using f.2.trans g.2.symm
      exact (hfg this).elim
  · intro x
    let f : E(banana u v {e}) := ⟨e, by simp⟩
    refine ⟨f, Set.mem_univ f, ?_⟩
    simpa [f, banana_inc] using x.2

end Graph
