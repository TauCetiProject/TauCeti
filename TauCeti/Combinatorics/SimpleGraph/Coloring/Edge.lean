/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.LineGraph
public import Mathlib.Combinatorics.SimpleGraph.Matching

/-!
# Edge-colourings and chromatic index of simple graphs

A proper edge-colouring of a simple graph `G` assigns a colour to every edge of `G` so that
distinct edges sharing a vertex receive distinct colours. Because two edges of `G` are adjacent in
`G.lineGraph` precisely when they are distinct and share an endpoint, proper edge-colourings of `G`
with colours in `α` are vertex colourings of `G.lineGraph` with colours in `α`.

Defining `SimpleGraph.EdgeColoring` as an abbreviation for `G.lineGraph.Coloring` makes Mathlib's
colouring infrastructure (`DFunLike` coercion to `G.edgeSet → α`, `SimpleGraph.Coloring.colorClass`,
`SimpleGraph.recolorOfEmbedding`, `SimpleGraph.recolorOfEquiv`, `SimpleGraph.recolorOfCardLE`)
available directly on edge-colourings. The `n`-edge-colourability predicate
`SimpleGraph.EdgeColorable` and the chromatic index `SimpleGraph.chromaticIndex` (`χ'(G) ∈ ℕ∞`) are
defined as `def`s with explicit interface lemmas so downstream developments do not depend on
definitional unfolding to `G.lineGraph`.

At any vertex `v`, the edges incident with `v` form a clique in `G.lineGraph` in bijection with
`G.neighborSet v`. Every proper edge-colouring is therefore injective on the incident edges at `v`,
and `(G.neighborSet v).encard ≤ G.chromaticIndex` holds without any finiteness or decidability
assumptions on `G` or its vertex type. Restricting to any vertex set containing `G.support` induces
an isomorphism of line graphs, and a graph with finitely many edges has finite support. Finally,
edge-colourings correspond bijectively to indexed partitions of `G.edgeSet` into matching subgraphs
(`SimpleGraph.Subgraph.IsMatching`), with empty matchings allowed so unused colours are retained.

## Main definitions

* `SimpleGraph.EdgeColoring G α`: proper edge-colourings of `G` with colours in `α`, an
  abbreviation for `G.lineGraph.Coloring α`.
* `SimpleGraph.EdgeColoring.mk`, `SimpleGraph.EdgeColoring.ofCopy`,
  `SimpleGraph.EdgeColoring.ofLE`, `SimpleGraph.edgeColoringCongr`: constructor and transport of
  edge-colourings along copies, subgraphs, and isomorphisms.
* `SimpleGraph.lineGraphInduceIsoOfSupportSubset`: restricting to a vertex set containing
  `G.support` preserves the line graph up to isomorphism.
* `SimpleGraph.EdgeColoring.colorClassSubgraph`, `SimpleGraph.EdgeColoring.ofMatchings`,
  `SimpleGraph.edgeColoringEquivMatchings`: correspondence between proper edge-colourings and
  indexed partitions into matching subgraphs.
* `SimpleGraph.EdgeColorable G n`: existence of a proper edge-colouring of `G` with `n` colours.
* `SimpleGraph.chromaticIndex G`: the chromatic index `χ'(G) : ℕ∞`, the least number of colours
  needed in a proper edge-colouring of `G` (or `⊤` if none is finite).

## Main results

* `SimpleGraph.isClique_lineGraph_incidenceSet`: the edges incident with a vertex form a clique of
  the line graph.
* `SimpleGraph.encard_neighborSet_le_chromaticIndex`,
  `SimpleGraph.ncard_neighborSet_le_chromaticIndex`, `SimpleGraph.degree_le_chromaticIndex`,
  `SimpleGraph.maxDegree_le_chromaticIndex`: degree lower bounds on the chromatic index.
* `SimpleGraph.finite_support_of_finite_edgeSet`: a graph with finitely many edges has finite
  support.
* `SimpleGraph.nonempty_edgeColoring_iff_exists_matchings` and
  `SimpleGraph.edgeColorable_iff_exists_matchings`: edge-colourability as a disjoint union of
  matchings covering `G.edgeSet`.

## References

* D. Kőnig, *Gráfok és alkalmazásuk a determinánsok és a halmazok elméletére*, Mat. Természett.
  Ért. 34 (1916), 104--119.
* V. G. Vizing, *On an estimate of the chromatic class of a p-graph*, Diskret. Analiz 3 (1964),
  25--30.
* R. Diestel, *Graph Theory*, 5th ed., Springer, 2017, Section 5.3.
-/

public section

open Function Set

universe u v w w'

namespace SimpleGraph

variable {V : Type u} {G : SimpleGraph V}

/-! ### Cliques of incident edges and support -/

/-- The edges incident with a vertex `v` form a clique in `G.lineGraph`. -/
theorem isClique_lineGraph_incidenceSet (G : SimpleGraph V) (v : V) :
    G.lineGraph.IsClique (Subtype.val ⁻¹' G.incidenceSet v) :=
  fun _ he₁ _ he₂ hne ↦ lineGraph_adj_iff_exists.2
    ⟨hne, v, G.edge_mem_incidenceSet_iff.1 he₁, G.edge_mem_incidenceSet_iff.1 he₂⟩

/-- Sending each neighbour `w` of `v` to the edge `s(v, w)` embeds `G.neighborSet v` as pairwise
adjacent vertices of `G.lineGraph`. -/
theorem pairwise_lineGraph_adj_neighborSet (G : SimpleGraph V) (v : V) :
    Pairwise fun w₁ w₂ : G.neighborSet v ↦
      G.lineGraph.Adj ⟨s(v, w₁), w₁.2⟩ ⟨s(v, w₂), w₂.2⟩ := by
  intro w₁ w₂ hne
  refine lineGraph_adj_iff_exists.2 ⟨?_, v, Sym2.mem_mk_left _ _, Sym2.mem_mk_left _ _⟩
  intro h
  exact hne (Subtype.ext (Sym2.congr_right.1 (Subtype.mk.inj h)))

/-- Inducing `G` on any vertex set `s` that contains `G.support` yields an isomorphic line graph,
since isolated vertices outside `s` are incident with no edges. -/
def lineGraphInduceIsoOfSupportSubset {s : Set V} (hs : G.support ⊆ s) :
    (G.induce s).lineGraph ≃g G.lineGraph where
  toFun := (Copy.induce G s).toLineGraphEmbedding
  invFun e := ⟨(e : Sym2 V).attachWith
      (fun _ ha ↦ Set.mem_sym2_iff_subset.1 (G.edgeSet_subset_sym2_iff.2 hs e.2) ha), by
    obtain ⟨p, hp⟩ := e
    induction p using Sym2.ind with
    | _ x y => exact hp⟩
  left_inv e := by
    obtain ⟨p, hp⟩ := e
    induction p using Sym2.ind with
    | _ x y => rfl
  right_inv e := Subtype.ext (Sym2.attachWith_map_subtypeVal _)
  map_rel_iff' := (Copy.induce G s).toLineGraphEmbedding.map_rel_iff

/-- `SimpleGraph.lineGraphInduceIsoOfSupportSubset` acts on edges by mapping endpoints along
`Subtype.val`. -/
@[simp]
theorem coe_lineGraphInduceIsoOfSupportSubset_apply {s : Set V} (hs : G.support ⊆ s)
    (e : (G.induce s).edgeSet) :
    (G.lineGraphInduceIsoOfSupportSubset hs e : Sym2 V) = (e : Sym2 s).map Subtype.val :=
  (rfl)

/-- A simple graph with finitely many edges has finite vertex support, since every vertex in
`G.support` belongs to the two-element vertex set of some edge. -/
theorem finite_support_of_finite_edgeSet (G : SimpleGraph V) [Finite G.edgeSet] :
    G.support.Finite := by
  have hcov : G.support = ⋃ e : G.edgeSet, (e : Set V) := by
    ext v
    simp only [mem_support, mem_iUnion]
    exact ⟨fun ⟨w, hvw⟩ ↦ ⟨⟨s(v, w), hvw⟩, Sym2.mem_mk_left v w⟩, fun ⟨⟨e, he⟩, hve⟩ ↦ by
      obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.1 hve
      exact ⟨w, he⟩⟩
  rw [hcov]
  refine finite_iUnion fun ⟨e, _⟩ ↦ ?_
  induction e using Sym2.ind with
  | _ x y =>
    have hpair : (s(x, y) : Set V) = {x, y} := by
      ext z
      simp
    rw [hpair]
    exact (finite_singleton y).insert x

/-- In a simple graph with finitely many edges, every vertex has finitely many neighbours. -/
theorem finite_neighborSet_of_finite_edgeSet (G : SimpleGraph V) [Finite G.edgeSet] (v : V) :
    (G.neighborSet v).Finite :=
  G.finite_support_of_finite_edgeSet.subset (G.neighborSet_subset_support v)

/-! ### Proper edge-colourings -/

/-- A proper edge-colouring of `G` with colours in `α` is a vertex colouring of `G.lineGraph`,
assigning a colour to each edge of `G` so that distinct edges with a common endpoint receive
distinct colours. -/
abbrev EdgeColoring (G : SimpleGraph V) (α : Type w) : Type (max u w) :=
  G.lineGraph.Coloring α

namespace EdgeColoring

section Basic

variable {α : Type w}

/-- Construct a proper edge-colouring from a function on `G.edgeSet` that assigns distinct colours
to distinct edges sharing a vertex. -/
def mk (c : G.edgeSet → α)
    (valid : ∀ ⦃e₁ e₂ : G.edgeSet⦄ ⦃v : V⦄,
      e₁ ≠ e₂ → v ∈ (e₁ : Sym2 V) → v ∈ (e₂ : Sym2 V) → c e₁ ≠ c e₂) :
    G.EdgeColoring α :=
  Coloring.mk c fun hadj ↦
    let ⟨hne, _, h₁, h₂⟩ := lineGraph_adj_iff_exists.1 hadj
    valid hne h₁ h₂

/-- Evaluating an edge-colouring built by `SimpleGraph.EdgeColoring.mk` applies the underlying
function. -/
@[simp]
theorem coe_mk (c : G.edgeSet → α)
    (valid : ∀ ⦃e₁ e₂ : G.edgeSet⦄ ⦃v : V⦄,
      e₁ ≠ e₂ → v ∈ (e₁ : Sym2 V) → v ∈ (e₂ : Sym2 V) → c e₁ ≠ c e₂) :
    ⇑(mk c valid) = c :=
  (rfl)

/-- Distinct edges sharing a vertex receive distinct colours. -/
theorem ne_of_mem (C : G.EdgeColoring α) {e₁ e₂ : G.edgeSet} {v : V} (hne : e₁ ≠ e₂)
    (h₁ : v ∈ (e₁ : Sym2 V)) (h₂ : v ∈ (e₂ : Sym2 V)) : C e₁ ≠ C e₂ :=
  C.valid (lineGraph_adj_iff_exists.2 ⟨hne, v, h₁, h₂⟩)

/-- Two edges `s(u, v)` and `s(u, w)` with `v ≠ w` receive distinct colours. -/
theorem ne_of_adj_left (C : G.EdgeColoring α) {u v w : V} (hvw : v ≠ w)
    (huv : G.Adj u v) (huw : G.Adj u w) :
    C ⟨s(u, v), huv⟩ ≠ C ⟨s(u, w), huw⟩ :=
  C.ne_of_mem (fun h ↦ hvw (Sym2.congr_right.1 (Subtype.mk.inj h)))
    (Sym2.mem_mk_left u v) (Sym2.mem_mk_left u w)

/-- Two edges `s(u, w)` and `s(v, w)` with `u ≠ v` receive distinct colours. -/
theorem ne_of_adj_right (C : G.EdgeColoring α) {u v w : V} (huv : u ≠ v)
    (huw : G.Adj u w) (hvw : G.Adj v w) :
    C ⟨s(u, w), huw⟩ ≠ C ⟨s(v, w), hvw⟩ :=
  C.ne_of_mem (fun h ↦ huv (Sym2.congr_left.1 (Subtype.mk.inj h)))
    (Sym2.mem_mk_right u w) (Sym2.mem_mk_right v w)

/-- A proper edge-colouring is injective on the edges incident with any vertex `v`. -/
theorem injOn_incidenceSet (C : G.EdgeColoring α) (v : V) :
    InjOn C (Subtype.val ⁻¹' G.incidenceSet v) :=
  fun _ he₁ _ he₂ hC ↦ by_contra fun hne ↦
    C.ne_of_mem hne (G.edge_mem_incidenceSet_iff.1 he₁) (G.edge_mem_incidenceSet_iff.1 he₂) hC

/-- Sending each neighbour `w` of `v` to the colour of `s(v, w)` is injective. -/
theorem injective_neighborSet (C : G.EdgeColoring α) (v : V) :
    Injective fun w : G.neighborSet v ↦ C ⟨s(v, w), w.2⟩ :=
  C.injective_comp_of_pairwise_adj _ (G.pairwise_lineGraph_adj_neighborSet v)

/-- At any vertex `v`, the extended cardinality of `G.neighborSet v` is at most `ENat.card α`. -/
theorem encard_neighborSet_le_card (C : G.EdgeColoring α) (v : V) :
    (G.neighborSet v).encard ≤ ENat.card α := by
  rw [← ENat.card_coe_set_eq]
  exact ENat.card_le_card_of_injective (C.injective_neighborSet v)

/-- If a graph admits a proper edge-colouring by a finite colour type, every vertex has finitely
many neighbours. -/
theorem finite_neighborSet [Finite α] (C : G.EdgeColoring α) (v : V) :
    (G.neighborSet v).Finite :=
  Finite.of_injective _ (C.injective_neighborSet v)

/-- A proper edge-colouring by a finite colour type `α` uses at least `(G.neighborSet v).ncard`
colours at every vertex `v`. -/
theorem ncard_neighborSet_le_card [Finite α] (C : G.EdgeColoring α) (v : V) :
    (G.neighborSet v).ncard ≤ Nat.card α := by
  rw [← Nat.card_coe_set_eq]
  exact Nat.card_le_card_of_injective _ (C.injective_neighborSet v)

/-- A proper edge-colouring by a `Fintype` colour type uses at least `G.degree v` colours at every
locally finite vertex `v`. -/
theorem degree_le_card [Fintype α] (C : G.EdgeColoring α) (v : V) [Fintype (G.neighborSet v)] :
    G.degree v ≤ Fintype.card α := by
  rw [← ncard_neighborSet, ← Nat.card_eq_fintype_card]
  exact C.ncard_neighborSet_le_card v

/-- Pull a proper edge-colouring back along a graph copy `Copy G G'`. -/
def ofCopy {V' : Type v} {G' : SimpleGraph V'} (f : Copy G G') (C : G'.EdgeColoring α) :
    G.EdgeColoring α :=
  C.comp f.toLineGraphEmbedding.toHom

/-- Pulling an edge-colouring back along a copy evaluates `C` on the embedded edge. -/
@[simp]
theorem ofCopy_apply {V' : Type v} {G' : SimpleGraph V'} (f : Copy G G') (C : G'.EdgeColoring α)
    (e : G.edgeSet) :
    C.ofCopy f e = C (f.toLineGraphEmbedding e) :=
  (rfl)

/-- Restrict a proper edge-colouring of `G'` to a subgraph `G ≤ G'`, such as `G'.deleteEdges s`. -/
def ofLE {G' : SimpleGraph V} (h : G ≤ G') (C : G'.EdgeColoring α) : G.EdgeColoring α :=
  C.ofCopy (Copy.ofLE G G' h)

/-- Restricting a proper edge-colouring along `G ≤ G'` preserves the colour of each edge. -/
@[simp]
theorem ofLE_apply {G' : SimpleGraph V} (h : G ≤ G') (C : G'.EdgeColoring α) (e : G.edgeSet) :
    C.ofLE h e = C ⟨e, edgeSet_mono h e.2⟩ := by
  simp only [ofLE, ofCopy_apply]
  congr 1
  exact Subtype.ext (congrFun Sym2.map_id' e.1)

end Basic

end EdgeColoring

/-- Equivalence of proper edge-colourings induced by a graph isomorphism and a colour
equivalence. -/
def edgeColoringCongr {V' : Type v} {G' : SimpleGraph V'} {α : Type w} {β : Type w'}
    (f : G ≃g G') (g : α ≃ β) : G.EdgeColoring α ≃ G'.EdgeColoring β :=
  coloringCongr f.lineGraph g

/-- Transporting an edge-colouring along `f : G ≃g G'` and `g : α ≃ β` pulls the edge back by
`f.symm.lineGraph` and relabels its colour by `g`. -/
@[simp]
theorem edgeColoringCongr_apply {V' : Type v} {G' : SimpleGraph V'} {α : Type w} {β : Type w'}
    (f : G ≃g G') (g : α ≃ β) (C : G.EdgeColoring α) (e : G'.edgeSet) :
    edgeColoringCongr f g C e = g (C (f.lineGraph.symm e)) :=
  (rfl)

/-- Equivalence between proper edge-colourings of `G.induce s` and `G` when `G.support ⊆ s`. -/
def edgeColoringInduceEquivOfSupportSubset {α : Type w} {s : Set V} (hs : G.support ⊆ s) :
    (G.induce s).EdgeColoring α ≃ G.EdgeColoring α :=
  coloringCongr (G.lineGraphInduceIsoOfSupportSubset hs) (.refl α)

/-- `SimpleGraph.edgeColoringInduceEquivOfSupportSubset` inverse restricts a proper edge-colouring
of `G` to `G.induce s` along `Copy.induce G s`. -/
@[simp]
theorem edgeColoringInduceEquivOfSupportSubset_symm_apply {α : Type w} {s : Set V}
    (hs : G.support ⊆ s) (C : G.EdgeColoring α) (e : (G.induce s).edgeSet) :
    (G.edgeColoringInduceEquivOfSupportSubset hs).symm C e =
      C ((G.lineGraphInduceIsoOfSupportSubset hs) e) :=
  (rfl)

/-! ### Edge-colourings and partitions into matchings -/

/-- The edges of a matching subgraph form an independent set of vertices in `G.lineGraph`. -/
theorem Subgraph.IsMatching.isIndepSet_lineGraph {M : G.Subgraph} (hM : M.IsMatching) :
    G.lineGraph.IsIndepSet (Subtype.val ⁻¹' M.edgeSet) := by
  intro e₁ he₁ e₂ he₂ hne hadj
  obtain ⟨_, v, hv₁, hv₂⟩ := lineGraph_adj_iff_exists.1 hadj
  obtain ⟨w₁, hw₁⟩ := Sym2.mem_iff_exists.1 hv₁
  obtain ⟨w₂, hw₂⟩ := Sym2.mem_iff_exists.1 hv₂
  have hadj₁ : M.Adj v w₁ := by
    rw [← M.mem_edgeSet, ← hw₁]
    exact he₁
  have hadj₂ : M.Adj v w₂ := by
    rw [← M.mem_edgeSet, ← hw₂]
    exact he₂
  exact hne (Subtype.ext (hw₁.trans (hM.eq_of_adj_left hadj₁ hadj₂ ▸ hw₂.symm)))

namespace EdgeColoring

variable {α : Type w}

/-- The subgraph of `G` formed by the edges of colour `i` and their endpoints. -/
def colorClassSubgraph (C : G.EdgeColoring α) (i : α) : G.Subgraph where
  verts := {v | ∃ e : G.edgeSet, C e = i ∧ v ∈ (e : Sym2 V)}
  Adj v w := ∃ h : G.Adj v w, C ⟨s(v, w), h⟩ = i
  adj_sub h := h.1
  edge_vert h := ⟨⟨s(_, _), h.1⟩, h.2, Sym2.mem_mk_left _ _⟩
  symm := ⟨fun _ _ ⟨h, hc⟩ ↦ ⟨h.symm, by
    convert hc using 2
    exact Subtype.ext Sym2.eq_swap⟩⟩

/-- A vertex belongs to `(C.colorClassSubgraph i).verts` iff it is an endpoint of an `i`-coloured
edge. -/
@[simp]
theorem mem_colorClassSubgraph_verts (C : G.EdgeColoring α) (i : α) {v : V} :
    v ∈ (C.colorClassSubgraph i).verts ↔ ∃ e : G.edgeSet, C e = i ∧ v ∈ (e : Sym2 V) :=
  Iff.rfl

/-- Two vertices are adjacent in `C.colorClassSubgraph i` iff they form an `i`-coloured edge of
`G`. -/
@[simp]
theorem colorClassSubgraph_adj (C : G.EdgeColoring α) (i : α) {v w : V} :
    (C.colorClassSubgraph i).Adj v w ↔ ∃ h : G.Adj v w, C ⟨s(v, w), h⟩ = i :=
  Iff.rfl

/-- The edge set of `C.colorClassSubgraph i` is the image in `Sym2 V` of the colour class
`C.colorClass i`. -/
@[simp]
theorem edgeSet_colorClassSubgraph (C : G.EdgeColoring α) (i : α) :
    (C.colorClassSubgraph i).edgeSet = Subtype.val '' C.colorClass i := by
  ext e
  induction e using Sym2.ind with
  | _ v w =>
    simp only [Subgraph.mem_edgeSet, colorClassSubgraph_adj, mem_image]
    refine ⟨fun ⟨h, hc⟩ ↦ ⟨⟨s(v, w), h⟩, hc, rfl⟩, fun ⟨e', hc, hvw⟩ ↦ ?_⟩
    have h : G.Adj v w := by
      rw [← G.mem_edgeSet, ← hvw]
      exact e'.2
    have he' : (⟨s(v, w), h⟩ : G.edgeSet) = e' := Subtype.ext hvw.symm
    exact ⟨h, he'.symm ▸ hc⟩

/-- Pulling `(C.colorClassSubgraph i).edgeSet` back to `G.edgeSet` recovers `C.colorClass i`. -/
theorem preimage_coe_edgeSet_colorClassSubgraph (C : G.EdgeColoring α) (i : α) :
    Subtype.val ⁻¹' (C.colorClassSubgraph i).edgeSet = C.colorClass i := by
  rw [edgeSet_colorClassSubgraph, preimage_image_eq _ Subtype.val_injective]

/-- Every colour-class subgraph of a proper edge-colouring is a matching. -/
theorem isMatching_colorClassSubgraph (C : G.EdgeColoring α) (i : α) :
    (C.colorClassSubgraph i).IsMatching := by
  intro v ⟨e, hce, hve⟩
  obtain ⟨w, hw⟩ := Sym2.mem_iff_exists.1 hve
  have hvw : G.Adj v w := by
    rw [← G.mem_edgeSet, ← hw]
    exact e.2
  have heq : (⟨s(v, w), hvw⟩ : G.edgeSet) = e := Subtype.ext hw.symm
  refine ⟨w, ⟨hvw, heq.symm ▸ hce⟩, fun w' ⟨hvw', hcw'⟩ ↦ by_contra fun hne ↦ ?_⟩
  exact C.ne_of_adj_left (Ne.symm hne) hvw hvw' ((heq.symm ▸ hce).trans hcw'.symm)

/-- Construct a proper edge-colouring from an `α`-indexed family of matching subgraphs partitioning
`G.edgeSet`. Empty matchings are allowed, and no inhabitant of `α` is assumed. -/
noncomputable def ofMatchings (M : α → G.Subgraph) (hM : ∀ i, (M i).IsMatching)
    (hpart : ∀ e : G.edgeSet, ∃! i, (e : Sym2 V) ∈ (M i).edgeSet) : G.EdgeColoring α :=
  mk (fun e ↦ (hpart e).choose) fun {e₁ e₂ v} hne hv₁ hv₂ hcol ↦ by
    have he₁ : (e₁ : Sym2 V) ∈ (M (hpart e₁).choose).edgeSet := (hpart e₁).choose_spec.1
    have he₂ : (e₂ : Sym2 V) ∈ (M (hpart e₁).choose).edgeSet := hcol ▸ (hpart e₂).choose_spec.1
    exact (hM _).isIndepSet_lineGraph he₁ he₂ hne (lineGraph_adj_iff_exists.2 ⟨hne, v, hv₁, hv₂⟩)

/-- `SimpleGraph.EdgeColoring.ofMatchings` assigns colour `i` to an edge `e` iff `e` lies in
`(M i).edgeSet`. -/
@[simp]
theorem ofMatchings_apply_eq_iff (M : α → G.Subgraph) (hM : ∀ i, (M i).IsMatching)
    (hpart : ∀ e : G.edgeSet, ∃! i, (e : Sym2 V) ∈ (M i).edgeSet) (e : G.edgeSet) (i : α) :
    ofMatchings M hM hpart e = i ↔ (e : Sym2 V) ∈ (M i).edgeSet := by
  simp only [ofMatchings, coe_mk]
  exact ⟨fun h ↦ h ▸ (hpart e).choose_spec.1, fun h ↦ ((hpart e).choose_spec.2 i h).symm⟩

/-- Taking the `i`-th colour-class subgraph of `ofMatchings M hM hpart` recovers `M i`, including
empty matchings. -/
@[simp]
theorem colorClassSubgraph_ofMatchings (M : α → G.Subgraph) (hM : ∀ i, (M i).IsMatching)
    (hpart : ∀ e : G.edgeSet, ∃! i, (e : Sym2 V) ∈ (M i).edgeSet) (i : α) :
    (ofMatchings M hM hpart).colorClassSubgraph i = M i := by
  refine Subgraph.IsMatching.injOn_edgeSet
    ((ofMatchings M hM hpart).isMatching_colorClassSubgraph i) (hM i) ?_
  ext p
  by_cases hp : p ∈ G.edgeSet
  · rw [edgeSet_colorClassSubgraph]
    refine ⟨fun ⟨e, he, hep⟩ ↦ hep ▸ (ofMatchings_apply_eq_iff M hM hpart e i).1 he,
      fun hpM ↦ ⟨⟨p, hp⟩, (ofMatchings_apply_eq_iff M hM hpart ⟨p, hp⟩ i).2 hpM, rfl⟩⟩
  · exact iff_of_false (fun h ↦ hp (Subgraph.edgeSet_subset _ h))
      (fun h ↦ hp (Subgraph.edgeSet_subset _ h))

/-- Rebuilding a proper edge-colouring from its colour-class subgraphs recovers the colouring. -/
@[simp]
theorem ofMatchings_colorClassSubgraph (C : G.EdgeColoring α)
    (hpart : ∀ e : G.edgeSet, ∃! i, (e : Sym2 V) ∈ (C.colorClassSubgraph i).edgeSet) :
    ofMatchings C.colorClassSubgraph C.isMatching_colorClassSubgraph hpart = C := by
  ext e
  refine (ofMatchings_apply_eq_iff _ _ _ e (C e)).2 ?_
  have hmem : e ∈ Subtype.val ⁻¹' (C.colorClassSubgraph (C e)).edgeSet := by
    rw [preimage_coe_edgeSet_colorClassSubgraph]
    exact C.mem_colorClass e
  exact hmem

end EdgeColoring

/-- Proper edge-colourings of `G` with colours in `α` correspond bijectively to `α`-indexed
families of matching subgraphs whose edge sets partition `G.edgeSet`. -/
noncomputable def edgeColoringEquivMatchings (G : SimpleGraph V) (α : Type w) :
    G.EdgeColoring α ≃
      {M : α → G.Subgraph //
        (∀ i, (M i).IsMatching) ∧ ∀ e : G.edgeSet, ∃! i, (e : Sym2 V) ∈ (M i).edgeSet} where
  toFun C := ⟨C.colorClassSubgraph, C.isMatching_colorClassSubgraph, fun e ↦ by
    refine ⟨C e, ?_, fun i hi ↦ ?_⟩
    · have hmem : e ∈ Subtype.val ⁻¹' (C.colorClassSubgraph (C e)).edgeSet := by
        rw [C.preimage_coe_edgeSet_colorClassSubgraph]
        exact C.mem_colorClass e
      exact hmem
    · have hi' : e ∈ Subtype.val ⁻¹' (C.colorClassSubgraph i).edgeSet := hi
      rw [C.preimage_coe_edgeSet_colorClassSubgraph] at hi'
      exact hi'.symm⟩
  invFun M := EdgeColoring.ofMatchings M.1 M.2.1 M.2.2
  left_inv C := C.ofMatchings_colorClassSubgraph _
  right_inv M := Subtype.ext (funext (EdgeColoring.colorClassSubgraph_ofMatchings M.1 M.2.1 M.2.2))

/-- The forward direction of `SimpleGraph.edgeColoringEquivMatchings` sends a colour `i` to
`C.colorClassSubgraph i`. -/
@[simp]
theorem edgeColoringEquivMatchings_apply {α : Type w} (C : G.EdgeColoring α) (i : α) :
    (G.edgeColoringEquivMatchings α C).1 i = C.colorClassSubgraph i :=
  (rfl)

/-- The inverse of `SimpleGraph.edgeColoringEquivMatchings` colours an edge by the unique index of
the matching containing it. -/
@[simp]
theorem edgeColoringEquivMatchings_symm_apply_eq_iff {α : Type w}
    (M : {M : α → G.Subgraph //
      (∀ i, (M i).IsMatching) ∧ ∀ e : G.edgeSet, ∃! i, (e : Sym2 V) ∈ (M i).edgeSet})
    (e : G.edgeSet) (i : α) :
    (G.edgeColoringEquivMatchings α).symm M e = i ↔ (e : Sym2 V) ∈ (M.1 i).edgeSet :=
  EdgeColoring.ofMatchings_apply_eq_iff M.1 M.2.1 M.2.2 e i

/-- A simple graph admits a proper edge-colouring by `α` iff `G.edgeSet` is the pairwise disjoint
union of the edge sets of an `α`-indexed family of matching subgraphs. -/
theorem nonempty_edgeColoring_iff_exists_matchings {α : Type w} :
    Nonempty (G.EdgeColoring α) ↔
      ∃ M : α → G.Subgraph, (∀ i, (M i).IsMatching) ∧
        Pairwise (Disjoint on fun i ↦ (M i).edgeSet) ∧ ⋃ i, (M i).edgeSet = G.edgeSet := by
  constructor
  · rintro ⟨C⟩
    refine ⟨C.colorClassSubgraph, C.isMatching_colorClassSubgraph, ?_, ?_⟩
    · intro i j hij
      rw [onFun, C.edgeSet_colorClassSubgraph i, C.edgeSet_colorClassSubgraph j]
      exact (pairwise_disjoint_fiber C hij).image Subtype.val_injective.injOn (subset_univ _)
        (subset_univ _)
    · refine (iUnion_subset fun i ↦ (C.colorClassSubgraph i).edgeSet_subset).antisymm fun p hp ↦ ?_
      refine mem_iUnion.2 ⟨C ⟨p, hp⟩, ?_⟩
      rw [C.edgeSet_colorClassSubgraph]
      exact ⟨⟨p, hp⟩, C.mem_colorClass ⟨p, hp⟩, rfl⟩
  · rintro ⟨M, hM, hdisj, hcover⟩
    refine ⟨EdgeColoring.ofMatchings M hM fun e ↦ ?_⟩
    have he : (e : Sym2 V) ∈ ⋃ i, (M i).edgeSet := by
      rw [hcover]
      exact e.2
    obtain ⟨i, hi⟩ := mem_iUnion.1 he
    refine ⟨i, hi, fun j hj ↦ by_contra fun hji ↦ ?_⟩
    exact Set.disjoint_left.1 (hdisj hji) hj hi

/-! ### Edge-colourability -/

/-- `G.EdgeColorable n` means that `G` admits a proper edge-colouring with `n` colours. -/
def EdgeColorable (G : SimpleGraph V) (n : ℕ) : Prop :=
  G.lineGraph.Colorable n

/-- `G` is `n`-edge-colourable iff `G.EdgeColoring (Fin n)` is nonempty. -/
theorem edgeColorable_def {n : ℕ} : G.EdgeColorable n ↔ Nonempty (G.EdgeColoring (Fin n)) :=
  Iff.rfl

/-- `G` is `n`-edge-colourable iff `G.lineGraph` is `n`-colourable. -/
theorem edgeColorable_iff_colorable_lineGraph {n : ℕ} :
    G.EdgeColorable n ↔ G.lineGraph.Colorable n :=
  Iff.rfl

/-- `G` is `n`-edge-colourable iff `G.edgeSet` is the pairwise disjoint union of `n` matchings. -/
theorem edgeColorable_iff_exists_matchings {n : ℕ} :
    G.EdgeColorable n ↔
      ∃ M : Fin n → G.Subgraph, (∀ i, (M i).IsMatching) ∧
        Pairwise (Disjoint on fun i ↦ (M i).edgeSet) ∧ ⋃ i, (M i).edgeSet = G.edgeSet :=
  nonempty_edgeColoring_iff_exists_matchings

/-- A simple graph is `0`-edge-colourable iff it has no edges. -/
@[simp]
theorem edgeColorable_zero_iff : G.EdgeColorable 0 ↔ G = ⊥ := by
  rw [edgeColorable_iff_colorable_lineGraph, colorable_zero_iff, isEmpty_coe_sort,
    edgeSet_eq_empty]

/-- The edgeless graph is `n`-edge-colourable for every `n`. -/
@[simp]
theorem edgeColorable_bot (n : ℕ) : (⊥ : SimpleGraph V).EdgeColorable n :=
  (edgeColorable_zero_iff.2 rfl).mono n.zero_le

/-- A simple graph is `1`-edge-colourable iff every vertex has at most one neighbour. -/
theorem edgeColorable_one_iff_subsingleton_neighborSet :
    G.EdgeColorable 1 ↔ ∀ v : V, (G.neighborSet v).Subsingleton := by
  rw [edgeColorable_iff_colorable_lineGraph, colorable_one_iff]
  refine ⟨fun h v w₁ hw₁ w₂ hw₂ ↦ by_contra fun hne ↦ ?_, fun h ↦ ?_⟩
  · have hadj : G.lineGraph.Adj ⟨s(v, w₁), hw₁⟩ ⟨s(v, w₂), hw₂⟩ :=
      @pairwise_lineGraph_adj_neighborSet _ G v ⟨w₁, hw₁⟩ ⟨w₂, hw₂⟩
        fun hw ↦ hne (congrArg Subtype.val hw)
    rw [h] at hadj
    exact hadj
  · ext e₁ e₂
    simp only [bot_adj, iff_false]
    rintro ⟨hne, v, hv₁, hv₂⟩
    obtain ⟨w₁, hw₁⟩ := Sym2.mem_iff_exists.1 hv₁
    obtain ⟨w₂, hw₂⟩ := Sym2.mem_iff_exists.1 hv₂
    have hadj₁ : w₁ ∈ G.neighborSet v := by
      rw [mem_neighborSet, ← G.mem_edgeSet, ← hw₁]
      exact e₁.2
    have hadj₂ : w₂ ∈ G.neighborSet v := by
      rw [mem_neighborSet, ← G.mem_edgeSet, ← hw₂]
      exact e₂.2
    exact hne (Subtype.ext (hw₁.trans (h v hadj₁ hadj₂ ▸ hw₂.symm)))

/-- Monotonicity of `SimpleGraph.EdgeColorable` in the number of colours. -/
theorem EdgeColorable.mono {n m : ℕ} (h : n ≤ m) (hc : G.EdgeColorable n) : G.EdgeColorable m :=
  Colorable.mono h hc

/-- Pull `n`-edge-colourability back along a graph copy `Copy G G'`. -/
theorem EdgeColorable.of_copy {V' : Type v} {G' : SimpleGraph V'} {n : ℕ} (f : Copy G G')
    (hc : G'.EdgeColorable n) : G.EdgeColorable n :=
  hc.of_hom f.toLineGraphEmbedding.toHom

/-- Subgraphs of `n`-edge-colourable graphs are `n`-edge-colourable. -/
theorem EdgeColorable.mono_left {G' : SimpleGraph V} (h : G ≤ G') {n : ℕ}
    (hc : G'.EdgeColorable n) : G.EdgeColorable n :=
  hc.of_copy (Copy.ofLE G G' h)

/-- Isomorphic simple graphs are `n`-edge-colourable for the same `n`. -/
theorem edgeColorable_congr {V' : Type v} {G' : SimpleGraph V'} {n : ℕ} (f : G ≃g G') :
    G.EdgeColorable n ↔ G'.EdgeColorable n :=
  colorable_congr f.lineGraph

/-- Restricting `G` to a vertex set containing `G.support` preserves `n`-edge-colourability. -/
theorem edgeColorable_induce_of_support_subset {s : Set V} (hs : G.support ⊆ s) {n : ℕ} :
    (G.induce s).EdgeColorable n ↔ G.EdgeColorable n :=
  colorable_congr (G.lineGraphInduceIsoOfSupportSubset hs)

/-- Any proper edge-colouring by a `Fintype` `α` witnesses `(Fintype.card α)`-edge-colourability. -/
theorem EdgeColoring.edgeColorable {α : Type w} [Fintype α] (C : G.EdgeColoring α) :
    G.EdgeColorable (Fintype.card α) :=
  Coloring.colorable C

/-- A simple graph with `Fintype G.edgeSet` is `(Fintype.card G.edgeSet)`-edge-colourable by giving
every edge its own colour. -/
theorem edgeColorable_of_fintype_edgeSet (G : SimpleGraph V) [Fintype G.edgeSet] :
    G.EdgeColorable (Fintype.card G.edgeSet) :=
  G.lineGraph.colorable_of_fintype

/-- Extract a proper edge-colouring by `α` from `G.EdgeColorable n` when `n ≤ Fintype.card α`. -/
noncomputable def EdgeColorable.toEdgeColoring {α : Type w} [Fintype α] {n : ℕ}
    (hc : G.EdgeColorable n) (hn : n ≤ Fintype.card α) : G.EdgeColoring α :=
  Colorable.toColoring hc hn

/-! ### Chromatic index -/

/-- The chromatic index `χ'(G) : ℕ∞` of a simple graph `G` is the least number of colours needed in
a proper edge-colouring of `G`, or `⊤` if `G` admits no finite proper edge-colouring. -/
noncomputable def chromaticIndex (G : SimpleGraph V) : ℕ∞ :=
  G.lineGraph.chromaticNumber

/-- The chromatic index of `G` equals the chromatic number of `G.lineGraph`. -/
theorem chromaticIndex_eq_chromaticNumber_lineGraph (G : SimpleGraph V) :
    G.chromaticIndex = G.lineGraph.chromaticNumber :=
  (rfl)

/-- `G.chromaticIndex ≤ n` iff `G` is `n`-edge-colourable. -/
theorem chromaticIndex_le_iff_edgeColorable {n : ℕ} :
    G.chromaticIndex ≤ n ↔ G.EdgeColorable n :=
  chromaticNumber_le_iff_colorable

/-- Every `n`-edge-colourable graph has chromatic index at most `n`. -/
theorem EdgeColorable.chromaticIndex_le {n : ℕ} (hc : G.EdgeColorable n) :
    G.chromaticIndex ≤ n :=
  Colorable.chromaticNumber_le hc

/-- `G.chromaticIndex ≠ ⊤` iff `G` is `n`-edge-colourable for some `n : ℕ`. -/
theorem chromaticIndex_ne_top_iff_exists :
    G.chromaticIndex ≠ ⊤ ↔ ∃ n : ℕ, G.EdgeColorable n :=
  chromaticNumber_ne_top_iff_exists

/-- When `G.chromaticIndex ≠ ⊤`, `G` is `(G.chromaticIndex.toNat)`-edge-colourable. -/
theorem edgeColorable_toNat_chromaticIndex_of_ne_top (h : G.chromaticIndex ≠ ⊤) :
    G.EdgeColorable G.chromaticIndex.toNat :=
  colorable_of_chromaticNumber_ne_top h

/-- Every graph with finitely many edges has finite chromatic index. -/
theorem chromaticIndex_ne_top_of_finite_edgeSet (G : SimpleGraph V) [Finite G.edgeSet] :
    G.chromaticIndex ≠ ⊤ := by
  let _ := Fintype.ofFinite G.edgeSet
  exact chromaticIndex_ne_top_iff_exists.2 ⟨_, G.edgeColorable_of_fintype_edgeSet⟩

/-- A graph with finitely many edges is `(G.chromaticIndex.toNat)`-edge-colourable. -/
theorem edgeColorable_toNat_chromaticIndex (G : SimpleGraph V) [Finite G.edgeSet] :
    G.EdgeColorable G.chromaticIndex.toNat :=
  edgeColorable_toNat_chromaticIndex_of_ne_top G.chromaticIndex_ne_top_of_finite_edgeSet

/-- The edgeless graph has chromatic index zero. -/
@[simp]
theorem chromaticIndex_bot : (⊥ : SimpleGraph V).chromaticIndex = 0 := by
  simp [chromaticIndex]

/-- `G.chromaticIndex = 0` iff `G` has no edges. -/
@[simp]
theorem chromaticIndex_eq_zero_iff : G.chromaticIndex = 0 ↔ G = ⊥ := by
  rw [chromaticIndex, chromaticNumber_eq_zero_iff, isEmpty_coe_sort, edgeSet_eq_empty]

/-- On a subsingleton vertex type, every simple graph has chromatic index zero. -/
@[simp]
theorem chromaticIndex_eq_zero_of_subsingleton [Subsingleton V] : G.chromaticIndex = 0 := by
  rw [chromaticIndex_eq_zero_iff]
  exact Subsingleton.elim G ⊥

/-- `G.chromaticIndex = 1` iff `G` has at least one edge and every vertex has at most one
neighbour. -/
theorem chromaticIndex_eq_one_iff :
    G.chromaticIndex = 1 ↔ G ≠ ⊥ ∧ ∀ v : V, (G.neighborSet v).Subsingleton := by
  rw [eq_iff_le_not_lt, Order.lt_one_iff_nonpos, ← Nat.cast_one, ← Nat.cast_zero,
    chromaticIndex_le_iff_edgeColorable, chromaticIndex_le_iff_edgeColorable,
    edgeColorable_one_iff_subsingleton_neighborSet, edgeColorable_zero_iff, and_comm]

/-- Monotonicity of `SimpleGraph.chromaticIndex` under subgraph inclusion `G ≤ G'`. -/
theorem chromaticIndex_mono {G' : SimpleGraph V} (h : G ≤ G') :
    G.chromaticIndex ≤ G'.chromaticIndex :=
  chromaticNumber_le_of_forall_imp fun _ hc ↦ EdgeColorable.mono_left h hc

/-- A graph copy `Copy G G'` gives `G.chromaticIndex ≤ G'.chromaticIndex`. -/
theorem Copy.chromaticIndex_le {V' : Type v} {G' : SimpleGraph V'} (f : Copy G G') :
    G.chromaticIndex ≤ G'.chromaticIndex :=
  chromaticNumber_mono_of_hom f.toLineGraphEmbedding.toHom

/-- Isomorphic simple graphs have equal chromatic index. -/
theorem chromaticIndex_congr {V' : Type v} {G' : SimpleGraph V'} (f : G ≃g G') :
    G.chromaticIndex = G'.chromaticIndex :=
  chromaticNumber_congr f.lineGraph

/-- Restricting `G` to a vertex set containing `G.support` preserves `G.chromaticIndex`. -/
theorem chromaticIndex_induce_of_support_subset {s : Set V} (hs : G.support ⊆ s) :
    (G.induce s).chromaticIndex = G.chromaticIndex :=
  chromaticNumber_congr (G.lineGraphInduceIsoOfSupportSubset hs)

/-- **Degree lower bound on the chromatic index.** For every graph `G` and vertex `v`, the extended
cardinality of `G.neighborSet v` is at most `G.chromaticIndex`, with no finiteness or decidability
assumptions. -/
theorem encard_neighborSet_le_chromaticIndex (G : SimpleGraph V) (v : V) :
    (G.neighborSet v).encard ≤ G.chromaticIndex := by
  by_cases htop : G.chromaticIndex = ⊤
  · simp [htop]
  · obtain ⟨n, hn⟩ := chromaticIndex_ne_top_iff_exists.1 htop
    obtain ⟨C⟩ := edgeColorable_def.1 hn
    let _ : Fintype (G.neighborSet v) := (C.finite_neighborSet v).fintype
    rw [encard_neighborSet, ← card_neighborSet_eq_degree, chromaticIndex]
    exact le_chromaticNumber_of_pairwise_adj Nat.card_eq_fintype_card.symm.le _
      (G.pairwise_lineGraph_adj_neighborSet v)

/-- For every graph `G` and vertex `v`, `((G.neighborSet v).ncard : ℕ∞) ≤ G.chromaticIndex`. -/
theorem ncard_neighborSet_le_chromaticIndex (G : SimpleGraph V) (v : V) :
    ((G.neighborSet v).ncard : ℕ∞) ≤ G.chromaticIndex :=
  (ncard_le_encard (G.neighborSet v)).trans (G.encard_neighborSet_le_chromaticIndex v)

/-- At any locally finite vertex `v`, `(G.degree v : ℕ∞) ≤ G.chromaticIndex`. -/
theorem degree_le_chromaticIndex (G : SimpleGraph V) (v : V) [Fintype (G.neighborSet v)] :
    (G.degree v : ℕ∞) ≤ G.chromaticIndex := by
  rw [← encard_neighborSet]
  exact G.encard_neighborSet_le_chromaticIndex v

/-- In a finite simple graph, `(G.maxDegree : ℕ∞) ≤ G.chromaticIndex`. -/
theorem maxDegree_le_chromaticIndex (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] :
    (G.maxDegree : ℕ∞) ≤ G.chromaticIndex := by
  rcases isEmpty_or_nonempty V with hV | hV
  · simp
  · obtain ⟨v, hv⟩ := G.exists_maximal_degree_vertex
    rw [hv]
    exact G.degree_le_chromaticIndex v

end SimpleGraph
