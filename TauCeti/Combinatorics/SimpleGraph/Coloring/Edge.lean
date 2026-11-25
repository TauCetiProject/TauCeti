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

An edge-colouring of a simple graph `G` is a vertex colouring of its line graph `G.lineGraph`,
assigning a colour to every edge so that distinct edges sharing a vertex receive distinct colours.
This module gives `SimpleGraph.EdgeColoring`, `SimpleGraph.EdgeColorableWith`,
`SimpleGraph.EdgeColorable`, and `SimpleGraph.chromaticIndex` as abbreviations on `G.lineGraph`,
making Mathlib's vertex-colouring API (`DFunLike` coercion to `G.edgeSet → C`,
`SimpleGraph.Coloring.colorClass`, `SimpleGraph.recolorOfEmbedding`, `SimpleGraph.recolorOfEquiv`,
`SimpleGraph.recolorOfCardLE`) apply directly to edge-colourings.

At any vertex `x`, the edges incident with `x` form a clique in `G.lineGraph` in bijection with
`G.neighborSet x`. Every proper edge-colouring is therefore injective on the incident edges at `x`,
and `(G.neighborSet x).encard ≤ G.chromaticIndex` holds without finiteness or decidability
assumptions on `G` or its vertex type. Edge-colourings correspond bijectively to indexed partitions
of `G.edgeSet` into matching subgraphs (`SimpleGraph.Subgraph.IsMatching`), with empty matchings
allowed so unused colours are retained.

## Main definitions

* `SimpleGraph.EdgeColoring G C`: proper edge-colourings of `G` with colours in `C`, an
  abbreviation for `G.lineGraph.Coloring C`.
* `SimpleGraph.EdgeColoring.mk`, `SimpleGraph.EdgeColoring.ofCopy`,
  `SimpleGraph.EdgeColoring.ofLE`, `SimpleGraph.edgeColoringCongr`: constructor and transport of
  edge-colourings along copies, subgraphs, and isomorphisms.
* `SimpleGraph.EdgeColorableWith G C`, `SimpleGraph.EdgeColorable G k`, and
  `SimpleGraph.chromaticIndex G`: edge-colourability by `C` or by `k` colours and the chromatic
  index `χ'(G) : ℕ∞`.
* `SimpleGraph.EdgeColoring.colorClassSubgraph`, `SimpleGraph.EdgeColoring.ofMatchings`, and
  `SimpleGraph.edgeColoringEquivMatchings`: correspondence between proper edge-colourings and
  indexed partitions into matching subgraphs.

## Main results

* `SimpleGraph.isClique_lineGraph_incidenceSet`: the edges incident with a vertex form a clique of
  the line graph.
* `SimpleGraph.encard_neighborSet_le_chromaticIndex`,
  `SimpleGraph.ncard_neighborSet_le_chromaticIndex`, `SimpleGraph.degree_le_chromaticIndex`, and
  `SimpleGraph.maxDegree_le_chromaticIndex`: degree lower bounds on the chromatic index.
* `SimpleGraph.edgeColorableWith_iff_exists_matchings` and
  `SimpleGraph.edgeColorable_iff_exists_matchings`: edge-colourability as a disjoint union of
  matchings covering `G.edgeSet`.

## References

* S. Broshi,
  [Mathlib pull request #33313](https://github.com/leanprover-community/mathlib4/pull/33313),
  from which the `EdgeColoring`, `EdgeColorableWith`, `EdgeColorable`, and `chromaticIndex`
  interface is adapted.
* D. Kőnig, *Gráfok és alkalmazásuk a determinánsok és a halmazok elméletére*, Mat. Természett.
  Ért. 34 (1916), 104--119.
* V. G. Vizing, *On an estimate of the chromatic class of a p-graph*, Diskret. Analiz 3 (1964),
  25--30.
* R. Diestel, *Graph Theory*, 5th ed., Springer, 2017, Section 5.3.
-/

public section

open Function Set

universe u v w x

namespace SimpleGraph

variable {V : Type u} {W : Type v} {G H : SimpleGraph V} {G' : SimpleGraph W}
  {C : Type w} {D : Type x} {k m : ℕ}

/-! ### Cliques of incident edges -/

/-- The edges incident with a vertex `x` form a clique in `G.lineGraph`. -/
theorem isClique_lineGraph_incidenceSet (G : SimpleGraph V) (x : V) :
    G.lineGraph.IsClique (Subtype.val ⁻¹' G.incidenceSet x) :=
  fun _ he₁ _ he₂ hne ↦ lineGraph_adj_iff_exists.2
    ⟨hne, x, G.edge_mem_incidenceSet_iff.1 he₁, G.edge_mem_incidenceSet_iff.1 he₂⟩

/-- Sending each neighbour `y` of `x` to the edge `s(x, y)` embeds `G.neighborSet x` as pairwise
adjacent vertices of `G.lineGraph`. -/
theorem pairwise_lineGraph_adj_neighborSet (G : SimpleGraph V) (x : V) :
    Pairwise fun y₁ y₂ : G.neighborSet x ↦
      G.lineGraph.Adj ⟨s(x, y₁), y₁.property⟩ ⟨s(x, y₂), y₂.property⟩ := by
  intro y₁ y₂ hne
  refine lineGraph_adj_iff_exists.2 ⟨?_, x, Sym2.mem_mk_left _ _, Sym2.mem_mk_left _ _⟩
  intro h
  exact hne (Subtype.ext (Sym2.congr_right.1 (Subtype.mk.inj h)))

/-! ### Proper edge-colourings -/

/-- A proper edge-colouring of a simple graph is a colouring of its line graph. -/
abbrev EdgeColoring (G : SimpleGraph V) (C : Type w) : Type (max u w) :=
  G.lineGraph.Coloring C

namespace EdgeColoring

/-- Construct a proper edge-colouring from a colour function on the edges in which distinct edges
with a common endpoint receive different colours. -/
def mk (c : G.edgeSet → C)
    (valid : ∀ ⦃e f : G.edgeSet⦄ ⦃x : V⦄, e ≠ f → x ∈ (e : Sym2 V) →
      x ∈ (f : Sym2 V) → c e ≠ c f) :
    G.EdgeColoring C :=
  SimpleGraph.Coloring.mk c fun h ↦
    let ⟨hef, _x, he, hf⟩ := lineGraph_adj_iff_exists.1 h
    valid hef he hf

/-- A proper edge-colouring built by `SimpleGraph.EdgeColoring.mk` is its colour function. -/
@[simp]
theorem coe_mk (c : G.edgeSet → C)
    (valid : ∀ ⦃e f : G.edgeSet⦄ ⦃x : V⦄, e ≠ f → x ∈ (e : Sym2 V) →
      x ∈ (f : Sym2 V) → c e ≠ c f) :
    ⇑(mk c valid) = c :=
  (rfl)

/-- Distinct edges with a common endpoint receive different colours. -/
theorem ne_of_mem (c : G.EdgeColoring C) {e f : G.edgeSet} (hef : e ≠ f) {x : V}
    (he : x ∈ (e : Sym2 V)) (hf : x ∈ (f : Sym2 V)) : c e ≠ c f :=
  c.valid (lineGraph_adj_iff_exists.2 ⟨hef, x, he, hf⟩)

/-- Two edges `s(u, v)` and `s(u, w)` with `v ≠ w` receive distinct colours. -/
theorem ne_of_adj_left (c : G.EdgeColoring C) {u v w : V} (hvw : v ≠ w)
    (huv : G.Adj u v) (huw : G.Adj u w) :
    c ⟨s(u, v), huv⟩ ≠ c ⟨s(u, w), huw⟩ :=
  c.ne_of_mem (fun h ↦ hvw (Sym2.congr_right.1 (Subtype.mk.inj h)))
    (Sym2.mem_mk_left u v) (Sym2.mem_mk_left u w)

/-- Two edges `s(u, w)` and `s(v, w)` with `u ≠ v` receive distinct colours. -/
theorem ne_of_adj_right (c : G.EdgeColoring C) {u v w : V} (huv : u ≠ v)
    (huw : G.Adj u w) (hvw : G.Adj v w) :
    c ⟨s(u, w), huw⟩ ≠ c ⟨s(v, w), hvw⟩ :=
  c.ne_of_mem (fun h ↦ huv (Sym2.congr_left.1 (Subtype.mk.inj h)))
    (Sym2.mem_mk_right u w) (Sym2.mem_mk_right v w)

/-- A proper edge-colouring is injective on the edges incident with any vertex `x`. -/
theorem injOn_incidenceSet (c : G.EdgeColoring C) (x : V) :
    InjOn c (Subtype.val ⁻¹' G.incidenceSet x) :=
  fun _ he₁ _ he₂ hc ↦ by_contra fun hne ↦
    c.ne_of_mem hne (G.edge_mem_incidenceSet_iff.1 he₁) (G.edge_mem_incidenceSet_iff.1 he₂) hc

/-- Sending each neighbour `y` of `x` to the colour of `s(x, y)` is injective. -/
theorem injective_neighborSet (c : G.EdgeColoring C) (x : V) :
    Injective fun y : G.neighborSet x ↦ c ⟨s(x, y), y.property⟩ :=
  c.injective_comp_of_pairwise_adj _ (G.pairwise_lineGraph_adj_neighborSet x)

/-- At any vertex `x`, the extended cardinality of `G.neighborSet x` is at most `ENat.card C`. -/
theorem encard_neighborSet_le_card (c : G.EdgeColoring C) (x : V) :
    (G.neighborSet x).encard ≤ ENat.card C := by
  rw [← ENat.card_coe_set_eq]
  exact ENat.card_le_card_of_injective (c.injective_neighborSet x)

/-- If a graph admits a proper edge-colouring by a finite colour type, every vertex has finitely
many neighbours. -/
theorem finite_neighborSet [Finite C] (c : G.EdgeColoring C) (x : V) :
    (G.neighborSet x).Finite :=
  Finite.of_injective _ (c.injective_neighborSet x)

/-- A proper edge-colouring by a finite colour type `C` uses at least `(G.neighborSet x).ncard`
colours at every vertex `x`. -/
theorem ncard_neighborSet_le_card [Finite C] (c : G.EdgeColoring C) (x : V) :
    (G.neighborSet x).ncard ≤ Nat.card C := by
  rw [← Nat.card_coe_set_eq]
  exact Nat.card_le_card_of_injective _ (c.injective_neighborSet x)

/-- A proper edge-colouring by a `Fintype` colour type uses at least `G.degree x` colours at every
locally finite vertex `x`. -/
theorem degree_le_card [Fintype C] (c : G.EdgeColoring C) (x : V) [Fintype (G.neighborSet x)] :
    G.degree x ≤ Fintype.card C := by
  rw [← ncard_neighborSet, ← Nat.card_eq_fintype_card]
  exact c.ncard_neighborSet_le_card x

/-- Pull a proper edge-colouring back along a copy of a graph. -/
def ofCopy (f : Copy G G') (c : G'.EdgeColoring C) : G.EdgeColoring C :=
  c.comp f.lineGraph.toHom

/-- Pulling back a proper edge-colouring along a copy applies it to the copied edge. -/
@[simp]
theorem ofCopy_apply (f : Copy G G') (c : G'.EdgeColoring C) (e : G.edgeSet) :
    c.ofCopy f e = c (f.lineGraph.toHom e) :=
  (rfl)

/-- Restrict a proper edge-colouring to a subgraph. -/
def ofLE (h : G ≤ H) (c : H.EdgeColoring C) : G.EdgeColoring C :=
  c.ofCopy (Copy.ofLE G H h)

/-- Restricting a proper edge-colouring keeps the colour of each edge. -/
@[simp]
theorem ofLE_apply (h : G ≤ H) (c : H.EdgeColoring C) (e : G.edgeSet) :
    c.ofLE h e = c ⟨e, edgeSet_mono h e.property⟩ := by
  simp [ofLE, Copy.lineGraph, Copy.toLineGraphEmbedding]

end EdgeColoring

/-! ### Edge-colourability and chromatic index -/

/-- A simple graph is edge-colourable with `C` when it has a proper edge-colouring by `C`. -/
abbrev EdgeColorableWith (G : SimpleGraph V) (C : Type w) : Prop :=
  Nonempty (G.EdgeColoring C)

/-- A simple graph is edge-colourable by at most `k` colours when its line graph is colourable by
at most `k` colours. -/
abbrev EdgeColorable (G : SimpleGraph V) (k : ℕ) : Prop :=
  G.lineGraph.Colorable k

/-- Edge-colourability by at most `k` colours is equivalent to the existence of an edge-colouring
by `Fin k`. -/
theorem edgeColorable_iff_edgeColorableWith (G : SimpleGraph V) :
    G.EdgeColorable k ↔ G.EdgeColorableWith (Fin k) :=
  Iff.rfl

/-- The chromatic index of a simple graph is the chromatic number of its line graph. -/
noncomputable abbrev chromaticIndex (G : SimpleGraph V) : ℕ∞ :=
  G.lineGraph.chromaticNumber

/-- Edge-colourability by zero colours characterizes the graph with no edges. -/
theorem edgeColorable_zero_iff : G.EdgeColorable 0 ↔ G = ⊥ := by
  unfold EdgeColorable
  rw [colorable_zero_iff, Set.isEmpty_coe_sort, edgeSet_eq_empty]

/-- A simple graph has chromatic index zero exactly when it has no edges. -/
theorem chromaticIndex_eq_zero_iff : G.chromaticIndex = 0 ↔ G = ⊥ := by
  rw [chromaticNumber_eq_zero_iff, Set.isEmpty_coe_sort, edgeSet_eq_empty]

/-- The graph with no edges has chromatic index zero. -/
theorem chromaticIndex_bot : (⊥ : SimpleGraph V).chromaticIndex = 0 :=
  chromaticIndex_eq_zero_iff.2 rfl

/-- Increasing the number of available colours preserves edge-colourability. -/
theorem EdgeColorable.mono (hkm : k ≤ m) (h : G.EdgeColorable k) : G.EdgeColorable m :=
  SimpleGraph.Colorable.mono hkm h

/-- The edgeless graph is `k`-edge-colourable for every `k`. -/
theorem edgeColorable_bot (k : ℕ) : (⊥ : SimpleGraph V).EdgeColorable k :=
  (edgeColorable_zero_iff.2 rfl).mono k.zero_le

/-- Containment in another graph preserves edge-colourability by a given colour type. -/
theorem EdgeColorableWith.of_isContained (hGG' : G ⊑ G') (h : G'.EdgeColorableWith C) :
    G.EdgeColorableWith C := by
  obtain ⟨f⟩ := hGG'
  obtain ⟨c⟩ := h
  exact ⟨EdgeColoring.ofCopy f c⟩

/-- Restricting a graph preserves edge-colourability by a given colour type. -/
theorem EdgeColorableWith.of_le (hGH : G ≤ H) (h : H.EdgeColorableWith C) :
    G.EdgeColorableWith C :=
  h.of_isContained (IsContained.of_le hGH)

/-- Containment in another graph preserves edge-colourability. -/
theorem EdgeColorable.of_isContained (hGG' : G ⊑ G') (h : G'.EdgeColorable k) :
    G.EdgeColorable k :=
  EdgeColorableWith.of_isContained hGG' h

/-- Restricting a graph preserves edge-colourability. -/
theorem EdgeColorable.of_le (hGH : G ≤ H) (h : H.EdgeColorable k) : G.EdgeColorable k :=
  h.of_isContained (IsContained.of_le hGH)

/-- Embedding the colour type preserves edge-colourability. -/
theorem EdgeColorableWith.of_embedding (f : C ↪ D) (h : G.EdgeColorableWith C) :
    G.EdgeColorableWith D :=
  ⟨G.lineGraph.recolorOfEmbedding f h.some⟩

/-- Graph and colour isomorphisms induce an equivalence of edge-colourings. -/
def edgeColoringCongr (f : G ≃g G') (g : C ≃ D) : G.EdgeColoring C ≃ G'.EdgeColoring D :=
  coloringCongr f.lineGraph g

/-- Transporting an edge-colouring applies the colour equivalence after relabelling the edge. -/
@[simp]
theorem edgeColoringCongr_apply (f : G ≃g G') (g : C ≃ D) (c : G.EdgeColoring C)
    (e : G'.edgeSet) : edgeColoringCongr f g c e = g (c (f.lineGraph.symm e)) :=
  (rfl)

/-- Inverse transport of an edge-colouring applies the inverse colour equivalence after relabelling
the edge. -/
@[simp]
theorem edgeColoringCongr_symm_apply (f : G ≃g G') (g : C ≃ D) (c : G'.EdgeColoring D)
    (e : G.edgeSet) : (edgeColoringCongr f g).symm c e = g.symm (c (f.lineGraph e)) :=
  (rfl)

/-- Graph and colour isomorphisms preserve edge-colourability by a given colour type. -/
theorem edgeColorableWith_congr (f : G ≃g G') (g : C ≃ D) :
    G.EdgeColorableWith C ↔ G'.EdgeColorableWith D :=
  (edgeColoringCongr f g).nonempty_congr

/-- Isomorphic graphs are edge-colourable by a given number of colours simultaneously. -/
theorem edgeColorable_congr (f : G ≃g G') : G.EdgeColorable k ↔ G'.EdgeColorable k :=
  edgeColorableWith_congr f (Equiv.refl _)

/-- Isomorphic graphs have the same chromatic index. -/
theorem chromaticIndex_congr (f : G ≃g G') : G.chromaticIndex = G'.chromaticIndex :=
  chromaticNumber_congr f.lineGraph

/-- Containment in another graph cannot increase the chromatic index. -/
theorem IsContained.chromaticIndex_mono (hGG' : G ⊑ G') :
    G.chromaticIndex ≤ G'.chromaticIndex :=
  chromaticNumber_mono_of_hom hGG'.some.lineGraph.toHom

/-- Passing to a subgraph cannot increase the chromatic index. -/
@[gcongr]
theorem chromaticIndex_mono (hGH : G ≤ H) : G.chromaticIndex ≤ H.chromaticIndex :=
  (IsContained.of_le hGH).chromaticIndex_mono

/-- The chromatic index is at most `k` exactly when the graph is edge-colourable by at most `k`
colours. -/
theorem chromaticIndex_le_iff_edgeColorable (G : SimpleGraph V) :
    G.chromaticIndex ≤ k ↔ G.EdgeColorable k :=
  chromaticNumber_le_iff_colorable

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

/-- The subgraph of `G` formed by the edges of colour `i` and their endpoints. -/
def colorClassSubgraph (c : G.EdgeColoring C) (i : C) : G.Subgraph where
  verts := {v | ∃ e : G.edgeSet, c e = i ∧ v ∈ (e : Sym2 V)}
  Adj v w := ∃ h : G.Adj v w, c ⟨s(v, w), h⟩ = i
  adj_sub h := h.1
  edge_vert h := ⟨⟨s(_, _), h.1⟩, h.2, Sym2.mem_mk_left _ _⟩
  symm := ⟨fun _ _ ⟨h, hc⟩ ↦ ⟨h.symm, by
    convert hc using 2
    exact Subtype.ext Sym2.eq_swap⟩⟩

/-- A vertex belongs to `(c.colorClassSubgraph i).verts` iff it is an endpoint of an `i`-coloured
edge. -/
@[simp]
theorem mem_colorClassSubgraph_verts (c : G.EdgeColoring C) (i : C) {v : V} :
    v ∈ (c.colorClassSubgraph i).verts ↔ ∃ e : G.edgeSet, c e = i ∧ v ∈ (e : Sym2 V) :=
  Iff.rfl

/-- Two vertices are adjacent in `c.colorClassSubgraph i` iff they form an `i`-coloured edge of
`G`. -/
@[simp]
theorem colorClassSubgraph_adj (c : G.EdgeColoring C) (i : C) {v w : V} :
    (c.colorClassSubgraph i).Adj v w ↔ ∃ h : G.Adj v w, c ⟨s(v, w), h⟩ = i :=
  Iff.rfl

/-- The edge set of `c.colorClassSubgraph i` is the image in `Sym2 V` of the colour class
`c.colorClass i`. -/
@[simp]
theorem edgeSet_colorClassSubgraph (c : G.EdgeColoring C) (i : C) :
    (c.colorClassSubgraph i).edgeSet = Subtype.val '' c.colorClass i := by
  ext e
  induction e using Sym2.ind with
  | _ v w =>
    simp only [Subgraph.mem_edgeSet, colorClassSubgraph_adj, mem_image]
    refine ⟨fun ⟨h, hc⟩ ↦ ⟨⟨s(v, w), h⟩, hc, rfl⟩, fun ⟨e', hc, hvw⟩ ↦ ?_⟩
    have h : G.Adj v w := by
      rw [← G.mem_edgeSet, ← hvw]
      exact e'.property
    have he' : (⟨s(v, w), h⟩ : G.edgeSet) = e' := Subtype.ext hvw.symm
    exact ⟨h, he'.symm ▸ hc⟩

/-- Pulling `(c.colorClassSubgraph i).edgeSet` back to `G.edgeSet` recovers `c.colorClass i`. -/
theorem preimage_coe_edgeSet_colorClassSubgraph (c : G.EdgeColoring C) (i : C) :
    Subtype.val ⁻¹' (c.colorClassSubgraph i).edgeSet = c.colorClass i := by
  rw [edgeSet_colorClassSubgraph, preimage_image_eq _ Subtype.val_injective]

/-- Every colour-class subgraph of a proper edge-colouring is a matching. -/
theorem isMatching_colorClassSubgraph (c : G.EdgeColoring C) (i : C) :
    (c.colorClassSubgraph i).IsMatching := by
  intro v ⟨e, hce, hve⟩
  obtain ⟨w, hw⟩ := Sym2.mem_iff_exists.1 hve
  have hvw : G.Adj v w := by
    rw [← G.mem_edgeSet, ← hw]
    exact e.property
  have heq : (⟨s(v, w), hvw⟩ : G.edgeSet) = e := Subtype.ext hw.symm
  refine ⟨w, ⟨hvw, heq.symm ▸ hce⟩, fun w' ⟨hvw', hcw'⟩ ↦ by_contra fun hne ↦ ?_⟩
  exact c.ne_of_adj_left (Ne.symm hne) hvw hvw' ((heq.symm ▸ hce).trans hcw'.symm)

/-- Construct a proper edge-colouring from a `C`-indexed family of matching subgraphs partitioning
`G.edgeSet`. Empty matchings are allowed, and no inhabitant of `C` is assumed. -/
noncomputable def ofMatchings (M : C → G.Subgraph) (hM : ∀ i, (M i).IsMatching)
    (hpart : ∀ e : G.edgeSet, ∃! i, (e : Sym2 V) ∈ (M i).edgeSet) : G.EdgeColoring C :=
  mk (fun e ↦ (hpart e).choose) fun {e₁ e₂ v} hne hv₁ hv₂ hcol ↦ by
    have he₁ : (e₁ : Sym2 V) ∈ (M (hpart e₁).choose).edgeSet := (hpart e₁).choose_spec.1
    have he₂ : (e₂ : Sym2 V) ∈ (M (hpart e₁).choose).edgeSet := hcol ▸ (hpart e₂).choose_spec.1
    exact (hM _).isIndepSet_lineGraph he₁ he₂ hne (lineGraph_adj_iff_exists.2 ⟨hne, v, hv₁, hv₂⟩)

/-- `SimpleGraph.EdgeColoring.ofMatchings` assigns colour `i` to an edge `e` iff `e` lies in
`(M i).edgeSet`. -/
@[simp]
theorem ofMatchings_apply_eq_iff (M : C → G.Subgraph) (hM : ∀ i, (M i).IsMatching)
    (hpart : ∀ e : G.edgeSet, ∃! i, (e : Sym2 V) ∈ (M i).edgeSet) (e : G.edgeSet) (i : C) :
    ofMatchings M hM hpart e = i ↔ (e : Sym2 V) ∈ (M i).edgeSet := by
  simp only [ofMatchings, coe_mk]
  exact ⟨fun h ↦ h ▸ (hpart e).choose_spec.1, fun h ↦ ((hpart e).choose_spec.2 i h).symm⟩

/-- Taking the `i`-th colour-class subgraph of `ofMatchings M hM hpart` recovers `M i`, including
empty matchings. -/
@[simp]
theorem colorClassSubgraph_ofMatchings (M : C → G.Subgraph) (hM : ∀ i, (M i).IsMatching)
    (hpart : ∀ e : G.edgeSet, ∃! i, (e : Sym2 V) ∈ (M i).edgeSet) (i : C) :
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
theorem ofMatchings_colorClassSubgraph (c : G.EdgeColoring C)
    (hpart : ∀ e : G.edgeSet, ∃! i, (e : Sym2 V) ∈ (c.colorClassSubgraph i).edgeSet) :
    ofMatchings c.colorClassSubgraph c.isMatching_colorClassSubgraph hpart = c := by
  ext e
  refine (ofMatchings_apply_eq_iff _ _ _ e (c e)).2 ?_
  have hmem : e ∈ Subtype.val ⁻¹' (c.colorClassSubgraph (c e)).edgeSet := by
    rw [preimage_coe_edgeSet_colorClassSubgraph]
    exact c.mem_colorClass e
  exact hmem

end EdgeColoring

/-- Proper edge-colourings of `G` with colours in `C` correspond bijectively to `C`-indexed
families of matching subgraphs whose edge sets partition `G.edgeSet`. -/
noncomputable def edgeColoringEquivMatchings (G : SimpleGraph V) (C : Type w) :
    G.EdgeColoring C ≃
      {M : C → G.Subgraph //
        (∀ i, (M i).IsMatching) ∧ ∀ e : G.edgeSet, ∃! i, (e : Sym2 V) ∈ (M i).edgeSet} where
  toFun c := ⟨c.colorClassSubgraph, c.isMatching_colorClassSubgraph, fun e ↦ by
    refine ⟨c e, ?_, fun i hi ↦ ?_⟩
    · have hmem : e ∈ Subtype.val ⁻¹' (c.colorClassSubgraph (c e)).edgeSet := by
        rw [c.preimage_coe_edgeSet_colorClassSubgraph]
        exact c.mem_colorClass e
      exact hmem
    · have hi' : e ∈ Subtype.val ⁻¹' (c.colorClassSubgraph i).edgeSet := hi
      rw [c.preimage_coe_edgeSet_colorClassSubgraph] at hi'
      exact hi'.symm⟩
  invFun M := EdgeColoring.ofMatchings M.val M.property.1 M.property.2
  left_inv c := c.ofMatchings_colorClassSubgraph _
  right_inv M := Subtype.ext <| funext <|
    EdgeColoring.colorClassSubgraph_ofMatchings M.val M.property.1 M.property.2

/-- The forward direction of `SimpleGraph.edgeColoringEquivMatchings` sends a colour `i` to
`c.colorClassSubgraph i`. -/
@[simp]
theorem edgeColoringEquivMatchings_apply (c : G.EdgeColoring C) (i : C) :
    (G.edgeColoringEquivMatchings C c).val i = c.colorClassSubgraph i :=
  (rfl)

/-- The inverse of `SimpleGraph.edgeColoringEquivMatchings` colours an edge by the unique index of
the matching containing it. -/
@[simp]
theorem edgeColoringEquivMatchings_symm_apply_eq_iff
    (M : {M : C → G.Subgraph //
      (∀ i, (M i).IsMatching) ∧ ∀ e : G.edgeSet, ∃! i, (e : Sym2 V) ∈ (M i).edgeSet})
    (e : G.edgeSet) (i : C) :
    (G.edgeColoringEquivMatchings C).symm M e = i ↔ (e : Sym2 V) ∈ (M.val i).edgeSet :=
  EdgeColoring.ofMatchings_apply_eq_iff M.val M.property.1 M.property.2 e i

/-- A simple graph admits a proper edge-colouring by `C` iff `G.edgeSet` is the pairwise disjoint
union of the edge sets of a `C`-indexed family of matching subgraphs. -/
theorem edgeColorableWith_iff_exists_matchings :
    G.EdgeColorableWith C ↔
      ∃ M : C → G.Subgraph, (∀ i, (M i).IsMatching) ∧
        Pairwise (Disjoint on fun i ↦ (M i).edgeSet) ∧ ⋃ i, (M i).edgeSet = G.edgeSet := by
  constructor
  · rintro ⟨c⟩
    refine ⟨c.colorClassSubgraph, c.isMatching_colorClassSubgraph, ?_, ?_⟩
    · intro i j hij
      rw [onFun, c.edgeSet_colorClassSubgraph i, c.edgeSet_colorClassSubgraph j]
      exact (pairwise_disjoint_fiber c hij).image Subtype.val_injective.injOn (subset_univ _)
        (subset_univ _)
    · refine (iUnion_subset fun i ↦ (c.colorClassSubgraph i).edgeSet_subset).antisymm fun p hp ↦ ?_
      refine mem_iUnion.2 ⟨c ⟨p, hp⟩, ?_⟩
      rw [c.edgeSet_colorClassSubgraph]
      exact ⟨⟨p, hp⟩, c.mem_colorClass ⟨p, hp⟩, rfl⟩
  · rintro ⟨M, hM, hdisj, hcover⟩
    refine ⟨EdgeColoring.ofMatchings M hM fun e ↦ ?_⟩
    have he : (e : Sym2 V) ∈ ⋃ i, (M i).edgeSet := by
      rw [hcover]
      exact e.property
    obtain ⟨i, hi⟩ := mem_iUnion.1 he
    refine ⟨i, hi, fun j hj ↦ by_contra fun hji ↦ ?_⟩
    exact Set.disjoint_left.1 (hdisj hji) hj hi

/-- `G` is `k`-edge-colourable iff `G.edgeSet` is the pairwise disjoint union of `k` matchings. -/
theorem edgeColorable_iff_exists_matchings :
    G.EdgeColorable k ↔
      ∃ M : Fin k → G.Subgraph, (∀ i, (M i).IsMatching) ∧
        Pairwise (Disjoint on fun i ↦ (M i).edgeSet) ∧ ⋃ i, (M i).edgeSet = G.edgeSet :=
  (G.edgeColorable_iff_edgeColorableWith).trans G.edgeColorableWith_iff_exists_matchings

/-! ### Degree lower bounds on the chromatic index -/

/-- **Degree lower bound on the chromatic index.** For every graph `G` and vertex `x`, the extended
cardinality of `G.neighborSet x` is at most `G.chromaticIndex`, with no finiteness or decidability
assumptions. -/
theorem encard_neighborSet_le_chromaticIndex (G : SimpleGraph V) (x : V) :
    (G.neighborSet x).encard ≤ G.chromaticIndex := by
  by_cases htop : G.chromaticIndex = ⊤
  · simp [htop]
  · obtain ⟨n, hn⟩ := chromaticNumber_ne_top_iff_exists.1 htop
    obtain ⟨c⟩ := hn
    let _ : Fintype (G.neighborSet x) := (EdgeColoring.finite_neighborSet c x).fintype
    rw [encard_neighborSet, ← card_neighborSet_eq_degree, chromaticIndex]
    exact le_chromaticNumber_of_pairwise_adj Nat.card_eq_fintype_card.symm.le _
      (G.pairwise_lineGraph_adj_neighborSet x)

/-- For every graph `G` and vertex `x`, `((G.neighborSet x).ncard : ℕ∞) ≤ G.chromaticIndex`. -/
theorem ncard_neighborSet_le_chromaticIndex (G : SimpleGraph V) (x : V) :
    ((G.neighborSet x).ncard : ℕ∞) ≤ G.chromaticIndex :=
  (ncard_le_encard (G.neighborSet x)).trans (G.encard_neighborSet_le_chromaticIndex x)

/-- At any locally finite vertex `x`, `(G.degree x : ℕ∞) ≤ G.chromaticIndex`. -/
theorem degree_le_chromaticIndex (G : SimpleGraph V) (x : V) [Fintype (G.neighborSet x)] :
    (G.degree x : ℕ∞) ≤ G.chromaticIndex := by
  rw [← encard_neighborSet]
  exact G.encard_neighborSet_le_chromaticIndex x

/-- In a finite simple graph, `(G.maxDegree : ℕ∞) ≤ G.chromaticIndex`. -/
theorem maxDegree_le_chromaticIndex (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] :
    (G.maxDegree : ℕ∞) ≤ G.chromaticIndex := by
  rcases isEmpty_or_nonempty V with _ | _
  · simp
  · obtain ⟨x, hx⟩ := G.exists_maximal_degree_vertex
    rw [hx]
    exact G.degree_le_chromaticIndex x

end SimpleGraph
