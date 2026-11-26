/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.LineGraph

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
assumptions on `G` or its vertex type. For the correspondence between proper edge-colourings and
indexed partitions into matching subgraphs, see
`TauCeti.Combinatorics.Graph.Matching.OfSimpleGraph`.

## Main definitions

* `SimpleGraph.EdgeColoring G C`: proper edge-colourings of `G` with colours in `C`, an
  abbreviation for `G.lineGraph.Coloring C`.
* `SimpleGraph.EdgeColoring.mk`, `SimpleGraph.EdgeColoring.ofCopy`,
  `SimpleGraph.EdgeColoring.ofLE`, `SimpleGraph.edgeColoringCongr`: constructor and transport of
  edge-colourings along copies, subgraphs, and isomorphisms.
* `SimpleGraph.EdgeColorableWith G C`, `SimpleGraph.EdgeColorable G k`, and
  `SimpleGraph.chromaticIndex G`: edge-colourability by `C` or by `k` colours and the chromatic
  index `χ'(G) : ℕ∞`.

## Main results

* `SimpleGraph.isClique_lineGraph_incidenceSet`: the edges incident with a vertex form a clique of
  the line graph.
* `SimpleGraph.encard_neighborSet_le_chromaticIndex`,
  `SimpleGraph.ncard_neighborSet_le_chromaticIndex`, `SimpleGraph.degree_le_chromaticIndex`, and
  `SimpleGraph.maxDegree_le_chromaticIndex`: degree lower bounds on the chromatic index.

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
