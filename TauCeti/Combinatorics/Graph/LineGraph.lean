/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.LineGraph
public import TauCeti.Combinatorics.Graph.Incidence
public import TauCeti.Combinatorics.Graph.Isomorphism

/-!
# Line graphs and edge-colourings of multigraphs

The line graph `G.lineGraph` of a multigraph `G : Graph α β` is the simple graph whose vertices are
the actual edge identities `E(G)`, two distinct edges being adjacent when they have a common end.
Edge identities are retained: distinct parallel edges are distinct, mutually adjacent vertices of
the line graph, and a loop is adjacent to every other edge at its vertex.

A proper edge-colouring `G.EdgeColoring C` is a colouring of the line graph: it assigns a colour in
`C` to every actual edge so that distinct edges with a common end receive different colours. It is
an abbreviation for `G.lineGraph.Coloring C`, so Mathlib's colouring API (relabelling colours by
`SimpleGraph.recolorOfEmbedding`, colour classes, `SimpleGraph.Colorable`) applies directly, and the
least number of colours of a proper edge-colouring is `G.lineGraph.chromaticNumber`.

The edges at a vertex form a clique of the line graph, so every proper edge-colouring uses at least
`Graph.incidenceCount` colours at any vertex; this is the number of edges at that vertex when there
are finitely many, and zero otherwise. Two vertices joined by a set `F` of parallel edges have a
complete line graph, so they need exactly `F.encard` colours; for finite `F` this attains the
bound. The converse bound for bipartite multigraphs is Kőnig's edge-colouring theorem (D. Kőnig,
*Gráfok és alkalmazásuk a determinánsok és a halmazok elméletére*, Mat. Természettud. Értesítő 34
(1916), 104--119).

## Main definitions

* `Graph.lineGraph G`: the line graph of `G`, a simple graph on `E(G)`.
* `Graph.lineGraphEmbeddingOfLE`: the line graph of a subgraph is an induced subgraph of the line
  graph.
* `Graph.Iso.lineGraph`: isomorphic multigraphs have isomorphic line graphs.
* `Graph.lineGraphOfSimpleGraphIso`: the line graph of `Graph.ofSimpleGraph H` is `H.lineGraph`.
* `Graph.EdgeColoring G C`: proper edge-colourings of `G` by `C`, with the constructor
  `Graph.EdgeColoring.mk` and the restriction `Graph.EdgeColoring.ofLE` to subgraphs, such as
  `G.deleteEdges F`.

## Main results

* `Graph.isClique_lineGraph_incidenceSet`: the edges at a vertex form a clique of the line graph.
* `Graph.EdgeColoring.incidenceCount_le_card` and
  `Graph.incidenceCount_le_chromaticNumber_lineGraph`: a proper edge-colouring needs at least
  `Graph.incidenceCount x` colours, the number of edges at `x` when there are finitely many (and
  zero otherwise).
* `Graph.chromaticNumber_lineGraph_banana`: two vertices joined by a set `F` of parallel edges need
  exactly `F.encard` colours.
* `Graph.chromaticNumber_lineGraph_ofSimpleGraph`: for a simple graph the least number of colours
  is that of Mathlib's `SimpleGraph.lineGraph`.
-/

public section

open Set

universe u v u' v' w

namespace Graph

variable {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
variable {G H : Graph α β} {G' : Graph α' β'} {x : α}

/-! ### The line graph -/

/-- The line graph of a multigraph `G` is the simple graph on the actual edges of `G` in which two
distinct edges are adjacent when they have a common end. Parallel edges remain distinct vertices
and are adjacent to each other, and a loop is adjacent to every other edge at its vertex. -/
def lineGraph (G : Graph α β) : SimpleGraph E(G) where
  Adj e f := e ≠ f ∧ ∃ x, G.Inc e x ∧ G.Inc f x
  symm := ⟨fun _ _ ⟨hne, x, he, hf⟩ ↦ ⟨hne.symm, x, hf, he⟩⟩
  loopless := ⟨fun _ h ↦ h.1 rfl⟩

/-- Two actual edges are adjacent in the line graph exactly when they are distinct and have a
common end. -/
@[simp]
theorem lineGraph_adj {e f : E(G)} :
    G.lineGraph.Adj e f ↔ e ≠ f ∧ ∃ x, G.Inc e x ∧ G.Inc f x :=
  Iff.rfl

/-- The actual edges at a vertex are pairwise adjacent in the line graph. -/
theorem isClique_lineGraph_incidenceSet (G : Graph α β) (x : α) :
    G.lineGraph.IsClique (Subtype.val ⁻¹' G.incidenceSet x) :=
  fun _ he _ hf hef ↦ lineGraph_adj.2 ⟨hef, x, he, hf⟩

/-- The actual edges at a vertex, viewed as vertices of the line graph through the inclusion of
the incidence set into the edge set, are pairwise adjacent. -/
private theorem pairwise_lineGraph_adj_inclusion (G : Graph α β) (x : α) :
    Pairwise fun e f : G.incidenceSet x ↦ G.lineGraph.Adj
      (inclusion (G.incidenceSet_subset_edgeSet x) e)
      (inclusion (G.incidenceSet_subset_edgeSet x) f) :=
  fun e f hef ↦ G.isClique_lineGraph_incidenceSet x e.2 f.2
    ((inclusion_injective (G.incidenceSet_subset_edgeSet x)).ne hef)

/-- The line graph of a subgraph `H ≤ G` is the subgraph of the line graph of `G` induced on the
actual edges of `H`. -/
def lineGraphEmbeddingOfLE (h : H ≤ G) : H.lineGraph ↪g G.lineGraph where
  toFun := inclusion h.edgeSet_mono
  inj' := inclusion_injective h.edgeSet_mono
  map_rel_iff' {e f} := by
    simp only [Function.Embedding.coeFn_mk, lineGraph_adj, ne_eq,
      (inclusion_injective h.edgeSet_mono).eq_iff, ← h.inc_congr e.2, ← h.inc_congr f.2]

/-- The embedding of line graphs induced by `H ≤ G` keeps each edge identity. -/
@[simp]
theorem lineGraphEmbeddingOfLE_apply (h : H ≤ G) (e : E(H)) :
    lineGraphEmbeddingOfLE h e = inclusion h.edgeSet_mono e :=
  (rfl)

/-- Isomorphic multigraphs have isomorphic line graphs, through the equivalence of their actual
edges. -/
def Iso.lineGraph (f : G.Iso G') : G.lineGraph ≃g G'.lineGraph where
  toEquiv := f.edgeEquiv
  map_rel_iff' {e e'} := by
    simp only [lineGraph_adj, ne_eq, EmbeddingLike.apply_eq_iff_eq]
    refine and_congr_right fun _ ↦ ⟨fun ⟨y, he, he'⟩ ↦ ?_, fun ⟨x, he, he'⟩ ↦ ?_⟩
    · exact ⟨f.vertexEquiv.symm ⟨y, he.vertex_mem⟩, (f.map_inc_iff e _).1 (by simpa using he),
        (f.map_inc_iff e' _).1 (by simpa using he')⟩
    · exact ⟨f.vertexEquiv ⟨x, he.vertex_mem⟩, (f.map_inc_iff e _).2 he,
        (f.map_inc_iff e' _).2 he'⟩

/-- The isomorphism of line graphs induced by a multigraph isomorphism acts by its edge
equivalence. -/
@[simp]
theorem Iso.lineGraph_apply (f : G.Iso G') (e : E(G)) : f.lineGraph e = f.edgeEquiv e :=
  (rfl)

/-- The line graph of the multigraph `Graph.ofSimpleGraph H` is the line graph of `H`; both have
the edges of `H` as vertices. -/
def lineGraphOfSimpleGraphIso (H : SimpleGraph α) :
    (ofSimpleGraph H).lineGraph ≃g H.lineGraph where
  toEquiv := equivOfEq (edgeSet_ofSimpleGraph H)
  map_rel_iff' {e f} := by
    obtain ⟨e, he⟩ := e
    obtain ⟨f, hf⟩ := f
    rw [edgeSet_ofSimpleGraph] at he hf
    simp [SimpleGraph.lineGraph_adj_iff_exists, he, hf, Subtype.ext_iff]

/-- The isomorphism `Graph.lineGraphOfSimpleGraphIso` keeps each edge. -/
@[simp]
theorem coe_lineGraphOfSimpleGraphIso_apply (H : SimpleGraph α) (e : E(ofSimpleGraph H)) :
    (lineGraphOfSimpleGraphIso H e : Sym2 α) = e :=
  (rfl)

/-! ### Edge-colourings -/

/-- A proper edge-colouring of a multigraph `G` by colours in `C` assigns a colour to every actual
edge so that distinct edges with a common end receive different colours. It is a colouring of the
line graph; in particular, the colour of a loop differs from those of the other edges at its
vertex. -/
abbrev EdgeColoring (G : Graph α β) (C : Type w) : Type (max v w) :=
  G.lineGraph.Coloring C

namespace EdgeColoring

variable {C : Type w}

/-- Construct a proper edge-colouring from a colour function on the actual edges in which distinct
edges with a common end receive different colours. -/
def mk (c : E(G) → C)
    (valid : ∀ ⦃e f : E(G)⦄ ⦃x : α⦄, e ≠ f → G.Inc e x → G.Inc f x → c e ≠ c f) :
    G.EdgeColoring C :=
  SimpleGraph.Coloring.mk c fun h ↦
    let ⟨hef, _, he, hf⟩ := lineGraph_adj.1 h
    valid hef he hf

/-- A proper edge-colouring built by `Graph.EdgeColoring.mk` is its colour function. -/
@[simp]
theorem coe_mk (c : E(G) → C)
    (valid : ∀ ⦃e f : E(G)⦄ ⦃x : α⦄, e ≠ f → G.Inc e x → G.Inc f x → c e ≠ c f) :
    ⇑(mk c valid) = c :=
  (rfl)

/-- Distinct edges with a common end receive different colours. -/
theorem ne_of_inc (c : G.EdgeColoring C) {e f : E(G)} (hef : e ≠ f) (he : G.Inc e x)
    (hf : G.Inc f x) : c e ≠ c f :=
  c.valid (lineGraph_adj.2 ⟨hef, x, he, hf⟩)

/-- The actual edges at a vertex receive pairwise distinct colours. -/
theorem injOn_incidenceSet (c : G.EdgeColoring C) (x : α) :
    InjOn c (Subtype.val ⁻¹' G.incidenceSet x) :=
  fun _ he _ hf hcef ↦ by_contra fun hef ↦ c.ne_of_inc hef he hf hcef

/-- The restriction of a proper edge-colouring of `G` to a subgraph `H ≤ G`, for instance to
`G.deleteEdges F`. -/
def ofLE (h : H ≤ G) (c : G.EdgeColoring C) : H.EdgeColoring C :=
  c.comp (lineGraphEmbeddingOfLE h).toHom

/-- The restriction of a proper edge-colouring to a subgraph keeps the colour of each edge. -/
@[simp]
theorem ofLE_apply (h : H ≤ G) (c : G.EdgeColoring C) (e : E(H)) :
    c.ofLE h e = c (inclusion h.edgeSet_mono e) :=
  (rfl)

/-- A proper edge-colouring by a finite type of colours uses at least as many colours as there
are actual edges at any vertex. -/
theorem incidenceCount_le_card [Finite C] (c : G.EdgeColoring C) (x : α) :
    G.incidenceCount x ≤ Nat.card C := by
  rw [incidenceCount_def, ← Nat.card_coe_set_eq]
  exact Nat.card_le_card_of_injective _
    (c.injective_comp_of_pairwise_adj _ (G.pairwise_lineGraph_adj_inclusion x))

end EdgeColoring

/-- The least number of colours of a proper edge-colouring is at least `G.incidenceCount x`, the
number of actual edges at `x` when there are finitely many (and zero otherwise). -/
theorem incidenceCount_le_chromaticNumber_lineGraph (G : Graph α β) (x : α) :
    (G.incidenceCount x : ℕ∞) ≤ G.lineGraph.chromaticNumber := by
  rw [incidenceCount_def]
  exact SimpleGraph.le_chromaticNumber_of_pairwise_adj (Nat.card_coe_set_eq _).ge _
    (G.pairwise_lineGraph_adj_inclusion x)

/-- For a simple graph `H`, proper edge-colourings of `Graph.ofSimpleGraph H` need as many colours
as colourings of Mathlib's `SimpleGraph.lineGraph`. -/
theorem chromaticNumber_lineGraph_ofSimpleGraph (H : SimpleGraph α) :
    (ofSimpleGraph H).lineGraph.chromaticNumber = H.lineGraph.chromaticNumber :=
  SimpleGraph.chromaticNumber_congr (lineGraphOfSimpleGraphIso H)

/-! ### Parallel edges -/

/-- Any two distinct edges joining the same two vertices have a common end, so the line graph of a
banana graph is complete. -/
@[simp]
theorem lineGraph_banana (u v : α) (F : Set β) : (banana u v F).lineGraph = ⊤ := by
  ext e f
  have he : (e : β) ∈ F := by simpa using e.2
  have hf : (f : β) ∈ F := by simpa using f.2
  simp only [lineGraph_adj, banana_inc, SimpleGraph.top_adj, and_iff_left_iff_imp]
  exact fun _ ↦ ⟨u, ⟨he, Or.inl rfl⟩, hf, Or.inl rfl⟩

/-- Two vertices joined by a set `F` of parallel edges need exactly `F.encard` colours in a proper
edge-colouring. -/
theorem chromaticNumber_lineGraph_banana (u v : α) (F : Set β) :
    (banana u v F).lineGraph.chromaticNumber = F.encard := by
  rw [lineGraph_banana, SimpleGraph.chromaticNumber_top_eq_enat_card, ENat.card_coe_set_eq,
    edgeSet_banana]

end Graph
