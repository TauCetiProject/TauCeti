/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.LineGraph

/-!
# Edge-colourings of simple graphs

An edge-colouring of a simple graph is a vertex colouring of its line graph. This module gives
that construction its standard names, so Mathlib's vertex-colouring API applies directly to
edge-colourings.

The `EdgeColoring`, `EdgeColorableWith`, `EdgeColorable`, and `chromaticIndex` interface is adapted
from [Mathlib pull request #33313](https://github.com/leanprover-community/mathlib4/pull/33313) by
Snir Broshi.
-/

public section

universe u v w x

namespace SimpleGraph

variable {V : Type u} {W : Type v} {G H : SimpleGraph V} {G' : SimpleGraph W}
  {C : Type w} {D : Type x} {k m : ℕ}

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

/-- Containment in another graph preserves edge-colourability. -/
theorem EdgeColorable.of_isContained (hGG' : G ⊑ G') (h : G'.EdgeColorable k) :
    G.EdgeColorable k := by
  obtain ⟨f⟩ := hGG'
  obtain ⟨c⟩ := h
  exact ⟨EdgeColoring.ofCopy f c⟩

/-- Restricting a graph preserves edge-colourability. -/
theorem EdgeColorable.of_le (hGH : G ≤ H) (h : H.EdgeColorable k) : G.EdgeColorable k :=
  h.of_isContained (IsContained.of_le hGH)

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

end SimpleGraph
