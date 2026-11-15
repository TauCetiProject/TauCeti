/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
public import Mathlib.Logic.Equiv.Bool

/-!
# Bipartite restrictions and two-colourings

Restricting a graph to pairs between two sets is intersection with the corresponding
restriction of the complete graph (`SimpleGraph.between_eq_inf_top_between`).
Complete-graph cuts respect symmetric difference (`SimpleGraph.top_between_symmDiff`). A
bipartition `G.IsBipartiteWith s t` extends to a covering bipartition on the whole vertex type by
adjoining the remaining isolated vertices to either side (`SimpleGraph.IsBipartiteWith.compl_right`
and `SimpleGraph.IsBipartiteWith.compl_left`).

A walk in a graph coloured by `Bool` has even length exactly when its endpoints have the same
colour (`SimpleGraph.Coloring.even_length_iff_congr`). On a preconnected graph every two vertices
are joined by a walk, so whether two vertices share a colour does not depend on the colouring.
Hence a preconnected graph carries at most two colourings by `Bool`, and any two of them either
agree or are exchanged by `not`. In particular the two colour classes of a connected bipartite
graph are determined up to their order, which is what makes constructions from a bipartition of a
tree, such as the bipartite Coxeter element of a Coxeter system with a tree as Coxeter graph,
independent of the colouring up to exchanging the two classes.

## Main results

* `SimpleGraph.IsBipartiteWith.compl_right`, `SimpleGraph.IsBipartiteWith.compl_left`: extending a
  bipartition to cover the whole vertex type.
* `SimpleGraph.Coloring.eq_or_eq_recolorOfEquiv_boolNot`: on a preconnected graph, two
  `Bool`-colourings agree or differ by exchanging the colours.
-/

public section

open scoped symmDiff

namespace SimpleGraph

variable {V : Type*}

/-- Restricting a graph to pairs between two sets is intersection with the corresponding
restriction of the complete graph. -/
theorem between_eq_inf_top_between (G : SimpleGraph V) (s t : Set V) :
    G.between s t = G ⊓ (⊤ : SimpleGraph V).between s t := by
  ext u v
  simp only [between_adj, inf_adj, top_adj]
  exact and_congr_right fun h ↦ (and_iff_right h.ne).symm

/-- The complete-graph cut of `S ∆ T` is the symmetric difference of the cuts of `S` and `T`. -/
theorem top_between_symmDiff (S T : Set V) :
    (⊤ : SimpleGraph V).between (S ∆ T) (S ∆ T)ᶜ =
      (⊤ : SimpleGraph V).between S Sᶜ ∆ (⊤ : SimpleGraph V).between T Tᶜ := by
  ext u v
  simp only [between_adj, top_adj, Set.mem_compl_iff, symmDiff_def, Set.mem_union,
    Set.mem_sdiff, sup_adj, sdiff_adj]
  tauto

/-- Adjoining all vertices outside `s ∪ t` to the right side yields a bipartition with sides `s`
and `sᶜ` covering the whole vertex type. -/
theorem IsBipartiteWith.compl_right {G : SimpleGraph V} {s t : Set V}
    (h : G.IsBipartiteWith s t) : G.IsBipartiteWith s sᶜ where
  disjoint := disjoint_compl_right
  mem_of_adj _ _ hadj := (h.mem_of_adj hadj).imp
    (And.imp_right fun hx ↦ h.disjoint.subset_compl_left hx)
    (And.imp_left fun hx ↦ h.disjoint.subset_compl_left hx)

/-- Adjoining all vertices outside `s ∪ t` to the left side yields a bipartition with sides `tᶜ`
and `t` covering the whole vertex type. -/
theorem IsBipartiteWith.compl_left {G : SimpleGraph V} {s t : Set V}
    (h : G.IsBipartiteWith s t) : G.IsBipartiteWith tᶜ t :=
  h.symm.compl_right.symm

end SimpleGraph

namespace SimpleGraph.Coloring

variable {V : Type*} {G : SimpleGraph V}

/-- **A preconnected graph has at most two colourings by `Bool`**: any two of them agree, or are
exchanged by `not`. -/
theorem eq_or_eq_recolorOfEquiv_boolNot (hG : G.Preconnected) (c c' : G.Coloring Bool) :
    c' = c ∨ c' = G.recolorOfEquiv Equiv.boolNot c := by
  rcases isEmpty_or_nonempty V with hV | ⟨⟨u⟩⟩
  · exact Or.inl (DFunLike.ext _ _ isEmptyElim)
  -- Whether a vertex has the colour of `u` is read off the parity of a walk from `u`, so it is the
  -- same for both colourings.
  have key (v : V) : (c u = c v ↔ c' u = c' v) := by
    obtain ⟨p⟩ := hG u v
    have h := (c.even_length_iff_congr p).symm.trans (c'.even_length_iff_congr p)
    simpa only [Bool.coe_iff_coe] using h
  by_cases hu : c' u = c u
  · refine Or.inl (DFunLike.ext _ _ fun v ↦ ?_)
    have hv := key v
    clear key
    revert hu hv
    generalize c u = a, c v = b, c' u = a', c' v = b'
    decide +revert
  · refine Or.inr (DFunLike.ext _ _ fun v ↦ ?_)
    have hv := key v
    clear key
    suffices c' v = !c v by simpa using this
    revert hu hv
    generalize c u = a, c v = b, c' u = a', c' v = b'
    decide +revert

end SimpleGraph.Coloring
