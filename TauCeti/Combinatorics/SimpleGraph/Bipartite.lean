/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
public import Mathlib.Logic.Equiv.Bool

/-!
# Two-colourings of a connected graph

A walk in a graph coloured by `Bool` has even length exactly when its endpoints have the same
colour (`SimpleGraph.Coloring.even_length_iff_congr`). On a preconnected graph every two vertices
are joined by a walk, so whether two vertices share a colour does not depend on the colouring.
Hence a preconnected graph carries at most two colourings by `Bool`, and any two of them either
agree or are exchanged by `not`. In particular the two colour classes of a connected bipartite
graph are determined up to their order, which is what makes constructions from a bipartition of a
tree, such as the bipartite Coxeter element of a Coxeter system with a tree as Coxeter graph,
independent of the colouring up to exchanging the two classes.

## Main results

* `SimpleGraph.Coloring.eq_or_eq_recolorOfEquiv_boolNot`: on a preconnected graph, two
  `Bool`-colourings agree or differ by exchanging the colours.
-/

public section

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
