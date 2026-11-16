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

universe u w

namespace SimpleGraph

variable {V : Type u} {k : ℕ}

/-- A proper edge-colouring of a simple graph is a colouring of its line graph. -/
abbrev EdgeColoring (G : SimpleGraph V) (C : Type w) : Type (max u w) :=
  G.lineGraph.Coloring C

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

end SimpleGraph
