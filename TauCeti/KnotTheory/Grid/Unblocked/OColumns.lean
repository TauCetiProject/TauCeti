/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Unblocked

/-!
# The `O`-markings of unions and intersections of squares

`GridDiagram.OColumnsOfSquares` records the columns whose `O`-marking a set of squares covers. It
commutes with unions and intersections, so the `O`-markings that two sets of squares carry, counted
with multiplicity, depend only on their union and their intersection. Two pairs of sets of squares
with the same union and the same intersection cover every square equally often; juxtaposition
arguments use this to compare the two domains of a composite with those of the pair it is matched
with.

## Main results

* `TauCeti.GridDiagram.OColumnsOfSquares_union` and `TauCeti.GridDiagram.OColumnsOfSquares_inter`:
  the covered `O`-columns of a union or an intersection of sets of squares.
* `TauCeti.GridDiagram.prod_OColumnsOfSquares_union_inter`: the product over the covered
  `O`-columns of two sets of squares depends only on their union and their intersection.
-/

public section

namespace TauCeti.GridDiagram

variable {n : ℕ} (G : GridDiagram n)

/-- The `O`-markings covered by a union of sets of squares are those covered by either set. -/
theorem OColumnsOfSquares_union (A B : Finset (Fin n × Fin n)) :
    G.OColumnsOfSquares (A ∪ B) = G.OColumnsOfSquares A ∪ G.OColumnsOfSquares B := by
  ext c
  simp only [Finset.mem_union, mem_OColumnsOfSquares]

/-- The `O`-markings covered by an intersection of sets of squares are those covered by both
sets. -/
theorem OColumnsOfSquares_inter (A B : Finset (Fin n × Fin n)) :
    G.OColumnsOfSquares (A ∩ B) = G.OColumnsOfSquares A ∩ G.OColumnsOfSquares B := by
  ext c
  simp only [Finset.mem_inter, mem_OColumnsOfSquares]

/-- A product over the covered `O`-columns of two sets of squares, counted with multiplicity, is
the product over the covered `O`-columns of their union and of their intersection. -/
theorem prod_OColumnsOfSquares_union_inter {M : Type*} [CommMonoid M] (f : Fin n → M)
    (A B : Finset (Fin n × Fin n)) :
    (∏ c ∈ G.OColumnsOfSquares (A ∪ B), f c) * ∏ c ∈ G.OColumnsOfSquares (A ∩ B), f c =
      (∏ c ∈ G.OColumnsOfSquares A, f c) * ∏ c ∈ G.OColumnsOfSquares B, f c := by
  rw [OColumnsOfSquares_union, OColumnsOfSquares_inter, Finset.prod_union_inter]

end TauCeti.GridDiagram
