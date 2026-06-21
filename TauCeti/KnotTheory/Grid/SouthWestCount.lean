/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TauCeti.KnotTheory.Grid.GradingInteger

/-!
# Column-index formulas for integer Maslov gradings

The grid `J`-function and the Maslov gradings it feeds are defined through the ordered southwest
count `GridPoint.I s t`, which ranges over all pairs of points `(p, q) ∈ s × t` and keeps those
with `p` strictly southwest of `q`. The column-index reductions for graph point sets and the
grid `J`-function live with the `J` API in `TauCeti.KnotTheory.Grid.JFunction`; this file applies
them to the integer Maslov gradings.

The resulting formulas rewrite `maslovOℤ` and `maslovXℤ` entirely as counts over column indices,
so they evaluate on an explicit grid without unfolding any point-pair product.

## Main results

* `TauCeti.GridDiagram.maslovOℤ_eq_card`, `TauCeti.GridDiagram.maslovXℤ_eq_card`: the integer
  Maslov gradings written entirely as counts over column indices.

## References

This advances `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane G item 2, "Gradings.
The `J`-function, `M_O`, `M_X`, `A`", and the standing convention that the gradings must
*compute* on explicit small grids. The southwest count and its reduction to a column-index count
follow Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Chapter 4.
-/

namespace TauCeti

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n)

/-- The integer `O`-Maslov grading of a grid state written entirely as counts over column
indices. Every southwest count in `maslovOℤ` is a state or marking point-set count, so it collapses
to a column-pair count and the grading evaluates without unfolding any point-pair product. -/
theorem maslovOℤ_eq_card (x : GridState n) :
    G.maslovOℤ x =
      ((Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ x p.1 < x p.2).card : ℤ)
        - ((Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ x p.1 < G.O p.2).card
          + (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ G.O p.1 < x p.2).card)
        + (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ G.O p.1 < G.O p.2).card + 1 := by
  rw [maslovOℤ_def, OSet, GridState.I_self_pointSet_eq x,
    GridState.JNum_pointSet_eq x G.O, GridState.I_self_pointSet_eq G.O]
  push_cast
  ring

/-- The integer `X`-Maslov grading of a grid state written entirely as counts over column
indices. -/
theorem maslovXℤ_eq_card (x : GridState n) :
    G.maslovXℤ x =
      ((Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ x p.1 < x p.2).card : ℤ)
        - ((Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ x p.1 < G.X p.2).card
          + (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ G.X p.1 < x p.2).card)
        + (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ G.X p.1 < G.X p.2).card + 1 := by
  rw [maslovXℤ_def, XSet, GridState.I_self_pointSet_eq x,
    GridState.JNum_pointSet_eq x G.X, GridState.I_self_pointSet_eq G.X]
  push_cast
  ring

end GridDiagram

end TauCeti
