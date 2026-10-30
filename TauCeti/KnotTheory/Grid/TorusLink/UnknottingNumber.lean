/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.TorusLink.FullTwist

/-!
# Unknotting numbers of torus link grids

This file bounds the unknotting number (`GridLink.unknottingNumber`) of the grid links presented
by the standard torus link grids. The Hopf link has unknotting number `⊤`, since it has two
components. Removing a full twist on `P` strands costs at most `P choose 2` crossing changes
(`GridLink.crossingChangeGraph_edist_torusLink_add_le`), so the `(P, k P + 1)` torus knot is
unknotted by `k (P choose 2) = (P - 1) ((k P + 1) - 1) / 2` crossing changes: the upper bound
`u(T_{P,Q}) ≤ (P - 1) (Q - 1) / 2` of the Milnor conjecture for `Q ≡ 1 mod P`. This covers the
trefoil `T_{2,3}`, unknotted by a single crossing change, and the `(3, 4)` torus knot, unknotted
by three.

## Main results

* `TauCeti.GridLink.unknottingNumber_toGridLink_torusLink_one_one`: the Hopf link has unknotting
  number `⊤`.
* `TauCeti.GridLink.unknottingNumber_toGridLink_torusLink_add_le`: removing a full twist from a
  torus link grid lowers the unknotting number by at most `P choose 2`.
* `TauCeti.GridLink.unknottingNumber_toGridLink_torusLink_mul_le`: the `(P, k P + 1)` torus knot
  has unknotting number at most `k (P choose 2)`.
* `TauCeti.GridLink.unknottingNumber_toGridLink_torusLink_one_two_le_one`: the trefoil has
  unknotting number at most one.
* `TauCeti.GridLink.unknottingNumber_toGridLink_torusLink_two_three_le_three`: the `(3, 4)` torus
  knot has unknotting number at most three.

## References

* P. Ozsváth, A. Stipsicz, Z. Szabó, *Grid Homology for Knots and Links*, AMS Mathematical Surveys
  and Monographs 208, 2015, Chapter 6: crossing changes as cross-commutations and the unknotting
  number.
-/

public section

namespace TauCeti

namespace GridLink

/-- The Hopf link, presented by the standard `4 × 4` grid of the `(2, 2)` torus link, has
unknotting number `⊤`: it has two components, so no sequence of crossing changes reaches the
unknot. -/
theorem unknottingNumber_toGridLink_torusLink_one_one :
    (GridDiagram.torusLink 1 1).toGridLink.unknottingNumber = ⊤ := by
  by_contra h
  have := isKnot_of_unknottingNumber_ne_top h
  rw [isKnot_toGridLink] at this
  exact GridDiagram.not_isKnot_torusLink_one_one this

/-- Removing a full twist: the unknotting number of the grid link of the standard
`(p + 1, (q + (p + 1)) + 1)` torus link grid exceeds that of the `(p + 1, q + 1)` torus link grid
by at most `(p + 1) choose 2`. -/
theorem unknottingNumber_toGridLink_torusLink_add_le (p q : ℕ) :
    (GridDiagram.torusLink p (q + (p + 1))).toGridLink.unknottingNumber ≤
      (p + 1).choose 2 + (GridDiagram.torusLink p q).toGridLink.unknottingNumber := by
  rw [unknottingNumber_def, unknottingNumber_def]
  exact SimpleGraph.edist_triangle.trans
    (by gcongr; exact crossingChangeGraph_edist_torusLink_add_le p q)

/-- The `(p + 1, k (p + 1) + 1)` torus knot, presented by its standard grid, has unknotting number
at most `k ((p + 1) choose 2)`. This is the upper bound `u(T_{P,Q}) ≤ (P - 1) (Q - 1) / 2` of the
Milnor conjecture for `P = p + 1` and `Q = k P + 1`: each of the `k` full twists is removed by
`P choose 2` crossing changes, and the `(p + 1, 1)` torus link grid is the standard unknot grid. -/
theorem unknottingNumber_toGridLink_torusLink_mul_le (p k : ℕ) :
    (GridDiagram.torusLink p (k * (p + 1))).toGridLink.unknottingNumber ≤ k * (p + 1).choose 2 := by
  induction k with
  | zero =>
    rw [Nat.zero_mul, GridDiagram.torusLink_zero_right, GridDiagram.toGridLink_unknot,
      unknottingNumber_unknot]
    exact zero_le
  | succ k ih =>
    rw [Nat.succ_mul]
    calc _ ≤ _ := unknottingNumber_toGridLink_torusLink_add_le p (k * (p + 1))
      _ ≤ (p + 1).choose 2 + k * (p + 1).choose 2 := by gcongr
      _ = (k + 1) * (p + 1).choose 2 := by ring

/-- The trefoil, presented by the standard `5 × 5` grid of the `(2, 3)` torus knot, has unknotting
number at most one. -/
theorem unknottingNumber_toGridLink_torusLink_one_two_le_one :
    (GridDiagram.torusLink 1 2).toGridLink.unknottingNumber ≤ 1 := by
  simpa using unknottingNumber_toGridLink_torusLink_mul_le 1 1

/-- The `(3, 4)` torus knot, presented by its standard `7 × 7` grid, has unknotting number at most
three.

This is the upper bound `u(T_{3,4}) ≤ (3 - 1) (4 - 1) / 2` of the Milnor conjecture for this torus
knot. -/
theorem unknottingNumber_toGridLink_torusLink_two_three_le_three :
    (GridDiagram.torusLink 2 3).toGridLink.unknottingNumber ≤ 3 := by
  simpa using unknottingNumber_toGridLink_torusLink_mul_le 2 1

end GridLink

end TauCeti
