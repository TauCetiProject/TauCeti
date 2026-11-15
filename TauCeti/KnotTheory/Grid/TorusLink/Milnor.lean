/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.CrossingChange.Tau
public import TauCeti.KnotTheory.Grid.TorusLink.UnknottingNumber
import Mathlib.Algebra.Field.ZMod

/-!
# The Milnor conjecture for grid knots

The Milnor conjecture, first proved by Kronheimer and Mrowka with gauge theory, says that the
`(P, Q)` torus knot, for coprime `P` and `Q`, has unknotting number `(P - 1) (Q - 1) / 2`. This file
proves it for the grid knots presented by the standard torus link grids, by the combinatorial
argument of grid homology. With `P = p + 1` and `Q = q + 1`, the bound is `p q / 2`.

The upper bound `u ≤ p q / 2` is the explicit unknotting sequence of
`GridLink.unknottingNumber_toGridLink_torusLink_le`, which removes full twists one crossing change
at a time. The lower bound combines `|τ(K)| ≤ u(K)`
(`GridLink.IsKnot.natAbs_tau_le_unknottingNumber`) with the value `2τ = -p q` of `τ` on the
standard torus grid (`GridLink.two_mul_tau_toGridLink_torusLink`), computed over `ZMod 2`. The
standard grid presents the mirror image of the positive torus knot, whose `τ` has the opposite
sign; the unknotting number does not see the sign.

The unknotting number here is that of grid links (`GridLink.unknottingNumber`), defined by
cross-commutations of grid diagrams. Its agreement with the unknotting number of the embedded
torus knot rests on Cromwell's theorem, which is not formalised here.

## Main results

* `TauCeti.GridLink.unknottingNumber_toGridLink_torusLink`: **the Milnor conjecture**, the knot
  of the standard `(p + 1, q + 1)` torus grid, for coprime `p + 1` and `q + 1`, has unknotting
  number `p q / 2`.
* `TauCeti.GridLink.unknottingNumber_toGridLink_torusLink_one_two`: the trefoil, the `(2, 3)`
  torus knot, has unknotting number one.
* `TauCeti.GridLink.unknottingNumber_toGridLink_torusLink_two_three`: the `(3, 4)` torus knot has
  unknotting number three.

## References

* P. Ozsváth, A. Stipsicz, Z. Szabó, *Grid Homology for Knots and Links*, AMS Mathematical Surveys
  and Monographs 208, 2015, Chapter 6, Section 6.3: the Milnor conjecture from the bound
  `|τ(K)| ≤ u(K)` and the value of `τ` on torus knots.
* S. Sarkar, *Grid diagrams and the Ozsváth--Szabó tau-invariant*, Math. Res. Lett. 18 (2011),
  arXiv:1011.5265: the combinatorial proof of the Milnor conjecture.
* P. B. Kronheimer, T. S. Mrowka, *Gauge theory for embedded surfaces. I*, Topology 32 (1993):
  the first proof of the Milnor conjecture.
-/

public section

namespace TauCeti.GridLink

open GridDiagram

/-- **The Milnor conjecture.** The knot presented by the standard `(p + 1, q + 1)` torus grid, for
coprime `p + 1` and `q + 1`, has unknotting number `p q / 2 = ((p + 1) - 1) ((q + 1) - 1) / 2`.

The upper bound is an explicit unknotting sequence. The lower bound is `|τ| ≤ u`, as `2τ = -p q`
for this knot. -/
theorem unknottingNumber_toGridLink_torusLink (p q : ℕ) (h : (p + 1).Coprime (q + 1)) :
    (torusLink p q).toGridLink.unknottingNumber = (p * q / 2 : ℕ) := by
  refine le_antisymm (unknottingNumber_toGridLink_torusLink_le p q h) ?_
  have hL := (isKnot_toGridLink _).mpr ((isKnot_torusLink_iff p q).mpr h)
  have hτ : 2 * hL.tau (ZMod 2) = -((p * q : ℕ) : ℤ) := by
    push_cast
    exact two_mul_tau_toGridLink_torusLink (ZMod 2) h
  have habs : (hL.tau (ZMod 2)).natAbs = p * q / 2 := by omega
  have hle := hL.natAbs_tau_le_unknottingNumber (ZMod 2)
  rwa [habs] at hle

/-- **The Milnor conjecture for the trefoil**: the knot of the standard `5 × 5` grid of the
`(2, 3)` torus knot has unknotting number one. -/
theorem unknottingNumber_toGridLink_torusLink_one_two :
    (torusLink 1 2).toGridLink.unknottingNumber = 1 := by
  simpa using unknottingNumber_toGridLink_torusLink 1 2 (by norm_num)

/-- **The Milnor conjecture for the `(3, 4)` torus knot**: the knot of its standard `7 × 7` grid
has unknotting number three. -/
theorem unknottingNumber_toGridLink_torusLink_two_three :
    (torusLink 2 3).toGridLink.unknottingNumber = 3 := by
  simpa using unknottingNumber_toGridLink_torusLink 2 3 (by norm_num)

end TauCeti.GridLink
