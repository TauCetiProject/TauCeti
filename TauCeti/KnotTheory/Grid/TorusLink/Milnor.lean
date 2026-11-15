/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.TorusLink.UnknottingNumber
import Mathlib.Algebra.Field.ZMod
import TauCeti.Data.Nat.Choose.Basic
import TauCeti.Data.Nat.GCD
import TauCeti.KnotTheory.Grid.CrossingChange.Tau

/-!
# The Milnor conjecture for grid torus knots

For coprime `P = p + 1` and `Q = q + 1`, the `(P, Q)` torus knot presented by its standard grid
diagram `GridDiagram.torusLink p q` has grid unknotting number

  `u(T_{P,Q}) = (P - 1)(Q - 1) / 2 = p q / 2`.

This file completes the proof by combining two ingredients:

1. **The combinatorial upper bound** (`GridLink.unknottingNumber_toGridLink_torusLink_le` in
   `TorusLink/UnknottingNumber.lean`), obtained by removing full twists on `P` strands at a cost of
   `P choose 2` crossing changes and reflecting across the diagonal along Euclid's algorithm.
2. **The homological lower bound** (`GridLink.le_unknottingNumber_toGridLink_torusLink`), obtained
   from the unknotting-number bound `|τ(L)| ≤ u(L)`
   (`GridLink.IsKnot.natAbs_tau_le_unknottingNumber` in `CrossingChange/Tau.lean`) evaluated over
   `ZMod 2`, together with the computation `τ(T_{P,Q}) = -(p q / 2)`
   (`GridLink.tau_toGridLink_torusLink` in `Move/Tau.lean`).

Applying the Lipschitz bound `|τ(L) - τ(L')| ≤ d(L, L')` directly to a single full twist likewise
pins down the exact crossing-change distance `(p + 1).choose 2` between the `(P, Q + P)` and
`(P, Q)` torus knots (`GridLink.crossingChangeGraph_edist_torusLink_add`).

All statements are formulated purely for `GridLink.unknottingNumber` and
`GridLink.crossingChangeGraph.edist`; the auxiliary field `ZMod 2` and grid homology appear only in
the proofs, and no identification between grid links and smooth knots in `S³` is used.

## Main results

* `TauCeti.GridLink.le_unknottingNumber_toGridLink_torusLink`: **the lower bound of the Milnor
  conjecture**, `p q / 2 ≤ u(T_{p+1, q+1})` for coprime `p + 1` and `q + 1`.
* `TauCeti.GridLink.unknottingNumber_toGridLink_torusLink`: **the Milnor conjecture for grid torus
  knots**, `u(T_{p+1, q+1}) = p q / 2` for coprime `p + 1` and `q + 1`.
* `TauCeti.GridLink.crossingChangeGraph_edist_torusLink_add`: removing a full twist from a torus
  knot has exact crossing-change distance `(p + 1).choose 2`.
* `TauCeti.GridLink.unknottingNumber_toGridLink_torusLink_add`: adding a full twist to a torus knot
  increases its unknotting number by `(p + 1).choose 2`.
* `TauCeti.GridLink.unknottingNumber_toGridLink_torusLink_mul`,
  `TauCeti.GridLink.unknottingNumber_toGridLink_torusLink_one_two_mul`,
  `TauCeti.GridLink.unknottingNumber_toGridLink_torusLink_two_mul_one`: exact unknotting numbers of
  the `(P, k P + 1)`, `(2, 2k + 1)`, and `(2k + 1, 2)` torus knots.
* `TauCeti.GridLink.unknottingNumber_toGridLink_torusLink_one_two`,
  `TauCeti.GridLink.unknottingNumber_toGridLink_torusLink_two_three`: the trefoil `T_{2,3}` has
  unknotting number `1`, and `T_{3,4}` has unknotting number `3`.

## References

* J. Milnor, *Singular Points of Complex Hypersurfaces*, Annals of Mathematics Studies 61,
  Princeton University Press, 1968, Section 10: the original conjecture `u(T_{P,Q}) = (P-1)(Q-1)/2`.
* P. B. Kronheimer, T. S. Mrowka, *Gauge theory for embedded surfaces, I*, Topology 32 (1993),
  773--826: the first proof of the Milnor conjecture, via gauge theory.
* P. Ozsváth, Z. Szabó, *Knot Floer homology and the four-ball genus*, Geom. Topol. 7 (2003),
  615--639: the concordance invariant `τ` and its proof of the Milnor conjecture.
* S. Sarkar, *Grid diagrams and the Ozsváth--Szabó tau-invariant*, Math. Res. Lett. 18 (2011),
  1239--1257, arXiv:1011.5265: the purely combinatorial proof from grid diagrams.
* P. Ozsváth, A. Stipsicz, Z. Szabó, *Grid Homology for Knots and Links*, AMS Mathematical Surveys
  and Monographs 208, 2015, Section 6.2, Corollary 6.2.4.
-/

public section

namespace TauCeti.GridLink

open GridDiagram

/-- **The lower bound of the Milnor conjecture.** If `p + 1` and `q + 1` are coprime, the grid knot
presented by `torusLink p q` has unknotting number at least `p * q / 2`. -/
theorem le_unknottingNumber_toGridLink_torusLink (p q : ℕ) (h : (p + 1).Coprime (q + 1)) :
    ((p * q / 2 : ℕ) : ℕ∞) ≤ (torusLink p q).toGridLink.unknottingNumber := by
  have hle := (isKnot_toGridLink_torusLink h).natAbs_tau_le_unknottingNumber (ZMod 2)
  rwa [tau_toGridLink_torusLink (ZMod 2) h, Int.natAbs_neg, Int.natAbs_natCast] at hle

/-- **The Milnor conjecture for grid torus knots.** If `P = p + 1` and `Q = q + 1` are coprime, the
`(P, Q)` torus knot presented by its standard grid diagram has unknotting number
`(P - 1)(Q - 1) / 2 = p * q / 2`. -/
theorem unknottingNumber_toGridLink_torusLink (p q : ℕ) (h : (p + 1).Coprime (q + 1)) :
    (torusLink p q).toGridLink.unknottingNumber = (p * q / 2 : ℕ) :=
  le_antisymm (unknottingNumber_toGridLink_torusLink_le p q h)
    (le_unknottingNumber_toGridLink_torusLink p q h)

/-- Removing a full twist from a torus knot requires at least `(p + 1).choose 2` crossing
changes. -/
theorem le_crossingChangeGraph_edist_torusLink_add (p q : ℕ) (h : (p + 1).Coprime (q + 1)) :
    ((p + 1).choose 2 : ℕ∞) ≤
      crossingChangeGraph.edist (torusLink p (q + (p + 1))).toGridLink
        (torusLink p q).toGridLink := by
  have h' := Nat.coprime_add_self_add_right.mpr h
  have hle := (isKnot_toGridLink_torusLink h').natAbs_tau_sub_le_edist
    (isKnot_toGridLink_torusLink h) (ZMod 2)
  rw [tau_toGridLink_torusLink (ZMod 2) h', tau_toGridLink_torusLink (ZMod 2) h,
    Nat.mul_add_succ_div_two] at hle
  have hdiff :
      ((-(((p + 1).choose 2 + p * q / 2 : ℕ) : ℤ) - -((p * q / 2 : ℕ) : ℤ)).natAbs : ℕ∞) =
        ((p + 1).choose 2 : ℕ∞) :=
    congrArg Nat.cast (by omega)
  rwa [hdiff] at hle

/-- **Exact crossing-change distance of a full twist.** For coprime `p + 1` and `q + 1`, the
`(p + 1, q + p + 2)` and `(p + 1, q + 1)` torus knots are at exact distance `(p + 1).choose 2` in
the crossing-change graph. -/
theorem crossingChangeGraph_edist_torusLink_add (p q : ℕ) (h : (p + 1).Coprime (q + 1)) :
    crossingChangeGraph.edist (torusLink p (q + (p + 1))).toGridLink
      (torusLink p q).toGridLink = (p + 1).choose 2 :=
  le_antisymm (crossingChangeGraph_edist_torusLink_add_le p q)
    (le_crossingChangeGraph_edist_torusLink_add p q h)

/-- Adding a full twist on `p + 1` strands to a torus knot increases its unknotting number by
exactly `(p + 1).choose 2`. -/
theorem unknottingNumber_toGridLink_torusLink_add (p q : ℕ) (h : (p + 1).Coprime (q + 1)) :
    (torusLink p (q + (p + 1))).toGridLink.unknottingNumber =
      (p + 1).choose 2 + (torusLink p q).toGridLink.unknottingNumber := by
  rw [unknottingNumber_toGridLink_torusLink p (q + (p + 1))
    (Nat.coprime_add_self_add_right.mpr h),
    unknottingNumber_toGridLink_torusLink p q h, ← Nat.cast_add, Nat.mul_add_succ_div_two]

/-- The `(p + 1, k (p + 1) + 1)` torus knot has unknotting number `k * (p + 1).choose 2`. -/
theorem unknottingNumber_toGridLink_torusLink_mul (p k : ℕ) :
    (torusLink p (k * (p + 1))).toGridLink.unknottingNumber = k * (p + 1).choose 2 := by
  induction k with
  | zero =>
    rw [Nat.zero_mul]
    simp [torusLink_zero_right]
  | succ k ih =>
    rw [Nat.succ_mul, unknottingNumber_toGridLink_torusLink_add p (k * (p + 1)) (by simp), ih,
      Nat.cast_add_one, add_one_mul, add_comm]

/-- The `(2, 2k + 1)` torus knot has unknotting number `k`. -/
theorem unknottingNumber_toGridLink_torusLink_one_two_mul (k : ℕ) :
    (torusLink 1 (2 * k)).toGridLink.unknottingNumber = k := by
  rw [Nat.mul_comm]
  simpa using unknottingNumber_toGridLink_torusLink_mul 1 k

/-- The `(2k + 1, 2)` torus knot has unknotting number `k`. -/
theorem unknottingNumber_toGridLink_torusLink_two_mul_one (k : ℕ) :
    (torusLink (2 * k) 1).toGridLink.unknottingNumber = k := by
  rw [unknottingNumber_toGridLink_torusLink_comm]
  exact unknottingNumber_toGridLink_torusLink_one_two_mul k

/-- The trefoil knot `T_{2,3}`, presented by its standard `5 × 5` grid, has unknotting number
`1`. -/
@[simp]
theorem unknottingNumber_toGridLink_torusLink_one_two :
    (torusLink 1 2).toGridLink.unknottingNumber = 1 := by
  simpa using unknottingNumber_toGridLink_torusLink_one_two_mul 1

/-- The `(3, 4)` torus knot `T_{3,4}`, presented by its standard `7 × 7` grid, has unknotting
number `3`. -/
@[simp]
theorem unknottingNumber_toGridLink_torusLink_two_three :
    (torusLink 2 3).toGridLink.unknottingNumber = 3 := by
  simpa using unknottingNumber_toGridLink_torusLink_mul 2 1

end TauCeti.GridLink
