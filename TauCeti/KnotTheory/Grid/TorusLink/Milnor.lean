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
# The Milnor conjecture for grid torus knots

For coprime winding numbers `P = p + 1` and `Q = q + 1`, the standard torus knot grid
`GridDiagram.torusLink p q` presents a grid knot whose unknotting number is bounded above by
`(P - 1)(Q - 1) / 2 = p q / 2` (`GridLink.unknottingNumber_toGridLink_torusLink_le`, proved by
removing full twists along Euclid's algorithm). Over `ZMod 2`, its grid homology invariant `τ`
equals `-(p q / 2)` (`GridLink.tau_toGridLink_torusLink`; the negative sign reflects that
`torusLink p q` presents the mirror of the positive `(P, Q)` torus knot), while the crossing-change
homotopy bound `|τ(L)| ≤ u(L)` (`GridLink.IsKnot.natAbs_tau_le_unknottingNumber`) bounds its
unknotting number below by `|τ| = p q / 2`. Combining the two bounds proves the Milnor conjecture
on grid links:

  `u(T_{P, Q}) = (P - 1)(Q - 1) / 2 = p q / 2`.

When `P` and `Q` are not coprime, `torusLink p q` has `gcd(P, Q) > 1` components and cannot reach
the unknot by crossing changes, so its unknotting number is `⊤`. This determines
`(torusLink p q).toGridLink.unknottingNumber` for all `p, q : ℕ`.

Here `GridLink.unknottingNumber` is the crossing-change distance from `GridLink.unknot` in
`GridLink.crossingChangeGraph` (cross-commutations modulo grid moves); the topological
identification of grid links and cross-commutations with smooth links and crossing changes in `S³`
is not part of this file.

## Main results

* `TauCeti.GridLink.le_unknottingNumber_toGridLink_torusLink`: **the lower bound of the Milnor
  conjecture**, `(p q / 2 : ℕ) ≤ (torusLink p q).toGridLink.unknottingNumber` for coprime `p + 1`
  and `q + 1`.
* `TauCeti.GridLink.unknottingNumber_toGridLink_torusLink`: **the Milnor conjecture for grid torus
  knots**, `(torusLink p q).toGridLink.unknottingNumber = (p q / 2 : ℕ)` for coprime `p + 1` and
  `q + 1`.
* `TauCeti.GridLink.unknottingNumber_toGridLink_torusLink_eq_ite`: complete closed form for every
  `p, q : ℕ`, equal to `(p q / 2 : ℕ)` when `(p + 1).Coprime (q + 1)` and `⊤` otherwise.
* `TauCeti.GridLink.unknottingNumber_toGridLink_torusLink_mul`,
  `TauCeti.GridLink.unknottingNumber_toGridLink_torusLink_one_two_mul`,
  `TauCeti.GridLink.unknottingNumber_toGridLink_torusLink_two_mul_one`: exact unknotting numbers
  of the `(P, k P + 1)`, `(2, 2 k + 1)`, and `(2 k + 1, 2)` torus knot families.
* `TauCeti.GridLink.unknottingNumber_toGridLink_torusLink_one_two`,
  `TauCeti.GridLink.unknottingNumber_toGridLink_torusLink_two_three`: the trefoil grid `T_{2,3}`
  has unknotting number `1` and the `(3, 4)` torus knot grid `T_{3,4}` has unknotting number `3`.

## References

* J. Milnor, *Singular Points of Complex Hypersurfaces*, Annals of Mathematics Studies 61,
  Princeton University Press, 1968, §10: statement of the unknotting-number conjecture for algebraic
  and torus knots.
* P. B. Kronheimer, T. S. Mrowka, *Gauge theory for embedded surfaces. I*, Topology 32 (1993),
  773--826: first proof of the Milnor conjecture via gauge theory.
* P. Ozsváth, Z. Szabó, *Knot Floer homology and the four-ball genus*, Geom. Topol. 7 (2003),
  615--639: proof via the Heegaard Floer invariant `τ`.
* S. Sarkar, *Grid diagrams and the Ozsváth--Szabó tau-invariant*, Math. Res. Lett. 18 (2011),
  1239--1257, arXiv:1011.5265: combinatorial proof of the Milnor conjecture from grid diagrams.
* P. Ozsváth, A. Stipsicz, Z. Szabó, *Grid Homology for Knots and Links*, AMS Mathematical Surveys
  and Monographs 208, 2015, Chapter 6, Theorem 6.2.4.
-/

public section

namespace TauCeti.GridLink

open GridDiagram

/-- **Lower bound of the Milnor conjecture.** When `p + 1` and `q + 1` are coprime, the grid knot
presented by `torusLink p q` requires at least `p q / 2` crossing changes to unknot, witnessed by
`|τ|` over `ZMod 2`. -/
theorem le_unknottingNumber_toGridLink_torusLink (p q : ℕ) (h : (p + 1).Coprime (q + 1)) :
    (p * q / 2 : ℕ) ≤ (torusLink p q).toGridLink.unknottingNumber := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK := (isKnot_toGridLink (torusLink p q)).mpr ((isKnot_torusLink_iff p q).mpr h)
  have hle := hK.natAbs_tau_le_unknottingNumber (ZMod 2)
  rwa [tau_toGridLink_torusLink (ZMod 2) h, Int.natAbs_neg, Int.natAbs_natCast] at hle

/-- **The Milnor conjecture for grid torus knots.** When `P = p + 1` and `Q = q + 1` are coprime,
the grid knot presented by the standard `(P, Q)` torus knot grid has unknotting number
`(P - 1)(Q - 1) / 2 = p q / 2`. -/
theorem unknottingNumber_toGridLink_torusLink (p q : ℕ) (h : (p + 1).Coprime (q + 1)) :
    (torusLink p q).toGridLink.unknottingNumber = (p * q / 2 : ℕ) :=
  le_antisymm (unknottingNumber_toGridLink_torusLink_le p q h)
    (le_unknottingNumber_toGridLink_torusLink p q h)

/-- When `p + 1` and `q + 1` are not coprime, `torusLink p q` has multiple components and its
unknotting number is `⊤`. -/
theorem unknottingNumber_toGridLink_torusLink_eq_top {p q : ℕ} (h : ¬(p + 1).Coprime (q + 1)) :
    (torusLink p q).toGridLink.unknottingNumber = ⊤ := by
  by_contra hne
  exact h ((isKnot_torusLink_iff p q).mp
    ((isKnot_toGridLink (torusLink p q)).mp (isKnot_of_unknottingNumber_ne_top hne)))

/-- Complete determination of the unknotting number of every standard torus link grid: `(p q / 2)`
for torus knots (`(p + 1).Coprime (q + 1)`) and `⊤` for multi-component torus links. -/
theorem unknottingNumber_toGridLink_torusLink_eq_ite (p q : ℕ) :
    (torusLink p q).toGridLink.unknottingNumber =
      if (p + 1).Coprime (q + 1) then ((p * q / 2 : ℕ) : ℕ∞) else ⊤ := by
  split_ifs with h
  · exact unknottingNumber_toGridLink_torusLink p q h
  · exact unknottingNumber_toGridLink_torusLink_eq_top h

/-- The `(p + 1, k (p + 1) + 1)` torus knot grid has unknotting number `k ((p + 1) choose 2)`. -/
theorem unknottingNumber_toGridLink_torusLink_mul (p k : ℕ) :
    (torusLink p (k * (p + 1))).toGridLink.unknottingNumber = k * (p + 1).choose 2 := by
  rw [unknottingNumber_toGridLink_torusLink p (k * (p + 1))
      ((Nat.coprime_mul_right_add_right _ _ _).mpr (Nat.coprime_one_right _)),
    ← Nat.cast_mul, Nat.choose_two_right, Nat.add_sub_cancel, Nat.mul_comm (p + 1) p,
    Nat.mul_left_comm, Nat.mul_div_assoc _ (Nat.even_mul_succ_self p).two_dvd]

/-- The `(2, 2 k + 1)` torus knot grid has unknotting number `k`. -/
theorem unknottingNumber_toGridLink_torusLink_one_two_mul (k : ℕ) :
    (torusLink 1 (2 * k)).toGridLink.unknottingNumber = k := by
  rw [Nat.mul_comm]
  simpa using unknottingNumber_toGridLink_torusLink_mul 1 k

/-- The `(2 k + 1, 2)` torus knot grid has unknotting number `k`. -/
theorem unknottingNumber_toGridLink_torusLink_two_mul_one (k : ℕ) :
    (torusLink (2 * k) 1).toGridLink.unknottingNumber = k := by
  rw [unknottingNumber_toGridLink_torusLink_comm,
    unknottingNumber_toGridLink_torusLink_one_two_mul]

/-- The `5 × 5` trefoil grid `torusLink 1 2` (`T_{2,3}`) has unknotting number `1`. -/
@[simp]
theorem unknottingNumber_toGridLink_torusLink_one_two :
    (torusLink 1 2).toGridLink.unknottingNumber = 1 := by
  simpa using unknottingNumber_toGridLink_torusLink_one_two_mul 1

/-- The `7 × 7` `(3, 4)` torus knot grid `torusLink 2 3` (`T_{3,4}`) has unknotting number `3`. -/
@[simp]
theorem unknottingNumber_toGridLink_torusLink_two_three :
    (torusLink 2 3).toGridLink.unknottingNumber = 3 := by
  simpa using unknottingNumber_toGridLink_torusLink_mul 2 1

end TauCeti.GridLink
