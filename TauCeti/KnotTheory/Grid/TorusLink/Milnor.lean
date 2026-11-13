/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Algebra.Field.ZMod
public import TauCeti.KnotTheory.Grid.CrossingChange.Tau
public import TauCeti.KnotTheory.Grid.TorusLink.UnknottingNumber

/-!
# The Milnor conjecture for grid knots

This file proves the Milnor conjecture for the grid knots presented by the standard torus link
grids: when `P = p + 1` and `Q = q + 1` are coprime, the unknotting number of the `(P, Q)` torus
knot `(GridDiagram.torusLink p q).toGridLink` is `(P - 1) (Q - 1) / 2 = p q / 2`
(`GridLink.unknottingNumber_toGridLink_torusLink`). When `P` and `Q` are not coprime, the grid link
has multiple components and its unknotting number is `⊤`
(`GridLink.unknottingNumber_toGridLink_torusLink_of_not_coprime`), giving a complete formula for
every `(p, q)` (`GridLink.unknottingNumber_toGridLink_torusLink_eq_ite`).

The upper bound `u ≤ p q / 2` is proved in `TorusLink/UnknottingNumber.lean` by removing full twists
along Euclid's algorithm (`GridLink.unknottingNumber_toGridLink_torusLink_le`). For the matching
lower bound (`GridLink.le_unknottingNumber_toGridLink_torusLink`), the `X`-marking state generates
the non-torsion tower of `GH⁻` in top Alexander degree `p q / 2`, so over `ZMod 2` the grid knot
invariant is `τ = -(p q / 2)` (`GridLink.tau_toGridLink_torusLink`) — negative because
`GridDiagram.torusLink p q` has negative crossings and presents the mirror of the positive `(P, Q)`
torus knot — while the crossing-change homotopy bound `|τ(L)| ≤ u(L)`
(`GridLink.IsKnot.natAbs_tau_le_unknottingNumber`) gives `p q / 2 = |τ| ≤ u`.

Here `GridLink.unknottingNumber` is the distance to the unknot in the crossing-change graph on grid
diagrams modulo grid moves (`CrossingChange/UnknottingNumber.lean`); no identification with smooth
embedded knots in `S³` via Cromwell's theorem is claimed here.

## Main results

* `TauCeti.GridLink.le_unknottingNumber_toGridLink_torusLink`: **the lower bound of the Milnor
  conjecture**, `(p * q / 2 : ℕ) ≤ (torusLink p q).toGridLink.unknottingNumber` for coprime
  `p + 1` and `q + 1`.
* `TauCeti.GridLink.unknottingNumber_toGridLink_torusLink`: **the Milnor conjecture**,
  `(torusLink p q).toGridLink.unknottingNumber = (p * q / 2 : ℕ)` for coprime `p + 1` and `q + 1`.
* `TauCeti.GridLink.unknottingNumber_toGridLink_torusLink_eq_top_iff` and
  `TauCeti.GridLink.unknottingNumber_toGridLink_torusLink_eq_ite`: complete characterization of the
  unknotting number of `(torusLink p q).toGridLink` for arbitrary `p` and `q`.
* `TauCeti.GridLink.unknottingNumber_toGridLink_torusLink_mul`,
  `TauCeti.GridLink.unknottingNumber_toGridLink_torusLink_one_two_mul`, and
  `TauCeti.GridLink.unknottingNumber_toGridLink_torusLink_two_mul_one`: exact unknotting numbers of
  the `(p + 1, k (p + 1) + 1)`, `(2, 2k + 1)`, and `(2k + 1, 2)` torus knots, plus `@[simp]`
  evaluations for the `(2, 3)` and `(3, 2)` trefoils and the `(3, 4)` and `(4, 3)` torus knots.

## References

* J. Milnor, *Singular Points of Complex Hypersurfaces*, Annals of Mathematics Studies 61,
  Princeton University Press, 1968, Section 10: the conjecture `u(T_{P,Q}) = (P - 1) (Q - 1) / 2`.
* P. B. Kronheimer, T. S. Mrowka, *Gauge theory for embedded surfaces. I*, Topology 32 (1993),
  773--826: the original gauge-theoretic proof of the Milnor conjecture.
* P. Ozsváth, Z. Szabó, *Knot Floer homology and the four-ball genus*, Geom. Topol. 7 (2003),
  615--639; J. Rasmussen, *Khovanov homology and the slice genus*, Invent. Math. 182 (2010),
  419--447: the Floer-homological and Khovanov-homological proofs.
* S. Sarkar, *Grid diagrams and the Ozsváth--Szabó tau-invariant*, Math. Res. Lett. 18 (2011),
  1239--1257, arXiv:1011.5265: the combinatorial grid-diagram proof of the Milnor conjecture.
* P. Ozsváth, A. Stipsicz, Z. Szabó, *Grid Homology for Knots and Links*, AMS Mathematical Surveys
  and Monographs 208, 2015, Section 6.2, Corollary 6.2.5.
-/

public section

namespace TauCeti

namespace GridLink

open GridDiagram

/-- **The lower bound of the Milnor conjecture.** If `P = p + 1` and `Q = q + 1` are coprime, the
`(P, Q)` torus knot, presented by its standard grid, has unknotting number at least
`(P - 1) (Q - 1) / 2 = p q / 2`.

Over `ZMod 2`, the grid knot invariant satisfies `τ = -(p q / 2)`
(`GridLink.tau_toGridLink_torusLink`), and `|τ| ≤ u`
(`GridLink.IsKnot.natAbs_tau_le_unknottingNumber`). -/
theorem le_unknottingNumber_toGridLink_torusLink (p q : ℕ) (h : (p + 1).Coprime (q + 1)) :
    (p * q / 2 : ℕ) ≤ (torusLink p q).toGridLink.unknottingNumber := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : (torusLink p q).toGridLink.IsKnot :=
    (isKnot_toGridLink _).mpr ((isKnot_torusLink_iff p q).mpr h)
  have hτ : (hK.tau (ZMod 2)).natAbs = p * q / 2 := by
    rw [tau_toGridLink_torusLink (ZMod 2) h, Int.natAbs_neg, Int.natAbs_natCast]
  simpa only [hτ] using hK.natAbs_tau_le_unknottingNumber (ZMod 2)

/-- **The Milnor conjecture for grid knots.** If `P = p + 1` and `Q = q + 1` are coprime, the
unknotting number of the `(P, Q)` torus knot, presented by its standard grid, is
`(P - 1) (Q - 1) / 2 = p q / 2`. -/
theorem unknottingNumber_toGridLink_torusLink (p q : ℕ) (h : (p + 1).Coprime (q + 1)) :
    (torusLink p q).toGridLink.unknottingNumber = (p * q / 2 : ℕ) :=
  le_antisymm (unknottingNumber_toGridLink_torusLink_le p q h)
    (le_unknottingNumber_toGridLink_torusLink p q h)

/-- When `p + 1` and `q + 1` are not coprime, the `(p + 1, q + 1)` torus link has more than one
component, so its unknotting number is `⊤`. -/
theorem unknottingNumber_toGridLink_torusLink_of_not_coprime {p q : ℕ}
    (h : ¬ (p + 1).Coprime (q + 1)) :
    (torusLink p q).toGridLink.unknottingNumber = ⊤ := by
  by_contra hne
  have hK : (torusLink p q).IsKnot :=
    (isKnot_toGridLink _).mp (isKnot_of_unknottingNumber_ne_top hne)
  exact h ((isKnot_torusLink_iff p q).mp hK)

/-- The standard `(p + 1, q + 1)` torus link has infinite unknotting number if and only if `p + 1`
and `q + 1` are not coprime. -/
theorem unknottingNumber_toGridLink_torusLink_eq_top_iff {p q : ℕ} :
    (torusLink p q).toGridLink.unknottingNumber = ⊤ ↔ ¬ (p + 1).Coprime (q + 1) := by
  refine ⟨fun htop hcop => ?_, unknottingNumber_toGridLink_torusLink_of_not_coprime⟩
  rw [unknottingNumber_toGridLink_torusLink p q hcop] at htop
  exact ENat.natCast_ne_top _ htop

/-- Complete formula for the unknotting number of the standard `(p + 1, q + 1)` torus link grid:
`(p * q / 2 : ℕ)` when `p + 1` and `q + 1` are coprime, and `⊤` otherwise. -/
theorem unknottingNumber_toGridLink_torusLink_eq_ite (p q : ℕ) :
    (torusLink p q).toGridLink.unknottingNumber =
      if (p + 1).Coprime (q + 1) then ((p * q / 2 : ℕ) : ℕ∞) else ⊤ := by
  split_ifs with h
  · exact unknottingNumber_toGridLink_torusLink p q h
  · exact unknottingNumber_toGridLink_torusLink_of_not_coprime h

/-! ### Special families and small torus knots -/

/-- The `(p + 1, k (p + 1) + 1)` torus knot, obtained from `k` full twists on `p + 1` strands, has
unknotting number `k ((p + 1) choose 2)`. -/
theorem unknottingNumber_toGridLink_torusLink_mul (p k : ℕ) :
    (torusLink p (k * (p + 1))).toGridLink.unknottingNumber = k * (p + 1).choose 2 := by
  rw [unknottingNumber_toGridLink_torusLink p (k * (p + 1))
    ((Nat.coprime_mul_right_add_right _ _ _).mpr (Nat.coprime_one_right _)),
    ← Nat.cast_mul, Nat.choose_two_right, Nat.add_sub_cancel, Nat.mul_comm (p + 1) p,
    Nat.mul_left_comm, Nat.mul_div_assoc _ (Nat.even_mul_succ_self p).two_dvd]

/-- The `(k (p + 1) + 1, p + 1)` torus knot has unknotting number `k ((p + 1) choose 2)`. -/
theorem unknottingNumber_toGridLink_torusLink_mul_left (p k : ℕ) :
    (torusLink (k * (p + 1)) p).toGridLink.unknottingNumber = k * (p + 1).choose 2 := by
  rw [unknottingNumber_toGridLink_torusLink_comm, unknottingNumber_toGridLink_torusLink_mul]

/-- The `(2, 2k + 1)` torus knot has unknotting number `k`. -/
theorem unknottingNumber_toGridLink_torusLink_one_two_mul (k : ℕ) :
    (torusLink 1 (2 * k)).toGridLink.unknottingNumber = k := by
  rw [Nat.mul_comm]
  simpa using unknottingNumber_toGridLink_torusLink_mul 1 k

/-- The `(2k + 1, 2)` torus knot has unknotting number `k`. -/
theorem unknottingNumber_toGridLink_torusLink_two_mul_one (k : ℕ) :
    (torusLink (2 * k) 1).toGridLink.unknottingNumber = k := by
  rw [unknottingNumber_toGridLink_torusLink_comm, unknottingNumber_toGridLink_torusLink_one_two_mul]

/-- The `(2, 3)` trefoil knot, presented by its standard `5 × 5` grid, has unknotting number `1`. -/
@[simp]
theorem unknottingNumber_toGridLink_torusLink_one_two :
    (torusLink 1 2).toGridLink.unknottingNumber = 1 := by
  simpa using unknottingNumber_toGridLink_torusLink_one_two_mul 1

/-- The `(3, 2)` trefoil knot, presented by its standard `5 × 5` grid, has unknotting number `1`. -/
@[simp]
theorem unknottingNumber_toGridLink_torusLink_two_one :
    (torusLink 2 1).toGridLink.unknottingNumber = 1 := by
  simpa using unknottingNumber_toGridLink_torusLink_two_mul_one 1

/-- The `(3, 4)` torus knot, presented by its standard `7 × 7` grid, has unknotting number `3`. -/
@[simp]
theorem unknottingNumber_toGridLink_torusLink_two_three :
    (torusLink 2 3).toGridLink.unknottingNumber = 3 := by
  simpa using unknottingNumber_toGridLink_torusLink_mul 2 1

/-- The `(4, 3)` torus knot, presented by its standard `7 × 7` grid, has unknotting number `3`. -/
@[simp]
theorem unknottingNumber_toGridLink_torusLink_three_two :
    (torusLink 3 2).toGridLink.unknottingNumber = 3 := by
  simpa using unknottingNumber_toGridLink_torusLink_mul_left 2 1

end GridLink

end TauCeti
