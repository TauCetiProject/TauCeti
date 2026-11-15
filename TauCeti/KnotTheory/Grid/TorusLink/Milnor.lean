/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.CrossingChange.Bound
public import TauCeti.KnotTheory.Grid.TorusLink.UnknottingNumber
import Mathlib.Algebra.Field.ZMod

/-!
# The Milnor conjecture for grid torus knots

In 1968 Milnor conjectured that the unknotting number of the `(P, Q)` torus knot, for coprime
positive integers `P` and `Q`, is `(P - 1)(Q - 1) / 2`. This file proves the theorem for the grid
links presented by the standard torus link grids `GridDiagram.torusLink p q` (where `P = p + 1` and
`Q = q + 1`):

* The upper bound `u(T_{P, Q}) ≤ p q / 2` is proved in
  `TauCeti.KnotTheory.Grid.TorusLink.UnknottingNumber` by removing full twists along Euclid's
  algorithm (`GridLink.unknottingNumber_toGridLink_torusLink_le`).
* Over `ZMod 2`, the grid knot invariant `τ` satisfies `|τ(T_{P, Q})| = p q / 2`
  (`GridLink.natAbs_tau_toGridLink_torusLink`) and `|τ(L)| ≤ u(L)`
  (`GridLink.IsKnot.natAbs_tau_le_unknottingNumber`), supplying the matching lower bound
  (`GridLink.le_unknottingNumber_toGridLink_torusLink`).

Combining the two bounds gives `(torusLink p q).toGridLink.unknottingNumber = (p * q / 2 : ℕ)`
whenever `p + 1` and `q + 1` are coprime (`GridLink.unknottingNumber_toGridLink_torusLink`). When
`p + 1` and `q + 1` are not coprime, `torusLink p q` has multiple components and therefore
unknotting number `⊤` (`GridLink.unknottingNumber_toGridLink_torusLink_of_not_coprime`), yielding a
complete closed formula for every `(p, q)`
(`GridLink.unknottingNumber_toGridLink_torusLink_eq_ite`).

As in `CrossingChange/UnknottingNumber.lean` and `TorusLink/Tau.lean`, `GridLink.unknottingNumber`
is the crossing-change distance from `unknot` on grid links (cross-commutations modulo grid moves),
and `torusLink p q` presents the mirror image of the positive torus knot (which has opposite `τ`
and the same unknotting number); the topological equivalence between grid-link and classical smooth
unknotting numbers is not formalised here.

## Main results

* `TauCeti.GridLink.le_unknottingNumber_toGridLink_torusLink`: **the lower bound of the Milnor
  conjecture**, `p q / 2 ≤ u(T_{p+1, q+1})` for coprime `p + 1` and `q + 1`.
* `TauCeti.GridLink.unknottingNumber_toGridLink_torusLink`: **the Milnor conjecture for grid torus
  knots**, `u(T_{p+1, q+1}) = p q / 2` for coprime `p + 1` and `q + 1`.
* `TauCeti.GridLink.unknottingNumber_toGridLink_torusLink_of_not_coprime` and
  `TauCeti.GridLink.unknottingNumber_toGridLink_torusLink_eq_ite`: the complete formula across all
  winding numbers `(p + 1, q + 1)`, equal to `p q / 2` in the coprime case and `⊤` otherwise.
* `TauCeti.GridLink.unknottingNumber_toGridLink_torusLink_eq_zero_iff`: a standard torus link grid
  has unknotting number `0` if and only if `p = 0` or `q = 0`.
* `TauCeti.GridLink.unknottingNumber_toGridLink_torusLink_mul`,
  `TauCeti.GridLink.unknottingNumber_toGridLink_torusLink_one_two_mul`, and
  `TauCeti.GridLink.unknottingNumber_toGridLink_torusLink_two_mul_one`: exact unknotting numbers for
  `(p + 1, k(p + 1) + 1)`, `(2, 2k + 1)`, and `(2k + 1, 2)` torus knots, together with `@[simp]`
  evaluations on the `(2, 3)` and `(3, 2)` trefoils and the `(3, 4)` and `(4, 3)` torus knots.

## References

* J. Milnor, *Singular Points of Complex Hypersurfaces*, Annals of Mathematics Studies 61,
  Princeton University Press, 1968, Section 10: statement of the conjecture.
* P. B. Kronheimer, T. S. Mrowka, *Gauge theory for embedded surfaces. I*, Topology 32 (1993),
  773--826: first proof of the Milnor conjecture, via gauge theory.
* P. Ozsváth, Z. Szabó, *Knot Floer homology and the four-ball genus*, Geom. Topol. 7 (2003),
  615--639; J. Rasmussen, *Khovanov homology and the slice genus*, Invent. Math. 182 (2010),
  419--447: gauge-theory-free proofs via `τ` and `s`.
* S. Sarkar, *Grid diagrams and the Ozsváth--Szabó tau-invariant*, Math. Res. Lett. 18 (2011),
  1239--1257, arXiv:1011.5265; P. Ozsváth, A. Stipsicz, Z. Szabó, *Grid Homology for Knots and
  Links*, AMS Mathematical Surveys and Monographs 208, 2015, Chapter 6: combinatorial proof from
  grid homology.
-/

public section

namespace TauCeti.GridLink

/-- **The lower bound of the Milnor conjecture.** For coprime `P = p + 1` and `Q = q + 1`, the grid
knot presented by `GridDiagram.torusLink p q` requires at least `(P - 1)(Q - 1) / 2 = p q / 2`
crossing changes to unknot, bounded below by `|τ|` over `ZMod 2`. -/
theorem le_unknottingNumber_toGridLink_torusLink (p q : ℕ) (h : (p + 1).Coprime (q + 1)) :
    ((p * q / 2 : ℕ) : ℕ∞) ≤ (GridDiagram.torusLink p q).toGridLink.unknottingNumber := by
  simpa [GridDiagram.natAbs_tau_torusLink h (ZMod 2)] using
    ((GridDiagram.isKnot_torusLink_iff p q).mpr h).natAbs_tau_le_unknottingNumber_toGridLink
      (ZMod 2)

/-- **The Milnor conjecture for grid torus knots.** If `P = p + 1` and `Q = q + 1` are coprime, the
grid knot presented by the standard torus link grid `GridDiagram.torusLink p q` has unknotting
number `(P - 1)(Q - 1) / 2 = p q / 2`. -/
theorem unknottingNumber_toGridLink_torusLink (p q : ℕ) (h : (p + 1).Coprime (q + 1)) :
    (GridDiagram.torusLink p q).toGridLink.unknottingNumber = (p * q / 2 : ℕ) :=
  le_antisymm (unknottingNumber_toGridLink_torusLink_le p q h)
    (le_unknottingNumber_toGridLink_torusLink p q h)

/-- When `p + 1` and `q + 1` are not coprime, the standard `(p + 1, q + 1)` torus link grid has
more than one component, so its unknotting number is `⊤`. -/
theorem unknottingNumber_toGridLink_torusLink_of_not_coprime (p q : ℕ)
    (h : ¬(p + 1).Coprime (q + 1)) :
    (GridDiagram.torusLink p q).toGridLink.unknottingNumber = ⊤ := by
  by_contra htop
  exact h ((GridDiagram.isKnot_torusLink_iff p q).mp
    ((isKnot_toGridLink _).mp (isKnot_of_unknottingNumber_ne_top htop)))

/-- Closed formula for the unknotting number of the grid link of `GridDiagram.torusLink p q` for
arbitrary `p, q : ℕ`: it equals `p q / 2` when `p + 1` and `q + 1` are coprime and `⊤` otherwise. -/
theorem unknottingNumber_toGridLink_torusLink_eq_ite (p q : ℕ) :
    (GridDiagram.torusLink p q).toGridLink.unknottingNumber =
      if (p + 1).Coprime (q + 1) then ((p * q / 2 : ℕ) : ℕ∞) else ⊤ := by
  split_ifs with h
  · exact unknottingNumber_toGridLink_torusLink p q h
  · exact unknottingNumber_toGridLink_torusLink_of_not_coprime p q h

/-- The grid link of `GridDiagram.torusLink p q` has unknotting number `0` (equivalently, is the
unknot) if and only if `p = 0` or `q = 0`. -/
theorem unknottingNumber_toGridLink_torusLink_eq_zero_iff (p q : ℕ) :
    (GridDiagram.torusLink p q).toGridLink.unknottingNumber = 0 ↔ p = 0 ∨ q = 0 := by
  rw [unknottingNumber_toGridLink_torusLink_eq_ite]
  split_ifs with h
  · simp only [Nat.cast_eq_zero]
    have h2 := GridDiagram.two_mul_tau_torusLink h (ZMod 2)
    have h1 := GridDiagram.tau_torusLink h (ZMod 2)
    constructor
    · intro h0
      exact mul_eq_zero.mp (by omega)
    · rintro (rfl | rfl) <;> simp
  · refine ⟨fun htop => absurd htop ENat.top_ne_zero, ?_⟩
    rintro (rfl | rfl)
    · exact absurd (Nat.coprime_one_left _) h
    · exact absurd (Nat.coprime_one_right _) h

/-- The `(p + 1, k (p + 1) + 1)` torus knot grid link has exact unknotting number
`k ((p + 1) choose 2)`: removing each of the `k` full twists by `(p + 1) choose 2` crossing changes
is optimal. -/
theorem unknottingNumber_toGridLink_torusLink_mul (p k : ℕ) :
    (GridDiagram.torusLink p (k * (p + 1))).toGridLink.unknottingNumber =
      (k * (p + 1).choose 2 : ℕ) := by
  rw [unknottingNumber_toGridLink_torusLink p (k * (p + 1))
    ((Nat.coprime_mul_right_add_right _ _ _).mpr (Nat.coprime_one_right _))]
  congr 1
  rw [Nat.choose_two_right, Nat.add_sub_cancel, Nat.mul_comm (p + 1) p,
    Nat.mul_left_comm, Nat.mul_div_assoc _ (Nat.even_mul_succ_self p).two_dvd]

/-- The `(2, 2k + 1)` torus knot grid link has unknotting number `k`. -/
theorem unknottingNumber_toGridLink_torusLink_one_two_mul (k : ℕ) :
    (GridDiagram.torusLink 1 (2 * k)).toGridLink.unknottingNumber = k := by
  rw [Nat.mul_comm]
  simpa using unknottingNumber_toGridLink_torusLink_mul 1 k

/-- The `(2k + 1, 2)` torus knot grid link has unknotting number `k`. -/
theorem unknottingNumber_toGridLink_torusLink_two_mul_one (k : ℕ) :
    (GridDiagram.torusLink (2 * k) 1).toGridLink.unknottingNumber = k := by
  rw [unknottingNumber_toGridLink_torusLink_comm]
  exact unknottingNumber_toGridLink_torusLink_one_two_mul k

/-- The `(2, 3)` trefoil grid link has unknotting number `1`. -/
@[simp]
theorem unknottingNumber_toGridLink_torusLink_one_two :
    (GridDiagram.torusLink 1 2).toGridLink.unknottingNumber = 1 := by
  simpa using unknottingNumber_toGridLink_torusLink_one_two_mul 1

/-- The `(3, 2)` trefoil grid link has unknotting number `1`. -/
@[simp]
theorem unknottingNumber_toGridLink_torusLink_two_one :
    (GridDiagram.torusLink 2 1).toGridLink.unknottingNumber = 1 := by
  simpa using unknottingNumber_toGridLink_torusLink_two_mul_one 1

/-- The `(3, 4)` torus knot grid link has unknotting number `3`. -/
@[simp]
theorem unknottingNumber_toGridLink_torusLink_two_three :
    (GridDiagram.torusLink 2 3).toGridLink.unknottingNumber = 3 := by
  simpa using unknottingNumber_toGridLink_torusLink_mul 2 1

/-- The `(4, 3)` torus knot grid link has unknotting number `3`. -/
@[simp]
theorem unknottingNumber_toGridLink_torusLink_three_two :
    (GridDiagram.torusLink 3 2).toGridLink.unknottingNumber = 3 := by
  rw [unknottingNumber_toGridLink_torusLink_comm]
  exact unknottingNumber_toGridLink_torusLink_two_three

end TauCeti.GridLink
