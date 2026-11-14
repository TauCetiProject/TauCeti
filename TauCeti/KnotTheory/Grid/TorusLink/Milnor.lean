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
# The Milnor conjecture for torus knots via grid homology

For coprime winding numbers `P = p + 1` and `Q = q + 1`, the standard torus knot grid
`GridDiagram.torusLink p q` presents a grid knot whose unknotting number is exactly

  `u(T_{P, Q}) = (P - 1) (Q - 1) / 2 = p q / 2`

(`GridLink.unknottingNumber_toGridLink_torusLink`). Both halves of the equality are purely
combinatorial on grid diagrams:

* *Upper bound* (`GridLink.unknottingNumber_toGridLink_torusLink_le`, in
  `TorusLink/UnknottingNumber.lean`): removing full twists by cross-commutations and reflecting in
  the diagonal, following Euclid's algorithm on `P` and `Q`, unknots the standard `(P, Q)` torus
  knot grid in at most `p q / 2` crossing changes.
* *Lower bound* (`GridLink.le_unknottingNumber_toGridLink_torusLink`): over `𝔽₂ = ZMod 2`, the
  grid-knot invariant `τ` has absolute value `|τ| = p q / 2`
  (`GridLink.natAbs_tau_toGridLink_torusLink`) and is bounded by the unknotting number
  (`GridLink.IsKnot.natAbs_tau_le_unknottingNumber`).

When `P` and `Q` are not coprime, `torusLink p q` has `gcd(P, Q) > 1` components and therefore
infinite unknotting number (`GridLink.unknottingNumber_toGridLink_torusLink_eq_top_of_not_coprime`),
giving a closed formula for every `(p, q)` (`GridLink.unknottingNumber_toGridLink_torusLink_eq_ite`)
and showing that `torusLink p q` presents the unknot if and only if `p = 0` or `q = 0`
(`GridDiagram.toGridLink_torusLink_eq_unknot_iff`).

These results concern `GridLink.unknottingNumber`, the distance from the unknot in the
cross-commutation graph on grid links; identifying grid links and cross-commutations with isotopy
classes and crossing changes of smooth knots in `S³` (via Cromwell's theorem) is not part of this
file.

## Main results

* `TauCeti.GridLink.le_unknottingNumber_toGridLink_torusLink`: the grid-homology lower bound
  `p q / 2 ≤ u` for coprime `p + 1` and `q + 1`.
* `TauCeti.GridLink.unknottingNumber_toGridLink_torusLink`: **the Milnor conjecture**,
  `(torusLink p q).toGridLink.unknottingNumber = p q / 2` for coprime `p + 1` and `q + 1`.
* `TauCeti.GridLink.unknottingNumber_toGridLink_torusLink_eq_ite`: complete closed formula for the
  unknotting number of `(torusLink p q).toGridLink` for all `p, q : ℕ`.
* `TauCeti.GridLink.unknottingNumber_toGridLink_torusLink_mul`,
  `TauCeti.GridLink.unknottingNumber_toGridLink_torusLink_one_two_mul`,
  `TauCeti.GridLink.unknottingNumber_toGridLink_torusLink_two_mul_one`,
  `TauCeti.GridLink.unknottingNumber_toGridLink_torusLink_one_two`,
  `TauCeti.GridLink.unknottingNumber_toGridLink_torusLink_two_three`: exact unknotting numbers of
  the `(p + 1, k (p + 1) + 1)` and `(2, 2k + 1)` families, the trefoil (`u = 1`), and the `(3, 4)`
  torus knot (`u = 3`).
* `TauCeti.GridDiagram.toGridLink_torusLink_eq_unknot_iff`: `(torusLink p q).toGridLink = unknot`
  if and only if `p = 0 ∨ q = 0`.

## References

* P. B. Kronheimer, T. S. Mrowka, *Gauge theory for embedded surfaces. I*, Topology 32 (1993),
  773--826: original gauge-theoretic proof of the Milnor conjecture.
* P. Ozsváth, Z. Szabó, *Knots with unknotting number one and Heegaard Floer homology*, Topology 44
  (2005), and P. Ozsváth, A. Stipsicz, Z. Szabó, *Grid Homology for Knots and Links*, AMS
  Mathematical Surveys and Monographs 208, 2015, Corollary 6.2.5: the combinatorial proof via `τ`
  in grid homology.
* S. Sarkar, *Grid diagrams and the Ozsváth--Szabó tau-invariant*, Math. Res. Lett. 18 (2011),
  arXiv:1011.5265: the purely combinatorial proof of the Milnor conjecture from grid diagrams.
-/

public section

namespace TauCeti

namespace GridLink

open GridDiagram

/-- **The lower bound of the Milnor conjecture.** For coprime `p + 1` and `q + 1`, the `(p + 1,
q + 1)` torus knot, presented by its standard grid, requires at least `p q / 2` crossing changes to
unknot: its `τ`-invariant over `ZMod 2` has absolute value `p q / 2` and changes by at most one per
crossing change. -/
theorem le_unknottingNumber_toGridLink_torusLink (p q : ℕ) (h : (p + 1).Coprime (q + 1)) :
    ((p * q / 2 : ℕ) : ℕ∞) ≤ (torusLink p q).toGridLink.unknottingNumber := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKnot : (torusLink p q).toGridLink.IsKnot :=
    (isKnot_toGridLink _).mpr ((isKnot_torusLink_iff p q).mpr h)
  simpa only [natAbs_tau_toGridLink_torusLink (ZMod 2) h] using
    hKnot.natAbs_tau_le_unknottingNumber (ZMod 2)

/-- **The Milnor conjecture.** If `P = p + 1` and `Q = q + 1` are coprime, the `(P, Q)` torus knot,
presented by its standard grid, has unknotting number `(P - 1) (Q - 1) / 2 = p q / 2`. -/
theorem unknottingNumber_toGridLink_torusLink (p q : ℕ) (h : (p + 1).Coprime (q + 1)) :
    (torusLink p q).toGridLink.unknottingNumber = (p * q / 2 : ℕ) :=
  le_antisymm (unknottingNumber_toGridLink_torusLink_le p q h)
    (le_unknottingNumber_toGridLink_torusLink p q h)

/-- When `p + 1` and `q + 1` are not coprime, the standard `(p + 1, q + 1)` torus link grid has
more than one component, so no sequence of crossing changes reaches the unknot and its unknotting
number is `⊤`. -/
theorem unknottingNumber_toGridLink_torusLink_eq_top_of_not_coprime {p q : ℕ}
    (h : ¬(p + 1).Coprime (q + 1)) :
    (torusLink p q).toGridLink.unknottingNumber = ⊤ := by
  by_contra htop
  exact h ((isKnot_torusLink_iff p q).mp
    ((isKnot_toGridLink _).mp (isKnot_of_unknottingNumber_ne_top htop)))

/-- Closed formula for the unknotting number of every standard torus link grid: `p q / 2` when the
winding numbers `p + 1` and `q + 1` are coprime, and `⊤` otherwise. -/
theorem unknottingNumber_toGridLink_torusLink_eq_ite (p q : ℕ) :
    (torusLink p q).toGridLink.unknottingNumber =
      if (p + 1).Coprime (q + 1) then ((p * q / 2 : ℕ) : ℕ∞) else ⊤ := by
  split_ifs with h
  · exact unknottingNumber_toGridLink_torusLink p q h
  · exact unknottingNumber_toGridLink_torusLink_eq_top_of_not_coprime h

/-- The `(p + 1, k (p + 1) + 1)` torus knot, presented by its standard grid, has unknotting number
`k ((p + 1) choose 2)`. -/
theorem unknottingNumber_toGridLink_torusLink_mul (p k : ℕ) :
    (torusLink p (k * (p + 1))).toGridLink.unknottingNumber = k * (p + 1).choose 2 := by
  rw [unknottingNumber_toGridLink_torusLink p (k * (p + 1))
    ((Nat.coprime_mul_right_add_right _ _ _).mpr (Nat.coprime_one_right _)),
    ← Nat.cast_mul, Nat.choose_two_right, Nat.add_sub_cancel, Nat.mul_comm (p + 1) p,
    Nat.mul_left_comm, Nat.mul_div_assoc _ (Nat.even_mul_succ_self p).two_dvd]

/-- The `(2, 2k + 1)` torus knot, presented by its standard grid, has unknotting number `k`. -/
@[simp]
theorem unknottingNumber_toGridLink_torusLink_one_two_mul (k : ℕ) :
    (torusLink 1 (2 * k)).toGridLink.unknottingNumber = k := by
  rw [Nat.mul_comm]
  simpa using unknottingNumber_toGridLink_torusLink_mul 1 k

/-- The `(2k + 1, 2)` torus knot, presented by its standard grid, has unknotting number `k`. -/
@[simp]
theorem unknottingNumber_toGridLink_torusLink_two_mul_one (k : ℕ) :
    (torusLink (2 * k) 1).toGridLink.unknottingNumber = k := by
  rw [unknottingNumber_toGridLink_torusLink_comm, unknottingNumber_toGridLink_torusLink_one_two_mul]

/-- The trefoil, presented by its standard `5 × 5` `(2, 3)` torus knot grid, has unknotting number
one. -/
@[simp]
theorem unknottingNumber_toGridLink_torusLink_one_two :
    (torusLink 1 2).toGridLink.unknottingNumber = 1 := by
  simpa using unknottingNumber_toGridLink_torusLink_one_two_mul 1

/-- The trefoil, presented by its standard `5 × 5` `(3, 2)` torus knot grid, has unknotting number
one. -/
@[simp]
theorem unknottingNumber_toGridLink_torusLink_two_one :
    (torusLink 2 1).toGridLink.unknottingNumber = 1 := by
  simpa using unknottingNumber_toGridLink_torusLink_two_mul_one 1

/-- The `(3, 4)` torus knot, presented by its standard `7 × 7` grid, has unknotting number
three. -/
@[simp]
theorem unknottingNumber_toGridLink_torusLink_two_three :
    (torusLink 2 3).toGridLink.unknottingNumber = 3 := by
  simpa using unknottingNumber_toGridLink_torusLink_mul 2 1

/-- The `(4, 3)` torus knot, presented by its standard `7 × 7` grid, has unknotting number
three. -/
@[simp]
theorem unknottingNumber_toGridLink_torusLink_three_two :
    (torusLink 3 2).toGridLink.unknottingNumber = 3 := by
  rw [unknottingNumber_toGridLink_torusLink_comm, unknottingNumber_toGridLink_torusLink_two_three]

end GridLink

namespace GridDiagram

/-- A standard `(p + 1, q + 1)` torus link grid presents the unknot if and only if `p = 0` or
`q = 0`: every non-trivial torus knot has positive unknotting number, and every multi-component
torus link has infinite unknotting number. -/
@[simp]
theorem toGridLink_torusLink_eq_unknot_iff (p q : ℕ) :
    (torusLink p q).toGridLink = GridLink.unknot ↔ p = 0 ∨ q = 0 := by
  refine ⟨fun hu => ?_, ?_⟩
  · have h0 : (torusLink p q).toGridLink.unknottingNumber = 0 :=
      GridLink.unknottingNumber_eq_zero_iff.mpr hu
    rw [GridLink.unknottingNumber_toGridLink_torusLink_eq_ite] at h0
    split_ifs at h0 with hcop
    · have hpq : p * q ≤ 1 := by
        have : p * q / 2 = 0 := Nat.cast_eq_zero.mp h0
        omega
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hpq with hpq0 | hpq1
      · exact Nat.mul_eq_zero.mp hpq0
      · obtain ⟨rfl, rfl⟩ := mul_eq_one.mp hpq1
        exact absurd hcop (by decide)
    · exact absurd h0 ENat.top_ne_zero
  · rintro (rfl | rfl)
    · exact toGridLink_torusLink_zero_left q
    · rw [torusLink_zero_right, toGridLink_unknot]

end GridDiagram

end TauCeti
