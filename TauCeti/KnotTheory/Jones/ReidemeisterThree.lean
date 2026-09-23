/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.TemperleyLieb

/-!
# The Jones-unit form of the third Reidemeister move

The Kauffman-bracket expansion of a crossing is the unit
`TauCeti.TemperleyLieb.jonesUnit`.  The third Reidemeister move is the braid relation for three
crossings: crossings on adjacent pairs of strands satisfy `σᵢ σᵢ₊₁ σᵢ =
σᵢ₊₁ σᵢ σᵢ₊₁`, while crossings on disjoint pairs commute.  The representation theorem in
`TauCeti.KnotTheory.TemperleyLieb` already proves these identities while constructing the Jones
representation; this module exposes the corresponding identities directly for the crossing units.

These are the algebraic local identities consumed by a planar Reidemeister-III move.  The
PD-code operation and its face-locality hypotheses belong to the planar presentation layer and are
not duplicated here.

## Main results

* `TauCeti.TemperleyLieb.jonesUnit_mul_jonesUnit_comm`: units for disjoint crossings commute.
* `TauCeti.TemperleyLieb.jonesUnit_braid`: units for adjacent crossings satisfy the third
  Reidemeister braid relation.

The conventions follow Jones, *A polynomial invariant for knots via von Neumann algebras*,
Bulletin of the AMS 12 (1985), and Lickorish, *An Introduction to Knot Theory*, Chapter 3.
-/

public section

namespace TauCeti.TemperleyLieb

variable {R : Type*} [CommRing R] {n : ℕ}

/-- Jones units on disjoint pairs of strands commute.  This is the commuting-crossing form of the
third Reidemeister calculus and is the algebraic counterpart of sliding two separated crossings
past one another in a planar diagram. -/
theorem jonesUnit_mul_jonesUnit_comm (a : Rˣ) {i j : Fin (n - 1)}
    (h : (i : ℕ) + 2 ≤ j ∨ (j : ℕ) + 2 ≤ i) :
    jonesUnit a i * jonesUnit a j = jonesUnit a j * jonesUnit a i := by
  rw [← jones_sigma (n := n) a i, ← jones_sigma (n := n) a j,
    ← (jones n a).map_mul, ← (jones n a).map_mul, BraidGroup.sigma_mul_sigma_comm h]

/-- Jones units on adjacent pairs of strands satisfy the braid relation, the algebraic form of the
third Reidemeister move. -/
theorem jonesUnit_braid (a : Rˣ) {i j : Fin (n - 1)}
    (h : (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i) :
    jonesUnit a i * jonesUnit a j * jonesUnit a i =
      jonesUnit a j * jonesUnit a i * jonesUnit a j := by
  simpa only [map_mul, jones_sigma] using congrArg (jones n a) (BraidGroup.sigma_braid h)

end TauCeti.TemperleyLieb
