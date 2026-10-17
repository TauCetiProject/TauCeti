/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.SpecialLinear.StandardCarrier.TwistedFrobenius
public import TauCeti.GroupTheory.FixedSubgroup.Finiteness

/-!
# Finite graph-twisted fixed groups of the type-A carrier

The graph-twisted fixed points lie over the subfield fixed by the
`p ^ (2 * k)`-power Frobenius, because the square of the twisted map is ordinary Frobenius
with twice the exponent. Over an algebraically closed base field this subfield has
`p ^ (2 * k)` elements.

The argument applies over any field of characteristic `p`, at every rank, provided `k ≠ 0`.
It establishes finiteness of the fixed group, without a simplicity assertion. Finiteness of
the ordinary Frobenius-fixed group is already proved in
`TauCeti.Algebra.Lie.SpecialLinear.StandardCarrier.FixedPoints`.
-/

public section

namespace TauCeti.SlStd

variable (r p k : ℕ) [Fact p.Prime]

/-- The graph-twisted Frobenius has finitely many fixed points: its square fixes their
coordinates under the Frobenius with twice the field exponent. -/
theorem finite_fixedSubgroup_twistedFrobenius (K : Type) [Field K] [CharP K p] (hk : k ≠ 0) :
    Finite ↥(fixedSubgroup (twistedFrobenius r p k K)) := by
  apply finite_fixedSubgroup_of_frobenius_matrix_subgroup p (points r K)
    (twistedFrobenius r p k K) (2 * k) 2 (mul_ne_zero (by decide) hk)
  intro g i j
  change ((twistedFrobenius r p k K (twistedFrobenius r p k K g) :
    Matrix.GeneralLinearGroup (Fin (r + 1)) K) i j) = _
  rw [twistedFrobenius_twistedFrobenius]
  exact coe_frobenius_apply r p (2 * k) K g i j

end TauCeti.SlStd
