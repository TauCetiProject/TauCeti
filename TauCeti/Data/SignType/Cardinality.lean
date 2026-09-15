/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Sign.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Cardinalities of fibers of sign-valued functions

This file records cardinality results for functions valued in `SignType`.

Since a sign takes only the three values `0`, `-1` and `1`, the cardinality of the zero fiber of a
sign-valued function on a finite type is determined by the size of the domain together with the
cardinalities of the two nonzero fibers.  This is what makes two sign-valued functions comparable
fiberwise once their positive and negative fibers are known to match: it upgrades an agreement of
the two nonzero fibers to an agreement of all three, as happens for the sign-valued
diagonalizations of two real quadratic forms with the same dimension and the same indices of
inertia.

## Main results

* `SignType.ncard_fiber_zero_add_ncard_fiber_neg_add_ncard_fiber_pos`: the three fibers of a
  sign-valued function exhaust its domain.
-/

public section

namespace TauCeti

/-- The three fibers of a sign-valued function exhaust its domain. -/
theorem _root_.SignType.ncard_fiber_zero_add_ncard_fiber_neg_add_ncard_fiber_pos
    {ι : Type*} [Finite ι] (u : ι → SignType) :
    {i | u i = 0}.ncard + {i | u i = -1}.ncard + {i | u i = 1}.ncard = Nat.card ι := by
  have hsigma : Nat.card ι = ∑ s : SignType, Nat.card ↥{i | u i = s} := by
    rw [← Nat.card_sigma]
    exact Nat.card_congr (Equiv.sigmaFiberEquiv u).symm
  simpa [SignType.univ_eq, add_assoc] using hsigma.symm

end TauCeti
