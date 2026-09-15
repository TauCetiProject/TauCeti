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
# Cardinalities of fibres of sign-valued functions

This file records cardinality results for functions valued in `SignType`.

## Main results

* `SignType.ncard_fibre_zero_add_ncard_fibre_neg_add_ncard_fibre_pos`: the three fibres of a
  sign-valued function exhaust its domain.
-/

public section

namespace TauCeti

/-- The three fibres of a sign-valued function exhaust its domain. -/
theorem _root_.SignType.ncard_fibre_zero_add_ncard_fibre_neg_add_ncard_fibre_pos
    {ι : Type*} [Finite ι] (u : ι → SignType) :
    {i | u i = 0}.ncard + {i | u i = -1}.ncard + {i | u i = 1}.ncard = Nat.card ι := by
  have hsigma : Nat.card ι = ∑ s : SignType, Nat.card ↥{i | u i = s} := by
    rw [← Nat.card_sigma]
    exact Nat.card_congr (Equiv.sigmaFiberEquiv u).symm
  simpa [SignType.univ_eq, add_assoc] using hsigma.symm

end TauCeti
