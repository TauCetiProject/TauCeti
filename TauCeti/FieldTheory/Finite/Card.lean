/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Finite.Basic

/-!
# The order of a finite field and the integers invertible in it

A finite field `K` has `q = p ^ k` elements, where `p` is its characteristic. An integer `n` is
nonzero in `K` exactly when `p ∤ n`, so `q` and `n` are then coprime. This is the form in which the
order `q` of a residue field enters arguments about torsion of order prime to the residue
characteristic: multiplication by `q` is injective on such torsion.

## Main results

* `TauCeti.FiniteField.natCard_coprime_of_natCast_ne_zero`: if `(n : K) ≠ 0`, then `Nat.card K`
  and `n` are coprime.
-/

public section

namespace TauCeti.FiniteField

/-- **The order of a finite field is prime to every integer nonzero in it.** If `(n : K) ≠ 0` in a
finite field `K`, then `Nat.card K = p ^ k` and `n` are coprime, `p` being the characteristic. -/
theorem natCard_coprime_of_natCast_ne_zero {K : Type*} [Field K] [Finite K] {n : ℕ}
    (hn : (n : K) ≠ 0) : (Nat.card K).Coprime n := by
  let := Fintype.ofFinite K
  obtain ⟨k, hp, hcard⟩ := FiniteField.card K (ringChar K)
  rw [Nat.card_eq_fintype_card, hcard]
  exact Nat.Coprime.pow_left _ (hp.coprime_iff_not_dvd.2 fun h ↦ hn ((ringChar.spec K n).2 h))

end TauCeti.FiniteField
