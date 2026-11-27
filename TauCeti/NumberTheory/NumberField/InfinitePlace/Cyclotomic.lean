/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import TauCeti.NumberTheory.NumberField.Cyclotomic.Finrank

/-!
# Infinite-place counts above a cyclotomic subfield

A primitive root of unity of order greater than two rules out real places. The number
of infinite places is then half the absolute degree, so adjoining the primitive root over
`ℚ` determines a factor of the place count even in a field that it does not generate.
-/

public section

open NumberField NumberField.InfinitePlace

/-- If `ζ` is a primitive `n`-th root of unity with `n > 2` in a number field `E`, its
number of infinite places is `(φ(n) / 2) * [E : ℚ(ζ)]`. -/
theorem IsPrimitiveRoot.card_infinitePlace_eq_totient_div_two_mul_finrank
    {E : Type*} [Field E] [NumberField E] {n : ℕ} {ζ : E}
    (hζ : IsPrimitiveRoot ζ n) (hn : 2 < n) :
    Fintype.card (InfinitePlace E) =
      n.totient / 2 * Module.finrank (IntermediateField.adjoin ℚ {ζ}) E := by
  let : NeZero n := ⟨by omega⟩
  have hreal := hζ.nrRealPlaces_eq_zero_of_two_lt hn
  rw [card_eq_nrRealPlaces_add_nrComplexPlaces, hreal, zero_add]
  have hdegree := card_add_two_mul_card_eq_rank E
  rw [hreal, zero_add, ← Module.finrank_mul_finrank ℚ (IntermediateField.adjoin ℚ {ζ}) E,
    hζ.finrank_adjoin_eq_totient] at hdegree
  obtain ⟨k, hk⟩ := Nat.totient_even hn
  rw [hk, ← two_mul, mul_assoc] at hdegree
  rw [hk, ← two_mul, Nat.mul_div_cancel_left _ (by decide : 0 < 2)]
  exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) hdegree
