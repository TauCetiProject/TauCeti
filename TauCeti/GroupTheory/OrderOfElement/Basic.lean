/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.OrderOfElement
public import TauCeti.Data.Nat.Factorization.MulDvd

/-!
# Orders of elements and cardinalities

Let `g` have finite order `n` and let `f` divide `n`. The order of `g ^ k` is `n / gcd n k`, so
`f` divides it exactly when `f * gcd n k` divides `n`. That condition is decided one prime of `f`
at a time: it fails at `p` exactly when `k` is divisible by `p ^ (v_p n - v_p f + 1)`, the room
`n` leaves at `p` after `f`, plus one.

In a finite additive group with one, the cardinality casts to `0`, as Mathlib's
`Nat.cast_card_eq_zero` records, so the cardinality minus one casts to `-1`.

## Main results

* `IsOfFinOrder.dvd_orderOf_pow_iff`, and its additive counterpart: divisibility of the order of
  a power as non-divisibility of its exponent by a prime power at each prime of `f`.
* `TauCeti.natCast_natCard_sub_one_eq_neg_one`: in a finite additive group with one of
  cardinality `q`, the cast of `q - 1` is `-1`, a companion of Mathlib's `Nat.cast_card_eq_zero`.
-/

public section

namespace IsOfFinOrder

variable {G : Type*} [Monoid G]

/-- **When a number divides the order of a power.** Let `g` have finite order and let `f` divide
that order. Then `f` divides the order of `g ^ k` exactly when, for every prime `p` of `f`, the
exponent `k` is not divisible by `p ^ (v_p (orderOf g) - v_p f + 1)`.

The exponent is the room `orderOf g` leaves at `p` after `f` has taken `v_p f`, plus one: the
order of `g ^ k` is `orderOf g / gcd (orderOf g) k`, so `k` may absorb at most
`v_p (orderOf g) - v_p f` powers of `p`; the first forbidden exponent is that room plus one. -/
@[to_additive
/-- **When a number divides the additive order of a multiple.** Let `g` have finite additive order
and let `f` divide that order. Then `f` divides the additive order of `k • g` exactly when, for
every prime `p` of `f`, the exponent `k` is not divisible by
`p ^ (v_p (addOrderOf g) - v_p f + 1)`. -/]
theorem dvd_orderOf_pow_iff {g : G} (hg : IsOfFinOrder g) {f : ℕ}
    (hf : f ∣ orderOf g) (k : ℕ) :
    f ∣ orderOf (g ^ k) ↔
      ∀ p ∈ f.primeFactors, ¬p ^ ((orderOf g).factorization p - f.factorization p + 1) ∣ k := by
  have h0 : orderOf g ≠ 0 := hg.orderOf_pos.ne'
  rw [hg.orderOf_pow, Nat.dvd_div_iff_mul_dvd (Nat.gcd_dvd_left _ k), mul_comm,
    Nat.mul_dvd_iff_forall_not_pow_dvd h0 hf (Nat.gcd_dvd_left _ k)]
  refine forall₂_congr fun p hp => not_congr ?_
  rw [Nat.dvd_gcd_iff, and_iff_right (Nat.pow_factorization_sub_factorization_add_one_dvd hf hp)]

end IsOfFinOrder

namespace TauCeti

/-- In a finite additive group with one of cardinality `q`, the cast of `q - 1` is `-1`. -/
@[simp high]
theorem natCast_natCard_sub_one_eq_neg_one (R : Type*) [AddGroupWithOne R] [Finite R] :
    ((Nat.card R - 1 : ℕ) : R) = -1 := by
  cases subsingleton_or_nontrivial R
  · exact Subsingleton.elim _ _
  have := Fintype.ofFinite R
  rw [Nat.cast_sub Finite.one_lt_card.le, Nat.card_eq_fintype_card, Nat.cast_card_eq_zero,
    Nat.cast_one, zero_sub]

end TauCeti
