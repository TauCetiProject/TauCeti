/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Lemmas

/-!
# Natural casts and `p`-power maps in exponential characteristic `p`

In an additive monoid with one of exponential characteristic `p`, the natural-number cast of
`p ^ n` vanishes whenever `1 < p ^ n`.

In a ring of exponential characteristic `p`, raising to the power `q = p ^ n` commutes with
negation. Mathlib records the special case `(-1) ^ q = -1` (`neg_one_pow_expChar_pow`) and the
additive laws `add_pow_expChar_pow` and `sub_pow_expChar_pow`; this file adds the general negation
law.

## Main results

* `TauCeti.natCast_pow_expChar_eq_zero`: the natural-number cast of `p ^ n` vanishes when
  `1 < p ^ n`.
* `TauCeti.neg_pow_expChar_pow`: `(-x) ^ p ^ n = -x ^ p ^ n`.
-/

public section

namespace TauCeti

/-- In an additive monoid with one of exponential characteristic `p`, the natural-number cast
of `p ^ n` vanishes whenever `1 < p ^ n`. -/
theorem natCast_pow_expChar_eq_zero {R : Type*} [AddMonoidWithOne R] {p n : ℕ} [ExpChar R p]
    (hq : 1 < p ^ n) : ((p ^ n : ℕ) : R) = 0 := by
  have hn : n ≠ 0 := by rintro rfl; simp at hq
  rcases ‹ExpChar R p› with _ | hp
  · simp at hq
  · exact (CharP.cast_eq_zero_iff R p (p ^ n)).2 (dvd_pow_self p hn)

variable {R : Type*} [Ring R] (p n : ℕ) [ExpChar R p]

/-- Raising to the power `q = p ^ n` commutes with negation in exponential characteristic `p`. -/
theorem neg_pow_expChar_pow (x : R) : (-x) ^ p ^ n = -x ^ p ^ n := by
  rw [neg_pow, neg_one_pow_expChar_pow, neg_one_mul]

end TauCeti
