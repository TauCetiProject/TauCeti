/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.RingTheory.Nilpotent.Defs

/-!
# Unipotent elements and `p`-power order in characteristic `p`

In a ring of exponential characteristic `p` the binomial theorem degenerates to
`(x - y) ^ p ^ n = x ^ p ^ n - y ^ p ^ n` for commuting `x` and `y`
(`sub_pow_expChar_pow_of_commute`).  Taking `y = 1` turns an equation `x ^ p ^ n = 1` into
`(x - 1) ^ p ^ n = 0`: **an element of `p`-power order is unipotent**.

When `p` is prime and the characteristic is exactly `p`, the converse holds too, because a power of
`p` can always be found above the nilpotency index of `x - 1`.  So in characteristic `p` the
unipotent elements are exactly the elements whose order divides a power of `p`.

Primality is used only in the converse direction, and it is not a technicality there: in a
`ℚ`-algebra containing a nonzero element `ε` of square zero, `1 + ε` is unipotent while
`(1 + ε) ^ n = 1 + n • ε` is `1` only for `n = 0`.  Exponential characteristic `1` is therefore not
enough, which is why the forward direction is stated for `ExpChar` and the converse for a prime
`CharP`.

## Main results

* `TauCeti.isNilpotent_sub_one_of_pow_expChar_pow_eq_one`: an element of `p`-power order is
  unipotent.
* `TauCeti.pow_char_pow_eq_one_of_pow_sub_one_eq_zero`: the quantitative converse, whose exponent
  is any power of `p` above a bound for the nilpotency index.
* `TauCeti.isNilpotent_sub_one_iff_exists_pow_char_pow_eq_one`: in characteristic `p`, "unipotent"
  and "of `p`-power order" are the same condition.

## References

The two implications are the standard characteristic-`p` dictionary between unipotent and
`p`-unipotent elements; see J. E. Humphreys, *Linear Algebraic Groups*, §15.3, and
T. A. Springer, *Linear Algebraic Groups*, §2.4.
-/

public section

namespace TauCeti

variable {R : Type*} [Ring R] {x : R}

/-- **An element of `p`-power order is unipotent** in a ring of exponential characteristic `p`:
subtracting `1` and raising to the power `p ^ n` commutes with the subtraction, so `x ^ p ^ n = 1`
forces `(x - 1) ^ p ^ n = 0`. -/
theorem isNilpotent_sub_one_of_pow_expChar_pow_eq_one (p n : ℕ) [ExpChar R p]
    (h : x ^ p ^ n = 1) : IsNilpotent (x - 1) :=
  ⟨p ^ n, by
    rw [sub_pow_expChar_pow_of_commute p n (Commute.one_right x), h, one_pow, sub_self]⟩

/-- **A unipotent element of a ring of prime characteristic `p` has `p`-power order**, with an
explicit exponent: any `n` with `p ^ n` at least the nilpotency index of `x - 1` works. -/
theorem pow_char_pow_eq_one_of_pow_sub_one_eq_zero (p : ℕ) [Fact p.Prime] [CharP R p] {m n : ℕ}
    (hmn : m ≤ p ^ n) (h : (x - 1) ^ m = 0) : x ^ p ^ n = 1 := by
  have hzero : (x - 1) ^ p ^ n = 0 := by
    rw [← Nat.add_sub_cancel' hmn, pow_add, h, zero_mul]
  rwa [sub_pow_char_pow_of_commute p n (Commute.one_right x), one_pow, sub_eq_zero] at hzero

/-- The existential form of `TauCeti.pow_char_pow_eq_one_of_pow_sub_one_eq_zero`: a unipotent
element of a ring of prime characteristic `p` has `p`-power order.  The nilpotency index `m` of
`x - 1` is itself below `p ^ m`, so no separate bound has to be produced. -/
theorem exists_pow_char_pow_eq_one_of_isNilpotent_sub_one (p : ℕ) [Fact p.Prime] [CharP R p]
    (h : IsNilpotent (x - 1)) : ∃ n : ℕ, x ^ p ^ n = 1 := by
  obtain ⟨m, hm⟩ := h
  exact ⟨m, pow_char_pow_eq_one_of_pow_sub_one_eq_zero p
    (Nat.le_of_lt (Nat.lt_pow_self (Fact.out : p.Prime).one_lt)) hm⟩

/-- **In a ring of prime characteristic `p`, an element is unipotent exactly when its order is a
power of `p`.** -/
theorem isNilpotent_sub_one_iff_exists_pow_char_pow_eq_one (p : ℕ) [Fact p.Prime] [CharP R p] :
    IsNilpotent (x - 1) ↔ ∃ n : ℕ, x ^ p ^ n = 1 :=
  ⟨exists_pow_char_pow_eq_one_of_isNilpotent_sub_one p, fun ⟨n, hn⟩ =>
    isNilpotent_sub_one_of_pow_expChar_pow_eq_one p n hn⟩

end TauCeti
