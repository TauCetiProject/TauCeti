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
`(x - 1) ^ p ^ n = 0`: **an element of `p`-power order is unipotent**.  Only exponential
characteristic `p` is needed, so the statement is read equally in characteristic zero, where it says
that an element with `x ^ 1 = 1` is `1`.

The converse — a unipotent element has `p`-power order — is not proved here.  It fails in
exponential characteristic `1`: in a `ℚ`-algebra containing a nonzero element `ε` of square zero,
`1 + ε` is unipotent while `(1 + ε) ^ n = 1 + n • ε` is `1` only for `n = 0`.

## Main results

* `TauCeti.isNilpotent_sub_one_of_pow_expChar_pow_eq_one`: an element of `p`-power order is
  unipotent.

## References

The implication is the standard characteristic-`p` dictionary between unipotent and `p`-unipotent
elements; see J. E. Humphreys, *Linear Algebraic Groups*, §15.3, and T. A. Springer, *Linear
Algebraic Groups*, §2.4.
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

end TauCeti
