/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.NatAntidiagonal
public import Mathlib.Data.Nat.Choose.Basic
import Mathlib.RingTheory.PowerSeries.WellKnown

/-!
# Upper-index Vandermonde convolution

This file proves the convolution identity for binomial coefficients whose *lower* index is
fixed and whose upper index runs along an antidiagonal:

```text
  ∑_{i + j = n} C(a + i, a) * C(b + j, b) = C(a + b + 1 + n, a + b + 1).
```

It is the coefficient identity behind `(1 - X)⁻⁽ᵃ⁺¹⁾ * (1 - X)⁻⁽ᵇ⁺¹⁾ = (1 - X)⁻⁽ᵃ⁺ᵇ⁺²⁾`, and
generalizes Mathlib's hockey-stick identity `Finset.sum_antidiagonal_choose_add` (the case
`b = 0`). In probability it normalizes the negative hypergeometric law: placing the `(a + 1)`st
of `a + b + 1` marked objects at position `a + 1 + i` among `a + b + 1 + n` objects leaves
`C(a + i, a)` choices before it and `C(b + j, b)` after it.

## Main results

* `Nat.sum_antidiagonal_choose_add_mul_choose_add`: the upper-index Vandermonde convolution.

## References

* R. L. Graham, D. E. Knuth, O. Patashnik, *Concrete Mathematics*, 2nd ed., Addison-Wesley, 1994,
  Section 5.1, equation (5.26).
-/

public section

open Finset

namespace Nat

/-- **Upper-index Vandermonde convolution:**
`∑_{i + j = n} C(a + i, a) * C(b + j, b) = C(a + b + 1 + n, a + b + 1)`.

For `b = 0` this is the hockey-stick identity `Finset.sum_antidiagonal_choose_add`. -/
theorem sum_antidiagonal_choose_add_mul_choose_add (a b n : ℕ) :
    ∑ ij ∈ antidiagonal n, (a + ij.1).choose a * (b + ij.2).choose b =
      (a + b + 1 + n).choose (a + b + 1) := by
  -- Compare the `n`th coefficients of `(∑ Xᵏ) ^ (a + b + 2) = (∑ Xᵏ) ^ (a + 1) * (∑ Xᵏ) ^ (b + 1)`.
  have h := congrArg (PowerSeries.coeff (R := ℤ) n)
    (pow_add (PowerSeries.mk 1 : PowerSeries ℤ) (a + 1) (b + 1))
  rw [show a + 1 + (b + 1) = a + b + 1 + 1 by omega, PowerSeries.mk_one_pow_eq_mk_choose_add,
    PowerSeries.mk_one_pow_eq_mk_choose_add, PowerSeries.mk_one_pow_eq_mk_choose_add,
    PowerSeries.coeff_mul] at h
  simp only [PowerSeries.coeff_mk] at h
  exact_mod_cast h.symm

end Nat
