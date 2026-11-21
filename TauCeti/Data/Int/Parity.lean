/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Int.Parity
public import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Algebra.Ring.Int.Units
import Mathlib.RingTheory.Coprime.Lemmas

/-!
# Parity of coprime integers

If one of two coprime integers is even, then the other is odd, since two even integers share the
non-unit common divisor `2`. This applies in particular to adjacent entries of matrices in
`SL(2, ℤ)`.

## Main results

* `IsCoprime.odd_of_even`: if `IsCoprime a b` and `Even a`, then `Odd b`.
-/

public section

/-- If one of two coprime integers is even, the other is odd. -/
theorem IsCoprime.odd_of_even {a b : ℤ} (hab : IsCoprime a b) (ha : Even a) : Odd b := by
  by_contra hb
  have hunit := hab.isUnit_of_dvd' (even_iff_two_dvd.mp ha)
    (even_iff_two_dvd.mp (Int.not_odd_iff_even.mp hb))
  rcases Int.isUnit_iff.mp hunit with h | h <;> norm_num at h
