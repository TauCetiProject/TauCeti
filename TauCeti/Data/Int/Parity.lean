/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Int.Parity
public import Mathlib.Data.Int.ModEq
public import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Algebra.Ring.Int.Units
import Mathlib.RingTheory.Coprime.Lemmas

/-!
# Parity of coprime integers and odd integer halves

If one of two coprime integers is even, then the other is odd, since two even integers share the
non-unit common divisor `2`. This applies in particular to adjacent entries of matrices in
`SL(2, ℤ)`. For an odd integer `a`, `(a - 1) / 2` has the same parity as `a.natAbs / 2 + [a < 0]`,
relating signed and natural-number exponents of `-1` in quadratic reciprocity.

## Main results

* `IsCoprime.odd_of_even`: if `IsCoprime a b` and `Even a`, then `Odd b`.
* `Int.sub_one_ediv_two_modEq_natAbs`: for odd `a`,
  `(a - 1) / 2 ≡ a.natAbs / 2 + [a < 0] [ZMOD 2]`.
-/

public section

/-- If one of two coprime integers is even, the other is odd. -/
theorem IsCoprime.odd_of_even {a b : ℤ} (hab : IsCoprime a b) (ha : Even a) : Odd b := by
  by_contra hb
  have hunit := hab.isUnit_of_dvd' (even_iff_two_dvd.mp ha)
    (even_iff_two_dvd.mp (Int.not_odd_iff_even.mp hb))
  rcases Int.isUnit_iff.mp hunit with h | h <;> norm_num at h

/-- For an odd integer `a`, `(a - 1) / 2` has the same parity as `a.natAbs / 2 + [a < 0]`. -/
theorem Int.sub_one_ediv_two_modEq_natAbs {a : ℤ} (ha : Odd a) :
    (a - 1) / 2 ≡ ((a.natAbs / 2 : ℕ) : ℤ) + (if a < 0 then 1 else 0) [ZMOD 2] := by
  obtain ⟨k, hk⟩ := Int.natAbs_odd.mpr ha
  have hdiv : a.natAbs / 2 = k := by omega
  rw [hdiv, Int.modEq_iff_dvd]
  rcases lt_or_ge a 0 with hneg | hnonneg
  · rw [ite_eq_left hneg]
    exact ⟨(k : ℤ) + 1, by omega⟩
  · rw [ite_eq_right (not_lt.mpr hnonneg)]
    exact ⟨0, by omega⟩
