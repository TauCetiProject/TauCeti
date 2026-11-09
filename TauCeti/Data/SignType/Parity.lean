/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Basic.Sign.Basic

/-!
# Sign changes twisted by powers of `-1`

Sturm-type counts compare the signs of consecutive entries at `+∞` and at `-∞`. At `-∞` a
leading sign `s` of a degree-`m` polynomial becomes `s * (-1) ^ m`. For signs `s` and `t`, the
sign-change indicator of the twisted pair minus that of the original pair is `s * t` when `m + n`
is odd and `0` otherwise.

## Main results

* `SignType.ite_mul_neg_one_pow_sub_ite`: the difference of the two sign-change indicators.
-/

public section

namespace TauCeti

/-- Comparing the signs `s * (-1) ^ m` and `t * (-1) ^ n` instead of `s` and `t` changes the
sign-change indicator by `s * t` when `m + n` is odd and leaves it unchanged otherwise. If `s` or
`t` is zero, both sides are `0`. -/
theorem _root_.SignType.ite_mul_neg_one_pow_sub_ite (s t : SignType) (m n : ℕ) :
    ((if s * (-1) ^ m = t * (-1) ^ n then 0 else 1 : ℤ) - if s = t then 0 else 1) =
      if Odd (m + n) then (s : ℤ) * t else 0 := by
  rcases Nat.even_or_odd m with hm | hm <;> rcases Nat.even_or_odd n with hn | hn <;>
    cases s <;> cases t <;>
    simp [hm.neg_one_pow, hn.neg_one_pow, hm, hn, Nat.odd_add, Nat.not_odd_iff_even.mpr]

end TauCeti
