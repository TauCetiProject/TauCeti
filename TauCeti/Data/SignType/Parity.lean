/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Basic.Sign.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

/-!
# Sign changes twisted by powers of `-1`

Sturm-type counts compare the signs of consecutive entries at `+∞` and at `-∞`. At `-∞` a
leading sign `s` of a degree-`m` polynomial becomes `s * (-1) ^ m`. For signs `s` and `t`, the
sign-change indicator of the twisted pair minus that of the original pair is `s * t` when `m + n`
is odd and `0` otherwise.

A finite family of signs with product `1` has an even number of signs `-1`.

## Main results

* `SignType.ite_mul_neg_one_pow_sub_ite`: the difference of the two sign-change indicators.
* `SignType.even_card_filter_eq_neg_one_of_prod_eq_one`: signs with product `1` have an even
  number of signs `-1`.
-/

public section

namespace SignType

/-- A finite family of signs with product `1` has an even number of signs `-1`: no sign is `0`,
and the product is `(-1)` to the number of signs `-1`. -/
theorem even_card_filter_eq_neg_one_of_prod_eq_one {ι : Type*} {s : Finset ι} {ε : ι → SignType}
    (hε : ∏ i ∈ s, ε i = 1) : Even {i ∈ s | ε i = -1}.card := by
  have h0 : ∀ i ∈ s, ε i ≠ 0 := Finset.prod_ne_zero_iff.mp (hε ▸ one_ne_zero)
  -- A nonzero sign is `-1` or `1`.
  have h : ∏ i ∈ s, ε i = ∏ i ∈ s, if ε i = -1 then -1 else 1 :=
    Finset.prod_congr rfl fun i hi ↦
      (by decide : ∀ t : SignType, t ≠ 0 → t = if t = -1 then -1 else 1) _ (h0 i hi)
  rw [h, Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one] at hε
  exact (neg_one_pow_eq_one_iff_even (by decide)).mp hε

/-- Comparing the signs `s * (-1) ^ m` and `t * (-1) ^ n` instead of `s` and `t` changes the
sign-change indicator by `s * t` when `m + n` is odd and leaves it unchanged otherwise. If `s` or
`t` is zero, both sides are `0`. -/
theorem ite_mul_neg_one_pow_sub_ite (s t : SignType) (m n : ℕ) :
    ((if s * (-1) ^ m = t * (-1) ^ n then 0 else 1 : ℤ) - if s = t then 0 else 1) =
      if Odd (m + n) then (s : ℤ) * t else 0 := by
  rcases Nat.even_or_odd m with hm | hm <;> rcases Nat.even_or_odd n with hn | hn <;>
    cases s <;> cases t <;>
    simp [hm.neg_one_pow, hn.neg_one_pow, hm, hn, Nat.odd_add, Nat.not_odd_iff_even.mpr]

end SignType
