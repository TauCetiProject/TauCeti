/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith

/-!
# Scalar and power bounds in ordered monoids

This file contains monotonicity and exponent bookkeeping for natural scalar multiples and powers
in ordered monoids. The power bound turns valuation estimates for exponential and logarithm
coefficients into geometric decay on deep ideals.

## Main results

* `TauCeti.nsmul_strictMono_of_pos`: natural scalar multiplication by a positive element is
  strictly monotone.
* `TauCeti.pow_mul_pow_le_of_le`: bounds a product of powers using a bound `t ≤ γ ^ i` and
  inequalities between the exponents.
-/

public section

namespace TauCeti

/-- In a preordered additive group with monotone left addition, natural scalar multiplication by
a positive element is strictly monotone. -/
theorem nsmul_strictMono_of_pos {A : Type*} [AddGroup A] [Preorder A] [AddLeftMono A] {a : A}
    (ha : 0 < a) : StrictMono fun n : ℕ ↦ n • a :=
  strictMono_nat_of_lt_succ fun n ↦ by
    rw [succ_nsmul]
    apply lt_of_le_not_ge (le_add_of_nonneg_right ha.le)
    intro h
    exact not_le_of_gt ha (by simpa using h)

/-- If `γ ≤ 1`, `t ≤ γ ^ i`, `e ≤ d * i` and `d * q < m`, then
`t ^ (m * d) * γ ^ (d * i - e) ≤ t ^ d * (γ ^ (d * i - e)) ^ m * γ ^ (d * (e * q))`. -/
theorem pow_mul_pow_le_of_le {M : Type*} [CommMonoid M] [Preorder M] [MulLeftMono M]
    {γ t : M} (hγ : γ ≤ 1) {d e i m q : ℕ} (ht : t ≤ γ ^ i) (hi : e ≤ d * i) (hq : d * q < m) :
    t ^ (m * d) * γ ^ (d * i - e) ≤ t ^ d * (γ ^ (d * i - e)) ^ m * γ ^ (d * (e * q)) := by
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  obtain ⟨s, hs⟩ : ∃ s, d * i = s + e := ⟨d * i - e, by omega⟩
  rw [hs, Nat.add_sub_cancel]
  have hexp : s * (m + 1) + d * (e * q) ≤ i * m * d + s := by
    have : e * (d * q) ≤ e * m := Nat.mul_le_mul_left e (by omega)
    nlinarith
  calc t ^ ((m + 1) * d) * γ ^ s = t ^ d * t ^ (m * d) * γ ^ s := by
        rw [add_mul, one_mul, pow_add, mul_comm (t ^ (m * d))]
    _ ≤ t ^ d * (γ ^ i) ^ (m * d) * γ ^ s := by
        gcongr
    _ = t ^ d * γ ^ (i * m * d + s) := by
        rw [← pow_mul, mul_assoc, ← pow_add, ← mul_assoc i]
    _ ≤ t ^ d * γ ^ (s * (m + 1) + d * (e * q)) :=
        mul_le_mul_right (pow_le_pow_right_of_le_one' hγ hexp) _
    _ = t ^ d * (γ ^ s) ^ (m + 1) * γ ^ (d * (e * q)) := by
        rw [pow_add, ← pow_mul, mul_assoc]

end TauCeti
