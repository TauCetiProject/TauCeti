/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.Tactic

/-!
# Power bounds in ordered monoids with zero

This file contains an exponent-bookkeeping inequality for elements bounded by a power of an
element at most `1`. It turns valuation estimates for exponential and logarithm coefficients into
geometric decay on deep ideals.

## Main results

* `TauCeti.pow_mul_pow_le_of_le`: bounds a product of powers using a bound `t ≤ γ ^ i` and
  inequalities between the exponents.
-/

public section

namespace TauCeti

/-- If `t ≤ γ ^ i`, `e ≤ d * i` and `d * q < m`, then
`t ^ (m * d) * γ ^ (d * i - e) ≤ t ^ d * (γ ^ (d * i - e)) ^ m * γ ^ (d * (e * q))`. -/
theorem pow_mul_pow_le_of_le {Γ₀ : Type*} [LinearOrderedCommMonoidWithZero Γ₀]
    {γ t : Γ₀} (hγ : γ ≤ 1) {d e i m q : ℕ} (ht : t ≤ γ ^ i) (hi : e ≤ d * i) (hq : d * q < m) :
    t ^ (m * d) * γ ^ (d * i - e) ≤ t ^ d * (γ ^ (d * i - e)) ^ m * γ ^ (d * (e * q)) := by
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  obtain ⟨s, hs⟩ : ∃ s, d * i = s + e := ⟨d * i - e, by omega⟩
  rw [hs, Nat.add_sub_cancel]
  have hdq : e * (d * q) ≤ e * m := Nat.mul_le_mul_left e (by omega)
  have hexp : s * (m + 1) + d * (e * q) ≤ i * m * d + s := by
    have : i * m * d = d * i * m := by ring
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
