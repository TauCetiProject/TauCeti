/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Data.Int.ModEq
import TauCeti.Algebra.Group.Coprime

/-!
# Basic lemmas on monoids and groups with zero

In a reduced commutative monoid with zero, powers can be cancelled from annihilation relations:
if `a * b ^ k = 0`, then `a * b = 0`. In any monoid with zero, two elements that are each either
`0` or an `n`-th root of unity are equal once they agree at a nonzero exponent coprime to `n`. In
a group with zero, integer powers of an `n`-th root of unity depend only on the exponent modulo
`n`.

## Main results

* `TauCeti.mul_eq_zero_of_mul_pow_eq_zero`: in a reduced commutative monoid with zero,
  `a * b ^ k = 0` implies `a * b = 0`.
* `TauCeti.eq_of_pow_eq_of_eq_zero_or_pow_eq_one`: in a monoid with zero, elements that are `0` or
  `n`-th roots of unity are determined by their `f`-th power for `f ≠ 0` coprime to `n`.
* `TauCeti.zpow_eq_zpow_of_modEq`: in a group with zero, if `η ^ n = 1` and `l ≡ m [ZMOD n]`,
  then `η ^ l = η ^ m`.
-/

public section

namespace TauCeti

/-- In a reduced commutative monoid with zero, if `a` kills `b ^ k` then `a` kills `b`. -/
theorem mul_eq_zero_of_mul_pow_eq_zero {M : Type*} [CommMonoidWithZero M] [IsReduced M]
    {a b : M} {k : ℕ} (h : a * b ^ k = 0) : a * b = 0 :=
  -- `(a * b) ^ (k + 1)` is a multiple of `a * b ^ k`.
  eq_zero_of_pow_eq_zero (n := k + 1) <| by
    rw [mul_pow, pow_succ a, pow_succ' b, mul_mul_mul_comm, h, mul_zero]

/-- In a monoid with zero, two elements, each either `0` or an `n`-th root of unity, are equal when
they have equal `f`-th powers for some `f ≠ 0` coprime to `n`. -/
theorem eq_of_pow_eq_of_eq_zero_or_pow_eq_one {M : Type*} [MonoidWithZero M]
    {x y : M} {f n : ℕ} (hf0 : f ≠ 0) (hfn : f.Coprime n) (hxy : x ^ f = y ^ f)
    (hx : x = 0 ∨ x ^ n = 1) (hy : y = 0 ∨ y ^ n = 1) : x = y := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [(Nat.coprime_zero_right f).mp hfn, pow_one, pow_one] at hxy
    exact hxy
  have hzero {a : M} (haf : a ^ f = 0) (han : a ^ n = 1) : a = 0 := by
    have h10 : (1 : M) = 0 := by
      rw [← one_pow f, ← han, ← pow_mul, mul_comm, pow_mul, haf, zero_pow hn]
    rw [← mul_one a, h10, mul_zero]
  rcases hx with rfl | hx <;> rcases hy with rfl | hy
  · rfl
  · exact (hzero (hxy.symm.trans (zero_pow hf0)) hy).symm
  · exact hzero (hxy.trans (zero_pow hf0)) hx
  · exact eq_of_pow_eq_of_pow_eq_one hfn hxy hx hy

/-- In a group with zero, powers of an `n`-th root of unity with exponents congruent modulo `n`
agree. -/
theorem zpow_eq_zpow_of_modEq {G₀ : Type*} [GroupWithZero G₀] {n : ℕ} {η : G₀}
    (hη : η ^ n = 1) {l m : ℤ} (h : l ≡ m [ZMOD n]) : η ^ l = η ^ m := by
  rcases eq_or_ne n 0 with rfl | hn
  · obtain rfl : l = m := by simpa [Int.ModEq] using h
    rfl
  have h₀ : η ≠ 0 := ne_zero_pow hn (hη ▸ one_ne_zero)
  obtain ⟨c, hc⟩ := h.dvd
  have hm : m = l + n * c := by omega
  simp [hm, zpow_add₀ h₀, zpow_mul, hη]

end TauCeti
