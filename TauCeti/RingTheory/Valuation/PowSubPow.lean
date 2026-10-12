/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.RingTheory.Valuation.Basic

import Mathlib.Tactic.FieldSimp

/-!
# The valuation of a difference of powers

For a valuation `v` on a commutative ring and elements `x`, `y` with `v x ≤ c` and `v y ≤ c`,
the factorization `x ^ n - y ^ n = (x - y) * ∑ j < n, x ^ j * y ^ (n - 1 - j)` and the
ultrametric inequality give

`v (x ^ n - y ^ n) ≤ v (x - y) * c ^ (n - 1)`.

This estimate controls the nonlinear terms of a power series on sufficiently deep inputs; for
instance, it shows that the logarithm is an isometry on the deep units of a local field.

The exact formulas here say that powers with unit exponent preserve the distance of a
principal unit from one, and compute differences of integer powers after translation by an
element of smaller valuation. These give the displacement orders of explicit
uniformizers in wildly ramified Artin--Schreier extensions.
-/

public section

namespace Valuation

variable {R Γ₀ : Type*} [CommRing R] [LinearOrderedCommMonoidWithZero Γ₀]

/-- If `v x ≤ c` and `v y ≤ c`, then `v (x ^ n - y ^ n) ≤ v (x - y) * c ^ (n - 1)`. -/
theorem map_pow_sub_pow_le (v : Valuation R Γ₀) {x y : R} {c : Γ₀} (hx : v x ≤ c)
    (hy : v y ≤ c) (n : ℕ) :
    v (x ^ n - y ^ n) ≤ v (x - y) * c ^ (n - 1) := by
  rw [← geom_sum₂_mul, map_mul, mul_comm]
  gcongr
  refine v.map_sum_le fun j hj => ?_
  -- Each summand `x ^ j * y ^ (n - 1 - j)` has total degree `n - 1`.
  have hdeg : j + (n - 1 - j) = n - 1 := by
    have := Finset.mem_range.mp hj
    omega
  calc v (x ^ j * y ^ (n - 1 - j)) ≤ c ^ j * c ^ (n - 1 - j) := by
        simp only [map_mul, map_pow]
        gcongr <;> exact zero_le
    _ = c ^ (n - 1) := by rw [← pow_add, hdeg]

/-- Raising a principal unit to a natural power of valuation one preserves its distance
from one. -/
@[simp] theorem map_one_add_pow_sub_one (v : Valuation R Γ₀) {x : R} (hx : v x < 1)
    (n : ℕ) (hn : v (n : R) = 1) : v ((1 + x) ^ n - 1) = v x := by
  have : Nontrivial Γ₀ := ⟨⟨v x, 1, ne_of_lt hx⟩⟩
  have ha : v (1 + x) = 1 := v.map_one_add_of_lt hx
  have hsum : v ((∑ i ∈ Finset.range n, (1 + x) ^ i) - (n : R)) < 1 := by
    have hcast : (n : R) = ∑ _i ∈ Finset.range n, (1 : R) := by simp
    rw [hcast, ← Finset.sum_sub_distrib]
    apply v.map_sum_lt one_ne_zero
    intro i _
    have h := v.map_pow_sub_pow_le ha.le (le_of_eq v.map_one) i
    simp only [one_pow, mul_one, add_sub_cancel_left] at h
    exact h.trans_lt hx
  have hs : v (∑ i ∈ Finset.range n, (1 + x) ^ i) = 1 := by
    have h := v.map_add_eq_of_lt_left (hsum.trans_eq hn.symm)
    simpa [hn] using h
  rw [← geom_sum_mul, map_mul, hs, one_mul]
  simp

variable {F Γ₁ : Type*} [Field F] [LinearOrderedCommGroupWithZero Γ₁]

/-- Raising a principal unit to an integer power of valuation one preserves its distance
from one, including negative powers. -/
@[simp] theorem map_one_add_zpow_sub_one (v : Valuation F Γ₁) {x : F} (hx : v x < 1)
    (n : ℤ) (hn : v (n : F) = 1) : v ((1 + x) ^ n - 1) = v x := by
  have ha : v (1 + x) = 1 := v.map_one_add_of_lt hx
  have ha0 : 1 + x ≠ 0 := by
    intro h
    simp [h] at ha
  cases n with
  | ofNat n => simpa using v.map_one_add_pow_sub_one hx n (by simpa using hn)
  | negSucc n =>
    have hneg : (Int.negSucc n : F) = -((n + 1 : ℕ) : F) := by
      push_cast
      ring
    rw [hneg, v.map_neg] at hn
    have hp := v.map_one_add_pow_sub_one hx (n + 1) hn
    have heq : (1 + x) ^ (Int.negSucc n) - 1 =
        -(((1 + x) ^ (n + 1) - 1) / (1 + x) ^ (n + 1)) := by
      simp only [zpow_negSucc]
      field_simp
      simp_all
    rw [heq, map_neg, map_div, hp, map_pow, ha, one_pow, div_one]

/-- Translating by an element of smaller valuation gives the exact valuation of the
difference of integer powers, when the exponent has valuation one. -/
@[simp] theorem map_add_zpow_sub_zpow (v : Valuation F Γ₁) {y c : F}
    (hc : v c < v y) (n : ℤ) (hn : v (n : F) = 1) :
    v ((y + c) ^ n - y ^ n) = v y ^ (n - 1) * v c := by
  have hyv : v y ≠ 0 := ne_of_gt (lt_of_le_of_lt zero_le hc)
  have hy0 : y ≠ 0 := v.ne_zero_iff.mp hyv
  have hx : v (c / y) < 1 := by
    rw [v.map_div]
    exact (div_lt_one₀ (zero_lt_iff.mpr hyv)).mpr hc
  have he : y + c = y * (1 + c / y) := by field_simp
  have heq : (y + c) ^ n - y ^ n = y ^ n * ((1 + c / y) ^ n - 1) := by
    rw [he, mul_zpow]
    ring
  rw [heq, v.map_mul, map_zpow₀, v.map_one_add_zpow_sub_one hx n hn, v.map_div,
    zpow_sub₀ hyv, zpow_one]
  simp [div_eq_mul_inv, mul_comm, mul_left_comm]

end Valuation
