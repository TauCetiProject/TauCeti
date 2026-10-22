/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Abel

/-!
# Two-variable geometric sums in a noncommutative semiring

Mathlib's `Commute.geom_sum₂_mul_add` and its relatives evaluate the two-variable geometric sum
`S = ∑_{i < m} x ^ i * y ^ (m - 1 - i)` when `x` and `y` commute. Without that hypothesis `S` still
satisfies a telescoping identity, `x * S + y ^ m = S * y + x ^ m`. In a ring it says that `S`
intertwines `x` and `y` up to the error `x ^ m - y ^ m`, so `S` is an exact intertwiner
`x * S = S * y` as soon as `x ^ m = y ^ m`.

The file also records the second-order expansions of `(1 + x) ^ r` and of the geometric sum
`∑_{i < r} (1 + x) ^ i` in a noncommutative ring.

In a ring without zero divisors and for `x ≠ 1`, the `x`-integer `[n]_x = ∑_{i < n} x ^ i` vanishes
exactly when `x ^ n = 1`, because `[n]_x * (x - 1) = x ^ n - 1`. Hence a product of `x`-integers,
such as the split-semisimplicity product `∏_{d=1}^{n} [d]_x` of a Hecke algebra, is nonzero
exactly when `x ^ d ≠ 1` for each of its indices `d`.

## Main results

* `TauCeti.mul_geom_sum₂_add_pow`: `x * S + y ^ m = S * y + x ^ m` in any semiring.
* `TauCeti.exists_one_add_pow_eq_and_geom_sum_eq`: `(1 + x) ^ r = 1 + r x + x² v` and
  `∑_{i < r} (1 + x) ^ i = r + C(r, 2) x + x² w` for some `v` and `w`.
* `TauCeti.geom_sum_eq_zero_iff_pow_eq_one`: for `x ≠ 1` without zero divisors,
  `∑_{i < n} x ^ i = 0 ↔ x ^ n = 1`.
* `TauCeti.prod_geom_sum_ne_zero_iff`: a product of `x`-integers is nonzero exactly when no index
  `d` has `x ^ d = 1`.
-/

public section

namespace TauCeti

open Finset

/-- Telescoping a two-variable geometric sum in a noncommutative semiring:
`x * S + y ^ m = S * y + x ^ m` for `S = ∑_{i < m} x ^ i * y ^ (m - 1 - i)`. -/
theorem mul_geom_sum₂_add_pow {S : Type*} [Semiring S] (x y : S) (m : ℕ) :
    x * (∑ i ∈ range m, x ^ i * y ^ (m - 1 - i)) + y ^ m =
      (∑ i ∈ range m, x ^ i * y ^ (m - 1 - i)) * y + x ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hsum : ∑ i ∈ range (m + 1), x ^ i * y ^ (m + 1 - 1 - i) =
        (∑ i ∈ range m, x ^ i * y ^ (m - 1 - i)) * y + x ^ m := by
      rw [sum_range_succ, sum_mul]
      congr 1
      · refine sum_congr rfl fun i hi ↦ ?_
        have hsub : m + 1 - 1 - i = m - 1 - i + 1 := by
          have := mem_range.mp hi
          omega
        rw [mul_assoc, ← pow_succ, hsub]
      · simp
    rw [hsum]
    calc x * ((∑ i ∈ range m, x ^ i * y ^ (m - 1 - i)) * y + x ^ m) + y ^ (m + 1)
        = (x * (∑ i ∈ range m, x ^ i * y ^ (m - 1 - i)) + y ^ m) * y + x ^ (m + 1) := by
          rw [pow_succ y, pow_succ' x]
          simp only [mul_add, add_mul, mul_assoc, add_comm, add_left_comm]
      _ = ((∑ i ∈ range m, x ^ i * y ^ (m - 1 - i)) * y + x ^ m) * y + x ^ (m + 1) := by rw [ih]

/-- `(1 + x) ^ r = 1 + r x + x² v` and `∑_{i < r} (1 + x) ^ i = r + C(r, 2) x + x² w` for some
`v` and `w`, in any ring. -/
theorem exists_one_add_pow_eq_and_geom_sum_eq {A : Type*} [Ring A] (x : A) (r : ℕ) :
    ∃ v w : A, (1 + x) ^ r = 1 + r * x + x ^ 2 * v ∧
      ∑ i ∈ range r, (1 + x) ^ i = r + (r.choose 2 : ℕ) * x + x ^ 2 * w := by
  induction r with
  | zero => exact ⟨0, 0, by simp, by simp⟩
  | succ r ih =>
    obtain ⟨v, w, hv, hw⟩ := ih
    refine ⟨r + v + v * x, w + v, ?_, ?_⟩
    · rw [pow_succ, hv]
      have h : (r : A) * x * x = x ^ 2 * r := by rw [mul_assoc, ← sq, Nat.cast_comm]
      push_cast
      simp only [mul_add, add_mul, mul_one, one_mul, h, ← mul_assoc]
      rw [sq]
      abel
    · rw [sum_range_succ, hw, hv, Nat.choose_succ_succ', Nat.choose_one_right]
      push_cast
      simp only [mul_add, add_mul]
      abel

/-- In a ring without zero divisors and for `x ≠ 1`, the `x`-integer `∑_{i < n} x ^ i` vanishes
exactly when `x ^ n = 1`. -/
theorem geom_sum_eq_zero_iff_pow_eq_one {R : Type*} [Ring R] [NoZeroDivisors R] {x : R}
    (hx : x ≠ 1) (n : ℕ) : ∑ i ∈ range n, x ^ i = 0 ↔ x ^ n = 1 := by
  rw [← sub_eq_zero (a := x ^ n), ← geom_sum_mul, mul_eq_zero, or_iff_left (sub_ne_zero.mpr hx)]

/-- In a commutative ring without zero divisors and for `x ≠ 1`, a product of `x`-integers
`∏_{d ∈ s} ∑_{i < d} x ^ i` is nonzero exactly when `x ^ d ≠ 1` for every `d ∈ s`. -/
theorem prod_geom_sum_ne_zero_iff {R : Type*} [CommRing R] [NoZeroDivisors R] {x : R}
    (hx : x ≠ 1) (s : Finset ℕ) :
    ∏ d ∈ s, ∑ i ∈ range d, x ^ i ≠ 0 ↔ ∀ d ∈ s, x ^ d ≠ 1 := by
  have : Nontrivial R := ⟨⟨x, 1, hx⟩⟩
  simp only [Finset.prod_ne_zero_iff, ne_eq, geom_sum_eq_zero_iff_pow_eq_one hx]

end TauCeti
