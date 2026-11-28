/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Tactic.Linarith

/-!
# Inequalities in ordered rings

For `0 ≤ c` and `1 ≤ p` in a linearly ordered commutative ring, a lower bound `-c < a * p` gives
`-c < a`, since multiplying a negative `a` by `p ≥ 1` only decreases it. With `c` the dimension
of the space, this is the exponent step showing that a power `‖x‖ ^ a` which is locally `Lᵖ` is
also locally integrable.

In an ordered semiring, for `s, t ≥ 0` and `i + j ≤ M`, the product `(1 + s) ^ i (1 + t) ^ j` is
at most `(1 + s + t) ^ M`. This combines polynomial weights in two variables into one, as in
decay estimates in `1 + ‖ξ‖ + ‖m‖`.

In a linearly ordered semiring, clipping two nonnegative elements `x`, `y` at `1` preserves a
lower bound `1 ≤ a x + y` when `a = 0` or `1 ≤ a`. This caps a dual certificate of a covering
linear programme at `1` without losing feasibility.

## Main results

* `TauCeti.neg_lt_of_neg_lt_mul`: `-c < a` from `-c < a * p` for `0 ≤ c` and `1 ≤ p`.
* `TauCeti.one_add_pow_mul_one_add_pow_le`: `(1 + s) ^ i (1 + t) ^ j ≤ (1 + s + t) ^ M` for
  `s, t ≥ 0` and `i + j ≤ M`.
* `TauCeti.one_le_mul_min_one_add_min_one`: `1 ≤ a min(x, 1) + min(y, 1)` from `1 ≤ a x + y` for
  `x, y ≥ 0` and `a = 0 ∨ 1 ≤ a`.
-/

public section

namespace TauCeti

/-- For `c ≥ 0` and `p ≥ 1`, the condition `a p > -c` implies `a > -c`, since multiplying a
negative `a` by `p` only decreases it. With `c` the dimension of the space: when `‖x‖ ^ a` is
locally `Lᵖ`, it is also locally integrable. -/
theorem neg_lt_of_neg_lt_mul {α : Type*} [CommRing α] [LinearOrder α] [IsStrictOrderedRing α]
    {a p c : α} (hc : 0 ≤ c) (hp : 1 ≤ p) (h : -c < a * p) : -c < a := by
  nlinarith

/-- `(1 + s) ^ i (1 + t) ^ j ≤ (1 + s + t) ^ M` for `s, t ≥ 0` and `i + j ≤ M`. -/
theorem one_add_pow_mul_one_add_pow_le {α : Type*} [Semiring α] [PartialOrder α]
    [IsOrderedRing α] {s t : α} (hs : 0 ≤ s) (ht : 0 ≤ t) {i j M : ℕ} (h : i + j ≤ M) :
    (1 + s) ^ i * (1 + t) ^ j ≤ (1 + s + t) ^ M := by
  have hs' : 0 ≤ 1 + s := add_nonneg zero_le_one hs
  have ht' : 0 ≤ 1 + t := add_nonneg zero_le_one ht
  have hst : 1 + t ≤ 1 + s + t := by rw [add_right_comm]; exact le_add_of_nonneg_right hs
  calc (1 + s) ^ i * (1 + t) ^ j ≤ (1 + s + t) ^ i * (1 + s + t) ^ j :=
        mul_le_mul (pow_le_pow_left₀ hs' (le_add_of_nonneg_right ht) i)
          (pow_le_pow_left₀ ht' hst j) (pow_nonneg ht' j) (pow_nonneg (ht'.trans hst) i)
    _ = (1 + s + t) ^ (i + j) := (pow_add _ _ _).symm
    _ ≤ (1 + s + t) ^ M :=
        pow_le_pow_right₀ ((le_add_of_nonneg_right ht).trans' (le_add_of_nonneg_right hs)) h

/-- Clipping at `1` preserves a covering inequality: for `x, y ≥ 0` and `a = 0` or `1 ≤ a`,
`1 ≤ a x + y` implies `1 ≤ a min(x, 1) + min(y, 1)`. -/
theorem one_le_mul_min_one_add_min_one {α : Type*} [Semiring α] [LinearOrder α]
    [IsOrderedRing α] {a x y : α} (hx : 0 ≤ x) (hy : 0 ≤ y) (ha : a = 0 ∨ 1 ≤ a)
    (h : 1 ≤ a * x + y) :
    1 ≤ a * min x 1 + min y 1 := by
  have ha0 : 0 ≤ a := ha.elim (·.ge) zero_le_one.trans
  rcases le_total y 1 with hy1 | hy1
  · rw [min_eq_left hy1]
    rcases le_total x 1 with hx1 | hx1
    · rwa [min_eq_left hx1]
    · rw [min_eq_right hx1, mul_one]
      rcases ha with rfl | ha
      · simpa using h
      · exact le_add_of_le_of_nonneg ha hy
  · rw [min_eq_right hy1]
    exact le_add_of_nonneg_left (mul_nonneg ha0 (le_min hx zero_le_one))

end TauCeti
