/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Tactic.ByContra
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

The two sums in the binary rearrangement inequality are equal exactly when one pair of
factors agrees. This criterion gives the equality cases of weighted Chebyshev inequalities.

## Main results

* `TauCeti.mul_add_mul_eq_mul_add_mul_iff`: the binary rearrangement sums are equal if and
  only if one pair of factors agrees.

* `TauCeti.neg_lt_of_neg_lt_mul`: `-c < a` from `-c < a * p` for `0 ≤ c` and `1 ≤ p`.
* `TauCeti.one_add_pow_mul_one_add_pow_le`: `(1 + s) ^ i (1 + t) ^ j ≤ (1 + s + t) ^ M` for
  `s, t ≥ 0` and `i + j ≤ M`.
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

/-- The binary rearrangement sums `a * d + b * c` and `a * c + b * d` are equal if and
only if `a = b` or `c = d`. -/
theorem mul_add_mul_eq_mul_add_mul_iff {R : Type*} [Semiring R] [LinearOrder R]
    [IsStrictOrderedRing R] [ExistsAddOfLE R] {a b c d : R} :
    a * d + b * c = a * c + b * d ↔ a = b ∨ c = d := by
  constructor
  · intro heq
    by_contra! h
    rcases lt_or_gt_of_ne h.1 with hab | hab <;> rcases lt_or_gt_of_ne h.2 with hcd | hcd
    · exact (mul_add_mul_lt_mul_add_mul hab hcd).ne heq
    · exact (mul_add_mul_lt_mul_add_mul hab hcd).ne heq.symm
    · exact (mul_add_mul_lt_mul_add_mul hab hcd).ne (by simpa only [add_comm] using heq.symm)
    · exact (mul_add_mul_lt_mul_add_mul hab hcd).ne (by simpa only [add_comm] using heq)
  · rintro (rfl | rfl) <;> simp [add_comm]

end TauCeti
