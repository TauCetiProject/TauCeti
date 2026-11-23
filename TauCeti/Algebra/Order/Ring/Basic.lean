/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Linarith

/-!
# Inequalities in ordered rings

For `0 ≤ c` and `1 ≤ p` in a linearly ordered commutative ring, a lower bound `-c < a * p` gives
`-c < a`, since multiplying a negative `a` by `p ≥ 1` only decreases it. With `c` the dimension
of the space, this is the exponent step showing that a power `‖x‖ ^ a` which is locally `Lᵖ` is
also locally integrable.

In an ordered semiring, if a finite indexed family `f : ι → S` is nonnegative and bounded above by
`B`, then `(Fintype.card ι : S) * B` is nonnegative even when `ι` is empty and `B < 0`
(`TauCeti.card_mul_nonneg_of_forall_le`). In an ordered commutative semiring, a bound `a ≤ r ^ n`
with `0 ≤ r * B` and `0 ≤ C` turns `a * ((r * B) ^ n * C)` into `(r ^ 2 * B) ^ n * C`
(`TauCeti.mul_mul_pow_le_sq_mul_pow`).

## Main results

* `TauCeti.neg_lt_of_neg_lt_mul`: `-c < a` from `-c < a * p` for `0 ≤ c` and `1 ≤ p`.
* `TauCeti.card_mul_nonneg_of_forall_le`: `0 ≤ (Fintype.card ι : S) * B` for a nonnegative family
  `f : ι → S` bounded above by `B`.
* `TauCeti.mul_mul_pow_le_sq_mul_pow`: `a * ((r * B) ^ n * C) ≤ (r ^ 2 * B) ^ n * C` from
  `a ≤ r ^ n`, `0 ≤ r * B`, and `0 ≤ C`.
-/

public section

namespace TauCeti

/-- For `c ≥ 0` and `p ≥ 1`, the condition `a p > -c` implies `a > -c`, since multiplying a
negative `a` by `p` only decreases it. With `c` the dimension of the space: when `‖x‖ ^ a` is
locally `Lᵖ`, it is also locally integrable. -/
theorem neg_lt_of_neg_lt_mul {α : Type*} [CommRing α] [LinearOrder α] [IsStrictOrderedRing α]
    {a p c : α} (hc : 0 ≤ c) (hp : 1 ≤ p) (h : -c < a * p) : -c < a := by
  nlinarith

/-- If every member of a finite indexed family `f : ι → S` in an ordered semiring is nonnegative
and bounded above by `B`, then `(Fintype.card ι : S) * B` is nonnegative (even when `ι` is empty
and `B < 0`). -/
theorem card_mul_nonneg_of_forall_le {ι S : Type*} [Fintype ι] [Semiring S] [PartialOrder S]
    [IsOrderedRing S] {f : ι → S} {B : S} (hf0 : ∀ i, 0 ≤ f i) (hfB : ∀ i, f i ≤ B) :
    0 ≤ (Fintype.card ι : S) * B := by
  by_cases hι : Nonempty ι
  · obtain ⟨i₀⟩ := hι
    exact mul_nonneg (Nat.cast_nonneg _) ((hf0 i₀).trans (hfB i₀))
  · rw [not_nonempty_iff] at hι
    simp

/-- If `a ≤ r ^ n`, `0 ≤ r * B`, and `0 ≤ C` in an ordered commutative semiring, then
`a * ((r * B) ^ n * C) ≤ (r ^ 2 * B) ^ n * C`. -/
theorem mul_mul_pow_le_sq_mul_pow {S : Type*} [CommSemiring S] [PartialOrder S] [IsOrderedRing S]
    {a r B C : S} {n : ℕ} (ha : a ≤ r ^ n) (hB0 : 0 ≤ r * B) (hC0 : 0 ≤ C) :
    a * ((r * B) ^ n * C) ≤ (r ^ 2 * B) ^ n * C := by
  calc a * ((r * B) ^ n * C)
      ≤ r ^ n * ((r * B) ^ n * C) :=
        mul_le_mul_of_nonneg_right ha (mul_nonneg (pow_nonneg hB0 _) hC0)
    _ = (r ^ 2 * B) ^ n * C := by rw [← mul_assoc, ← mul_pow, sq, mul_assoc]

end TauCeti
