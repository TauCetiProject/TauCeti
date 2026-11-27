/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.LinearAlgebra.Projectivization.Cardinality

/-!
# The number of lines of `k^ι`

Over a finite division ring `k` with `q` elements, the projective space `ℙ(k^n)` has
`(q^n − 1)/(q − 1)` points (`Projectivization.card''`), so `#ℙ(k^n) · (q − 1) ≤ q^n`. This file
states that product bound with `Nat.card` for an arbitrary division ring `k` and an arbitrary
index type `ι`. It holds trivially outside the finite case: when `ι` is infinite, `ℙ(k^ι)` is
infinite, so its `Nat.card` is `0`; when `k` is infinite, `#k − 1` is `0` in `ℕ` (and `−1` in an
ordered ring). Only for finite `k` does it read as the quotient bound `#ℙ(k^ι) ≤ q^{#ι}/(q − 1)`.
This is the form in which the number of lines of `k^n` enters bounds by powers of `q`, such as
those for the step weights of Kneser's neighbour method.

## Main results

* `Projectivization.card_pi_mul_le_pow`: `#ℙ(k^ι) · (#k − 1) ≤ #k^{#ι}` in `ℕ`.
* `Projectivization.cast_card_pi_mul_le_pow`: the same bound read in an ordered ring, with the
  subtraction `#k − 1` taken there.
-/

public section

namespace Projectivization

open scoped LinearAlgebra.Projectivization

/-- **The number of lines of `k^ι`.** Over a division ring `k`, `#ℙ(k^ι) · (#k − 1) ≤ #k^{#ι}`,
all read with `Nat.card` and with truncated subtraction in `ℕ`. For finite `k` this says that
`ℙ(k^ι)` has at most `#k^{#ι}/(#k − 1)` points; for infinite `k` both `#k` and `#k − 1` are `0`. -/
theorem card_pi_mul_le_pow (k ι : Type*) [DivisionRing k] :
    Nat.card (ℙ k (ι → k)) * (Nat.card k - 1) ≤ Nat.card k ^ Nat.card ι := by
  have hV : Nat.card (ι → k) ≤ Nat.card k ^ Nat.card ι := by
    rcases finite_or_infinite ι with hι | hι
    · rw [Nat.card_fun]
    · rw [Nat.card_eq_zero_of_infinite]
      exact Nat.zero_le _
  exact card k (ι → k) ▸ (Nat.sub_le _ _).trans hV

/-- **The number of lines of `k^ι`, read in an ordered ring.** Over a division ring `k`,
`#ℙ(k^ι) · (#k − 1) ≤ #k^{#ι}` in any ordered ring `R`, with the subtraction taken in `R`: this is
`Projectivization.card_pi_mul_le_pow` when `k` is finite, and for infinite `k` the left side is
`−#ℙ(k^ι) ≤ 0`. -/
theorem cast_card_pi_mul_le_pow (k ι : Type*) [DivisionRing k] {R : Type*} [Ring R]
    [PartialOrder R] [IsOrderedRing R] :
    (Nat.card (ℙ k (ι → k)) : R) * ((Nat.card k : R) - 1) ≤ (Nat.card k : R) ^ Nat.card ι := by
  rcases Nat.eq_zero_or_pos (Nat.card k) with h | h
  · rw [h, Nat.cast_zero, zero_sub, mul_neg_one]
    exact (neg_nonpos.2 (Nat.cast_nonneg _)).trans (pow_nonneg le_rfl _)
  · rw [← Nat.cast_one, ← Nat.cast_sub h, ← Nat.cast_mul, ← Nat.cast_pow]
    exact Nat.mono_cast (card_pi_mul_le_pow k ι)

end Projectivization
