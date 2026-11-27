/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Group.Unbundled.Int
public import Mathlib.Data.Nat.Sqrt
public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Thue's lemma

For a positive modulus `n` and a residue `t` modulo `n`, **Thue's lemma** provides integers `a`
and `b`, not both zero and of absolute value at most `√n`, with `a + t b ≡ 0 (mod n)`. It follows
from the pigeonhole principle: there are `(⌊√n⌋ + 1) ^ 2 > n` pairs `(x, y)` with
`0 ≤ x, y ≤ ⌊√n⌋`, so two of them have the same value of `x + t y` modulo `n`, and their
difference is the required pair.

The lemma is the standard elementary tool for representing a prime by a binary quadratic form
once a root of the form modulo the prime is known.

## Main results

* `ZMod.exists_abs_le_sqrt_and_intCast_add_mul_eq_zero`: Thue's lemma.
-/

public section

open Finset

namespace ZMod

/-- **Thue's lemma.** For a positive modulus `n` and a residue `t` modulo `n`, there are integers
`a` and `b`, not both zero and of absolute value at most `Nat.sqrt n`, such that `a + t * b = 0`
in `ZMod n`. -/
theorem exists_abs_le_sqrt_and_intCast_add_mul_eq_zero (n : ℕ) [NeZero n] (t : ZMod n) :
    ∃ a b : ℤ, (a ≠ 0 ∨ b ≠ 0) ∧ |a| ≤ n.sqrt ∧ |b| ≤ n.sqrt ∧ (a : ZMod n) + t * b = 0 := by
  have hk : n < (n.sqrt + 1) ^ 2 := Nat.sqrt_lt'.1 (Nat.lt_add_one _)
  obtain ⟨x, hx, y, hy, hxy, hf⟩ := exists_ne_map_eq_of_card_lt_of_maps_to
    (s := range (n.sqrt + 1) ×ˢ range (n.sqrt + 1)) (t := (univ : Finset (ZMod n)))
    (by rw [card_product, card_range, card_univ, ZMod.card, ← sq]; exact hk)
    (f := fun z : ℕ × ℕ ↦ (z.1 : ZMod n) + t * z.2) (fun _ _ ↦ mem_univ _)
  rw [mem_product, mem_range, mem_range] at hx hy
  refine ⟨(x.1 : ℤ) - y.1, (x.2 : ℤ) - y.2, ?_, ?_, ?_, ?_⟩
  · by_contra h
    rw [not_or, not_not, not_not] at h
    exact hxy (Prod.ext (by omega) (by omega))
  · rw [abs_le]
    constructor <;> omega
  · rw [abs_le]
    constructor <;> omega
  · push_cast
    linear_combination hf

end ZMod
