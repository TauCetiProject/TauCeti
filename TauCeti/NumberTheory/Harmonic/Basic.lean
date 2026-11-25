/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Data.Rat.Cast.CharZero
public import Mathlib.NumberTheory.Harmonic.Defs

/-!
# Basic facts about the harmonic numbers

Mathlib defines the harmonic number `harmonic n = ∑_{i < n} 1 / (i + 1)` as a rational number.
This file records its cast to a characteristic-zero division ring as the corresponding sum
(`TauCeti.harmonic_cast_eq_sum_range`) and its nonnegativity (`TauCeti.harmonic_nonneg`).
-/

public section

namespace TauCeti

/-- The harmonic number `H_n` cast to a characteristic-zero division ring is the sum
`∑_{i < n} 1 / (i + 1)` there. -/
theorem harmonic_cast_eq_sum_range {K : Type*} [DivisionRing K] [CharZero K] (n : ℕ) :
    (harmonic n : K) = ∑ i ∈ Finset.range n, ((i + 1 : ℕ) : K)⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [harmonic_succ, Rat.cast_add, Rat.cast_inv, Rat.cast_natCast, Finset.sum_range_succ, ih]

/-- The harmonic numbers are nonnegative. -/
theorem harmonic_nonneg (n : ℕ) : 0 ≤ harmonic n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [harmonic_succ]
    exact add_nonneg ih (inv_nonneg.2 (Nat.cast_nonneg _))

end TauCeti
