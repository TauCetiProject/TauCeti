/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Floor.Semifield
public import TauCeti.NumberTheory.Harmonic.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

/-!
# Floor sums and harmonic numbers

For `x` in a linearly ordered field with a floor function and the `M`-th harmonic number `H_M`,
the floor sum `∑_{0 < a ≤ M} ⌊x / a⌋` lies between `x * H_M - M` and, for `x ≥ 0`, `x * H_M`:
each term `⌊x / a⌋ = ⌊⌊x⌋ / a⌋` is within one of `x / a`. This is the comparison used to
evaluate the sum in Dirichlet's hyperbola method.

## Main results

* `TauCeti.sum_Ioc_natFloor_div_le_mul_harmonic`: `∑_{0 < a ≤ M} ⌊x⌋₊ / a ≤ x * H_M` for `x ≥ 0`.
* `TauCeti.mul_harmonic_sub_le_sum_Ioc_natFloor_div`: `x * H_M - M ≤ ∑_{0 < a ≤ M} ⌊x⌋₊ / a`.
-/

public section

open Finset

namespace TauCeti

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorSemiring K]

/-- For `x ≥ 0`, the floor sum `∑_{0 < a ≤ M} ⌊x⌋₊ / a` (natural division, which equals
`⌊x / a⌋₊`) is at most `x * H_M`, where `H_M` is the `M`-th harmonic number. -/
theorem sum_Ioc_natFloor_div_le_mul_harmonic {x : K} (hx : 0 ≤ x) (M : ℕ) :
    ∑ a ∈ Ioc 0 M, ((⌊x⌋₊ / a : ℕ) : K) ≤ x * harmonic M := by
  rw [cast_harmonic_eq_sum_Ioc, mul_sum]
  refine sum_le_sum fun a _ ↦ Nat.cast_div_le.trans ?_
  rw [← div_eq_mul_inv]
  exact div_le_div_of_nonneg_right (Nat.floor_le hx) (Nat.cast_nonneg a)

/-- The floor sum `∑_{0 < a ≤ M} ⌊x⌋₊ / a` (natural division, which equals `⌊x / a⌋₊`) is at
least `x * H_M - M`, where `H_M` is the `M`-th harmonic number. -/
theorem mul_harmonic_sub_le_sum_Ioc_natFloor_div (x : K) (M : ℕ) :
    x * harmonic M - M ≤ ∑ a ∈ Ioc 0 M, ((⌊x⌋₊ / a : ℕ) : K) := by
  have hcard : (M : K) = ∑ _a ∈ Ioc 0 M, (1 : K) := by simp
  rw [cast_harmonic_eq_sum_Ioc, mul_sum, hcard, ← sum_sub_distrib]
  refine sum_le_sum fun a _ ↦ ?_
  rw [← Nat.floor_div_natCast, ← div_eq_mul_inv]
  linarith [Nat.lt_floor_add_one (x / a)]

end TauCeti
