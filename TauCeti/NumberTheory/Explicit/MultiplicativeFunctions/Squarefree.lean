/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import TauCeti.NumberTheory.Explicit.MultiplicativeFunctions.Moebius.Basic
import Mathlib.Algebra.Order.Floor.Semifield
import TauCeti.NumberTheory.AbelSummation
import TauCeti.NumberTheory.ArithmeticFunction.DilateSq
import TauCeti.NumberTheory.ArithmeticFunction.Moebius
import TauCeti.NumberTheory.Explicit.MultiplicativeFunctions.Liouville

/-!
# The squarefree count through the Mertens function

The squarefree count `Q(x) = ∑_{n ≤ x} μ(n)²` (`TauCeti.squarefreeCount`) is the sum of the
square of the Möbius function over `Finset.Icc 1 ⌊x⌋₊`, so it vanishes for `x < 1`, like the
Mertens function `M(x) = TauCeti.moebiusSum x`.

Both identities below come from `μ² = ζ * μ_□`, that is `μ(n)² = ∑_{d² ∣ n} μ(d)`
(`ArithmeticFunction.coe_zeta_mul_dilateSq_moebius_apply`). Summed over `n ≤ x`, this is a sum
over the pairs `(k, d)` with `k d² ≤ x`. Grouping the pairs by `d` gives
`Q(x) = ∑_{d ≤ √x} μ(d) ⌊x / d²⌋`; grouping them by `k` gives `Q(x) = ∑_{k ≤ x} M(√(x / k))`,
since the `d` paired with a given `k` are those with `d ≤ √(x / k)`.

The squarefree count and its expression through `M` are adapted from `Q-def` and
`mobius-lemma-1-sub` (`MobiusLemma.Q`, `MobiusLemma.mobius_lemma_1_sub`) in
[Alex Kontorovich, Terence Tao and contributors, *Prime Number Theorem and More*][PNT-mobius-lemma].

## Main declarations

* `TauCeti.squarefreeCount`: the squarefree count `Q`.
* `TauCeti.squarefreeCount_natCast`, `TauCeti.squarefreeCount_natFloor`: agreement with the sum
  over `Finset.Icc 1 N` and constancy on `[N, N + 1)`.
* `TauCeti.squarefreeCount_eq_sum_moebius_mul_natFloor`: `Q(x) = ∑_{d ≤ √x} μ(d) ⌊x / d²⌋`.
* `TauCeti.squarefreeCount_eq_sum_moebiusSum`: `Q(x) = ∑_{k ≤ x} M(√(x / k))`.

[PNT-mobius-lemma]: https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/471f10c8164d59ed782680c5cd5d884e632e43c9/PrimeNumberTheoremAnd/IEANTN/MobiusLemma.lean#L30-L243
-/

public section

open Finset
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace TauCeti

variable {x : ℝ}

/-! ### The squarefree count -/

/-- The squarefree count `Q(x) = ∑_{n ≤ x} μ(n)²` at a real argument; the sum runs over
`Finset.Icc 1 ⌊x⌋₊`, so `Q(x) = 0` for `x < 1`. -/
noncomputable def squarefreeCount (x : ℝ) : ℝ :=
  ∑ n ∈ Icc 1 ⌊x⌋₊, (μ n : ℝ) ^ 2

/-- The defining sum of `Q(x)`. -/
theorem squarefreeCount_def (x : ℝ) :
    squarefreeCount x = ∑ n ∈ Icc 1 ⌊x⌋₊, (μ n : ℝ) ^ 2 := (rfl)

/-- `Q(x) = 0` for `x < 1`: the sum is empty. -/
theorem squarefreeCount_of_lt_one (hx : x < 1) : squarefreeCount x = 0 :=
  sum_Icc_one_natFloor_eq_zero _ hx

/-- At a natural number `N`, `Q(N)` is the sum of `μ²` over `Finset.Icc 1 N`. -/
@[simp]
theorem squarefreeCount_natCast (N : ℕ) :
    squarefreeCount N = ∑ n ∈ Icc 1 N, (μ n : ℝ) ^ 2 := by
  simp [squarefreeCount]

/-- `Q` is constant on each interval `[N, N + 1)`: `Q(x) = Q(⌊x⌋₊)`. -/
@[simp high]
theorem squarefreeCount_natFloor (x : ℝ) : squarefreeCount ⌊x⌋₊ = squarefreeCount x := by
  simp [squarefreeCount]

/-! ### The squarefree count through the Möbius function -/

/-- `Q(x) = ∑_{d ≤ √x} μ(d) ⌊x / d²⌋`, the sum running over the naturals `1 ≤ d ≤ √x`: the pairs
`(k, d)` with `k d² ≤ x` grouped by `d`. -/
theorem squarefreeCount_eq_sum_moebius_mul_natFloor (x : ℝ) :
    squarefreeCount x = ∑ d ∈ Icc 1 (Nat.sqrt ⌊x⌋₊), (μ d : ℝ) * ⌊x / d ^ 2⌋₊ := by
  have h := sum_Icc_natFloor_mul_dilateSq (ζ : ArithmeticFunction ℤ) μ x
  simp only [ArithmeticFunction.coe_zeta_mul_dilateSq_moebius_apply] at h
  push_cast at h
  rw [squarefreeCount_def, h]
  refine sum_congr rfl fun d _ ↦ congrArg _ ?_
  have hζ : ∀ k ∈ Icc 1 ⌊x / d ^ 2⌋₊, (((ζ : ArithmeticFunction ℤ) k : ℤ) : ℝ) = 1 :=
    fun k hk ↦ by
      rw [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply_ne
        (Nat.one_le_iff_ne_zero.1 (mem_Icc.1 hk).1), Nat.cast_one, Int.cast_one]
  rw [sum_congr rfl hζ, sum_const, Nat.card_Icc, add_tsub_cancel_right, nsmul_one]

/-- For a natural `k`, `⌊√(x / k)⌋₊ = Nat.sqrt (⌊x⌋₊ / k)`. -/
private theorem natFloor_sqrt_div_natCast (x : ℝ) (k : ℕ) :
    ⌊√(x / k)⌋₊ = Nat.sqrt (⌊x⌋₊ / k) := by
  rw [← Nat.floor_div_natCast]
  rcases lt_or_ge (x / k) 0 with hy | hy
  · rw [Real.sqrt_eq_zero'.2 hy.le, Nat.floor_zero, Nat.floor_eq_zero.2 (hy.trans one_pos),
      Nat.sqrt_zero]
  refine eq_of_forall_le_iff fun d ↦ ?_
  rw [Nat.le_floor_iff (Real.sqrt_nonneg _), Real.le_sqrt (Nat.cast_nonneg _) hy, Nat.le_sqrt',
    Nat.le_floor_iff hy, Nat.cast_pow]

/-- `Q(x) = ∑_{k ≤ x} M(√(x / k))`, the sum running over the naturals `1 ≤ k ≤ x`: the pairs
`(k, d)` with `k d² ≤ x` grouped by `k`. -/
theorem squarefreeCount_eq_sum_moebiusSum (x : ℝ) :
    squarefreeCount x = ∑ k ∈ Icc 1 ⌊x⌋₊, moebiusSum √(x / k) := by
  have h := congrArg (Int.cast : ℤ → ℝ) (ArithmeticFunction.sum_Ioc_mul_eq_sum_sum
    (ζ : ArithmeticFunction ℤ) (μ : ArithmeticFunction ℤ).dilateSq ⌊x⌋₊)
  simp only [ArithmeticFunction.coe_zeta_mul_dilateSq_moebius_apply,
    ArithmeticFunction.sum_Ioc_dilateSq] at h
  push_cast at h
  simp only [← Icc_add_one_left_eq_Ioc, zero_add] at h
  rw [squarefreeCount_def, h]
  refine sum_congr rfl fun k hk ↦ ?_
  rw [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply_ne
    (Nat.one_le_iff_ne_zero.1 (mem_Icc.1 hk).1), Nat.cast_one, Int.cast_one, one_mul,
    moebiusSum_def, natFloor_sqrt_div_natCast]

end TauCeti
