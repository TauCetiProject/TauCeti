/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.IsPrimePow
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.NumberTheory.Chebyshev
import TauCeti.Algebra.Order.Floor.Semifield
import TauCeti.Analysis.SpecialFunctions.Log.Bounds
import TauCeti.NumberTheory.PrimeCounting

/-!
# Counting prime powers

For `x ≥ 0`, grouping the prime powers `m ≤ x` by their exponent `k` expresses their count as
`∑_{1 ≤ k ≤ log x / log 2} π(x^{1/k})`. Since each term with `k ≥ 2` is at most `√x`, the count
for `x ≥ 2` is at most `π(x) + (log x / log 2 − 1) √x ≤ 6 x / log x`, yielding the asymptotic
bound `O(x / log x)` (and `O(N / log N)` for prime powers strictly below `N : ℕ`).

## Main results

* `TauCeti.card_filter_isPrimePow_eq_sum_primeCounting`: exact decomposition of the prime-power
  count up to `x ≥ 0` into `∑_{1 ≤ k ≤ log x / log 2} π(x^{1/k})`.
* `TauCeti.card_filter_isPrimePow_le`:
  `#{n ∈ Ioc 0 ⌊x⌋₊ | IsPrimePow n} ≤ π(x) + (log x / log 2 - 1) √x` for `x ≥ 2`.
* `TauCeti.card_filter_isPrimePow_le_six_mul_div_log`:
  explicit `6 x / log x` upper bound for `x ≥ 2`.
* `TauCeti.card_filter_range_isPrimePow_le_six_mul_div_log`: explicit `6 N / log N` upper bound
  for prime powers strictly below `N ≥ 2`.
* `TauCeti.isBigO_card_filter_isPrimePow_div_log`,
  `TauCeti.isBigO_card_filter_range_isPrimePow_div_log`: asymptotic `O(x / log x)` and
  `O(N / log N)` prime-power counts.

## References

* The decomposition `TauCeti.card_filter_isPrimePow_eq_sum_primeCounting` adapts Mathlib's
  `Chebyshev.sum_PrimePow_eq_sum_sum`, and `TauCeti.card_filter_isPrimePow_le_six_mul_div_log`
  combines it with Mathlib's `Chebyshev.pi_le_log4_mul_div`.
-/

public section

open Finset Filter Real
open scoped Asymptotics Chebyshev

namespace TauCeti

/-- The prime powers `m ≤ x` number `∑_{1 ≤ k ≤ log x / log 2} π(x^{1/k})`, for `x ≥ 0`. -/
theorem card_filter_isPrimePow_eq_sum_primeCounting {x : ℝ} (hx : 0 ≤ x) :
    #{n ∈ Ioc 0 ⌊x⌋₊ | IsPrimePow n} =
      ∑ k ∈ Icc 1 ⌊log x / log 2⌋₊, Nat.primeCounting ⌊x ^ ((1 : ℝ) / k)⌋₊ := by
  rw [card_eq_sum_ones]
  convert Chebyshev.sum_PrimePow_eq_sum_sum (fun _ ↦ 1) hx using 2 with k
  rw [← card_eq_sum_ones, ← Nat.primesLE_eq_filter_Ioc_zero, Nat.primesLE_card_eq_primeCounting]

/-- For `x ≥ 2`, the prime powers `m ≤ x` number at most `π(x) + (log x / log 2 − 1) √x`: each
`π(x^{1/k})` with `k ≥ 2` is at most `√x`. -/
theorem card_filter_isPrimePow_le {x : ℝ} (hx : 2 ≤ x) :
    (#{n ∈ Ioc 0 ⌊x⌋₊ | IsPrimePow n} : ℝ) ≤
      Nat.primeCounting ⌊x⌋₊ + (log x / log 2 - 1) * √x := by
  have hx0 : 0 ≤ x := by linarith
  have hL : 1 ≤ log x / log 2 := by
    rw [le_div_iff₀ (log_pos one_lt_two), one_mul]
    exact log_le_log two_pos hx
  have hK : 1 ≤ ⌊log x / log 2⌋₊ := Nat.le_floor (by exact_mod_cast hL)
  have hsplit : Icc 1 ⌊log x / log 2⌋₊ = insert 1 (Icc 2 ⌊log x / log 2⌋₊) := by
    ext k
    simp only [mem_Icc, mem_insert]
    omega
  rw [card_filter_isPrimePow_eq_sum_primeCounting hx0, hsplit, sum_insert (by simp),
    Nat.cast_add, Nat.cast_sum]
  simp only [Nat.cast_one, div_one, rpow_one]
  gcongr
  refine (TauCeti.sum_Icc_floor_le_max_mul (by linarith) (sqrt_nonneg x) 2
    fun k hk ↦ ?_).trans_eq ?_
  · have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast (mem_Icc.mp hk).1
    calc (Nat.primeCounting ⌊x ^ ((1 : ℝ) / k)⌋₊ : ℝ)
        ≤ ⌊x ^ ((1 : ℝ) / k)⌋₊ := by exact_mod_cast Nat.primeCounting_le_self _
      _ ≤ x ^ ((1 : ℝ) / k) := Nat.floor_le (rpow_nonneg hx0 _)
      _ ≤ x ^ ((1 : ℝ) / 2) := rpow_le_rpow_of_exponent_le (by linarith) (by gcongr)
      _ = √x := (sqrt_eq_rpow x).symm
  · rw [max_eq_left (by push_cast; linarith)]
    push_cast
    ring

/-- For `x ≥ 2`, the prime powers `m ≤ x` number at most `6 x / log x`. -/
theorem card_filter_isPrimePow_le_six_mul_div_log {x : ℝ} (hx : 2 ≤ x) :
    (#{n ∈ Ioc 0 ⌊x⌋₊ | IsPrimePow n} : ℝ) ≤ 6 * x / log x := by
  have hx0 : 0 < x := by linarith
  have hL : 0 < log x := log_pos (by linarith)
  have hl2 := log_two_gt_d9
  have hl2' := log_two_lt_d9
  have he := exp_one_gt_d9
  have hsx : √x * √x = x := mul_self_sqrt hx0.le
  have hπ := Chebyshev.pi_le_log4_mul_div (by linarith : 1 < x)
  rw [log_sqrt hx0.le, show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow] at hπ
  have hkey := sq_log_mul_exp_one_le_sixteen_mul_sqrt (by linarith : (1 : ℝ) ≤ x)
  have hcount := card_filter_isPrimePow_le hx
  rw [le_div_iff₀ hL]
  -- `π(x) ≤ 4 log 2 · x / log x + √x`, and `(log x)² √x ≤ 16 x / e²`.
  have hπ' : (Nat.primeCounting ⌊x⌋₊ : ℝ) * log x ≤ 4 * log 2 * x + √x * log x := by
    have e : ((2 : ℕ) : ℝ) * log 2 * x / (log x / 2) * log x = 4 * log 2 * x := by
      field_simp
      norm_num
    have := mul_le_mul_of_nonneg_right hπ hL.le
    rw [add_mul, e] at this
    exact this
  have hsq : log x ^ 2 * √x * exp 1 ^ 2 ≤ 16 * x := by
    nlinarith [sqrt_nonneg x]
  have hpos : 0 < log 2 := by linarith
  calc (#{n ∈ Ioc 0 ⌊x⌋₊ | IsPrimePow n} : ℝ) * log x
      ≤ (Nat.primeCounting ⌊x⌋₊ + (log x / log 2 - 1) * √x) * log x :=
        mul_le_mul_of_nonneg_right hcount hL.le
    _ ≤ 4 * log 2 * x + log x ^ 2 * √x / log 2 := by
        have : (log x / log 2 - 1) * √x * log x = log x ^ 2 * √x / log 2 - √x * log x := by
          field_simp
        nlinarith
    _ ≤ 6 * x := by
        -- numerically, `4 log 2 + 16 / (e² log 2) < 5.9`
        have he2 : 7.38 < exp 1 ^ 2 := by nlinarith
        have hl : 2.23 < (6 - 4 * log 2) * log 2 := by nlinarith
        have h16 : (16 : ℝ) ≤ (6 - 4 * log 2) * log 2 * exp 1 ^ 2 := by nlinarith
        have : log x ^ 2 * √x / log 2 ≤ (6 - 4 * log 2) * x := by
          rw [div_le_iff₀ hpos]
          refine le_of_mul_le_mul_right ?_ (by positivity : 0 < exp 1 ^ 2)
          nlinarith
        linarith

/-- For every integer `N ≥ 2`, the prime powers below `N` number at most `6 N / log N`. -/
theorem card_filter_range_isPrimePow_le_six_mul_div_log {N : ℕ} (hN : 2 ≤ N) :
    (#{m ∈ range N | IsPrimePow m} : ℝ) ≤ 6 * N / log N := by
  refine le_trans ?_ (card_filter_isPrimePow_le_six_mul_div_log (by exact_mod_cast hN))
  rw [Nat.floor_natCast]
  exact_mod_cast card_le_card fun m hm ↦ by
    simp only [mem_filter, mem_range, mem_Ioc] at hm ⊢
    exact ⟨⟨hm.2.pos, hm.1.le⟩, hm.2⟩

/-- Asymptotic bound for the prime-power count on `ℝ`:
`#{n ∈ Ioc 0 ⌊x⌋₊ | IsPrimePow n} = O(x / log x)` as `x → ∞`. -/
theorem isBigO_card_filter_isPrimePow_div_log :
    (fun x : ℝ ↦ (#{n ∈ Ioc 0 ⌊x⌋₊ | IsPrimePow n} : ℝ)) =O[atTop]
      (fun x : ℝ ↦ x / log x) := by
  refine Asymptotics.IsBigO.of_bound 6 ?_
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
  have hlog : 0 < log x := log_pos (by linarith)
  rw [norm_of_nonneg (Nat.cast_nonneg _), norm_of_nonneg (by positivity)]
  simpa only [mul_div_assoc] using card_filter_isPrimePow_le_six_mul_div_log hx

/-- Asymptotic bound for the prime-power count below `N : ℕ`:
`#{n ∈ range N | IsPrimePow n} = O(N / log N)` as `N → ∞`. -/
theorem isBigO_card_filter_range_isPrimePow_div_log :
    (fun N : ℕ ↦ (#{n ∈ range N | IsPrimePow n} : ℝ)) =O[atTop]
      (fun N : ℕ ↦ (N : ℝ) / log N) := by
  refine Asymptotics.IsBigO.of_bound 6 ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hlog : 0 < log N := log_pos (by exact_mod_cast (by omega : 1 < N))
  rw [norm_of_nonneg (Nat.cast_nonneg _), norm_of_nonneg (by positivity)]
  simpa only [mul_div_assoc] using card_filter_range_isPrimePow_le_six_mul_div_log hN

end TauCeti
