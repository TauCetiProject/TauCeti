/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Chebyshev
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.Complex.ExponentialBounds
import TauCeti.Analysis.SpecialFunctions.Log.Factorial
import TauCeti.NumberTheory.Chebyshev.LogFactorial

/-!
# Chebyshev's weight method

Chebyshev's elementary bounds for `ψ(x) = ∑_{n ≤ x} Λ(n)` with explicit constants. Let
`ν = e₁ − e₂ − e₃ − e₅ + e₃₀` and
`E(y) = ∑_m ν(m) ⌊y / m⌋ = ⌊y⌋ − ⌊y / 2⌋ − ⌊y / 3⌋ − ⌊y / 5⌋ + ⌊y / 30⌋`
(`Chebyshev.floorWeight`). Then `E` takes only the values `0` and `1`, is periodic of period `30`
on `y ≥ 0` and equals `1` on `[1, 6)`. Chebyshev's identity
`log ⌊x⌋₊! = ∑_{n ≤ x} Λ(n) ⌊x / n⌋` (`Chebyshev.log_floor_factorial_eq_sum_vonMangoldt`) applied
to each `x / m` (`Chebyshev.log_floor_div_factorial_eq_sum_vonMangoldt`) gives

`U(x) = ∑_m ν(m) log ⌊x / m⌋₊! = ∑_{n ≤ x} Λ(n) E(x / n)`

(`Chebyshev.weightedLogFactorial`), so that `ψ(x) − ψ(x / 6) ≤ U(x) ≤ ψ(x)`. On the other hand
`∑_m ν(m) / m = 0`, so the Stirling estimates for `log ⌊y⌋₊!` make the main terms of `U(x)` collapse
to `a x` with `a = −∑_m ν(m) log m / m = 0.92129…` (`Chebyshev.weightConstant`), and
`|U(x) − a x| ≤ 5 log x − 5` for `x ≥ 30`. This gives the lower bound
`ψ(x) ≥ a x − 5 log x + 5` for `x ≥ 30`, and iterating `ψ(x) − ψ(x / 6) ≤ a x + 5 log x − 5` along
`x, x / 6, x / 6², …` gives upper bounds for `ψ` once the values of `ψ` on a bounded range are
known.

## Main results

* `Chebyshev.floorWeight_eq_zero_or_eq_one`, `Chebyshev.floorWeight_eq_one`,
  `Chebyshev.floorWeight_add_thirty`: `E` takes the values `0` and `1`, equals `1` on `[1, 6)` and
  has period `30` on `y ≥ 0`.
* `Chebyshev.weightConstant_gt_d5`, `Chebyshev.weightConstant_lt_d4`: `0.92129 < a < 0.9213`.
* `Chebyshev.weightedLogFactorial_eq_sum_vonMangoldt`: `U(x) = ∑_{n ≤ x} Λ(n) E(x / n)`.
* `Chebyshev.psi_sub_psi_div_six_le_weightedLogFactorial`, `Chebyshev.weightedLogFactorial_le_psi`:
  `ψ(x) − ψ(x / 6) ≤ U(x) ≤ ψ(x)`.
* `Chebyshev.abs_weightedLogFactorial_sub_le`: `|U(x) − a x| ≤ 5 log x − 5` for `x ≥ 30`.
* `Chebyshev.weightConstant_mul_sub_le_psi`, `Chebyshev.psi_sub_psi_div_six_le`: the lower bound
  `a x − 5 log x + 5 ≤ ψ(x)` and the upper bound `ψ(x) − ψ(x / 6) ≤ a x + 5 log x − 5`, for
  `x ≥ 30`; `Chebyshev.mul_sub_le_psi` is the lower bound with `a` replaced by `0.92129`.
* `Chebyshev.psi_le_three_mul_self`: the unconditional bound `ψ(x) ≤ 3 x` for `x ≥ 0`, from
  Mathlib's `Chebyshev.psi_le`.
* `Chebyshev.psi_le_of_forall_psi_le_mul`: if `ψ(y) ≤ 1.015 y` for `0 < y ≤ 30`, then
  `ψ(x) ≤ (6a / 5) x + (log (x / 5) / log 6) (5 log x − 5)` for `x ≥ 30`.
* `Chebyshev.psi_le_mul_of_forall_psi_le_mul`: if `ψ(y) ≤ 1.11 y` for `0 < y ≤ 11723`, then
  `ψ(x) ≤ 1.11 x` for every `x > 0`.
* `Chebyshev.WeightRange`: the finite-range hypothesis, the conjunction of the two hypotheses
  above, with the two upper bounds `Chebyshev.WeightRange.psi_le` and
  `Chebyshev.WeightRange.psi_le_mul` under it.

The two finite ranges are computations on the values of `ψ` (the largest value of `ψ(y) / y` is
`ψ(19) / 19 = 1.0139…` on `(0, 30]` and `ψ(113) / 113 = 1.0388…` on `(0, 11723]`); they are
hypotheses here, and no computation is performed.

## References

* P. L. Chebyshev, *Mémoire sur les nombres premiers*, J. Math. Pures Appl. 17 (1852), 366–390,
  §§IV–V.
* J. B. Rosser, L. Schoenfeld, *Approximate formulas for some functions of prime numbers*,
  Illinois J. Math. 6 (1962), 64–94, for the values of `ψ(y) / y` on the bounded ranges.
-/

public section

open Finset Real
open ArithmeticFunction hiding log
open scoped Chebyshev Nat

namespace Chebyshev

/-! ### The weight `E` -/

/-- Chebyshev's weight `E(y) = ⌊y⌋ − ⌊y / 2⌋ − ⌊y / 3⌋ − ⌊y / 5⌋ + ⌊y / 30⌋`, the combination of
floors attached to `ν = e₁ − e₂ − e₃ − e₅ + e₃₀`. It takes only the values `0` and `1`
(`Chebyshev.floorWeight_eq_zero_or_eq_one`). -/
noncomputable def floorWeight (y : ℝ) : ℝ :=
  ⌊y⌋₊ - ⌊y / 2⌋₊ - ⌊y / 3⌋₊ - ⌊y / 5⌋₊ + ⌊y / 30⌋₊

theorem floorWeight_def (y : ℝ) :
    floorWeight y = ⌊y⌋₊ - ⌊y / 2⌋₊ - ⌊y / 3⌋₊ - ⌊y / 5⌋₊ + ⌊y / 30⌋₊ := (rfl)

/-- `E(y)` depends only on `k = ⌊y⌋₊`: it is `(k + ⌊k/30⌋) − (⌊k/2⌋ + ⌊k/3⌋ + ⌊k/5⌋)`. -/
private theorem floorWeight_eq_natCast_sub_natCast (y : ℝ) :
    floorWeight y = ((⌊y⌋₊ + ⌊y⌋₊ / 30 : ℕ) : ℝ) - ((⌊y⌋₊ / 2 + ⌊y⌋₊ / 3 + ⌊y⌋₊ / 5 : ℕ) : ℝ) := by
  rw [floorWeight_def, Nat.floor_div_ofNat, Nat.floor_div_ofNat, Nat.floor_div_ofNat,
    Nat.floor_div_ofNat]
  push_cast
  ring

/-- Shifting `k` by `30` shifts `k / 2`, `k / 3`, `k / 5` and `k / 30` by `15`, `10`, `6`
and `1`. -/
private theorem add_thirty_div (k : ℕ) :
    (k + 30) / 2 = k / 2 + 15 ∧ (k + 30) / 3 = k / 3 + 10 ∧ (k + 30) / 5 = k / 5 + 6 ∧
      (k + 30) / 30 = k / 30 + 1 := by
  omega

/-- The integer form of `E ∈ {0, 1}`, proved on `[0, 30)` by cases and extended by periodicity. -/
private theorem add_div_thirty_eq_or (k : ℕ) :
    k + k / 30 = k / 2 + k / 3 + k / 5 ∨ k + k / 30 = k / 2 + k / 3 + k / 5 + 1 := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases lt_or_ge k 30 with hk | hk
    · interval_cases k <;> omega
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 30 := ⟨k - 30, by omega⟩
      have := ih j (by omega)
      obtain ⟨h₂, h₃, h₅, h₃₀⟩ := add_thirty_div j
      omega

/-- Chebyshev's weight takes only the values `0` and `1`. -/
theorem floorWeight_eq_zero_or_eq_one (y : ℝ) : floorWeight y = 0 ∨ floorWeight y = 1 := by
  rw [floorWeight_eq_natCast_sub_natCast]
  rcases add_div_thirty_eq_or ⌊y⌋₊ with h | h <;> rw [h] <;> push_cast <;> simp

theorem floorWeight_nonneg (y : ℝ) : 0 ≤ floorWeight y := by
  rcases floorWeight_eq_zero_or_eq_one y with h | h <;> simp [h]

theorem floorWeight_le_one (y : ℝ) : floorWeight y ≤ 1 := by
  rcases floorWeight_eq_zero_or_eq_one y with h | h <;> simp [h]

/-- Chebyshev's weight equals `1` on `[1, 6)`. -/
theorem floorWeight_eq_one {y : ℝ} (h₁ : 1 ≤ y) (h₆ : y < 6) : floorWeight y = 1 := by
  have h₁' : 1 ≤ ⌊y⌋₊ := Nat.one_le_floor_iff y |>.mpr h₁
  have h₆' : ⌊y⌋₊ < 6 := (Nat.floor_lt (by linarith)).mpr (by exact_mod_cast h₆)
  have h : ⌊y⌋₊ + ⌊y⌋₊ / 30 = ⌊y⌋₊ / 2 + ⌊y⌋₊ / 3 + ⌊y⌋₊ / 5 + 1 := by
    interval_cases ⌊y⌋₊ <;> rfl
  rw [floorWeight_eq_natCast_sub_natCast, h]
  push_cast
  ring

/-- Chebyshev's weight is periodic of period `30` on `y ≥ 0`. -/
theorem floorWeight_add_thirty {y : ℝ} (hy : 0 ≤ y) : floorWeight (y + 30) = floorWeight y := by
  rw [floorWeight_eq_natCast_sub_natCast, floorWeight_eq_natCast_sub_natCast,
    Nat.floor_add_ofNat hy]
  obtain ⟨h₂, h₃, h₅, h₃₀⟩ := add_thirty_div ⌊y⌋₊
  rw [h₂, h₃, h₅, h₃₀]
  push_cast
  ring

/-! ### The weighted sum of logarithms of factorials -/

/-- Chebyshev's weighted sum
`U(x) = log ⌊x⌋₊! − log ⌊x / 2⌋₊! − log ⌊x / 3⌋₊! − log ⌊x / 5⌋₊! + log ⌊x / 30⌋₊!`. It equals
`∑_{n ≤ x} Λ(n) E(x / n)` (`Chebyshev.weightedLogFactorial_eq_sum_vonMangoldt`). -/
noncomputable def weightedLogFactorial (x : ℝ) : ℝ :=
  log ⌊x⌋₊ ! - log ⌊x / 2⌋₊ ! - log ⌊x / 3⌋₊ ! - log ⌊x / 5⌋₊ ! + log ⌊x / 30⌋₊ !

theorem weightedLogFactorial_def (x : ℝ) :
    weightedLogFactorial x =
      log ⌊x⌋₊ ! - log ⌊x / 2⌋₊ ! - log ⌊x / 3⌋₊ ! - log ⌊x / 5⌋₊ ! + log ⌊x / 30⌋₊ ! := (rfl)

/-- **Chebyshev's identity** for the weighted sum: `U(x) = ∑_{n ≤ x} Λ(n) E(x / n)`. -/
theorem weightedLogFactorial_eq_sum_vonMangoldt (x : ℝ) :
    weightedLogFactorial x = ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n * floorWeight (x / n) := by
  have h := log_floor_div_factorial_eq_sum_vonMangoldt x
  have h₁ := h 1
  have h₂ := h 2
  have h₃ := h 3
  have h₅ := h 5
  have h₃₀ := h 30
  simp only [Nat.cast_one, div_one, Nat.cast_ofNat] at h₁ h₂ h₃ h₅ h₃₀
  simp only [weightedLogFactorial_def, floorWeight_def, mul_add, mul_sub, sum_add_distrib,
    sum_sub_distrib, h₁, h₂, h₃, h₅, h₃₀]

/-- `U(x) ≤ ψ(x)`, since `E ≤ 1`. -/
theorem weightedLogFactorial_le_psi (x : ℝ) : weightedLogFactorial x ≤ ψ x := by
  rw [weightedLogFactorial_eq_sum_vonMangoldt, psi]
  exact sum_le_sum fun n _ ↦
    mul_le_of_le_one_right vonMangoldt_nonneg (floorWeight_le_one _)

/-- `ψ(x) − ψ(x / 6) ≤ U(x)`, since `E(x / n) = 1` for `x / 6 < n ≤ x` and `E ≥ 0`. -/
theorem psi_sub_psi_div_six_le_weightedLogFactorial (x : ℝ) :
    ψ x - ψ (x / 6) ≤ weightedLogFactorial x := by
  have h6' : ⌊x / 6⌋₊ = ⌊x⌋₊ / 6 := Nat.floor_div_natCast x 6
  have h6 : ⌊x / 6⌋₊ ≤ ⌊x⌋₊ := h6' ▸ Nat.div_le_self _ _
  rw [weightedLogFactorial_eq_sum_vonMangoldt, psi, psi,
    ← sum_Ioc_consecutive _ (Nat.zero_le _) h6, add_sub_cancel_left]
  calc ∑ n ∈ Ioc ⌊x / 6⌋₊ ⌊x⌋₊, Λ n
      = ∑ n ∈ Ioc ⌊x / 6⌋₊ ⌊x⌋₊, Λ n * floorWeight (x / n) := by
        refine sum_congr rfl fun n hn ↦ ?_
        obtain ⟨hn₆, hnx⟩ := mem_Ioc.mp hn
        have hn₀ : n ≠ 0 := by omega
        have hn₀' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn₀
        rw [floorWeight_eq_one ((one_le_div hn₀').mpr <| (Nat.le_floor_iff' hn₀).mp hnx)
          ((div_lt_iff₀ hn₀').mpr <| by linarith [(Nat.floor_lt' hn₀).mp hn₆]), mul_one]
    _ ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n * floorWeight (x / n) :=
        sum_le_sum_of_subset_of_nonneg (Ioc_subset_Ioc_left (Nat.zero_le _))
          fun _ _ _ ↦ mul_nonneg vonMangoldt_nonneg (floorWeight_nonneg _)

/-! ### The main term of the weighted sum -/

/-- Chebyshev's constant `a = log 2 / 2 + log 3 / 3 + log 5 / 5 − log 30 / 30 = 0.92129…`, the
coefficient of the main term `a x` of `U(x)`. -/
noncomputable def weightConstant : ℝ :=
  log 2 / 2 + log 3 / 3 + log 5 / 5 - log 30 / 30

theorem weightConstant_def :
    weightConstant = log 2 / 2 + log 3 / 3 + log 5 / 5 - log 30 / 30 := (rfl)

private theorem log_thirty : log 30 = log 2 + log 3 + log 5 := by
  rw [← log_mul two_ne_zero three_ne_zero, ← log_mul (by norm_num) (by norm_num)]
  norm_num

/-- Chebyshev's constant as `a = (7 / 15) log 2 + (3 / 10) log 3 + (1 / 6) log 5`. -/
theorem weightConstant_eq :
    weightConstant = 7 / 15 * log 2 + 3 / 10 * log 3 + 1 / 6 * log 5 := by
  rw [weightConstant_def, log_thirty]
  ring

/-- The lower decimal bound `0.92129 < a`. -/
theorem weightConstant_gt_d5 : 0.92129 < weightConstant := by
  rw [weightConstant_eq]
  linarith [log_two_gt_d9, log_three_gt_d9, log_five_gt_d9]

/-- The upper decimal bound `a < 0.9213`. -/
theorem weightConstant_lt_d4 : weightConstant < 0.9213 := by
  rw [weightConstant_eq]
  linarith [log_two_lt_d9, log_three_lt_d9, log_five_lt_d9]

/-- The Stirling estimate for `log ⌊x / m⌋₊!`, with `log (x / m)` expanded. -/
private theorem abs_log_floor_div_factorial_sub_le {x m : ℝ} (hm : 0 < m) (hmx : m ≤ x) :
    |log ⌊x / m⌋₊ ! - (x / m * log x - x / m * log m - x / m)| ≤ (log x - log m) / 2 + 1 := by
  have h := abs_log_floor_factorial_sub_le ((one_le_div hm).mpr hmx)
  rwa [log_div (by linarith : (0 : ℝ) < x).ne' hm.ne', mul_sub] at h

/-- `|U(x) − a x| ≤ 5 log x − 5` for `x ≥ 30`. -/
theorem abs_weightedLogFactorial_sub_le {x : ℝ} (hx : 30 ≤ x) :
    |weightedLogFactorial x - weightConstant * x| ≤ 5 * log x - 5 := by
  have h₁ := abs_log_floor_div_factorial_sub_le one_pos (by linarith : (1 : ℝ) ≤ x)
  have h₂ := abs_log_floor_div_factorial_sub_le two_pos (by linarith : (2 : ℝ) ≤ x)
  have h₃ := abs_log_floor_div_factorial_sub_le three_pos (by linarith : (3 : ℝ) ≤ x)
  have h₅ := abs_log_floor_div_factorial_sub_le (by norm_num) (by linarith : (5 : ℝ) ≤ x)
  have h₃₀ := abs_log_floor_div_factorial_sub_le (by norm_num) hx
  rw [div_one, log_one] at h₁
  rw [abs_le] at h₁ h₂ h₃ h₅ h₃₀ ⊢
  have hlog : log 30 ≤ log x := log_le_log (by norm_num) hx
  have h30 := log_thirty
  have := log_two_gt_d9
  have := log_three_gt_d9
  have := log_five_gt_d9
  rw [weightedLogFactorial_def, weightConstant_def]
  constructor <;> linarith

/-- **Chebyshev's lower bound**: `a x − 5 log x + 5 ≤ ψ(x)` for `x ≥ 30`. -/
theorem weightConstant_mul_sub_le_psi {x : ℝ} (hx : 30 ≤ x) :
    weightConstant * x - 5 * log x + 5 ≤ ψ x := by
  have := (abs_le.mp (abs_weightedLogFactorial_sub_le hx)).1
  linarith [weightedLogFactorial_le_psi x]

/-- **Chebyshev's lower bound** with a decimal constant: `0.92129 x − 5 log x + 5 ≤ ψ(x)` for
`x ≥ 30`. -/
theorem mul_sub_le_psi {x : ℝ} (hx : 30 ≤ x) : 0.92129 * x - 5 * log x + 5 ≤ ψ x := by
  have := mul_le_mul_of_nonneg_right weightConstant_gt_d5.le (by linarith : (0 : ℝ) ≤ x)
  linarith [weightConstant_mul_sub_le_psi hx]

/-- The upper bound for one step of Chebyshev's iteration:
`ψ(x) − ψ(x / 6) ≤ a x + 5 log x − 5` for `x ≥ 30`. -/
theorem psi_sub_psi_div_six_le {x : ℝ} (hx : 30 ≤ x) :
    ψ x - ψ (x / 6) ≤ weightConstant * x + 5 * log x - 5 := by
  have := (abs_le.mp (abs_weightedLogFactorial_sub_le hx)).2
  linarith [psi_sub_psi_div_six_le_weightedLogFactorial x]

/-! ### An unconditional linear upper bound -/

/-- Chebyshev's bound `ψ x ≤ 3 x` for `x ≥ 0`. It follows from `Chebyshev.psi_le` and
`log x ≤ (2 / e) √x`, as `log 4 + 4 / e < 3`; compare `Chebyshev.psi_le_const_mul_self`, whose
constant is `log 4 + 4`. -/
theorem psi_le_three_mul_self {x : ℝ} (hx : 0 ≤ x) : ψ x ≤ 3 * x := by
  rcases lt_or_ge x 1 with hx1 | hx1
  · rw [psi_eq_zero_of_lt_two (by linarith)]
    positivity
  have hs : 0 < √x := Real.sqrt_pos.2 (by linarith)
  have hlog : Real.log x ≤ 2 * √x / Real.exp 1 := by
    have h := Real.log_le_sub_one_of_pos (div_pos hs (Real.exp_pos 1))
    rw [Real.log_div hs.ne' (Real.exp_pos 1).ne', Real.log_exp, Real.log_sqrt hx] at h
    have h' : 2 * √x / Real.exp 1 = 2 * (√x / Real.exp 1) := by ring
    linarith
  have h4 : Real.log 4 < 1.39 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul two_ne_zero two_ne_zero]
    linarith [Real.log_two_lt_d9]
  have he : 4 / Real.exp 1 < 1.5 := by
    rw [div_lt_iff₀ (Real.exp_pos 1)]
    linarith [Real.exp_one_gt_d9]
  calc ψ x ≤ Real.log 4 * x + 2 * √x * Real.log x := psi_le hx1
    _ ≤ Real.log 4 * x + 2 * √x * (2 * √x / Real.exp 1) := by gcongr
    _ = (Real.log 4 + 4 / Real.exp 1) * x := by
      rw [show 2 * √x * (2 * √x / Real.exp 1) = 4 / Real.exp 1 * (√x * √x) by ring,
        Real.mul_self_sqrt hx]
      ring
    _ ≤ 3 * x := by gcongr; linarith

/-! ### Upper bounds by iteration -/

/-- `5 log x − 5 ≥ 0` for `x ≥ 30`. -/
private theorem five_mul_log_sub_five_nonneg {x : ℝ} (hx : 30 ≤ x) : 0 ≤ 5 * log x - 5 := by
  have : 1 ≤ log x := by
    rw [le_log_iff_exp_le (by linarith : (0 : ℝ) < x)]
    linarith [exp_one_lt_d9]
  linarith

/-- **Chebyshev's upper bound** from a bounded range: if `ψ(y) ≤ 1.015 y` for `0 < y ≤ 30`, then
`ψ(x) ≤ (6a / 5) x + (log (x / 5) / log 6) (5 log x − 5)` for every `x ≥ 30`. The coefficient
`log (x / 5) / log 6` bounds the number of steps `x ↦ x / 6` that stay above `30`. -/
theorem psi_le_of_forall_psi_le_mul (h : ∀ y, 0 < y → y ≤ 30 → ψ y ≤ 1.015 * y) {x : ℝ}
    (hx : 30 ≤ x) :
    ψ x ≤ 6 * weightConstant / 5 * x + log (x / 5) / log 6 * (5 * log x - 5) := by
  have hlog6 : 0 < log 6 := log_pos (by norm_num)
  have ha := weightConstant_gt_d5
  -- Induction on `n` with `x < 30 · 6ⁿ`; the case `x < 180` is the last step.
  suffices H : ∀ n : ℕ, ∀ x : ℝ, 30 ≤ x → x < 30 * 6 ^ n →
      ψ x ≤ 6 * weightConstant / 5 * x + log (x / 5) / log 6 * (5 * log x - 5) by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (x / 30) (by norm_num : (1 : ℝ) < 6)
    exact H n x hx (by linarith)
  intro n
  induction n with
  | zero => intro x hx hx'; norm_num at hx'; linarith
  | succ n ih =>
    intro x hx hx'
    have hstep := psi_sub_psi_div_six_le hx
    have hL := five_mul_log_sub_five_nonneg hx
    rcases lt_or_ge x 180 with h180 | h180
    · -- One step lands in `[5, 30)`, where the hypothesis applies.
      have hy := h (x / 6) (by positivity) (by linarith)
      have hq : 1 ≤ log (x / 5) / log 6 := by
        rw [le_div_iff₀ hlog6, one_mul]
        exact log_le_log (by norm_num) (by linarith)
      -- `ψ(x / 6) ≤ 1.015 x / 6 ≤ a x / 5`, and
      -- `5 log x − 5 ≤ (log (x / 5) / log 6) (5 log x − 5)`.
      have := mul_le_mul_of_nonneg_right ha.le (by linarith : (0 : ℝ) ≤ x)
      have := mul_le_mul_of_nonneg_right hq hL
      linarith
    · -- Otherwise apply the induction hypothesis at `x / 6 ≥ 30`.
      have hy := ih (x / 6) (by linarith) (by rw [pow_succ] at hx'; linarith)
      have hlog : log (x / 6) ≤ log x := log_le_log (by positivity) (by linarith)
      have hq : 0 ≤ log (x / 6 / 5) / log 6 :=
        div_nonneg (log_nonneg (by linarith)) hlog6.le
      have hq' : log (x / 6 / 5) / log 6 + 1 = log (x / 5) / log 6 := by
        rw [div_add_one hlog6.ne', ← log_mul (by positivity) (by norm_num)]
        congr 2
        ring
      -- `a x + (6a / 5)(x / 6) = (6a / 5) x`, and the coefficients of `5 log − 5` add up to `hq'`.
      have : log (x / 6 / 5) / log 6 * (5 * log (x / 6) - 5) ≤
          log (x / 6 / 5) / log 6 * (5 * log x - 5) :=
        mul_le_mul_of_nonneg_left (by linarith) hq
      rw [← hq']
      linarith

/-- `5 log x − 5 ≤ 0.0037 x` for `x ≥ 11723`, from the tangent line of `log` at `12000`. -/
private theorem five_mul_log_sub_five_le {x : ℝ} (hx : 11723 ≤ x) :
    5 * log x - 5 ≤ 0.0037 * x := by
  have h := log_le_sub_one_of_pos (by positivity : 0 < x / 12000)
  have h12 : log 12000 = 5 * log 2 + log 3 + 3 * log 5 := by
    rw [show (12000 : ℝ) = 2 ^ 5 * 3 * 5 ^ 3 by norm_num, log_mul (by norm_num) (by norm_num),
      log_mul (by norm_num) (by norm_num), log_pow, log_pow]
    push_cast
    ring
  rw [log_div (by linarith) (by norm_num), h12] at h
  linarith [log_two_lt_d9, log_three_lt_d9, log_five_lt_d9]

/-- **Chebyshev's upper bound** `ψ(x) ≤ 1.11 x` for every `x > 0`, from the same bound on
`0 < y ≤ 11723`. -/
theorem psi_le_mul_of_forall_psi_le_mul (h : ∀ y, 0 < y → y ≤ 11723 → ψ y ≤ 1.11 * y) {x : ℝ}
    (hx : 0 < x) : ψ x ≤ 1.11 * x := by
  have ha := weightConstant_lt_d4
  -- Induction on `n` with `x ≤ 11723 · 6ⁿ`.
  suffices H : ∀ n : ℕ, ∀ x : ℝ, 0 < x → x ≤ 11723 * 6 ^ n → ψ x ≤ 1.11 * x by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (x / 11723) (by norm_num : (1 : ℝ) < 6)
    exact H n x hx (by linarith)
  intro n
  induction n with
  | zero => intro x hx hx'; exact h x hx (by simpa using hx')
  | succ n ih =>
    intro x hx hx'
    rcases le_or_gt x 11723 with hsmall | hlarge
    · exact h x hx hsmall
    have hy := ih (x / 6) (by positivity) (by rw [pow_succ] at hx'; linarith)
    have hstep := psi_sub_psi_div_six_le (by linarith : (30 : ℝ) ≤ x)
    have hL := five_mul_log_sub_five_le hlarge.le
    have := mul_le_mul_of_nonneg_right ha.le hx.le
    -- The constants have no slack: `1.11 / 6 + 0.9213 + 0.0037 = 1.11` exactly.
    linarith

/-- Chebyshev's finite-range hypothesis: `ψ(y) ≤ 1.015 y` for `0 < y ≤ 30` and `ψ(y) ≤ 1.11 y` for
`0 < y ≤ 11723`. These are computations on the values of `ψ` (the largest values of `ψ(y) / y` on
the two ranges are `ψ(19) / 19 = 1.0139…` and `ψ(113) / 113 = 1.0388…`); they start the iterations
of `Chebyshev.WeightRange.psi_le` and `Chebyshev.WeightRange.psi_le_mul`. -/
structure WeightRange : Prop where
  /-- `ψ(y) ≤ 1.015 y` for `0 < y ≤ 30`. -/
  psi_le_of_le_thirty : ∀ y, 0 < y → y ≤ 30 → ψ y ≤ 1.015 * y
  /-- `ψ(y) ≤ 1.11 y` for `0 < y ≤ 11723`. -/
  psi_le_of_le_11723 : ∀ y, 0 < y → y ≤ 11723 → ψ y ≤ 1.11 * y

/-- Under Chebyshev's finite-range hypothesis,
`ψ(x) ≤ (6a / 5) x + (log (x / 5) / log 6) (5 log x − 5)` for every `x ≥ 30`. -/
theorem WeightRange.psi_le (h : WeightRange) {x : ℝ} (hx : 30 ≤ x) :
    ψ x ≤ 6 * weightConstant / 5 * x + log (x / 5) / log 6 * (5 * log x - 5) :=
  psi_le_of_forall_psi_le_mul h.psi_le_of_le_thirty hx

/-- Under Chebyshev's finite-range hypothesis, `ψ(x) ≤ 1.11 x` for every `x > 0`. -/
theorem WeightRange.psi_le_mul (h : WeightRange) {x : ℝ} (hx : 0 < x) : ψ x ≤ 1.11 * x :=
  psi_le_mul_of_forall_psi_le_mul h.psi_le_of_le_11723 hx

end Chebyshev
