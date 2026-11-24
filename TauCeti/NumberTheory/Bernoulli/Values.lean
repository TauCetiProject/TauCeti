/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ZetaValues
public import TauCeti.NumberTheory.Bernoulli.Basic

/-!
# Signs and values of the even Bernoulli numbers

The Bernoulli numbers here are Mathlib's `bernoulli`, with `B₁ = -1/2`. Mathlib evaluates them
up to `B₆`, and `TauCeti.bernoulli_twelve` in `TauCeti.NumberTheory.Bernoulli.Basic` evaluates
`B₁₂`. This file continues the list of the even ones up to `B₃₈`, and proves that they
alternate in sign, `(-1)^(k+1) B_{2k} > 0` for `k ≥ 1`; in particular no even Bernoulli number
vanishes.

Each value is obtained from Mathlib's recursion `bernoulli'_def`, after substituting the values
already proved, by exact rational arithmetic. The sign comes from Euler's evaluation
`hasSum_zeta_nat` of `ζ(2k)` as a positive series.

These values are the input of exact evaluations of products of Bernoulli numbers, such as the mass
of the genus of positive definite even unimodular lattices of rank `n ≤ 40`, whose largest
Bernoulli index is `n - 2`.

## Main results

* `TauCeti.neg_one_pow_mul_bernoulli_two_mul_pos`: `(-1)^(k+1) B_{2k} > 0` for `k ≠ 0`.
* `TauCeti.bernoulli_two_mul_ne_zero`: `B_{2k} ≠ 0` for every `k`.
* `TauCeti.bernoulli_eight`, …, `TauCeti.bernoulli_thirtyEight`: the values of `B₈, …, B₃₈`
  other than `B₁₂`.

## References

* M. Abramowitz and I. A. Stegun, *Handbook of Mathematical Functions*, Table 23.2, for the
  values of the Bernoulli numbers.
-/

public section

open Finset

namespace TauCeti

/-- **The even Bernoulli numbers alternate in sign**: `(-1)^(k+1) B_{2k} > 0` for `k ≠ 0`, since
by Euler's formula `(-1)^(k+1) 2^(2k-1) π^(2k) B_{2k} / (2k)!` is the sum `ζ(2k)` of positive
terms. -/
theorem neg_one_pow_mul_bernoulli_two_mul_pos {k : ℕ} (hk : k ≠ 0) :
    0 < (-1) ^ (k + 1) * bernoulli (2 * k) := by
  have hsum := hasSum_zeta_nat hk
  have hpos : 0 < ∑' n : ℕ, 1 / (n : ℝ) ^ (2 * k) :=
    hsum.summable.tsum_pos (fun n => by positivity) 1 (by simp)
  rw [hsum.tsum_eq] at hpos
  have hfac : (0 : ℝ) < 2 ^ (2 * k - 1) * Real.pi ^ (2 * k) / (2 * k).factorial := by
    positivity
  have h : (0 : ℝ) < (-1) ^ (k + 1) * bernoulli (2 * k) := by
    refine (mul_pos_iff_of_pos_right hfac).mp ?_
    convert hpos using 1
    ring
  exact_mod_cast h

/-- **No even Bernoulli number vanishes.** For `k = 0` this is `B₀ = 1`; for `k ≠ 0` it follows
from the sign `TauCeti.neg_one_pow_mul_bernoulli_two_mul_pos`. -/
theorem bernoulli_two_mul_ne_zero (k : ℕ) : bernoulli (2 * k) ≠ 0 := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  · exact right_ne_zero_of_mul (neg_one_pow_mul_bernoulli_two_mul_pos hk).ne'

/-! ### The values of `B₈, …, B₃₈`

Each value is read off Mathlib's recursion `bernoulli'_def` for `bernoulli' = bernoulli` in
positive even index. After expanding the sum, the odd values vanish, `bernoulli' 1 = 1/2`, and the
even values below are the ones already proved, so that the remaining identity is an identity of
rational numbers with binomial coefficients, which the kernel checks. -/

@[simp]
theorem bernoulli_eight : bernoulli 8 = -30⁻¹ := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide), bernoulli'_def]
  simp (disch := decide) only [sum_range_succ, sum_range_zero, bernoulli'_one,
    ← bernoulli_eq_bernoulli'_of_ne_one, bernoulli_eq_zero_of_odd, bernoulli_zero, bernoulli_two,
    bernoulli_four, bernoulli_six]
  decide +kernel

@[simp]
theorem bernoulli_ten : bernoulli 10 = 5 / 66 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide), bernoulli'_def]
  simp (disch := decide) only [sum_range_succ, sum_range_zero, bernoulli'_one,
    ← bernoulli_eq_bernoulli'_of_ne_one, bernoulli_eq_zero_of_odd, bernoulli_zero, bernoulli_two,
    bernoulli_four, bernoulli_six, bernoulli_eight]
  decide +kernel

@[simp]
theorem bernoulli_fourteen : bernoulli 14 = 7 / 6 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide), bernoulli'_def]
  simp (disch := decide) only [sum_range_succ, sum_range_zero, bernoulli'_one,
    ← bernoulli_eq_bernoulli'_of_ne_one, bernoulli_eq_zero_of_odd, bernoulli_zero, bernoulli_two,
    bernoulli_four, bernoulli_six, bernoulli_eight, bernoulli_ten, bernoulli_twelve]
  decide +kernel

@[simp]
theorem bernoulli_sixteen : bernoulli 16 = -3617 / 510 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide), bernoulli'_def]
  simp (disch := decide) only [sum_range_succ, sum_range_zero, bernoulli'_one,
    ← bernoulli_eq_bernoulli'_of_ne_one, bernoulli_eq_zero_of_odd, bernoulli_zero, bernoulli_two,
    bernoulli_four, bernoulli_six, bernoulli_eight, bernoulli_ten, bernoulli_twelve,
    bernoulli_fourteen]
  decide +kernel

@[simp]
theorem bernoulli_eighteen : bernoulli 18 = 43867 / 798 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide), bernoulli'_def]
  simp (disch := decide) only [sum_range_succ, sum_range_zero, bernoulli'_one,
    ← bernoulli_eq_bernoulli'_of_ne_one, bernoulli_eq_zero_of_odd, bernoulli_zero, bernoulli_two,
    bernoulli_four, bernoulli_six, bernoulli_eight, bernoulli_ten, bernoulli_twelve,
    bernoulli_fourteen, bernoulli_sixteen]
  decide +kernel

@[simp]
theorem bernoulli_twenty : bernoulli 20 = -174611 / 330 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide), bernoulli'_def]
  simp (disch := decide) only [sum_range_succ, sum_range_zero, bernoulli'_one,
    ← bernoulli_eq_bernoulli'_of_ne_one, bernoulli_eq_zero_of_odd, bernoulli_zero, bernoulli_two,
    bernoulli_four, bernoulli_six, bernoulli_eight, bernoulli_ten, bernoulli_twelve,
    bernoulli_fourteen, bernoulli_sixteen, bernoulli_eighteen]
  decide +kernel

@[simp]
theorem bernoulli_twentyTwo : bernoulli 22 = 854513 / 138 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide), bernoulli'_def]
  simp (disch := decide) only [sum_range_succ, sum_range_zero, bernoulli'_one,
    ← bernoulli_eq_bernoulli'_of_ne_one, bernoulli_eq_zero_of_odd, bernoulli_zero, bernoulli_two,
    bernoulli_four, bernoulli_six, bernoulli_eight, bernoulli_ten, bernoulli_twelve,
    bernoulli_fourteen, bernoulli_sixteen, bernoulli_eighteen, bernoulli_twenty]
  decide +kernel

@[simp]
theorem bernoulli_twentyFour : bernoulli 24 = -236364091 / 2730 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide), bernoulli'_def]
  simp (disch := decide) only [sum_range_succ, sum_range_zero, bernoulli'_one,
    ← bernoulli_eq_bernoulli'_of_ne_one, bernoulli_eq_zero_of_odd, bernoulli_zero, bernoulli_two,
    bernoulli_four, bernoulli_six, bernoulli_eight, bernoulli_ten, bernoulli_twelve,
    bernoulli_fourteen, bernoulli_sixteen, bernoulli_eighteen, bernoulli_twenty,
    bernoulli_twentyTwo]
  decide +kernel

@[simp]
theorem bernoulli_twentySix : bernoulli 26 = 8553103 / 6 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide), bernoulli'_def]
  simp (disch := decide) only [sum_range_succ, sum_range_zero, bernoulli'_one,
    ← bernoulli_eq_bernoulli'_of_ne_one, bernoulli_eq_zero_of_odd, bernoulli_zero, bernoulli_two,
    bernoulli_four, bernoulli_six, bernoulli_eight, bernoulli_ten, bernoulli_twelve,
    bernoulli_fourteen, bernoulli_sixteen, bernoulli_eighteen, bernoulli_twenty,
    bernoulli_twentyTwo, bernoulli_twentyFour]
  decide +kernel

@[simp]
theorem bernoulli_twentyEight : bernoulli 28 = -23749461029 / 870 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide), bernoulli'_def]
  simp (disch := decide) only [sum_range_succ, sum_range_zero, bernoulli'_one,
    ← bernoulli_eq_bernoulli'_of_ne_one, bernoulli_eq_zero_of_odd, bernoulli_zero, bernoulli_two,
    bernoulli_four, bernoulli_six, bernoulli_eight, bernoulli_ten, bernoulli_twelve,
    bernoulli_fourteen, bernoulli_sixteen, bernoulli_eighteen, bernoulli_twenty,
    bernoulli_twentyTwo, bernoulli_twentyFour, bernoulli_twentySix]
  decide +kernel

@[simp]
theorem bernoulli_thirty : bernoulli 30 = 8615841276005 / 14322 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide), bernoulli'_def]
  simp (disch := decide) only [sum_range_succ, sum_range_zero, bernoulli'_one,
    ← bernoulli_eq_bernoulli'_of_ne_one, bernoulli_eq_zero_of_odd, bernoulli_zero, bernoulli_two,
    bernoulli_four, bernoulli_six, bernoulli_eight, bernoulli_ten, bernoulli_twelve,
    bernoulli_fourteen, bernoulli_sixteen, bernoulli_eighteen, bernoulli_twenty,
    bernoulli_twentyTwo, bernoulli_twentyFour, bernoulli_twentySix, bernoulli_twentyEight]
  decide +kernel

@[simp]
theorem bernoulli_thirtyTwo : bernoulli 32 = -7709321041217 / 510 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide), bernoulli'_def]
  simp (disch := decide) only [sum_range_succ, sum_range_zero, bernoulli'_one,
    ← bernoulli_eq_bernoulli'_of_ne_one, bernoulli_eq_zero_of_odd, bernoulli_zero, bernoulli_two,
    bernoulli_four, bernoulli_six, bernoulli_eight, bernoulli_ten, bernoulli_twelve,
    bernoulli_fourteen, bernoulli_sixteen, bernoulli_eighteen, bernoulli_twenty,
    bernoulli_twentyTwo, bernoulli_twentyFour, bernoulli_twentySix, bernoulli_twentyEight,
    bernoulli_thirty]
  decide +kernel

@[simp]
theorem bernoulli_thirtyFour : bernoulli 34 = 2577687858367 / 6 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide), bernoulli'_def]
  simp (disch := decide) only [sum_range_succ, sum_range_zero, bernoulli'_one,
    ← bernoulli_eq_bernoulli'_of_ne_one, bernoulli_eq_zero_of_odd, bernoulli_zero, bernoulli_two,
    bernoulli_four, bernoulli_six, bernoulli_eight, bernoulli_ten, bernoulli_twelve,
    bernoulli_fourteen, bernoulli_sixteen, bernoulli_eighteen, bernoulli_twenty,
    bernoulli_twentyTwo, bernoulli_twentyFour, bernoulli_twentySix, bernoulli_twentyEight,
    bernoulli_thirty, bernoulli_thirtyTwo]
  decide +kernel

@[simp]
theorem bernoulli_thirtySix : bernoulli 36 = -26315271553053477373 / 1919190 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide), bernoulli'_def]
  simp (disch := decide) only [sum_range_succ, sum_range_zero, bernoulli'_one,
    ← bernoulli_eq_bernoulli'_of_ne_one, bernoulli_eq_zero_of_odd, bernoulli_zero, bernoulli_two,
    bernoulli_four, bernoulli_six, bernoulli_eight, bernoulli_ten, bernoulli_twelve,
    bernoulli_fourteen, bernoulli_sixteen, bernoulli_eighteen, bernoulli_twenty,
    bernoulli_twentyTwo, bernoulli_twentyFour, bernoulli_twentySix, bernoulli_twentyEight,
    bernoulli_thirty, bernoulli_thirtyTwo, bernoulli_thirtyFour]
  decide +kernel

@[simp]
theorem bernoulli_thirtyEight : bernoulli 38 = 2929993913841559 / 6 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide), bernoulli'_def]
  simp (disch := decide) only [sum_range_succ, sum_range_zero, bernoulli'_one,
    ← bernoulli_eq_bernoulli'_of_ne_one, bernoulli_eq_zero_of_odd, bernoulli_zero, bernoulli_two,
    bernoulli_four, bernoulli_six, bernoulli_eight, bernoulli_ten, bernoulli_twelve,
    bernoulli_fourteen, bernoulli_sixteen, bernoulli_eighteen, bernoulli_twenty,
    bernoulli_twentyTwo, bernoulli_twentyFour, bernoulli_twentySix, bernoulli_twentyEight,
    bernoulli_thirty, bernoulli_thirtyTwo, bernoulli_thirtyFour, bernoulli_thirtySix]
  decide +kernel

end TauCeti
