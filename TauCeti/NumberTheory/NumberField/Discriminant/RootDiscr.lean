/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import TauCeti.Algebra.Order.Field.OneAddInvPow

/-!
# Minkowski lower bounds for the root discriminant

Minkowski's bound `NumberField.abs_discr_ge'` gives `n^{2n} / ((4/π)^{2r₂} (n!)²) ≤ |d_K|` for a
number field `K` of degree `n` with `r₂` complex places. Since `4/π ≥ 1` and `2r₂ ≤ n`, the
signature-free quantity

`B_n = (π/4)ⁿ (nⁿ/n!)²` (`TauCeti.NumberField.minkowskiDiscrBound`)

is also a lower bound for `|d_K|`. Consecutive values satisfy `B_{n+1} = (π/4) (1 + 1/n)^{2n} B_n`,
and `(1 + 1/n)ⁿ` is nondecreasing (`TauCeti.monotone_one_add_inv_pow`). Hence once `cⁿ < B_n`
holds at one degree `n₀` with `4c ≤ π (1 + 1/n₀)^{2n₀}`, it holds at every larger degree, and
then the root discriminant `rd(K) = |d_K|^{1/n}` exceeds `c`.

Evaluating `B_n` at degrees `3`, `6` and `12` with rational bounds on `π` gives the thresholds

* `n ≥ 3 → rd(K) > 2` (`TauCeti.NumberField.two_lt_rootDiscr`),
* `n ≥ 6 → rd(K) > 3` (`TauCeti.NumberField.three_lt_rootDiscr`),
* `n ≥ 12 → rd(K) > 4` (`TauCeti.NumberField.four_lt_rootDiscr`),

and, contrapositively, a number field of root discriminant at most `2`, `3` or `4` has degree at
most `2`, `5` or `11`, respectively. These degree bounds bound the order of the Galois group of a
small Galois number field once a local estimate bounds its root discriminant, as in Tate's proof
that there is no irreducible two-dimensional mod-`2` Galois representation of `ℚ` unramified
outside `2`. The thresholds are not sharp: the analytic bounds of Odlyzko and Poitou are much
stronger, but these follow from Minkowski's bound alone.

## References

* A. M. Odlyzko, *Bounds for discriminants and related estimates for class numbers, regulators
  and zeros of zeta functions: a survey of recent results*, J. Théor. Nombres Bordeaux 2 (1990),
  119–141, §1, p. 119.
-/

public section

open Module NumberField NumberField.InfinitePlace Real
open scoped Nat

namespace TauCeti.NumberField

/-- The signature-free Minkowski lower bound `(π/4)ⁿ (nⁿ/n!)²` for the absolute value of the
discriminant of a number field of degree `n` (see `minkowskiDiscrBound_le_abs_discr`). It is the
Minkowski bound `n^{2n} / ((4/π)^{2r₂} (n!)²)` in the worst case `2r₂ = n`. -/
noncomputable def minkowskiDiscrBound (n : ℕ) : ℝ :=
  (π / 4) ^ n * ((n : ℝ) ^ n / n !) ^ 2

/-- The defining formula of the Minkowski discriminant bound. -/
theorem minkowskiDiscrBound_def (n : ℕ) :
    minkowskiDiscrBound n = (π / 4) ^ n * ((n : ℝ) ^ n / n !) ^ 2 := (rfl)

/-- In degree zero the Minkowski discriminant bound is `1`, because `0⁰ = 0! = 1`. -/
@[simp]
theorem minkowskiDiscrBound_zero : minkowskiDiscrBound 0 = 1 := by
  simp [minkowskiDiscrBound_def]

/-- The Minkowski discriminant bound is positive. -/
theorem minkowskiDiscrBound_pos (n : ℕ) : 0 < minkowskiDiscrBound n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [minkowskiDiscrBound_def]
    have : (0 : ℝ) < n := by exact_mod_cast hn
    positivity

/-- The recursion `B_{n+1} = (π/4) (1 + 1/n)^{2n} B_n` for the Minkowski discriminant bound. At
`n = 0` it reads `B₁ = π/4`, because `(0 : ℝ)⁻¹ = 0`. -/
theorem minkowskiDiscrBound_succ (n : ℕ) :
    minkowskiDiscrBound (n + 1) = π / 4 * (1 + (n : ℝ)⁻¹) ^ (2 * n) * minkowskiDiscrBound n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [minkowskiDiscrBound_def]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have h1 : 1 + (n : ℝ)⁻¹ = (n + 1) / n := by field_simp
  rw [minkowskiDiscrBound_def, minkowskiDiscrBound_def, h1, Nat.factorial_succ]
  push_cast
  simp only [div_pow, mul_pow, ← pow_mul]
  field_simp
  ring

/-- **Minkowski's bound, uniform in the signature.** A number field of degree `n` satisfies
`(π/4)ⁿ (nⁿ/n!)² ≤ |d_K|`. -/
theorem minkowskiDiscrBound_le_abs_discr (K : Type*) [Field K] [NumberField K] :
    minkowskiDiscrBound (finrank ℚ K) ≤ |discr K| := by
  have hr : 2 * nrComplexPlaces K ≤ finrank ℚ K := by
    rw [← card_add_two_mul_card_eq_rank]
    exact Nat.le_add_left _ _
  have h4 : (1 : ℝ) ≤ 4 / π := (one_le_div pi_pos).2 pi_le_four
  have hn : (0 : ℝ) < finrank ℚ K := Nat.cast_pos.mpr finrank_pos
  calc minkowskiDiscrBound (finrank ℚ K)
      = (finrank ℚ K : ℝ) ^ (2 * finrank ℚ K) /
          ((4 / π) ^ finrank ℚ K * ((finrank ℚ K)! : ℝ) ^ 2) := by
        rw [minkowskiDiscrBound_def, div_pow, div_pow, div_pow, ← pow_mul]
        field_simp
        ring
    _ ≤ (finrank ℚ K : ℝ) ^ (2 * finrank ℚ K) /
          ((4 / π) ^ (2 * nrComplexPlaces K) * ((finrank ℚ K)! : ℝ) ^ 2) := by
        gcongr
    _ ≤ |discr K| := abs_discr_ge' K

/-- **Propagation of a Minkowski threshold.** If `c ^ n₀ < B_{n₀}` and the ratio
`B_{n₀+1} / B_{n₀} = (π/4) (1 + 1/n₀)^{2n₀}` is at least `c`, then `cⁿ < B_n` for every `n ≥ n₀`:
the ratios `B_{n+1} / B_n` only increase with `n`. -/
theorem pow_lt_minkowskiDiscrBound {c : ℝ} {n₀ n : ℕ} (hc : 0 ≤ c)
    (hbase : c ^ n₀ < minkowskiDiscrBound n₀)
    (hstep : 4 * c ≤ π * (1 + (n₀ : ℝ)⁻¹) ^ (2 * n₀)) (hn : n₀ ≤ n) :
    c ^ n < minkowskiDiscrBound n := by
  induction n, hn using Nat.le_induction with
  | base => exact hbase
  | succ m hm ih =>
    have hmono : (1 + (n₀ : ℝ)⁻¹) ^ (2 * n₀) ≤ (1 + (m : ℝ)⁻¹) ^ (2 * m) := by
      rw [pow_mul', pow_mul']
      gcongr
      exact monotone_one_add_inv_pow hm
    have hratio : c ≤ π / 4 * (1 + (m : ℝ)⁻¹) ^ (2 * m) := by
      nlinarith [mul_le_mul_of_nonneg_left hmono pi_pos.le]
    have hpos : 0 < π / 4 * (1 + (m : ℝ)⁻¹) ^ (2 * m) := by
      have := pi_pos
      positivity
    rw [pow_succ, minkowskiDiscrBound_succ, mul_comm (π / 4 * _)]
    exact (mul_le_mul_of_nonneg_left hratio (pow_nonneg hc m)).trans_lt
      (mul_lt_mul_of_pos_right ih hpos)

/-- A number field of degree `n` whose Minkowski bound `B_n` exceeds `cⁿ` has root discriminant
greater than `c`. -/
theorem lt_rootDiscr_of_pow_lt_minkowskiDiscrBound {K : Type*} [Field K] [NumberField K] {c : ℝ}
    (h : c ^ finrank ℚ K < minkowskiDiscrBound (finrank ℚ K)) : c < rootDiscr K := by
  have hd : (0 : ℝ) ≤ |discr K| := by positivity
  rw [rootDiscr_def]
  rcases lt_or_ge c 0 with hc | hc
  · exact hc.trans_le (rpow_nonneg hd _)
  have hn : (0 : ℝ) < finrank ℚ K := Nat.cast_pos.mpr finrank_pos
  rw [lt_rpow_inv_iff_of_pos hc hd hn, rpow_natCast]
  exact h.trans_le (minkowskiDiscrBound_le_abs_discr K)

/-- A lower bound `l ≤ π` reduces `cⁿ < B_n` to an inequality between rational numbers. -/
private theorem pow_lt_minkowskiDiscrBound_of_le_pi {c l : ℝ} {n : ℕ} (hl : 0 ≤ l) (hlπ : l ≤ π)
    (h : c ^ n < (l / 4) ^ n * ((n : ℝ) ^ n / n !) ^ 2) : c ^ n < minkowskiDiscrBound n := by
  rw [minkowskiDiscrBound_def]
  refine h.trans_le ?_
  gcongr

/-- **Minkowski threshold two.** A number field of degree at least `3` has root discriminant
greater than `2`. -/
theorem two_lt_rootDiscr {K : Type*} [Field K] [NumberField K] (h : 3 ≤ finrank ℚ K) :
    2 < rootDiscr K := by
  refine lt_rootDiscr_of_pow_lt_minkowskiDiscrBound (pow_lt_minkowskiDiscrBound zero_le_two
    (pow_lt_minkowskiDiscrBound_of_le_pi (l := 3) (by norm_num) pi_gt_three.le
      (by norm_num [Nat.factorial])) ?_ h)
  nlinarith [pi_gt_three]

/-- **Minkowski threshold three.** A number field of degree at least `6` has root discriminant
greater than `3`. -/
theorem three_lt_rootDiscr {K : Type*} [Field K] [NumberField K] (h : 6 ≤ finrank ℚ K) :
    3 < rootDiscr K := by
  refine lt_rootDiscr_of_pow_lt_minkowskiDiscrBound (pow_lt_minkowskiDiscrBound zero_le_three
    (pow_lt_minkowskiDiscrBound_of_le_pi (l := 3) (by norm_num) pi_gt_three.le
      (by norm_num [Nat.factorial])) ?_ h)
  nlinarith [pi_gt_three]

/-- **Minkowski threshold four.** A number field of degree at least `12` has root discriminant
greater than `4`. -/
theorem four_lt_rootDiscr {K : Type*} [Field K] [NumberField K] (h : 12 ≤ finrank ℚ K) :
    4 < rootDiscr K := by
  refine lt_rootDiscr_of_pow_lt_minkowskiDiscrBound (pow_lt_minkowskiDiscrBound zero_le_four
    (pow_lt_minkowskiDiscrBound_of_le_pi (l := 3.14) (by norm_num) pi_gt_d2.le
      (by norm_num [Nat.factorial])) ?_ h)
  nlinarith [pi_gt_three]

/-- A number field of root discriminant at most `2` has degree at most `2`. -/
theorem finrank_le_two_of_rootDiscr_le_two {K : Type*} [Field K] [NumberField K]
    (h : rootDiscr K ≤ 2) : finrank ℚ K ≤ 2 := by
  by_contra! hK
  exact (two_lt_rootDiscr hK).not_ge h

/-- A number field of root discriminant at most `3` has degree at most `5`. -/
theorem finrank_le_five_of_rootDiscr_le_three {K : Type*} [Field K] [NumberField K]
    (h : rootDiscr K ≤ 3) : finrank ℚ K ≤ 5 := by
  by_contra! hK
  exact (three_lt_rootDiscr hK).not_ge h

/-- A number field of root discriminant at most `4` has degree at most `11`. -/
theorem finrank_le_eleven_of_rootDiscr_le_four {K : Type*} [Field K] [NumberField K]
    (h : rootDiscr K ≤ 4) : finrank ℚ K ≤ 11 := by
  by_contra! hK
  exact (four_lt_rootDiscr hK).not_ge h

end TauCeti.NumberField
