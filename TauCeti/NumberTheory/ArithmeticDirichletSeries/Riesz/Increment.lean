/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Riesz.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Normed.Group.Basic

/-!
# Finite differences of first Riesz sums

The forward difference of a first Riesz sum is its initial affine increment plus a ramp sum
supported only on the integers crossed by the cutoff. This controls the error when recovering a
sharp logarithmically weighted sum from a bound for a smoothed increment.
-/

public section

open Finset

namespace TauCeti

/-- The excess over the initial affine increment comes only from the newly included terms. -/
theorem rieszSum_sub_eq_mul_sum_div_add_sum_Ioc (a : ℕ → ℂ) {z y : ℝ} (hzy : z ≤ y) :
    rieszSum a y - rieszSum a z =
      ((y - z : ℝ) : ℂ) * (∑ n ∈ Icc 1 ⌊z⌋₊, a n / n) +
        ∑ n ∈ Ioc ⌊z⌋₊ ⌊y⌋₊, a n * ((y : ℂ) / n - 1) := by
  have hfloor := Nat.floor_le_floor hzy
  have hsplit (f : ℕ → ℂ) :
      (∑ n ∈ Icc 1 ⌊z⌋₊, f n) + (∑ n ∈ Ioc ⌊z⌋₊ ⌊y⌋₊, f n) =
        ∑ n ∈ Icc 1 ⌊y⌋₊, f n := by
    have hIcc (n : ℕ) : Icc 1 n = Ioc 0 n := Icc_add_one_left_eq_Ioc 0 n
    rw [hIcc, hIcc, sum_Ioc_consecutive f (Nat.zero_le _) hfloor]
  rw [rieszSum_def a y, rieszSum_def a z, ← hsplit, add_sub_right_comm,
    ← sum_sub_distrib, mul_sum]
  exact congrArg (· + _) (sum_congr rfl fun n _ ↦ by push_cast; ring)

/-- A forward difference quotient of a first Riesz sum recovers the inclusive sharp sum up to
an error of at most `M / z` per crossed integer, if those coefficients have norm at most `M`.
No bound is needed on the coefficients at or below the starting cutoff. -/
theorem norm_rieszSum_sub_div_sub_sum_div_le (a : ℕ → ℂ) {z y M : ℝ}
    (hz : 0 < z) (hzy : z < y) (hM : ∀ n ∈ Ioc ⌊z⌋₊ ⌊y⌋₊, ‖a n‖ ≤ M) :
    ‖(rieszSum a y - rieszSum a z) / ((y - z : ℝ) : ℂ) -
        ∑ n ∈ Icc 1 ⌊z⌋₊, a n / n‖ ≤ ((Ioc ⌊z⌋₊ ⌊y⌋₊).card : ℝ) * (M / z) := by
  have hstep : 0 < y - z := sub_pos.mpr hzy
  have hstep₀ : ((y - z : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hstep.ne'
  rw [rieszSum_sub_eq_mul_sum_div_add_sum_Ioc a hzy.le, add_div,
    mul_div_cancel_left₀ _ hstep₀, add_sub_cancel_left, sum_div]
  refine (norm_sum_le _ _).trans ?_
  rw [← nsmul_eq_mul, ← sum_const]
  refine sum_le_sum fun n hn ↦ ?_
  obtain ⟨hnz, hny⟩ := mem_Ioc.mp hn
  have hn0 : n ≠ 0 := by omega
  have hzn : z < n := (Nat.floor_lt' hn0).mp hnz
  have hny' : (n : ℝ) ≤ y := (Nat.le_floor_iff' hn0).mp hny
  have hratio : 0 ≤ y / (n : ℝ) - 1 := sub_nonneg.mpr ((one_le_div (hz.trans hzn)).mpr hny')
  rw [norm_div, norm_mul, ← Complex.ofReal_natCast, ← Complex.ofReal_div, ← Complex.ofReal_one,
    ← Complex.ofReal_sub, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hratio,
    Real.norm_of_nonneg hstep.le]
  calc
    ‖a n‖ * (y / n - 1) / (y - z) ≤ M * (y / n - 1) / (y - z) := by gcongr; exact hM n hn
    _ ≤ M / z := by
      rw [mul_div_assoc, ← mul_one_div M z]
      refine mul_le_mul_of_nonneg_left ?_ ((norm_nonneg _).trans (hM n hn))
      calc
        (y / n - 1) / (y - z) = (y - n) / (y - z) / n := by field_simp
        _ ≤ 1 / z := by
          gcongr
          exact (div_le_one hstep).mpr (by linarith)

end TauCeti
