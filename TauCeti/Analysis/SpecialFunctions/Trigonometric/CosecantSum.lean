/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import TauCeti.Analysis.Convex.Integral
import TauCeti.Analysis.SpecialFunctions.Integrals.Trigonometric.Basic
import TauCeti.Analysis.SpecialFunctions.Trigonometric.Bounds
import TauCeti.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Cosecant sums

Using the continuity, convexity, and antiderivative of `x ↦ (sin x)⁻¹` on `(0, π)`
(`TauCeti.continuousOn_inv_sin_Ioo`, `TauCeti.convexOn_inv_sin_Ioo`, `TauCeti.integral_inv_sin`),
together with midpoint Jensen's inequality (`ConvexOn.sub_mul_le_intervalIntegral`), the cosecant
sum `∑_{b=1}^{q-1} (sin (π b / q))⁻¹` (`q ≥ 1`) satisfies Pomerance's explicit bound

  `∑_{b=1}^{q-1} (sin (π b / q))⁻¹ < (2 * q / π) * (log q + log (4 / π) + π ^ 2 / (12 * q ^ 2))`.

For `q ≥ 4`, separating the end terms `b = 1` and `b = q - 1` and bounding the middle `q - 3`
terms by integrating `(sin x)⁻¹` over `[3π / (2q), π - 3π / (2q)]` gives
`2 / sin (π / q) + (2q / π) log cot (3π / (4q))`, which is bounded by the closed form above via
`sin x ≥ x - x ^ 3 / 6` and `tan t ≥ t`. For `q ≥ 3`, this also yields
`∑_{b=1}^{q-1} (sin (π b / q))⁻¹ < q * log q`.

## Main statements

* `TauCeti.sum_Ico_inv_sin_pi_mul_div_lt`: Pomerance's cosecant sum bound for `1 ≤ q`.
* `TauCeti.two_div_pi_mul_log_add_le_log`: for real `x ≥ 3`,
  `(2 / π) * (log x + log (4 / π) + π ^ 2 / (12 * x ^ 2)) ≤ log x`.
* `TauCeti.sum_Ico_inv_sin_pi_mul_div_lt_mul_log`: for integer `q ≥ 2`,
  `∑_{b=1}^{q-1} (sin (π b / q))⁻¹ < q * log q`.

## References

* C. Pomerance, *Remarks on the Pólya–Vinogradov inequality*, Integers 11 (2011), Lemma 4 and
  displays (4)–(5).
-/

public section

open Real Finset

namespace TauCeti

/-! ### Numeric and trigonometric inequalities -/

/-- Lower bound `1 - π / 4 ≤ log (4 / π)`. -/
private lemma one_sub_pi_div_four_le_log_four_div_pi : 1 - π / 4 ≤ log (4 / π) := by
  have h := one_sub_inv_le_log_of_pos (div_pos (by norm_num : (0 : ℝ) < 4) pi_pos)
  rwa [inv_div] at h

/-- Each midpoint-Jensen step interval `[π(b - 1/2)/q, π(b + 1/2)/q]` for `2 ≤ b` and
`b + 1 ≤ q - 1` lies inside `(0, π)`. -/
private lemma Icc_mid_step_subset_Ioo {q b : ℕ} (hq : 0 < q) (hb2 : 2 ≤ b)
    (hbq : b + 1 ≤ q - 1) :
    Set.Icc (π * ((b : ℝ) - 1 / 2) / q) (π * (((b + 1 : ℕ) : ℝ) - 1 / 2) / q) ⊆
      Set.Ioo 0 π := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hbR : (2 : ℝ) ≤ b := by exact_mod_cast hb2
  have hbqR : ((b + 1 : ℕ) : ℝ) ≤ (q : ℝ) - 1 := by
    have h : ((b + 1 + 1 : ℕ) : ℝ) ≤ q := by exact_mod_cast (by omega : b + 1 + 1 ≤ q)
    push_cast at h ⊢
    linarith
  refine Set.Icc_subset_Ioo (div_pos (mul_pos pi_pos (by linarith)) hqpos) ?_
  rw [div_lt_iff₀ hqpos]
  nlinarith [pi_pos]

/-- Midpoint Jensen bound on a single step `[π(b - 1/2)/q, π(b + 1/2)/q]` for `(sin x)⁻¹`. -/
private lemma inv_sin_le_mul_integral {q b : ℕ} (hq : 0 < q) (hb2 : 2 ≤ b)
    (hbq : b + 1 ≤ q - 1) :
    (sin (π * b / q))⁻¹ ≤
      (q / π) * ∫ x in (π * ((b : ℝ) - 1 / 2) / q)..(π * (((b + 1 : ℕ) : ℝ) - 1 / 2) / q),
        (sin x)⁻¹ := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hsub : π * (((b + 1 : ℕ) : ℝ) - 1 / 2) / q - π * ((b : ℝ) - 1 / 2) / q = π / q := by
    push_cast
    ring
  have hmid : (π * ((b : ℝ) - 1 / 2) / q + π * (((b + 1 : ℕ) : ℝ) - 1 / 2) / q) / 2 =
      π * b / q := by
    push_cast
    ring
  have hle : π * ((b : ℝ) - 1 / 2) / q ≤ π * (((b + 1 : ℕ) : ℝ) - 1 / 2) / q := by
    linarith [hsub, div_pos pi_pos hqpos]
  have hsub_Ioo := Icc_mid_step_subset_Ioo hq hb2 hbq
  have hj := (convexOn_inv_sin_Ioo.subset hsub_Ioo (convex_Icc _ _)).sub_mul_le_intervalIntegral hle
  rw [hsub, hmid] at hj
  rw [← mul_le_mul_iff_right₀ (div_pos pi_pos hqpos)]
  calc
    π / q * (sin (π * b / q))⁻¹
      ≤ ∫ x in (π * ((b : ℝ) - 1 / 2) / q)..(π * (((b + 1 : ℕ) : ℝ) - 1 / 2) / q),
          (sin x)⁻¹ := hj
    _ = π / q * ((q / π) *
          ∫ x in (π * ((b : ℝ) - 1 / 2) / q)..(π * (((b + 1 : ℕ) : ℝ) - 1 / 2) / q),
            (sin x)⁻¹) := by
        field_simp [pi_ne_zero, hqpos.ne']

/-- Separate the `b = 1` and `b = q - 1` boundary terms from `∑_{b=1}^{q-1} (sin (π b / q))⁻¹`. -/
private lemma sum_Ico_inv_sin_split {q : ℕ} (hq : 4 ≤ q) :
    ∑ b ∈ Ico 1 q, (sin (π * b / q))⁻¹ =
      2 * (sin (π / q))⁻¹ + ∑ b ∈ Ico 2 (q - 1), (sin (π * b / q))⁻¹ := by
  have hsing : Ico (q - 1) q = {q - 1} := by
    ext x
    simp only [mem_Ico, mem_singleton]
    omega
  have htop : ∑ b ∈ Ico 2 q, (sin (π * b / q))⁻¹ =
      (∑ b ∈ Ico 2 (q - 1), (sin (π * b / q))⁻¹) + (sin (π * ↑(q - 1) / q))⁻¹ := by
    rw [← sum_Ico_consecutive _ (by omega : 2 ≤ q - 1) (by omega : q - 1 ≤ q), hsing,
      sum_singleton]
  rw [sum_eq_sum_Ico_succ_bot (by omega : 1 < q), htop]
  have hsin_end : sin (π * ↑(q - 1) / q) = sin (π / q) := by
    have hq0 : (q : ℝ) ≠ 0 := by positivity
    have harg : π * ((q : ℝ) - 1) / q = π - π / q := by field_simp [hq0]
    rw [Nat.cast_sub (by omega : 1 ≤ q), Nat.cast_one, harg, sin_pi_sub]
  rw [Nat.cast_one, mul_one, hsin_end]
  ring

/-- Upper bound on `log (tan (3π / (4q)))⁻¹` for `q ≥ 4` via `TauCeti.log_inv_tan_lt_neg_log`. -/
private lemma log_tan_three_pi_div_four_mul_lt {q : ℕ} (hq : 4 ≤ q) :
    log (tan (3 * π / (4 * q)))⁻¹ < log q + log (4 / π) - log 3 := by
  have hqpos : (0 : ℝ) < q := by positivity
  have ht_pos : 0 < 3 * π / (4 * q) := by positivity
  have ht_lt : 3 * π / (4 * q) < π / 2 := by
    have hq4 : (4 : ℝ) ≤ q := by exact_mod_cast hq
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [pi_pos]
  refine (log_inv_tan_lt_neg_log ht_pos ht_lt).trans_eq ?_
  rw [log_div (by positivity) (by positivity), log_mul (by norm_num) pi_ne_zero,
    log_mul (by norm_num) hqpos.ne', log_div (by norm_num) pi_ne_zero]
  ring

/-- Bound on the interior cosecant sum `∑_{b=2}^{q-2} (sin (π b / q))⁻¹` for `q ≥ 4`. -/
private lemma sum_Ico_mid_inv_sin_le {q : ℕ} (hq : 4 ≤ q) :
    ∑ b ∈ Ico 2 (q - 1), (sin (π * b / q))⁻¹ ≤
      (2 * q / π) * log (tan (3 * π / (4 * q)))⁻¹ := by
  have hqR : (4 : ℝ) ≤ q := by exact_mod_cast hq
  let a : ℕ → ℝ := fun b ↦ π * ((b : ℝ) - 1 / 2) / q
  have hmid_le : ∑ b ∈ Ico 2 (q - 1), (sin (π * b / q))⁻¹ ≤
      (q / π) * ∫ x in a 2..a (q - 1), (sin x)⁻¹ := by
    calc
      ∑ b ∈ Ico 2 (q - 1), (sin (π * b / q))⁻¹
        ≤ ∑ b ∈ Ico 2 (q - 1), (q / π) * ∫ x in a b..a (b + 1), (sin x)⁻¹ :=
          sum_le_sum fun b hb ↦ inv_sin_le_mul_integral (by omega) (mem_Ico.mp hb).1
            (by have := (mem_Ico.mp hb).2; omega)
      _ = (q / π) * ∑ b ∈ Ico 2 (q - 1), ∫ x in a b..a (b + 1), (sin x)⁻¹ := by rw [← mul_sum]
      _ = (q / π) * ∫ x in a 2..a (q - 1), (sin x)⁻¹ := by
          congr 1
          refine intervalIntegral.sum_integral_adjacent_intervals_Ico (by omega) fun b hb ↦ ?_
          rw [Set.mem_Ico] at hb
          have hsub_Ioo := Icc_mid_step_subset_Ioo (q := q) (by omega) hb.1 (by omega)
          have hle : a b ≤ a (b + 1) := by dsimp only [a]; gcongr; linarith
          exact (continuousOn_inv_sin_Ioo.mono hsub_Ioo).intervalIntegrable_of_Icc hle
  have ha2 : a 2 = 3 * π / (2 * q) := by dsimp only [a]; push_cast; ring
  have ha_top : a (q - 1) = π - a 2 := by
    dsimp only [a]; rw [Nat.cast_sub (by omega : 1 ≤ q), Nat.cast_one]; field_simp; ring
  have hint_eq : ∫ x in a 2..a (q - 1), (sin x)⁻¹ = 2 * log (tan (3 * π / (4 * q)))⁻¹ := by
    have ha2_half : a 2 / 2 = 3 * π / (4 * q) := by rw [ha2]; ring
    rw [ha_top, integral_inv_sin_pi_sub (by rw [ha2]; positivity)
      (by rw [ha2, div_lt_iff₀ (by positivity)]; nlinarith [pi_pos]), ha2_half]
  calc
    ∑ b ∈ Ico 2 (q - 1), (sin (π * b / q))⁻¹
      ≤ (q / π) * (2 * log (tan (3 * π / (4 * q)))⁻¹) := hint_eq ▸ hmid_le
    _ = (2 * q / π) * log (tan (3 * π / (4 * q)))⁻¹ := by ring

/-- For `q ≥ 4`, Pomerance's cosecant sum bound holds. -/
private lemma sum_Ico_inv_sin_pi_mul_div_lt_of_four_le {q : ℕ} (hq : 4 ≤ q) :
    ∑ b ∈ Ico 1 q, (sin (π * b / q))⁻¹ <
      2 * q / π * (log q + log (4 / π) + π ^ 2 / (12 * (q : ℝ) ^ 2)) := by
  have hqR : (4 : ℝ) ≤ q := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < q := by linarith
  have hend_le : 2 * (sin (π / q))⁻¹ ≤ 2 * q / π * (1 + π ^ 2 / (5 * (q : ℝ) ^ 2)) := by
    have h := inv_sin_le_of_pos_of_le_one (div_pos pi_pos hqpos)
      ((div_le_one hqpos).mpr (by linarith [pi_lt_d4]))
    calc
      2 * (sin (π / q))⁻¹ ≤ 2 * ((1 + (π / q) ^ 2 / 5) / (π / q)) := by gcongr
      _ = 2 * q / π * (1 + π ^ 2 / (5 * (q : ℝ) ^ 2)) := by field_simp
  have hconst : 1 + 7 * π ^ 2 / (60 * (q : ℝ) ^ 2) < log 3 := by
    have hpi : π < 3.15 := pi_lt_d4.trans (by norm_num)
    have hqsq : (16 : ℝ) ≤ (q : ℝ) ^ 2 := by nlinarith
    have hterm : 7 * π ^ 2 / (60 * (q : ℝ) ^ 2) ≤ 7 * 3.15 ^ 2 / (60 * 16) := by gcongr
    linarith [(by norm_num : (1.09 : ℝ) < 1.0986122885).trans log_three_gt_d9]
  calc
    ∑ b ∈ Ico 1 q, (sin (π * b / q))⁻¹
      = 2 * (sin (π / q))⁻¹ + ∑ b ∈ Ico 2 (q - 1), (sin (π * b / q))⁻¹ :=
        sum_Ico_inv_sin_split hq
    _ ≤ 2 * q / π * (1 + π ^ 2 / (5 * (q : ℝ) ^ 2)) +
          (2 * q / π) * log (tan (3 * π / (4 * q)))⁻¹ :=
        add_le_add hend_le (sum_Ico_mid_inv_sin_le hq)
    _ < 2 * q / π * (1 + π ^ 2 / (5 * (q : ℝ) ^ 2)) +
          2 * q / π * (log q + log (4 / π) - log 3) := by
        gcongr
        exact log_tan_three_pi_div_four_mul_lt hq
    _ = 2 * q / π * (log q + log (4 / π) + π ^ 2 / (12 * (q : ℝ) ^ 2) +
          (1 + 7 * π ^ 2 / (60 * (q : ℝ) ^ 2) - log 3)) := by ring
    _ < 2 * q / π * (log q + log (4 / π) + π ^ 2 / (12 * (q : ℝ) ^ 2)) := by
        have : 0 < 2 * (q : ℝ) / π := by positivity
        nlinarith

/-- Exact value of the cosecant sum at `q = 2`. -/
private lemma sum_Ico_inv_sin_pi_mul_div_two :
    ∑ b ∈ Ico (1 : ℕ) 2, (sin (π * b / (2 : ℕ)))⁻¹ = 1 := by
  have hI : Ico (1 : ℕ) 2 = {1} := by decide
  rw [hI, sum_singleton]
  simp

/-- Base case `q = 2` of Pomerance's cosecant sum bound. -/
private lemma sum_Ico_inv_sin_pi_mul_div_lt_two :
    ∑ b ∈ Ico 1 (2 : ℕ), (sin (π * b / (2 : ℕ)))⁻¹ <
      2 * (2 : ℕ) / π * (log (2 : ℕ) + log (4 / π) + π ^ 2 / (12 * ((2 : ℕ) : ℝ) ^ 2)) := by
  have hpi_gt : 3.14 < π := pi_gt_d4.trans' (by norm_num)
  have hpi_lt : π < 3.15 := pi_lt_d4.trans (by norm_num)
  have hlog2 : 0.693 < log 2 := log_two_gt_d9.trans' (by norm_num)
  have hinner : 1.1 < log 2 + log (4 / π) + π ^ 2 / (12 * (2 : ℝ) ^ 2) := by
    nlinarith [sq_nonneg (π - 3.14), one_sub_pi_div_four_le_log_four_div_pi]
  have hfac : 4 / 3.15 < 2 * (2 : ℝ) / π := by
    rw [div_lt_div_iff₀ (by norm_num) pi_pos]
    linarith
  rw [sum_Ico_inv_sin_pi_mul_div_two]
  push_cast
  calc
    (1 : ℝ) < 4 / 3.15 * 1.1 := by norm_num
    _ < 2 * (2 : ℝ) / π * (log 2 + log (4 / π) + π ^ 2 / (12 * (2 : ℝ) ^ 2)) := by gcongr

/-- Base case `q = 3` of Pomerance's cosecant sum bound. -/
private lemma sum_Ico_inv_sin_pi_mul_div_lt_three :
    ∑ b ∈ Ico 1 (3 : ℕ), (sin (π * b / (3 : ℕ)))⁻¹ <
      2 * (3 : ℕ) / π * (log (3 : ℕ) + log (4 / π) + π ^ 2 / (12 * ((3 : ℕ) : ℝ) ^ 2)) := by
  have hpi_gt : 3.14 < π := pi_gt_d4.trans' (by norm_num)
  have hpi_lt : π < 3.15 := pi_lt_d4.trans (by norm_num)
  have hI : Ico 1 3 = {1, 2} := by decide
  rw [hI, sum_pair (by decide)]
  have hsin2 : sin (π * (2 : ℕ) / (3 : ℕ)) = √3 / 2 := by
    have harg : π * ((2 : ℕ) : ℝ) / ((3 : ℕ) : ℝ) = π - π / 3 := by push_cast; ring
    rw [harg, sin_pi_sub, sin_pi_div_three]
  have hsin1 : sin (π * ((1 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)) = √3 / 2 := by simp [sin_pi_div_three]
  rw [hsin2, hsin1]
  have hlhs : (√3 / 2)⁻¹ + (√3 / 2)⁻¹ < 2.32 := by
    have hsq : (16 : ℝ) < (2.32 * √3) ^ 2 := by
      rw [mul_pow, sq_sqrt (by norm_num)]; norm_num
    have hpos : 0 < 2.32 * √3 := by positivity
    have hlt : 4 < 2.32 * √3 := by nlinarith
    have hlhs_eq : (√3 / 2)⁻¹ + (√3 / 2)⁻¹ = 4 / √3 := by ring
    rw [hlhs_eq]
    exact (div_lt_iff₀ (by positivity)).mpr hlt
  have hinner : 1.39 < log 3 + log (4 / π) + π ^ 2 / (12 * (3 : ℝ) ^ 2) := by
    nlinarith [sq_nonneg (π - 3.14), one_sub_pi_div_four_le_log_four_div_pi,
      (by norm_num : (1.09 : ℝ) < 1.0986122885).trans log_three_gt_d9]
  have hfac : 6 / 3.15 < 2 * (3 : ℝ) / π := by
    rw [div_lt_div_iff₀ (by norm_num) pi_pos]; linarith
  push_cast
  calc
    (√3 / 2)⁻¹ + (√3 / 2)⁻¹ < 2.32 := hlhs
    _ < 6 / 3.15 * 1.39 := by norm_num
    _ < 2 * (3 : ℝ) / π * (log 3 + log (4 / π) + π ^ 2 / (12 * (3 : ℝ) ^ 2)) := by gcongr

/-- **Pomerance's cosecant sum bound.** For every integer `q ≥ 1`,
`∑_{b=1}^{q-1} (sin (π b / q))⁻¹ < (2 * q / π) * (log q + log (4 / π) + π ^ 2 / (12 * q ^ 2))`. -/
theorem sum_Ico_inv_sin_pi_mul_div_lt {q : ℕ} (hq : 1 ≤ q) :
    ∑ b ∈ Ico 1 q, (sin (π * b / q))⁻¹ <
      2 * q / π * (log q + log (4 / π) + π ^ 2 / (12 * (q : ℝ) ^ 2)) := by
  by_cases hq4 : 4 ≤ q
  · exact sum_Ico_inv_sin_pi_mul_div_lt_of_four_le hq4
  interval_cases q
  · simp only [Ico_self, sum_empty, Nat.cast_one, mul_one, log_one, zero_add, one_pow]
    have hlog4pi : 0 < log (4 / π) :=
      log_pos ((one_lt_div pi_pos).mpr (pi_lt_d4.trans (by norm_num)))
    positivity
  · exact sum_Ico_inv_sin_pi_mul_div_lt_two
  · exact sum_Ico_inv_sin_pi_mul_div_lt_three

/-- For every real `x ≥ 3`,
`(2 / π) * (log x + log (4 / π) + π ^ 2 / (12 * x ^ 2)) ≤ log x`.
In particular, the classical Pólya–Vinogradov bound for a primitive character modulo `q ≥ 3`
is at most `√q * log q`. -/
theorem two_div_pi_mul_log_add_le_log {x : ℝ} (hx : 3 ≤ x) :
    2 / π * (log x + log (4 / π) + π ^ 2 / (12 * x ^ 2)) ≤ log x := by
  have hlogx : 1.09 ≤ log x :=
    ((by norm_num : (1.09 : ℝ) < 1.0986122885).trans log_three_gt_d9).le.trans
      (log_le_log (by norm_num) hx)
  have hlog_pi : log (4 / π) ≤ 4 / π - 1 := log_le_sub_one_of_pos (div_pos (by norm_num) pi_pos)
  have hpi_gt : 3.1415 < π := pi_gt_d4
  have hpi_lt : π < 3.1416 := pi_lt_d4
  have hsq : (9 : ℝ) ≤ x ^ 2 := by nlinarith
  have hterm : π ^ 2 / (12 * x ^ 2) ≤ 3.1416 ^ 2 / 108 := by
    calc
      π ^ 2 / (12 * x ^ 2) ≤ 3.1416 ^ 2 / (12 * 9) := by gcongr
      _ = 3.1416 ^ 2 / 108 := by norm_num
  have hpi_sub : 2 * (4 / π - 1 + 3.1416 ^ 2 / 108) ≤ (π - 2) * 1.09 := by
    have h4pi : 4 / π ≤ 4 / 3.1415 := by gcongr
    linarith
  have hmul : 2 * (log x + log (4 / π) + π ^ 2 / (12 * x ^ 2)) ≤ π * log x := by
    have h1 : 2 * (log (4 / π) + π ^ 2 / (12 * x ^ 2)) ≤ (π - 2) * log x := by
      have h1b : (π - 2) * 1.09 ≤ (π - 2) * log x :=
        mul_le_mul_of_nonneg_left hlogx (by linarith)
      linarith
    linarith
  rw [div_mul_eq_mul_div, div_le_iff₀ pi_pos]
  linarith

/-- For every integer `q ≥ 2`, `∑_{b=1}^{q-1} (sin (π b / q))⁻¹ < q * log q`. -/
theorem sum_Ico_inv_sin_pi_mul_div_lt_mul_log {q : ℕ} (hq : 2 ≤ q) :
    ∑ b ∈ Ico 1 q, (sin (π * b / q))⁻¹ < q * log q := by
  by_cases hq3 : 3 ≤ q
  · have h1 := sum_Ico_inv_sin_pi_mul_div_lt (Nat.le_of_succ_le hq)
    have h2 := two_div_pi_mul_log_add_le_log (x := q) (by exact_mod_cast hq3)
    have hqnn : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    have hfac : 2 * (q : ℝ) / π * (log q + log (4 / π) + π ^ 2 / (12 * (q : ℝ) ^ 2)) =
        (q : ℝ) * (2 / π * (log q + log (4 / π) + π ^ 2 / (12 * (q : ℝ) ^ 2))) := by ring
    calc
      ∑ b ∈ Ico 1 q, (sin (π * b / q))⁻¹
        < q * (2 / π * (log q + log (4 / π) + π ^ 2 / (12 * (q : ℝ) ^ 2))) := by
          simpa only [hfac] using h1
      _ ≤ q * log q := mul_le_mul_of_nonneg_left h2 hqnn
  · have hq2 : q = 2 := by omega
    subst hq2
    have hlog2 : 0.693 < log 2 := log_two_gt_d9.trans' (by norm_num)
    rw [sum_Ico_inv_sin_pi_mul_div_two]
    push_cast
    linarith

/-! ### Checks -/

/-- At `q = 3`, the cosecant sum is `4 / √3 < 3 * log 3`. -/
example : ∑ b ∈ Ico (1 : ℕ) 3, (sin (π * b / (3 : ℕ)))⁻¹ < 3 * log 3 := by
  simpa using sum_Ico_inv_sin_pi_mul_div_lt_mul_log (by omega : 2 ≤ 3)

/-- At `x = 2` the inequality fails, so `3` is the least integer for which
`two_div_pi_mul_log_add_le_log` applies. -/
example : log 2 < 2 / π * (log 2 + log (4 / π) + π ^ 2 / (12 * (2 : ℝ) ^ 2)) := by
  have hpi_gt : 3.1415 < π := pi_gt_d4
  have hpi_lt : π < 3.1416 := pi_lt_d4
  have hlog2 : log 2 < 0.6932 := log_two_lt_d9.trans (by norm_num)
  have hlog_pi := one_sub_pi_div_four_le_log_four_div_pi
  rw [div_mul_eq_mul_div, lt_div_iff₀ pi_pos]
  nlinarith [sq_nonneg (π - 3.1415)]

end TauCeti
