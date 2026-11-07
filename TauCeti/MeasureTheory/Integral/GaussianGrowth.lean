/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Polynomially weighted Gaussian integrability

Gaussian decay dominates real powers of `1 + |x|` on the real line.
-/

public section

open MeasureTheory Real

namespace TauCeti

/-- A polynomial bound on powers of `1 + |x|` with an even power of `x`. -/
theorem one_add_abs_pow_le_two_pow_mul (x : ℝ) (k : ℕ) :
    (1 + |x|) ^ k ≤ 2 ^ k * (1 + x ^ (2 * k : ℕ)) := by
  have hu : 0 ≤ |x| := abs_nonneg x
  have hsum : 1 + |x| ≤ 2 * max 1 |x| := by
    by_cases h : 1 ≤ |x|
    · rw [max_eq_right h]
      nlinarith
    · rw [max_eq_left (le_of_not_ge h)]
      nlinarith
  have hsumPow : (1 + |x|) ^ k ≤ (2 * max 1 |x|) ^ k :=
    pow_le_pow_left₀ (by nlinarith [abs_nonneg x]) hsum k
  have hmax : max 1 |x| ^ k ≤ 1 + x ^ (2 * k : ℕ) := by
    have hxeven : 0 ≤ x ^ (2 * k : ℕ) := (even_two_mul k).pow_nonneg x
    by_cases hx1 : |x| ≤ 1
    · rw [max_eq_left hx1]
      simpa only [one_pow] using (le_add_of_nonneg_right hxeven : 1 ≤ 1 + x ^ (2 * k : ℕ))
    · rw [max_eq_right (le_of_not_ge hx1)]
      have hxgt : 1 < |x| := lt_of_not_ge hx1
      have hpowle : |x| ^ k ≤ |x| ^ (2 * k) := by
        apply pow_le_pow_right₀ (by linarith : 1 ≤ |x|)
        omega
      have heven : |x| ^ (2 * k) = x ^ (2 * k : ℕ) := by
        rw [← abs_pow]
        exact abs_of_nonneg hxeven
      exact hpowle.trans (heven ▸ le_add_of_nonneg_left (by norm_num))
  calc
    (1 + |x|) ^ k ≤ (2 * max 1 |x|) ^ k := hsumPow
    _ = 2 ^ k * max 1 |x| ^ k := by rw [mul_pow]
    _ ≤ 2 ^ k * (1 + x ^ (2 * k : ℕ)) := by
      gcongr

/-- Gaussian decay makes every real power of `1 + |x|` integrable. -/
theorem integrable_one_add_abs_rpow_mul_exp_neg_sq {p a : ℝ}
    (ha : 0 < a) :
    Integrable (fun x : ℝ => (1 + |x|) ^ p * exp (-a * x ^ 2)) volume := by
  let k := ⌈p⌉₊
  have hpk : p ≤ (k : ℝ) := Nat.le_ceil p
  have hconst : Integrable (fun x : ℝ => exp (-a * x ^ 2)) volume :=
    integrable_exp_neg_mul_sq ha
  have hk_gt : -1 < ((2 * k : ℕ) : ℝ) := by
    have hnonneg : 0 ≤ ((2 * k : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have hpow : Integrable (fun x : ℝ => x ^ (2 * k : ℕ) * exp (-a * x ^ 2)) volume := by
    simpa only [Real.rpow_natCast] using
      (integrable_rpow_mul_exp_neg_mul_sq ha
        (s := ((2 * k : ℕ) : ℝ)) hk_gt)
  have hmajor : Integrable (fun x : ℝ =>
      2 ^ k * (exp (-a * x ^ 2) + x ^ (2 * k : ℕ) * exp (-a * x ^ 2))) volume :=
    (hconst.add hpow).const_mul (2 ^ k)
  have hbound : ∀ x : ℝ,
      (1 + |x|) ^ p * exp (-a * x ^ 2) ≤
        2 ^ k * (exp (-a * x ^ 2) + x ^ (2 * k : ℕ) * exp (-a * x ^ 2)) := by
    intro x
    have hx : 1 ≤ 1 + |x| := by nlinarith [abs_nonneg x]
    have hsmall : (1 + |x|) ^ p ≤ (1 + |x|) ^ (k : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hx hpk
    have hlarge := one_add_abs_pow_le_two_pow_mul x k
    have hexp : 0 ≤ exp (-a * x ^ 2) := (exp_pos _).le
    have hkcast : (1 + |x|) ^ (k : ℝ) = (1 + |x|) ^ k := by
      rw [Real.rpow_natCast]
    rw [hkcast] at hsmall
    calc
      _ ≤ (1 + |x|) ^ k * exp (-a * x ^ 2) := by gcongr
      _ ≤ 2 ^ k * (1 + x ^ (2 * k : ℕ)) * exp (-a * x ^ 2) := by
        gcongr
      _ = 2 ^ k * (exp (-a * x ^ 2) +
          x ^ (2 * k : ℕ) * exp (-a * x ^ 2)) := by ring
  have hbase : Continuous (fun x : ℝ => 1 + |x|) := by fun_prop
  have hcont : Continuous (fun x : ℝ => (1 + |x|) ^ p) :=
    hbase.rpow_const (fun x => Or.inl (by positivity))
  have hproduct : Continuous (fun x : ℝ => (1 + |x|) ^ p * exp (-a * x ^ 2)) :=
    hcont.mul (by fun_prop)
  apply Integrable.mono' hmajor hproduct.aestronglyMeasurable
  · filter_upwards with x
    simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤
      (1 + |x|) ^ p * exp (-a * x ^ 2))] using hbound x

end TauCeti
