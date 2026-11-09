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

/-- Gaussian decay makes every real power of `1 + |x|` integrable. -/
theorem integrable_one_add_abs_rpow_mul_exp_neg_mul_sq {p a : ℝ}
    (ha : 0 < a) :
    Integrable (fun x : ℝ => (1 + |x|) ^ p * exp (-a * x ^ 2)) volume := by
  let k := ⌈p⌉₊
  have hpk : p ≤ (k : ℝ) := Nat.le_ceil p
  have hconst : Integrable (fun x : ℝ => exp (-a * x ^ 2)) volume :=
    integrable_exp_neg_mul_sq ha
  have hpow : Integrable (fun x : ℝ => x ^ (k : ℝ) * exp (-a * x ^ 2)) volume :=
    integrable_rpow_mul_exp_neg_mul_sq ha (s := (k : ℝ))
      (by have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg _; linarith)
  have hpow_norm : Integrable (fun x : ℝ => |x| ^ k * exp (-a * x ^ 2)) volume := by
    convert hpow.norm using 1
    ext x
    rw [Real.norm_eq_abs, Real.rpow_natCast, abs_mul, abs_pow, abs_of_pos (exp_pos _)]
  have hmajor : Integrable (fun x : ℝ =>
      2 ^ (k - 1) * (exp (-a * x ^ 2) + |x| ^ k * exp (-a * x ^ 2))) volume :=
    (hconst.add hpow_norm).const_mul (2 ^ (k - 1))
  have hbound : ∀ x : ℝ,
      (1 + |x|) ^ p * exp (-a * x ^ 2) ≤
        2 ^ (k - 1) * (exp (-a * x ^ 2) + |x| ^ k * exp (-a * x ^ 2)) := by
    intro x
    have hx : 1 ≤ 1 + |x| := by nlinarith [abs_nonneg x]
    have hsmall : (1 + |x|) ^ p ≤ (1 + |x|) ^ (k : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hx hpk
    have hkcast : (1 + |x|) ^ (k : ℝ) = (1 + |x|) ^ k := by
      rw [Real.rpow_natCast]
    rw [hkcast] at hsmall
    have hpoly : (1 + |x|) ^ k ≤ 2 ^ (k - 1) * (1 + |x| ^ k) := by
      simpa using add_pow_le (zero_le_one : (0 : ℝ) ≤ 1) (abs_nonneg x) k
    calc
      _ ≤ (1 + |x|) ^ k * exp (-a * x ^ 2) := by gcongr
      _ ≤ 2 ^ (k - 1) * (1 + |x| ^ k) * exp (-a * x ^ 2) := by
        gcongr
      _ = 2 ^ (k - 1) * (exp (-a * x ^ 2) +
          |x| ^ k * exp (-a * x ^ 2)) := by ring
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
