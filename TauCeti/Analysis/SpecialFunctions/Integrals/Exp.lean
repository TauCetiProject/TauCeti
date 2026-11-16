/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Bounds for exponential interval integrals

A decaying exponential, and a nonnegative multiple of the sum of two endpoint exponentials,
have length-independent integral bounds. The majorant bound uses the totalized interval
integral, so it also applies without an integrability hypothesis on the smaller function.
-/

public section

open Set MeasureTheory intervalIntegral

namespace TauCeti

/-- The oriented integral of a decaying exponential is at most the reciprocal scale,
for any real endpoint, including negative endpoints. -/
theorem integral_exp_neg_mul_le {L scale : ℝ} (hscale : 0 < scale) :
    (∫ t : ℝ in 0..L, Real.exp (-scale * t)) ≤ 1 / scale := by
  rw [intervalIntegral.integral_comp_mul_left Real.exp (neg_ne_zero.mpr hscale.ne')]
  simp only [mul_zero, integral_exp, Real.exp_zero, smul_eq_mul]
  have hpos := (Real.exp_pos (-(scale * L))).le
  apply (mul_le_mul_iff_of_pos_left hscale).mp
  field_simp
  nlinarith

/-- An exponential-pair majorant gives a length-independent upper bound for an interval
integral. If the integrand is not interval integrable, its integral is zero. -/
theorem integral_le_exp_pair {f : ℝ → ℝ} {L scale K : ℝ}
    (hL : 0 ≤ L) (hscale : 0 < scale) (hK : 0 ≤ K)
    (hbound : ∀ t ∈ Icc 0 L, f t ≤
      K * (Real.exp (-scale * t) + Real.exp (-scale * (L - t)))) :
    (∫ t in (0 : ℝ)..L, f t) ≤ K * (2 / scale) := by
  by_cases hf : IntervalIntegrable f volume 0 L
  swap
  · rw [integral_undef hf]
    positivity
  have hA : Continuous (fun t : ℝ ↦ Real.exp (-scale * t)) := by fun_prop
  have hB : Continuous (fun t : ℝ ↦ Real.exp (-scale * (L - t))) := by fun_prop
  have hreflect : (∫ t : ℝ in 0..L, Real.exp (-scale * (L - t))) =
      ∫ t : ℝ in 0..L, Real.exp (-scale * t) := by
    rw [intervalIntegral.integral_comp_sub_left (fun t ↦ Real.exp (-scale * t)) L]
    simp only [sub_self, sub_zero]
  calc
    (∫ t in (0 : ℝ)..L, f t) ≤
        ∫ t in (0 : ℝ)..L,
          K * (Real.exp (-scale * t) + Real.exp (-scale * (L - t))) :=
      intervalIntegral.integral_mono_on hL hf
        (((hA.add hB).const_mul K).intervalIntegrable 0 L) hbound
    _ = K * (2 * ∫ t : ℝ in 0..L, Real.exp (-scale * t)) := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_add (hA.intervalIntegrable 0 L) (hB.intervalIntegrable 0 L),
        hreflect, ← two_mul]
    _ ≤ K * (2 / scale) :=
      mul_le_mul_of_nonneg_left
        (by simpa only [mul_one_div] using
          mul_le_mul_of_nonneg_left (integral_exp_neg_mul_le hscale) (by norm_num : (0 : ℝ) ≤ 2)) hK

end TauCeti
