/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Positive divided differences of the real exponential

The divided difference of the exponential is the integral of the exponential along the segment
between its arguments. In particular it is strictly positive, including when the arguments
coincide. It is jointly real analytic, including on the diagonal. These divided differences
are the scalar coefficients in the derivative of the matrix exponential at a Hermitian matrix.

Averaging the monotone exponential along the segment places the divided difference between the
values at the endpoints, `exp (min a b) ≤ dslope exp a b ≤ exp (max a b)`. For nearby arguments
it is close to the derivative at either endpoint:
`|dslope exp a b - exp a| ≤ exp a |b - a|` when `|b - a| ≤ 1`. Writing a difference
`exp b - exp a` as `(b - a) dslope exp a b` turns a nonlinear term `exp u` of a partial
differential equation into a potential multiplying a difference of solutions.

## Main statements

* `Real.dslope_exp_eq_integral`: the divided difference is the average along the segment.
* `Real.dslope_exp_pos`: it is strictly positive.
* `Real.exp_min_le_dslope_exp`, `Real.dslope_exp_le_exp_max`: it lies between the values at the
  endpoints.
* `Real.abs_dslope_exp_sub_exp_le`: it differs from `exp a` by at most `exp a |b - a|`.
* `Real.abs_exp_sub_exp_sub_exp_add_exp_sub_dslope_mul_le`: a second difference of `exp` is a
  divided difference times the second difference of the arguments, up to a quadratic error.
* `Real.dslope_exp_eq_exp_mul_dslope_zero`: translation to zero extracts the factor `exp a`.
* `Real.contDiff_dslope_exp`: it is jointly smooth and real analytic.
-/

public section

open scoped ContDiff

namespace Real

/-- The divided difference of the exponential is its average along a segment. -/
theorem dslope_exp_eq_integral (a b : ℝ) :
    dslope exp a b = ∫ t in (0 : ℝ)..1, exp ((1 - t) * a + t * b) := by
  have heq (t : ℝ) : (1 - t) * a + t * b = a + t * (b - a) := by ring
  simp_rw [heq]
  have h := intervalIntegral.integral_unitInterval_deriv_eq_sub
    (by fun_prop : ContinuousOn (fun t : ℝ ↦ exp (a + t * (b - a))) (Set.Icc 0 1))
    (fun t _ ↦ hasDerivAt_exp (a + t * (b - a)))
  simp only [smul_eq_mul, add_sub_cancel] at h
  by_cases hab : b = a
  · simp [hab]
  · rw [dslope_of_ne exp hab, slope_def_field, div_eq_iff (sub_ne_zero.mpr hab)]
    simpa only [mul_comm] using h.symm

/-- All divided differences of the real exponential are strictly positive. -/
theorem dslope_exp_pos (a b : ℝ) : 0 < dslope exp a b := by
  rw [dslope_exp_eq_integral]
  exact intervalIntegral.integral_pos (by norm_num) (by fun_prop)
    (fun t _ ↦ (exp_pos _).le) ⟨0, by simp, exp_pos _⟩

/-- The divided difference of the exponential is at least its value at the smaller argument. -/
theorem exp_min_le_dslope_exp (a b : ℝ) : exp (min a b) ≤ dslope exp a b := by
  rw [dslope_exp_eq_integral]
  have h := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) zero_le_one
    intervalIntegrable_const
    ((by fun_prop : Continuous fun t : ℝ ↦ exp ((1 - t) * a + t * b)).intervalIntegrable 0 1)
    (f := fun _ ↦ exp (min a b)) (g := fun t ↦ exp ((1 - t) * a + t * b)) fun t ht ↦ by
      have h₁ : 0 ≤ 1 - t := by linarith [ht.2]
      exact exp_le_exp.mpr (by nlinarith [min_le_left a b, min_le_right a b, ht.1])
  simpa using h

/-- The divided difference of the exponential is at most its value at the larger argument. -/
theorem dslope_exp_le_exp_max (a b : ℝ) : dslope exp a b ≤ exp (max a b) := by
  rw [dslope_exp_eq_integral]
  have h := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) zero_le_one
    ((by fun_prop : Continuous fun t : ℝ ↦ exp ((1 - t) * a + t * b)).intervalIntegrable 0 1)
    intervalIntegrable_const (f := fun t ↦ exp ((1 - t) * a + t * b))
    (g := fun _ ↦ exp (max a b)) fun t ht ↦ by
      have h₁ : 0 ≤ 1 - t := by linarith [ht.2]
      exact exp_le_exp.mpr (by nlinarith [le_max_left a b, le_max_right a b, ht.1])
  simpa using h

/-- For nearby arguments, the divided difference of the exponential is close to the derivative
`exp a` at an endpoint: `|dslope exp a b - exp a| ≤ exp a |b - a|` when `|b - a| ≤ 1`. -/
theorem abs_dslope_exp_sub_exp_le {a b : ℝ} (hab : |b - a| ≤ 1) :
    |dslope exp a b - exp a| ≤ exp a * |b - a| := by
  rcases eq_or_ne b a with rfl | hne
  · simp
  have hba : 0 < |b - a| := abs_pos.mpr (sub_ne_zero.mpr hne)
  -- `(b - a) (dslope exp a b - exp a) = exp a (exp (b - a) - 1 - (b - a))`.
  have hid : (b - a) * (dslope exp a b - exp a) = exp a * (exp (b - a) - 1 - (b - a)) := by
    have h := sub_smul_dslope exp a b
    rw [smul_eq_mul] at h
    rw [mul_sub, h, mul_sub, mul_sub, ← exp_add, add_sub_cancel, mul_one]
    ring
  have hT := abs_exp_sub_one_sub_id_le hab
  have h := congrArg abs hid
  rw [abs_mul, abs_mul, abs_of_pos (exp_pos a)] at h
  refine le_of_mul_le_mul_left ?_ hba
  calc |b - a| * |dslope exp a b - exp a| = exp a * |exp (b - a) - 1 - (b - a)| := h
    _ ≤ exp a * (b - a) ^ 2 := mul_le_mul_of_nonneg_left hT (exp_pos a).le
    _ = |b - a| * (exp a * |b - a|) := by rw [← sq_abs]; ring

/-- The second difference `exp d - exp b - exp c + exp a` is the divided difference
`dslope exp b d` times `d - b - c + a`, up to an error quadratic in the first differences, when
`a, b ≤ 0` and the differences `d - b`, `c - a` are at most `1`. -/
theorem abs_exp_sub_exp_sub_exp_add_exp_sub_dslope_mul_le {a b c d : ℝ} (ha : a ≤ 0)
    (hb : b ≤ 0) (hdb : |d - b| ≤ 1) (hca : |c - a| ≤ 1) :
    |exp d - exp b - exp c + exp a - dslope exp b d * (d - b - c + a)| ≤
      |c - a| * (|d - b| + |b - a| + |c - a|) := by
  set V := dslope exp b d
  set W := dslope exp a c
  have hV : (d - b) * V = exp d - exp b := by
    simpa only [smul_eq_mul] using sub_smul_dslope exp b d
  have hW : (c - a) * W = exp c - exp a := by
    simpa only [smul_eq_mul] using sub_smul_dslope exp a c
  have hU : (b - a) * dslope exp a b = exp b - exp a := by
    simpa only [smul_eq_mul] using sub_smul_dslope exp a b
  have hid : exp d - exp b - exp c + exp a - V * (d - b - c + a) =
      (c - a) * (V - W) := by linear_combination hW - hV
  -- `V` and `W` are close to `exp b` and `exp a`, which are close to each other.
  have hVb : |V - exp b| ≤ |d - b| :=
    (abs_dslope_exp_sub_exp_le hdb).trans
      (mul_le_of_le_one_left (abs_nonneg _) (exp_le_one_iff.mpr hb))
  have hWa : |W - exp a| ≤ |c - a| :=
    (abs_dslope_exp_sub_exp_le hca).trans
      (mul_le_of_le_one_left (abs_nonneg _) (exp_le_one_iff.mpr ha))
  have hba : |exp b - exp a| ≤ |b - a| := by
    rw [← hU, abs_mul, abs_of_pos (dslope_exp_pos a b)]
    exact mul_le_of_le_one_right (abs_nonneg _)
      ((dslope_exp_le_exp_max a b).trans (exp_le_one_iff.mpr (max_le ha hb)))
  have hVW : |V - W| ≤ |d - b| + |b - a| + |c - a| := by
    calc |V - W| = |(V - exp b) + (exp b - exp a) - (W - exp a)| := by
          ring_nf
      _ ≤ |V - exp b| + |exp b - exp a| + |W - exp a| :=
          (abs_sub _ _).trans (by gcongr; exact abs_add_le _ _)
      _ ≤ _ := by gcongr
  rw [hid, abs_mul]
  exact mul_le_mul_of_nonneg_left hVW (abs_nonneg _)

/-- Translating the real exponential divided difference to zero extracts the factor `exp a`. -/
theorem dslope_exp_eq_exp_mul_dslope_zero (a b : ℝ) :
    dslope exp a b = exp a * dslope exp 0 (b - a) := by
  rw [dslope_exp_eq_integral a b, dslope_exp_eq_integral 0 (b - a),
    ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  rw [← exp_add]
  congr 1
  ring

/-- The real exponential divided difference is jointly smooth, including its removable
value at equal arguments. The regularity parameter also permits real analyticity. -/
theorem contDiff_dslope_exp (m : ℕ∞ω) :
    ContDiff ℝ m (fun p : ℝ × ℝ ↦ dslope exp p.1 p.2) := by
  have hz : ContDiff ℝ m (dslope exp 0) :=
    ((analyticOnNhd_rexp (u := Set.univ)).dslope 0).contDiff
  have h : ContDiff ℝ m (fun p : ℝ × ℝ ↦ exp p.1 * dslope exp 0 (p.2 - p.1)) :=
    (contDiff_fst.exp).mul (hz.comp (contDiff_snd.sub contDiff_fst))
  convert h using 1
  funext p
  exact dslope_exp_eq_exp_mul_dslope_zero p.1 p.2

end Real
