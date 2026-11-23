/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import TauCeti.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Euler-kernel substitution and interval integrability

Interval integrability and the rational substitution `w = (1 - x) s / (x + (1 - x) s)` on `[0, 1]`
for real Euler-type kernels `(1 - s)^(b - 1) s^(a - 1) (x + (1 - x) s)^c`, shared between the
Euler integral representation of real digamma and the zero-balanced hypergeometric connection
formula.

## Main declarations

* `TauCeti.one_sub_rpow_mul_integral_rpow_mul_add_mul_rpow`: the substitution
  `w = (1 - x) s / (x + (1 - x) s)` relating `(1 - x)^a ∫₀¹ s^(a-1) (x + (1-x) s)^(-a)` to
  `∫₀^(1-x) w^(a-1) / (1 - w)` for `x ∈ (0, 1)`.
* `TauCeti.intervalIntegrable_rpow_mul_add_mul_rpow`,
  `TauCeti.intervalIntegrable_one_sub_rpow_mul_rpow_mul_add_mul_rpow`, and
  `TauCeti.intervalIntegrable_one_sub_rpow_sub_one_mul_rpow_mul_add_mul_rpow`: interval
  integrability on `[0, 1]` of the singular and regularized Euler kernels.
-/

public section

namespace TauCeti

/-- For every `a : ℝ` and `x ∈ (0, 1)`, substituting `w = (1 - x) s / (x + (1 - x) s)` on `[0, 1]`
gives
`(1 - x) ^ a * ∫ s in (0 : ℝ)..1, s ^ (a - 1) * (x + (1 - x) * s) ^ (-a) =`
`∫ w in (0 : ℝ)..(1 - x), w ^ (a - 1) / (1 - w)`.
-/
theorem one_sub_rpow_mul_integral_rpow_mul_add_mul_rpow {a x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    (1 - x) ^ a * (∫ s in (0 : ℝ)..1, s ^ (a - 1) * (x + (1 - x) * s) ^ (-a)) =
      ∫ w in (0 : ℝ)..(1 - x), w ^ (a - 1) / (1 - w) := by
  let u : ℝ → ℝ := fun s ↦ (1 - x) * s / (x + (1 - x) * s)
  let u' : ℝ → ℝ := fun s ↦ x * (1 - x) / (x + (1 - x) * s) ^ 2
  have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (f := u) (f' := u') (a := (0 : ℝ)) (b := 1)
    (ContinuousOn.div (by fun_prop) (by fun_prop) fun s hs ↦
      (by rw [Set.uIcc_of_le zero_le_one] at hs; nlinarith [hx.1, hx.2, hs.1, hs.2] :
        0 < x + (1 - x) * s).ne')
    (fun s hs ↦ by
      rw [min_eq_left zero_le_one, max_eq_right zero_le_one] at hs
      exact (((hasDerivAt_id s).const_mul (1 - x)).div
        (((hasDerivAt_id s).const_mul (1 - x)).const_add x)
        (by nlinarith [hx.1, hx.2, hs.1, hs.2] : 0 < x + (1 - x) * s).ne').congr_deriv
        (by dsimp [u']; ring))
    (fun _ _ ↦ div_nonneg (mul_nonneg hx.1.le (sub_nonneg.mpr hx.2.le)) (sq_nonneg _))
    (g := fun w : ℝ ↦ w ^ (a - 1) / (1 - w))
  rw [(by simp [u] : u 0 = 0),
    (by dsimp [u]; rw [mul_one, add_sub_cancel, div_one] : u 1 = 1 - x)] at hsub
  rw [← hsub, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun s hs ↦ ?_)
  rw [Set.uIoc_of_le zero_le_one] at hs
  have h1x := sub_pos.mpr hx.2
  have hD : 0 < x + (1 - x) * s := by nlinarith [hx.1, h1x, hs.1]
  have h1u : 1 - (1 - x) * s / (x + (1 - x) * s) = x / (x + (1 - x) * s) := by
    field_simp [hD.ne']; ring
  have h1xa : (1 - x) ^ a = (1 - x) ^ (a - 1) * (1 - x) := by
    simpa only [sub_add_cancel] using Real.rpow_add_one h1x.ne' (a - 1)
  have hDa : (x + (1 - x) * s) ^ a = (x + (1 - x) * s) ^ (a - 1) * (x + (1 - x) * s) := by
    simpa only [sub_add_cancel] using Real.rpow_add_one hD.ne' (a - 1)
  dsimp [u, u']
  rw [Real.div_rpow (mul_nonneg h1x.le hs.1.le) hD.le, Real.mul_rpow h1x.le hs.1.le, h1u,
    h1xa, Real.rpow_neg hD.le, hDa]
  field_simp [hx.1.ne', hD.ne', (Real.rpow_pos_of_pos hD (a - 1)).ne']

/-- Interval integrability on `[0, 1]` of the half-singular Euler kernel
`s ^ (a - 1) * (x + (1 - x) * s) ^ c` for `0 < a` and `0 < x`. -/
theorem intervalIntegrable_rpow_mul_add_mul_rpow {a x : ℝ} (ha : 0 < a) (hx₀ : 0 < x) (c : ℝ) :
    IntervalIntegrable (fun s : ℝ ↦ s ^ (a - 1) * (x + (1 - x) * s) ^ c)
      MeasureTheory.volume 0 1 := by
  have hcont : ContinuousOn (fun s : ℝ ↦ (x + (1 - x) * s) ^ c) (Set.uIcc 0 1) :=
    ContinuousOn.rpow_const (by fun_prop) fun s hs ↦ Or.inl <| by
      rw [Set.uIcc_of_le zero_le_one] at hs
      rcases eq_or_lt_of_le hs.1 with h0 | hs0
      · simp [← h0, hx₀.ne']
      · linarith [mul_nonneg hx₀.le (sub_nonneg.mpr hs.2)]
  exact (intervalIntegral.intervalIntegrable_rpow' (by linarith)).mul_continuousOn hcont

/-- Interval integrability on `[0, 1]` of the beta-weighted Euler kernel
`(1 - s) ^ (b - 1) * s ^ (a - 1) * (x + (1 - x) * s) ^ c` for `0 < a`, `0 < b`, and
`0 < x`. -/
theorem intervalIntegrable_one_sub_rpow_mul_rpow_mul_add_mul_rpow {a b x : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hx₀ : 0 < x) (c : ℝ) :
    IntervalIntegrable (fun s : ℝ ↦ (1 - s) ^ (b - 1) * s ^ (a - 1) * (x + (1 - x) * s) ^ c)
      MeasureTheory.volume 0 1 := by
  have hpos {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) : x + (1 - x) * s ≠ 0 := by
    rcases eq_or_lt_of_le hs.1 with h0 | hs0
    · simp [← h0, hx₀.ne']
    · linarith [mul_nonneg hx₀.le (sub_nonneg.mpr hs.2)]
  have h1 : IntervalIntegrable
      (fun s : ℝ ↦ (1 - s) ^ (b - 1) * s ^ (a - 1) * (x + (1 - x) * s) ^ c)
      MeasureTheory.volume 0 (1 / 2) := by
    have hcont : ContinuousOn
        (fun s : ℝ ↦ (1 - s) ^ (b - 1) * (x + (1 - x) * s) ^ c) (Set.uIcc 0 (1 / 2)) := by
      rw [Set.uIcc_of_le (by norm_num)]
      exact ((continuousOn_const.sub continuousOn_id).rpow_const fun s hs ↦
          Or.inl (by linarith [hs.2] : 1 - s ≠ 0)).mul
        (((continuousOn_const.add (continuousOn_const.mul continuousOn_id))).rpow_const fun s hs ↦
          Or.inl (hpos ⟨hs.1, le_trans hs.2 (by norm_num)⟩))
    exact ((intervalIntegral.intervalIntegrable_rpow' (r := a - 1)
      (by linarith)).mul_continuousOn hcont).congr fun _ _ ↦ by ring
  have h2 : IntervalIntegrable
      (fun s : ℝ ↦ (1 - s) ^ (b - 1) * s ^ (a - 1) * (x + (1 - x) * s) ^ c)
      MeasureTheory.volume (1 / 2) 1 := by
    have hcont : ContinuousOn
        (fun s : ℝ ↦ s ^ (a - 1) * (x + (1 - x) * s) ^ c) (Set.uIcc (1 / 2) 1) := by
      rw [Set.uIcc_of_le (by norm_num)]
      exact (continuousOn_id.rpow_const fun s hs ↦
          Or.inl (by linarith [hs.1] : s ≠ 0)).mul
        (((continuousOn_const.add (continuousOn_const.mul continuousOn_id))).rpow_const fun s hs ↦
          Or.inl (hpos ⟨le_trans (by norm_num) hs.1, hs.2⟩))
    exact ((intervalIntegrable_sub_rpow (by linarith : -1 < b - 1) (1 / 2) 1).mul_continuousOn
      hcont).congr fun _ _ ↦ by ring
  exact h1.trans h2

/-- Interval integrability on `[0, 1]` of the regularized Euler kernel
`((1 - s) ^ (b - 1) - 1) * s ^ (a - 1) * (x + (1 - x) * s) ^ c` for `0 < a`, `0 < b`, and
`0 < x`. -/
theorem intervalIntegrable_one_sub_rpow_sub_one_mul_rpow_mul_add_mul_rpow {a b x : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hx₀ : 0 < x) (c : ℝ) :
    IntervalIntegrable
      (fun s : ℝ ↦ ((1 - s) ^ (b - 1) - 1) * s ^ (a - 1) * (x + (1 - x) * s) ^ c)
      MeasureTheory.volume 0 1 :=
  ((intervalIntegrable_one_sub_rpow_mul_rpow_mul_add_mul_rpow ha hb hx₀ c).sub
    (intervalIntegrable_rpow_mul_add_mul_rpow ha hx₀ c)).congr fun _ _ ↦ by ring

end TauCeti
