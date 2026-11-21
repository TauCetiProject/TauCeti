/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Integral.IteratedTailIntegral.Basic

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Prod
import TauCeti.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Single-integral representations and explicit evaluations of iterated tail integrals

This file establishes Cauchy's single-integral representation for `TauCeti.iteratedTailIntegral`
via a triangular Fubini swap on `(y, ∞)`, together with closed-form evaluation for decaying
exponentials.

## Main results

* `TauCeti.integrableOn_integral_Ioi_sub_pow_smul` and
  `TauCeti.integral_Ioi_integral_Ioi_sub_pow_smul`: the Cauchy triangle Fubini swap on `(y, ∞)`.
* `TauCeti.iteratedTailIntegral_succ_eq_inv_factorial_smul_integral_Ioi`: Cauchy's repeated
  tail-integral formula
  `iteratedTailIntegral f (n + 1) x = (n !)⁻¹ • ∫ t in Ioi x, (t - x) ^ n • f t` when the
  weighted tail is Bochner integrable.
* `TauCeti.iteratedTailIntegral_exp_neg_mul`: closed form
  `iteratedTailIntegral (fun t ↦ exp (-(a * t))) n x = exp (-(a * x)) / a ^ n` for `0 < a`.
-/

public section

namespace TauCeti

open MeasureTheory Set
open scoped Interval

section CauchyTriangle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Triangular Cauchy kernel `(s, t) ↦ (t - s) ^ m • f t` supported on `y < s < t`. -/
private noncomputable def cauchyTriangleKernel (f : ℝ → E) (y : ℝ) (m : ℕ) : ℝ × ℝ → E :=
  {p : ℝ × ℝ | y < p.1 ∧ p.1 < p.2}.indicator
    fun p ↦ (p.2 - p.1) ^ m • (Ioi y).indicator f p.2

/-- Horizontal slice of `cauchyTriangleKernel` at fixed `t`. -/
private theorem cauchyTriangleKernel_snd (f : ℝ → E) (y : ℝ) (m : ℕ) (t : ℝ) :
    (fun s : ℝ ↦ cauchyTriangleKernel f y m (s, t)) =
      if y < t then (Ioo y t).indicator fun s ↦ (t - s) ^ m • f t else (0 : ℝ → E) := by
  ext s; split_ifs with ht <;> simp only [cauchyTriangleKernel, Pi.zero_apply, indicator,
    mem_ofPred_eq, mem_Ioo, mem_Ioi]
  · by_cases hs : y < s ∧ s < t <;> simp [hs, ht]
  · exact ite_eq_right_iff.mpr fun h ↦ absurd (h.1.trans h.2) ht

/-- Vertical slice of `cauchyTriangleKernel` at fixed `s`. -/
private theorem cauchyTriangleKernel_fst (f : ℝ → E) (y : ℝ) (m : ℕ) (s : ℝ) :
    (fun t : ℝ ↦ cauchyTriangleKernel f y m (s, t)) =
      if y < s then (Ioi s).indicator fun t ↦ (t - s) ^ m • f t else (0 : ℝ → E) := by
  ext t; split_ifs with hs <;> simp only [cauchyTriangleKernel, Pi.zero_apply, indicator,
    mem_ofPred_eq, mem_Ioi]
  · by_cases hst : s < t
    · simp [hs, hst, hs.trans hst]
    · simp [hst]
  · exact ite_eq_right_iff.mpr fun h ↦ absurd h.1 hs

/-- Vertical slice integral of `cauchyTriangleKernel` at fixed `s`. -/
private theorem integral_cauchyTriangleKernel_fst (f : ℝ → E) (y : ℝ) (m : ℕ) (s : ℝ) :
    (∫ t, cauchyTriangleKernel f y m (s, t)) =
      (Ioi y).indicator (fun r ↦ ∫ t in Ioi r, (t - r) ^ m • f t) s := by
  rw [cauchyTriangleKernel_fst]
  split_ifs with hs
  · rw [indicator_of_mem hs, MeasureTheory.integral_indicator measurableSet_Ioi]
  · simp [hs]

/-- Horizontal slice integral of `cauchyTriangleKernel` at fixed `t`. -/
private theorem integral_cauchyTriangleKernel_snd [CompleteSpace E]
    (f : ℝ → E) (y : ℝ) (m : ℕ) (t : ℝ) :
    (∫ s, cauchyTriangleKernel f y m (s, t)) =
      (Ioi y).indicator (fun r ↦ ((m + 1 : ℝ)⁻¹ * (r - y) ^ (m + 1)) • f r) t := by
  rw [cauchyTriangleKernel_snd]
  split_ifs with ht
  · have hsub : ∫ s in y..t, (t - s) ^ m = (t - y) ^ (m + 1) / (m + 1 : ℝ) := by
      simpa only [Real.rpow_natCast, ← Nat.cast_add_one] using
        integral_sub_rpow (r := (m : ℝ)) (by linarith [Nat.cast_nonneg (α := ℝ) m]) y t
    rw [indicator_of_mem ht, MeasureTheory.integral_indicator measurableSet_Ioo,
      ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le ht.le,
      intervalIntegral.integral_smul_const, hsub, div_eq_inv_mul]
  · simp [ht]

/-- Product integrability of `cauchyTriangleKernel` on `ℝ × ℝ` from integrability of
`t ↦ (t - y) ^ (m + 1) • f t` on `(y, ∞)`. -/
private theorem integrable_cauchyTriangleKernel {f : ℝ → E} {y : ℝ} {m : ℕ}
    (hfm1 : IntegrableOn (fun t : ℝ ↦ (t - y) ^ (m + 1) • f t) (Ioi y)) :
    Integrable (cauchyTriangleKernel f y m) (volume.prod volume) := by
  have hS : MeasurableSet {p : ℝ × ℝ | y < p.1 ∧ p.1 < p.2} :=
    (isOpen_lt continuous_const continuous_fst).measurableSet.inter
      (isOpen_lt continuous_fst continuous_snd).measurableSet
  have hf_meas : AEStronglyMeasurable f (volume.restrict (Ioi y)) :=
    (aestronglyMeasurable_fun_smul_iff₀
      (by fun_prop : Continuous fun t : ℝ ↦ (t - y) ^ (m + 1)).aestronglyMeasurable
      (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : y < t)
          exact pow_ne_zero _ (sub_pos.mpr ht).ne')).mp hfm1.aestronglyMeasurable
  have hmeas : AEStronglyMeasurable (cauchyTriangleKernel f y m) (volume.prod volume) :=
    (((by fun_prop : Continuous fun p : ℝ × ℝ ↦ (p.2 - p.1) ^ m).aestronglyMeasurable).smul
      (((aestronglyMeasurable_indicator_iff measurableSet_Ioi).mpr hf_meas).comp_snd)).indicator hS
  rw [integrable_prod_iff' hmeas]
  refine ⟨ae_of_all _ fun t ↦ ?_, ?_⟩
  · rw [cauchyTriangleKernel_snd]
    split_ifs
    · rw [integrable_indicator_iff measurableSet_Ioo]
      exact (((by fun_prop : Continuous fun s : ℝ ↦ (t - s) ^ m).integrableOn_Icc).mono_set
        Ioo_subset_Icc_self).smul_const (f t)
    · exact integrable_zero _ _ _
  · have hnorm_pt (s t : ℝ) :
        ‖cauchyTriangleKernel f y m (s, t)‖ = cauchyTriangleKernel (fun r ↦ ‖f r‖) y m (s, t) := by
      simp only [cauchyTriangleKernel, norm_indicator_eq_indicator_norm]
      by_cases h : y < s ∧ s < t
      · simp [h, norm_smul, abs_of_nonneg (sub_nonneg.mpr h.2.le),
          norm_indicator_eq_indicator_norm]
      · simp [h]
    simp_rw [hnorm_pt, integral_cauchyTriangleKernel_snd, smul_eq_mul]
    rw [integrable_indicator_iff measurableSet_Ioi]
    refine IntegrableOn.congr_fun (hfm1.norm.const_mul (m + 1 : ℝ)⁻¹) (fun t ht ↦ ?_)
      measurableSet_Ioi
    rw [norm_smul, Real.norm_of_nonneg (pow_nonneg (sub_nonneg.mpr (mem_Ioi.mp ht).le) _),
      mul_assoc]

/-- Integrability of the Cauchy tail transform `s ↦ ∫ t in Ioi s, (t - s) ^ m • f t` on `(y, ∞)`
whenever `t ↦ (t - y) ^ (m + 1) • f t` is integrable on `(y, ∞)`. -/
theorem integrableOn_integral_Ioi_sub_pow_smul {f : ℝ → E} {y : ℝ} {m : ℕ}
    (hf : IntegrableOn (fun t : ℝ ↦ (t - y) ^ (m + 1) • f t) (Ioi y)) :
    IntegrableOn (fun s : ℝ ↦ ∫ t in Ioi s, (t - s) ^ m • f t) (Ioi y) := by
  by_cases hE : CompleteSpace E
  swap
  · simp_rw [integral_of_not_completeSpace hE]
    exact integrableOn_zero
  exact (integrable_indicator_iff measurableSet_Ioi).mp
    ((integrable_cauchyTriangleKernel hf).integral_prod_left.congr
      (ae_of_all _ (integral_cauchyTriangleKernel_fst f y m)))

/-- **Cauchy Fubini swap on `(y, ∞)`.** Whenever `t ↦ (t - y) ^ (m + 1) • f t` is integrable on
`(y, ∞)`,
`∫ s in Ioi y, ∫ t in Ioi s, (t - s) ^ m • f t = (m + 1)⁻¹ • ∫ t in Ioi y, (t - y) ^ (m + 1) • f t`.
-/
theorem integral_Ioi_integral_Ioi_sub_pow_smul {f : ℝ → E} {y : ℝ} {m : ℕ}
    (hf : IntegrableOn (fun t : ℝ ↦ (t - y) ^ (m + 1) • f t) (Ioi y)) :
    ∫ s in Ioi y, (∫ t in Ioi s, (t - s) ^ m • f t) =
      ((m + 1 : ℝ)⁻¹) • ∫ t in Ioi y, (t - y) ^ (m + 1) • f t := by
  by_cases hE : CompleteSpace E
  swap
  · simp [integral_of_not_completeSpace hE]
  calc
    ∫ s in Ioi y, (∫ t in Ioi s, (t - s) ^ m • f t)
        = ∫ s, ∫ t, cauchyTriangleKernel f y m (s, t) := by
          rw [← MeasureTheory.integral_indicator measurableSet_Ioi]
          exact integral_congr_ae
            (ae_of_all _ fun s ↦ (integral_cauchyTriangleKernel_fst f y m s).symm)
    _ = ∫ t, ∫ s, cauchyTriangleKernel f y m (s, t) :=
          integral_integral_swap (integrable_cauchyTriangleKernel hf)
    _ = ((m + 1 : ℝ)⁻¹) • ∫ t in Ioi y, (t - y) ^ (m + 1) • f t := by
          rw [← MeasureTheory.integral_smul, ← MeasureTheory.integral_indicator measurableSet_Ioi]
          refine integral_congr_ae (ae_of_all _ fun t ↦ ?_)
          dsimp only; rw [integral_cauchyTriangleKernel_snd]
          by_cases ht : y < t <;> simp [ht, mul_smul]

end CauchyTriangle

/-- **Cauchy's repeated tail-integral formula.** If `t ↦ (t - x) ^ n • f t` is Bochner integrable
on `(x, ∞)`, then
`iteratedTailIntegral f (n + 1) x = (n !)⁻¹ • ∫ t in Ioi x, (t - x) ^ n • f t`. -/
theorem iteratedTailIntegral_succ_eq_inv_factorial_smul_integral_Ioi
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → E} {x : ℝ} {n : ℕ}
    (hf_top : IntegrableOn (fun t : ℝ ↦ (t - x) ^ n • f t) (Ioi x)) :
    iteratedTailIntegral f (n + 1) x =
      (n.factorial : ℝ)⁻¹ • ∫ t in Ioi x, (t - x) ^ n • f t := by
  by_cases hE : CompleteSpace E
  swap
  · rw [iteratedTailIntegral_succ_of_not_completeSpace hE, integral_of_not_completeSpace hE,
      smul_zero]
  induction n generalizing x with
  | zero =>
    simp only [pow_zero, one_smul, Nat.factorial_zero, Nat.cast_one, inv_one] at hf_top ⊢
    exact iteratedTailIntegral_one_eq_integral_Ioi hf_top
  | succ m ih =>
    have hsub (s : ℝ) (hs : x < s) :
        IntegrableOn (fun t : ℝ ↦ (t - s) ^ m • f t) (Ioi s) := by
      have hf_meas : AEStronglyMeasurable f (volume.restrict (Ioi x)) :=
        (aestronglyMeasurable_fun_smul_iff₀
          (by fun_prop : Continuous fun t : ℝ ↦ (t - x) ^ (m + 1)).aestronglyMeasurable
          (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : x < t)
              exact pow_ne_zero _ (sub_pos.mpr ht).ne')).mp hf_top.aestronglyMeasurable
      refine ((hf_top.mono_set (Ioi_subset_Ioi hs.le)).norm.const_mul ((s - x)⁻¹)).mono'
        (((by fun_prop : Continuous fun t : ℝ ↦ (t - s) ^ m).aestronglyMeasurable).smul
          (hf_meas.mono_set (Ioi_subset_Ioi hs.le))) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : s < t)
      have htx : 0 < t - x := sub_pos.mpr (hs.trans ht)
      have hts : 0 < t - s := sub_pos.mpr ht
      have hsx : 0 < s - x := sub_pos.mpr hs
      rw [norm_smul, norm_smul, Real.norm_of_nonneg (pow_nonneg hts.le _),
        Real.norm_of_nonneg (pow_nonneg htx.le _), ← mul_assoc]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      rw [inv_mul_eq_div, le_div_iff₀' hsx, pow_succ']
      exact mul_le_mul (by linarith) (pow_le_pow_left₀ hts.le (by linarith) m)
        (pow_nonneg hts.le _) htx.le
    have heq_on : EqOn (iteratedTailIntegral f (m + 1))
        (fun s ↦ (m.factorial : ℝ)⁻¹ • ∫ t in Ioi s, (t - s) ^ m • f t) (Ioi x) :=
      fun s hs ↦ ih (hsub s hs)
    have hint_swap := integrableOn_integral_Ioi_sub_pow_smul hf_top
    rw [iteratedTailIntegral_succ_eq_integral_Ioi
        (IntegrableOn.congr_fun (hint_swap.smul (m.factorial : ℝ)⁻¹) heq_on.symm
          measurableSet_Ioi),
      setIntegral_congr_fun measurableSet_Ioi heq_on, integral_smul,
      integral_Ioi_integral_Ioi_sub_pow_smul hf_top, smul_smul]
    congr 1
    simp [Nat.factorial_succ, mul_comm]

/-- Closed form of `iteratedTailIntegral` for a decaying exponential `t ↦ exp (-(a * t))` with
`0 < a`: `iteratedTailIntegral (fun t ↦ exp (-(a * t))) n x = exp (-(a * x)) / a ^ n`. -/
theorem iteratedTailIntegral_exp_neg_mul {a : ℝ} (ha : 0 < a) (n : ℕ) (x : ℝ) :
    iteratedTailIntegral (fun t : ℝ ↦ Real.exp (-(a * t))) n x = Real.exp (-(a * x)) / a ^ n := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    have hint : IntegrableOn (fun t : ℝ ↦ Real.exp (-(a * t)) / a ^ n) (Ioi x) :=
      IntegrableOn.congr_fun ((integrableOn_exp_mul_Ioi (neg_lt_zero.mpr ha) x).mul_const (a ^ n)⁻¹)
        (fun _ _ ↦ by rw [← neg_mul, div_eq_mul_inv]) measurableSet_Ioi
    rw [iteratedTailIntegral_succ_eq_integral_Ioi
        (hint.congr_fun (fun t _ ↦ (ih t).symm) measurableSet_Ioi),
      setIntegral_congr_fun measurableSet_Ioi (fun t _ ↦ ih t)]
    simp_rw [div_eq_mul_inv, ← neg_mul]
    rw [integral_mul_const, integral_exp_mul_Ioi (neg_lt_zero.mpr ha)]
    field_simp [ha.ne']; ring

end TauCeti
