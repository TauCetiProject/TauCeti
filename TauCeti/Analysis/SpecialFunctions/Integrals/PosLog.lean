/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.Analysis.SpecialFunctions.Integrability.PosLog
import Mathlib.MeasureTheory.Integral.IntervalAverage
import TauCeti.Analysis.SpecialFunctions.Log.Bounds
import TauCeti.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Integral

/-!
# Dyadic integral bounds for the positive logarithm

`TauCeti.intervalIntegrable_posLog_one_div_abs_one_sub_div` proves integrability of
`Real.posLog (1 / |1 - r / a|)` on every finite interval, for arbitrary real scales `a`.
`TauCeti.integral_posLog_one_div_abs_one_sub_div_le` bounds its integral on `[R, 2 * R]`
by `(log 2 + 12 * sqrt 6) * R` for `R ≥ 0`.

For nonnegative weights and `R > 0`,
`Finset.exists_mem_Ioc_notMem_sum_mul_posLog_one_div_abs_one_sub_div_le` selects a point
in `(R, 2 * R]` outside any prescribed Lebesgue-null set, with the weighted sum bounded
by the same universal constant times the sum of the weights.

All expressions use totalized division and logarithms: the summand is zero at `r = a`,
and zero or negative scales contribute zero on positive intervals. To exclude the singular
points themselves, include the image of the scales in the excluded null set.

The averaging argument is adapted from Matteo Cipollina's `CartanBound.lean` in PNT+,
for the good-circle minimum-modulus argument in finite-order Hadamard factorization.
-/

public section

open Real MeasureTheory intervalIntegral
open scoped Topology ENNReal BigOperators

namespace TauCeti

noncomputable section

private def kernel (t : ℝ) : ℝ := Real.posLog (1 / |1 - t|)

private abbrev majorantIntegral : ℝ :=
  ∫ t : ℝ in (1 / 4 : ℝ)..(4 : ℝ), Real.sqrt (2 / |1 - t|)

private abbrev averageBound : ℝ := Real.log 2 + 12 * Real.sqrt 6

/-- The positive logarithm of the reciprocal distance from a scaled real point is interval
integrable on arbitrary finite intervals, including intervals crossing the singularity. -/
theorem intervalIntegrable_posLog_one_div_abs_one_sub_div (a A B : ℝ) :
    IntervalIntegrable (fun r ↦ Real.posLog (1 / |1 - r / a|)) volume A B := by
  have hm : MeromorphicOn (fun r : ℝ ↦ 1 / (1 - r / a)) (Set.uIcc A B) := by
    intro t _
    fun_prop
  simpa only [Real.norm_eq_abs, abs_div, abs_one, one_div, abs_inv] using
    hm.intervalIntegrable_posLog_norm

private lemma kernel_intervalIntegrable (A B : ℝ) : IntervalIntegrable kernel volume A B := by
  change IntervalIntegrable (fun r ↦ Real.posLog (1 / |1 - r|)) volume A B
  simpa only [div_one] using intervalIntegrable_posLog_one_div_abs_one_sub_div 1 A B

private lemma kernel_le_sqrt_aux {t : ℝ} : kernel t ≤ Real.sqrt (2 / |1 - t|) := by
  rw [kernel]
  simpa only [abs_div, abs_one, abs_abs, mul_one_div] using
    Real.posLog_le_sqrt_two_mul (1 / |1 - t|)

private lemma intervalIntegrable_majorant (A B : ℝ) :
    IntervalIntegrable (fun t : ℝ ↦ Real.sqrt (2 / |1 - t|)) volume A B := by
  let f : ℝ → ℝ := fun u ↦ Real.sqrt (2 / |u|)
  have hnorm (u : ℝ) : ‖f u‖ = Real.sqrt 2 * ‖u‖ ^ (-(1 / 2 : ℝ)) := by
    change ‖Real.sqrt (2 / |u|)‖ = _
    rw [Real.norm_of_nonneg (Real.sqrt_nonneg _),
      Real.sqrt_div (by norm_num)]
    simp only [Real.sqrt_eq_rpow, div_eq_mul_inv, Real.rpow_neg (abs_nonneg u),
      Real.norm_eq_abs]
  have hlocal : LocallyIntegrable f volume :=
    locallyIntegrable_of_norm_le_rpow (by simp : 1 ≤ Module.finrank ℝ ℝ)
      (α := (1 / 2 : ℝ)) (by norm_num)
      (Filter.Eventually.of_forall fun u ↦ (hnorm u).le)
      (by
        apply Measurable.aestronglyMeasurable
        dsimp [f]
        fun_prop)
  simpa only [f, sub_sub_cancel] using
    ((hlocal.integrableOn_isCompact
      (isCompact_uIcc (a := 1 - A) (b := 1 - B))).intervalIntegrable).comp_sub_left 1

/-- The exact integral of the square-root majorant for the positive logarithmic singularity
on `[1 / 4, 4]`, including its totalized value at `t = 1`. -/
theorem integral_sqrt_two_div_abs_one_sub :
    (∫ t : ℝ in (1 / 4 : ℝ)..(4 : ℝ), Real.sqrt (2 / |1 - t|)) =
      3 * Real.sqrt 6 := by
  have hpoint (u : ℝ) : Real.sqrt (2 / |u|) =
      Real.sqrt 2 * |u| ^ (-(1 / 2 : ℝ)) := by
    rw [Real.sqrt_div (by norm_num)]
    simp only [Real.sqrt_eq_rpow, div_eq_mul_inv, Real.rpow_neg (abs_nonneg u)]
  have hl := intervalIntegrable_majorant (1 / 4) 1
  have hr := intervalIntegrable_majorant 1 4
  have hleft : (∫ t : ℝ in (1 / 4 : ℝ)..1, Real.sqrt (2 / |1 - t|)) =
      Real.sqrt 2 * ((1 - (1 / 4 : ℝ)) ^ (1 / 2 : ℝ) / (1 / 2 : ℝ)) := by
    calc
      _ = ∫ t : ℝ in (1 / 4 : ℝ)..1,
          Real.sqrt 2 * (1 - t) ^ (-(1 / 2 : ℝ)) := by
        apply intervalIntegral.integral_congr
        intro t ht
        dsimp only
        rw [hpoint, abs_of_nonneg (by
          rw [Set.uIcc_of_le (by norm_num)] at ht
          linarith [ht.2])]
      _ = _ := by
        rw [intervalIntegral.integral_const_mul, TauCeti.integral_sub_rpow (by norm_num)]
        norm_num
  have hright : (∫ t : ℝ in (1 : ℝ)..4, Real.sqrt (2 / |1 - t|)) =
      Real.sqrt 2 * ((4 - (1 : ℝ)) ^ (1 / 2 : ℝ) / (1 / 2 : ℝ)) := by
    calc
      _ = ∫ t : ℝ in (1 : ℝ)..4,
          Real.sqrt 2 * (t - 1) ^ (-(1 / 2 : ℝ)) := by
        apply intervalIntegral.integral_congr
        intro t ht
        dsimp only
        rw [hpoint, abs_of_nonpos (by
          rw [Set.uIcc_of_le (by norm_num)] at ht
          linarith [ht.1]), neg_sub]
      _ = _ := by
        rw [intervalIntegral.integral_const_mul, TauCeti.integral_sub_const_rpow (by norm_num)]
        norm_num
  have hsqrt : Real.sqrt 2 * Real.sqrt 3 = Real.sqrt 6 := by
    rw [← Real.sqrt_mul (by norm_num)]
    norm_num
  rw [← intervalIntegral.integral_add_adjacent_intervals hl hr, hleft, hright]
  have hs4 : Real.sqrt (4 : ℝ) = 2 := by
    convert Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2) using 1; norm_num
  norm_num only [show (1 - (1 / 4 : ℝ)) = 3 / 4 by norm_num,
    show (4 - (1 : ℝ)) = 3 by norm_num]
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, Real.sqrt_div (by norm_num), hs4]
  calc
    _ = 3 * (Real.sqrt 2 * Real.sqrt 3) := by ring
    _ = _ := by rw [hsqrt]

private lemma majorantIntegral_nonneg : 0 ≤ majorantIntegral :=
  intervalIntegral.integral_nonneg (by norm_num) fun _ _ ↦ Real.sqrt_nonneg _

private lemma log_two_le_averageBound : Real.log 2 ≤ averageBound := by
  dsimp only [averageBound]
  linarith [Real.sqrt_nonneg (6 : ℝ)]

private lemma averageBound_nonneg : 0 ≤ averageBound :=
  (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)).trans log_two_le_averageBound

private lemma kernel_le_log_two_of_le_half {t : ℝ} (ht : t ≤ (1 / 2 : ℝ)) :
    kernel t ≤ Real.log 2 := by
  have hden : (1 / 2 : ℝ) ≤ |1 - t| := by
    rw [abs_of_nonneg (by linarith : 0 ≤ 1 - t)]
    linarith
  have hfrac : (1 / |1 - t| : ℝ) ≤ 2 := by
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 2) hden
  simp only [kernel]
  exact (Real.posLog_le_posLog (neg_one_lt_zero.le.trans (by positivity)) hfrac).trans_eq
    (Real.posLog_eq_log (by norm_num : (1 : ℝ) ≤ |2|))

private lemma kernel_eq_zero_of_one_le_abs {t : ℝ} (h : 1 ≤ |1 - t|) :
    kernel t = 0 := by
  rw [kernel]
  apply (Real.posLog_eq_zero_iff _).mpr
  rw [abs_of_nonneg (by positivity : 0 ≤ (1 / |1 - t| : ℝ))]
  exact (div_le_one (lt_of_lt_of_le zero_lt_one h)).mpr h

private lemma kernel_eq_zero_of_two_le {t : ℝ} (ht : (2 : ℝ) ≤ t) : kernel t = 0 := by
  apply kernel_eq_zero_of_one_le_abs
  rw [abs_of_nonpos (by linarith : 1 - t ≤ 0)]
  linarith

private lemma kernel_eq_zero_of_nonpos {t : ℝ} (ht : t ≤ 0) : kernel t = 0 := by
  apply kernel_eq_zero_of_one_le_abs
  rw [abs_of_nonneg (by linarith : 0 ≤ 1 - t)]
  linarith

-- The logarithmic singularity has a uniform mean on all nonnegative dyadic intervals.
private lemma integral_kernel_dyadic_le {A : ℝ} (hA : 0 ≤ A) :
    (∫ t in A..(2 * A), kernel t) ≤ averageBound * A := by
  have hA2A : A ≤ 2 * A := by linarith
  by_cases hsmall : A ≤ 1 / 4
  · calc
      (∫ t in A..(2 * A), kernel t) ≤ ∫ _ in A..(2 * A), Real.log 2 := by
        apply intervalIntegral.integral_mono_on hA2A (kernel_intervalIntegrable _ _)
          intervalIntegrable_const
        intro t ht
        exact kernel_le_log_two_of_le_half (by linarith [ht.2])
      _ = Real.log 2 * A := by simp [intervalIntegral.integral_const, two_mul]; ring
      _ ≤ averageBound * A := mul_le_mul_of_nonneg_right log_two_le_averageBound hA
  by_cases hlarge : 2 ≤ A
  · have hz : (∫ t in A..(2 * A), kernel t) = 0 := by
      have heq : Set.EqOn kernel (fun _ ↦ (0 : ℝ)) (Set.uIcc A (2 * A)) := by
        intro t ht
        have ht' : t ∈ Set.Icc A (2 * A) := by
          simpa only [Set.uIcc_of_le hA2A] using ht
        exact kernel_eq_zero_of_two_le (hlarge.trans ht'.1)
      simpa using intervalIntegral.integral_congr heq
    rw [hz]
    exact mul_nonneg averageBound_nonneg hA
  have hlo : (1 / 4 : ℝ) ≤ A := (lt_of_not_ge hsmall).le
  have hhi : A ≤ (2 : ℝ) := (lt_of_not_ge hlarge).le
  calc
    (∫ t in A..(2 * A), kernel t) ≤
        ∫ t in A..(2 * A), Real.sqrt (2 / |1 - t|) := by
      exact intervalIntegral.integral_mono_on hA2A (kernel_intervalIntegrable _ _)
        (intervalIntegrable_majorant _ _)
        (fun _ _ ↦ kernel_le_sqrt_aux)
    _ ≤ majorantIntegral :=
      intervalIntegral.integral_mono_interval hlo hA2A (by linarith only [hhi])
        (Filter.Eventually.of_forall fun _ ↦ Real.sqrt_nonneg _) (intervalIntegrable_majorant _ _)
    _ ≤ (4 * majorantIntegral) * A := by
      nlinarith [mul_nonneg majorantIntegral_nonneg (by linarith : 0 ≤ 4 * A - 1)]
    _ ≤ averageBound * A := by
      apply mul_le_mul_of_nonneg_right _ hA
      dsimp only [averageBound]
      rw [majorantIntegral, integral_sqrt_two_div_abs_one_sub]
      linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]


/-- A scale-uniform dyadic integral bound for the totalized positive logarithm. -/
theorem integral_posLog_one_div_abs_one_sub_div_le (a : ℝ) {R : ℝ} (hR : 0 ≤ R) :
    (∫ r in R..(2 * R), Real.posLog (1 / |1 - r / a|)) ≤
      (Real.log 2 + 12 * Real.sqrt 6) * R := by
  change (∫ r in R..(2 * R), kernel (r / a)) ≤ averageBound * R
  by_cases ha : 0 < a
  · have hscale : (∫ r in R..(2 * R), kernel (r / a)) =
        a * ∫ t in (R / a)..(2 * (R / a)), kernel t := by
      rw [intervalIntegral.integral_comp_div kernel ha.ne', smul_eq_mul, mul_div_assoc]
    rw [hscale]
    have h := mul_le_mul_of_nonneg_left
      (integral_kernel_dyadic_le (div_nonneg hR ha.le)) ha.le
    have heq : a * (averageBound * (R / a)) = averageBound * R := by
      field_simp
    simpa only [heq] using h
  · have ha' : a ≤ 0 := le_of_not_gt ha
    have hz : Set.EqOn (fun r ↦ kernel (r / a)) (fun _ ↦ (0 : ℝ))
        (Set.uIcc R (2 * R)) := by
      intro r hr
      have hr' : r ∈ Set.Icc R (2 * R) := by
        simpa only [Set.uIcc_of_le (by linarith : R ≤ 2 * R)] using hr
      exact kernel_eq_zero_of_nonpos
        (div_nonpos_of_nonneg_of_nonpos (hR.trans hr'.1) ha')
    have hi : (∫ r in R..(2 * R), kernel (r / a)) = 0 := by
      simpa using intervalIntegral.integral_congr hz
    rw [hi]
    exact mul_nonneg averageBound_nonneg hR

private lemma integral_sum_mul_kernel_le {ι : Type*} (s : Finset ι) (w a : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) {R : ℝ} (hR : 0 ≤ R) :
    (∫ r in R..(2 * R), ∑ i ∈ s, w i * kernel (r / a i)) ≤
      averageBound * (∑ i ∈ s, w i) * R := by
  rw [intervalIntegral.integral_finsetSum]
  · calc
      (∑ i ∈ s, ∫ r in R..(2 * R), w i * kernel (r / a i)) =
          ∑ i ∈ s, w i * ∫ r in R..(2 * R), kernel (r / a i) := by
        simp only [intervalIntegral.integral_const_mul]
      _ ≤ ∑ i ∈ s, w i * (averageBound * R) :=
        Finset.sum_le_sum fun i hi ↦ mul_le_mul_of_nonneg_left
          (integral_posLog_one_div_abs_one_sub_div_le (a i) hR) (hw i hi)
      _ = averageBound * (∑ i ∈ s, w i) * R := by rw [← Finset.sum_mul]; ring
  · exact fun i _ ↦ (intervalIntegrable_posLog_one_div_abs_one_sub_div
      (a i) R (2 * R)).const_mul (w i)

end
end TauCeti

namespace Finset

/-- For `R > 0` and weights nonnegative on `s`, choose a point in `(R, 2 * R]` outside
any Lebesgue-null set, bounding the sum by an explicit universal constant times the weight sum.
The constant is independent of `R`, the excluded set, and the real scales `a`.
Repeated scales, zero weights, and the empty family are allowed. At `r = a i` the summand is
zero by totalization; include `s.image a` in `bad` when those points must be avoided. -/
theorem exists_mem_Ioc_notMem_sum_mul_posLog_one_div_abs_one_sub_div_le {ι : Type*}
    (s : Finset ι) (w a : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    {bad : Set ℝ} (hbad : volume bad = 0) {R : ℝ} (hR : 0 < R) :
    ∃ r ∈ Set.Ioc R (2 * R), r ∉ bad ∧
      (∑ i ∈ s, w i * Real.posLog (1 / |1 - r / a i|)) ≤
        (Real.log 2 + 12 * Real.sqrt 6) * ∑ i ∈ s, w i := by
  let g : ℝ → ℝ := ∑ i ∈ s, fun r ↦ w i * TauCeti.kernel (r / a i)
  let S : Set ℝ := Set.Ioc R (2 * R) \ bad
  have hS : S =ᵐ[volume] Set.Ioc R (2 * R) := sdiff_null_ae_eq_self hbad
  have hvolume : volume S ≠ 0 := by
    have hmeasure : volume S = volume (Set.Ioc R (2 * R)) := measure_congr hS
    rw [hmeasure, Real.volume_Ioc]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (by linarith))
  have hg : IntegrableOn g (Set.Ioc R (2 * R)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith : R ≤ 2 * R)).mp
      (IntervalIntegrable.sum (s := s) (f := fun i r ↦ w i * TauCeti.kernel (r / a i))
        (fun i _ ↦ (TauCeti.intervalIntegrable_posLog_one_div_abs_one_sub_div
          (a i) R (2 * R)).const_mul (w i)))
  obtain ⟨r, hr, hle⟩ := exists_le_setAverage hvolume
    (ne_top_of_le_ne_top (by simp : volume (Set.Ioc R (2 * R)) ≠ ∞)
      (measure_mono Set.sdiff_subset)) (hg.mono_set Set.sdiff_subset)
  have havg : (⨍ x in S, g x) ≤ TauCeti.averageBound * ∑ i ∈ s, w i := by
    rw [setAverage_congr hS, ← Set.uIoc_of_le (by linarith : R ≤ 2 * R),
      interval_average_eq_div]
    apply (div_le_iff₀ (by linarith : 0 < 2 * R - R)).mpr
    calc
      _ ≤ TauCeti.averageBound * (∑ i ∈ s, w i) * R := by
        simpa only [g, Finset.sum_apply] using
          TauCeti.integral_sum_mul_kernel_le s w a hw hR.le
      _ = _ := by ring
  refine ⟨r, hr.1, hr.2, ?_⟩
  simpa only [g, Finset.sum_apply, TauCeti.kernel] using hle.trans havg

end Finset
