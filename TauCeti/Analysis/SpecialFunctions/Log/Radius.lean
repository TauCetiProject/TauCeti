/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.Analysis.SpecialFunctions.Integrability.PosLog
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# A weighted good radius for the logarithmic singularity

On some radius in `(R, 2 * R]`, a finite weighted sum of
`Real.posLog (1 / |1 - r / a i|)` is bounded by a fixed multiple of the sum of the weights.
The scales may be arbitrary real numbers, including zero and negative values.
The radius can avoid any prescribed finite set. The estimate keeps the explicit integral
constant used in the good-circle minimum-modulus argument for finite-order Hadamard products.

The proof bounds the singularity by an integrable inverse-square-root function, obtains a
scale-uniform dyadic integral estimate, and applies Mathlib's below-average selection theorem
away from the finite null set. The kernel uses the ordinary totalized real logarithm and
inverse, including its value zero at the singularity. No kernel carrier is exported.

The argument is adapted from Matteo Cipollina's `CartanBound.lean` in PNT+.
-/

public section

open Real MeasureTheory intervalIntegral
open scoped Topology ENNReal BigOperators

namespace CartanRadius

noncomputable section

private abbrev kernel (t : ℝ) : ℝ := Real.posLog (1 / |1 - t|)

private abbrev majorantIntegral : ℝ :=
  ∫ t : ℝ in (1 / 4 : ℝ)..(4 : ℝ), Real.sqrt (2 / |1 - t|)

private abbrev averageBound : ℝ := Real.log 2 + 4 * majorantIntegral + 1

private lemma kernel_intervalIntegrable (A B : ℝ) : IntervalIntegrable kernel volume A B := by
  have hm : MeromorphicOn (fun t : ℝ ↦ 1 / (1 - t)) (Set.uIcc A B) := by
    intro t _
    fun_prop
  have heq : kernel = fun t : ℝ ↦ Real.posLog ‖1 / (1 - t)‖ := by
    funext t
    simp only [kernel, Real.norm_eq_abs, one_div, abs_inv]
  rw [heq]
  exact hm.intervalIntegrable_posLog_norm

private lemma neg_log_le_sqrt_two_div {x : ℝ} (hx : 0 < x) (hxle : x ≤ 1) :
    -Real.log x ≤ Real.sqrt (2 / x) := by
  have hx0 : 0 ≤ x := le_of_lt hx
  have ht : 0 ≤ -Real.log x := by
    have : Real.log x ≤ 0 := Real.log_nonpos hx0 hxle
    linarith
  have hmain : (-Real.log x) ^ 2 / 2 ≤ Real.exp (-Real.log x) := by
    simpa using Real.pow_div_factorial_le_exp (-Real.log x) ht 2
  have hexp : Real.exp (-Real.log x) = x⁻¹ := by simp [Real.exp_neg, Real.exp_log hx]
  have hsq2 : (-Real.log x) ^ 2 ≤ 2 * Real.exp (-Real.log x) := by nlinarith [hmain]
  have hsq' : (-Real.log x) ^ 2 ≤ 2 / x := by simpa [hexp, div_eq_mul_inv, mul_assoc] using hsq2
  have hy : 0 ≤ 2 / x := div_nonneg (by norm_num) (le_of_lt hx)
  exact (Real.le_sqrt ht hy).2 hsq'

private lemma kernel_le_sqrt_aux {t : ℝ} :
    Real.posLog (1 / |1 - t|) ≤ Real.sqrt (2 / |1 - t|) := by
  by_cases ht : |1 - t| ≤ 1
  · by_cases h0 : |1 - t| = 0
    · have : t = 1 := by
        have : 1 - t = 0 := by simpa [abs_eq_zero] using h0
        linarith
      subst this
      simp
    · have hpos : 0 < |1 - t| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm h0)
      have hle : -Real.log |1 - t| ≤ Real.sqrt (2 / |1 - t|) :=
        neg_log_le_sqrt_two_div (x := |1 - t|) hpos ht
      have hlog : Real.log (1 / |1 - t|) = -Real.log |1 - t| := by simp [Real.log_inv]
      have hnonneg : 0 ≤ Real.log (1 / |1 - t|) := by
        exact Real.log_nonneg ((one_le_div hpos).2 ht)
      have hmax : Real.posLog (1 / |1 - t|) = Real.log (1 / |1 - t|) :=
        max_eq_right hnonneg
      calc
        Real.posLog (1 / |1 - t|) = Real.log (1 / |1 - t|) := hmax
        _ = -Real.log |1 - t| := hlog
        _ ≤ Real.sqrt (2 / |1 - t|) := hle
  · have hlt : 1 < |1 - t| := lt_of_not_ge ht
    have hle0 : Real.log (1 / |1 - t|) ≤ 0 := by
      have hpos : 0 < |1 - t| := lt_trans (by norm_num) hlt
      have : (1 / |1 - t| : ℝ) ≤ 1 := (div_le_one hpos).2 (le_of_lt hlt)
      exact le_trans (Real.log_le_log (by positivity) this) (by simp)
    have hmax : Real.posLog (1 / |1 - t|) = 0 := max_eq_left hle0
    have hrhs : 0 ≤ Real.sqrt (2 / |1 - t|) := by
      exact Real.sqrt_nonneg _
    rw [hmax]
    exact hrhs

private lemma intervalIntegrable_majorant :
    IntervalIntegrable (fun t : ℝ ↦ Real.sqrt (2 / |1 - t|)) volume (1 / 4 : ℝ) 4 := by
  let f : ℝ → ℝ := fun u ↦ Real.sqrt (2 / |u|)
  have hnorm (u : ℝ) : ‖f u‖ = Real.sqrt 2 * ‖u‖ ^ (-(1 / 2 : ℝ)) := by
    dsimp [f]
    rw [abs_of_nonneg (Real.sqrt_nonneg _),
      Real.sqrt_div (by norm_num)]
    simp only [Real.sqrt_eq_rpow, div_eq_mul_inv, Real.rpow_neg (abs_nonneg u)]
  have hlocal : LocallyIntegrable f volume :=
    locallyIntegrable_of_norm_le_rpow (by simp : 1 ≤ Module.finrank ℝ ℝ)
      (α := (1 / 2 : ℝ)) (by norm_num)
      (Filter.Eventually.of_forall fun u ↦ (hnorm u).le)
      (by
        apply Measurable.aestronglyMeasurable
        dsimp [f]
        fun_prop)
  have hf : IntervalIntegrable f volume (-3 : ℝ) (3 / 4 : ℝ) := by
    rw [intervalIntegrable_iff]
    exact (hlocal.integrableOn_isCompact isCompact_uIcc).mono_set Set.uIoc_subset_uIcc
  convert (hf.comp_sub_left (c := (1 : ℝ))).symm using 1 <;> norm_num [f]

private lemma majorantIntegral_nonneg : 0 ≤ majorantIntegral :=
  intervalIntegral.integral_nonneg (by norm_num) fun _ _ ↦ Real.sqrt_nonneg _

private lemma log_two_le_averageBound : Real.log 2 ≤ averageBound := by
  dsimp [averageBound]
  linarith [majorantIntegral_nonneg]

private lemma averageBound_nonneg : 0 ≤ averageBound :=
  (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)).trans log_two_le_averageBound

private lemma kernel_le_log_two_of_le_half {t : ℝ} (ht : t ≤ (1 / 2 : ℝ)) :
    kernel t ≤ Real.log 2 := by
  have hden : (1 / 2 : ℝ) ≤ |1 - t| := by
    rw [abs_of_nonneg (by linarith : 0 ≤ 1 - t)]
    linarith
  have hfrac : (1 / |1 - t| : ℝ) ≤ 2 := by
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 2) hden
  exact (Real.posLog_le_posLog (neg_one_lt_zero.le.trans (by positivity)) hfrac).trans_eq
    (Real.posLog_eq_log (by norm_num : (1 : ℝ) ≤ |2|))

private lemma kernel_eq_zero_of_two_le {t : ℝ} (ht : (2 : ℝ) ≤ t) : kernel t = 0 := by
  apply (Real.posLog_eq_zero_iff _).mpr
  have hden : (1 : ℝ) ≤ |1 - t| := by
    rw [abs_of_nonpos (by linarith : 1 - t ≤ 0)]
    linarith
  rw [abs_of_nonneg (by positivity : 0 ≤ (1 / |1 - t| : ℝ))]
  exact (div_le_one (lt_of_lt_of_le zero_lt_one hden)).mpr hden

private lemma kernel_eq_zero_of_nonpos {t : ℝ} (ht : t ≤ 0) : kernel t = 0 := by
  apply (Real.posLog_eq_zero_iff _).mpr
  have hden : (1 : ℝ) ≤ |1 - t| := by
    rw [abs_of_nonneg (by linarith : 0 ≤ 1 - t)]
    linarith
  rw [abs_of_nonneg (by positivity : 0 ≤ (1 / |1 - t| : ℝ))]
  exact (div_le_one (lt_of_lt_of_le zero_lt_one hden)).mpr hden

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
  have hmajorant : IntervalIntegrable (fun t : ℝ ↦ Real.sqrt (2 / |1 - t|))
      volume A (2 * A) := by
    apply intervalIntegrable_majorant.mono_set
    apply Set.uIcc_subset_uIcc
    · exact Set.mem_uIcc.mpr (Or.inl ⟨hlo, by linarith [hhi]⟩)
    · exact Set.mem_uIcc.mpr (Or.inl ⟨by linarith, by linarith [hhi]⟩)
  calc
    (∫ t in A..(2 * A), kernel t) ≤
        ∫ t in A..(2 * A), Real.sqrt (2 / |1 - t|) := by
      exact intervalIntegral.integral_mono_on hA2A (kernel_intervalIntegrable _ _) hmajorant
        (fun _ _ ↦ kernel_le_sqrt_aux)
    _ ≤ majorantIntegral :=
      intervalIntegral.integral_mono_interval hlo hA2A (by linarith)
        (Filter.Eventually.of_forall fun _ ↦ Real.sqrt_nonneg _) intervalIntegrable_majorant
    _ ≤ (4 * majorantIntegral) * A := by
      nlinarith [mul_nonneg majorantIntegral_nonneg (by linarith : 0 ≤ 4 * A - 1)]
    _ ≤ averageBound * A := by
      apply mul_le_mul_of_nonneg_right _ hA
      dsimp [averageBound]
      linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]

private lemma kernel_div_intervalIntegrable (a A B : ℝ) :
    IntervalIntegrable (fun r ↦ kernel (r / a)) volume A B := by
  have hm : MeromorphicOn (fun r : ℝ ↦ 1 / (1 - r / a)) (Set.uIcc A B) := by
    intro t _
    fun_prop
  simpa only [kernel, Real.norm_eq_abs, abs_div, abs_one, one_div, abs_inv] using
    hm.intervalIntegrable_posLog_norm

private lemma integral_kernel_div_le (a : ℝ) {R : ℝ} (hR : 0 ≤ R) :
    (∫ r in R..(2 * R), kernel (r / a)) ≤ averageBound * R := by
  by_cases ha : 0 < a
  · have hscale : (∫ r in R..(2 * R), kernel (r / a)) =
        a * ∫ t in (R / a)..(2 * (R / a)), kernel t := by
      simp [smul_eq_mul, mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv, ha.ne']
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
          (integral_kernel_div_le (a i) hR) (hw i hi)
      _ = averageBound * (∑ i ∈ s, w i) * R := by rw [← Finset.sum_mul]; ring
  · exact fun i _ ↦ (kernel_div_intervalIntegrable (a i) R (2 * R)).const_mul (w i)

end
end CartanRadius

namespace Finset

/-- A weighted logarithmic singularity has a good radius in `(R, 2 * R]`, avoiding any finite
set, with an explicit universal bound independent of all real scales. Zero and negative scales
contribute zero. Repeated scales, zero weights and the empty finite set are allowed. -/
theorem exists_radius_sum_mul_posLog_inv_abs_one_sub_div_le {ι : Type*}
    (s : Finset ι) (w a : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (bad : Finset ℝ) {R : ℝ} (hR : 0 < R) :
    ∃ r ∈ Set.Ioc R (2 * R), r ∉ bad ∧
      (∑ i ∈ s, w i * Real.posLog (1 / |1 - r / a i|)) ≤
        (Real.log 2 + 4 * (∫ t : ℝ in (1 / 4 : ℝ)..(4 : ℝ),
          Real.sqrt (2 / |1 - t|)) + 1) * ∑ i ∈ s, w i := by
  let g : ℝ → ℝ := ∑ i ∈ s, fun r ↦ w i * CartanRadius.kernel (r / a i)
  let S : Set ℝ := Set.Ioc R (2 * R) \ (bad : Set ℝ)
  have hnull : volume (bad : Set ℝ) = 0 := bad.measure_zero volume
  have hS : S =ᵐ[volume] Set.Ioc R (2 * R) := sdiff_null_ae_eq_self hnull
  have hvolume : volume S ≠ 0 := by
    have hmeasure : volume S = volume (Set.Ioc R (2 * R)) := measure_congr hS
    rw [hmeasure, Real.volume_Ioc]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (by linarith))
  have hg : IntegrableOn g (Set.Ioc R (2 * R)) :=
    (IntervalIntegrable.sum (s := s) (f := fun i r ↦ w i * CartanRadius.kernel (r / a i))
      (fun i _ ↦ (CartanRadius.kernel_div_intervalIntegrable (a i) R (2 * R)).const_mul
        (w i))).1
  obtain ⟨r, hr, hle⟩ := exists_le_setAverage hvolume
    (ne_top_of_le_ne_top (by simp : volume (Set.Ioc R (2 * R)) ≠ ∞)
      (measure_mono Set.sdiff_subset)) (hg.mono_set Set.sdiff_subset)
  have hlength : 2 * R - R = R := by ring
  have havg : (⨍ x in S, g x) ≤ CartanRadius.averageBound * ∑ i ∈ s, w i := by
    rw [setAverage_congr hS, setAverage_eq, measureReal_def, Real.volume_Ioc,
      ENNReal.toReal_ofReal (by linarith : 0 ≤ 2 * R - R),
      hlength, smul_eq_mul, mul_comm, ← div_eq_mul_inv,
      ← intervalIntegral.integral_of_le (by linarith : R ≤ 2 * R)]
    apply (div_le_iff₀ hR).mpr
    simpa only [g, Finset.sum_apply] using
      CartanRadius.integral_sum_mul_kernel_le s w a hw hR.le
  refine ⟨r, hr.1, hr.2, ?_⟩
  simpa only [g, Finset.sum_apply] using hle.trans havg

end Finset
