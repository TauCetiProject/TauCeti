/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Integral.L2
public import TauCeti.Probability.BrownianMotion.Tilted
import TauCeti.MeasureTheory.Function.Lp.Norm
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Probability.Independence.Integration
import TauCeti.Probability.Process.ElementaryDensity

/-!
# The Brownian exponential as an integral

The exponential martingale has diffusion coefficient equal to its value times its
parameter. We identify this coefficient in the completed predictable L² Brownian
integral, without assuming an Itô formula. The argument uses the Gaussian exponential
tilt to compute the pairing with elementary increments, then the integral isometry.
This supplies the integral equation for the stochastic exponential with constant
parameter. All statements concern a fixed finite horizon and the original filtration;
no continuous integral process or strong SDE solution is asserted here.

`coeFn_l2Integral_exponentialMartingale` gives the integral equation, including zero
parameters and zero horizons. `memLp_exponentialMartingale_predictableMeasure` supplies
its integrand domain. The increment pairing is also available independently of any
predictable version.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2 and §3.5.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped NNReal ENNReal InnerProductSpace

namespace TauCeti.Probability.IsFilteredPreBrownianReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {ℱ : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}

/-- A predictable Brownian exponential has finite expected square energy on each horizon.
Neither continuity of paths nor usual conditions on the filtration are needed. -/
theorem memLp_exponentialMartingale_predictableMeasure
    (hW : IsFilteredPreBrownianReal ℱ W P) (hpred : IsStronglyPredictable ℱ W)
    (θ : ℝ) (T : ℝ≥0) :
    MemLp (fun p : ℝ≥0 × Ω ↦ exponentialMartingale θ W p.1 p.2) 2
      (ℱ.predictableMeasure P T) := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  have hZ : StronglyMeasurable[ℱ.predictable]
      (fun p : ℝ≥0 × Ω ↦ exponentialMartingale θ W p.1 p.2) := by
    simp only [exponentialMartingale_def]
    apply Measurable.stronglyMeasurable
    exact Real.measurable_exp.comp ((hpred.measurable.const_mul θ).sub
      ((measurable_subtype_coe.comp ℱ.measurable_fst_predictable).const_mul (θ ^ 2) |>.div_const 2))
  rw [ℱ.memLp_predictableMeasure_iff P hZ T 2]
  apply (memLp_two_iff_integrable_sq
    (hZ.mono ℱ.predictable_le_prod).aestronglyMeasurable).2
  have hsq : AEStronglyMeasurable (fun p : ℝ≥0 × Ω ↦
      exponentialMartingale θ W p.1 p.2 ^ 2) ((timeMeasure T).prod P) :=
    (hZ.mono ℱ.predictable_le_prod).aestronglyMeasurable.pow 2
  apply (integrable_prod_iff hsq).2
  refine ⟨Eventually.of_forall fun t ↦ ?_, ?_⟩
  · exact (hW.memLp_exponentialMartingale θ t (by norm_num : (2 : ℝ≥0∞) ≠ ∞)).integrable_sq
  · simp_rw [Real.norm_eq_abs, abs_sq, hW.integral_sq_exponentialMartingale]
    apply (integrable_const (exp (θ ^ 2 * T))).mono'
      (by fun_prop : AEStronglyMeasurable (fun t : ℝ≥0 ↦ exp (θ ^ 2 * t)) (timeMeasure T))
    filter_upwards [ae_mem_Ioc_timeMeasure T] with t ht
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    exact exp_le_exp.mpr (mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.mpr ht.2) (sq_nonneg θ))

/-- Pairing the terminal exponential with a Brownian increment on a past event.
The factor `θ (t-s)` is the mean of that increment under the exponential tilt. -/
theorem integral_exponentialMartingale_mul_indicator_sub
    (hW : IsFilteredPreBrownianReal ℱ W P) (θ : ℝ)
    {s t T : ℝ≥0} (hst : s ≤ t) (htT : t ≤ T)
    {A : Set Ω} (hA : MeasurableSet[ℱ s] A) :
    ∫ ω, exponentialMartingale θ W T ω *
      (A.indicator (fun _ ↦ (1 : ℝ)) ω * (W t ω - W s ω)) ∂P =
      θ * ((t : ℝ) - s) * ∫ ω in A, exponentialMartingale θ W s ω ∂P := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  let Q := P.tilted (fun ω ↦ θ * W T ω)
  have := isProbabilityMeasure_tilted (hW.integrable_exp_mul_eval θ T)
  have hQA : MeasurableSet A := ℱ.le s _ hA
  have hid : IndepFun (A.indicator (fun _ ↦ (1 : ℝ))) (W t - W s) Q :=
    indep_of_indep_of_le (hW.indep_sub_tilted_mul_eval θ hst htT).symm
      (measurable_const.indicator hA).comap_le le_rfl
  have hi := hid.integral_mul_eq_mul_integral
    (stronglyMeasurable_const.indicator hQA).aestronglyMeasurable
    (((hW.adapted.measurable.sub hW.adapted.measurable).stronglyMeasurable.aestronglyMeasurable
      (μ := P)).mono_ac (tilted_absolutelyContinuous _ _))
  have hmean : ∫ ω, (W t - W s) ω ∂Q = θ * ((t : ℝ) - s) :=
    ((hW.hasLaw_sub_tilted_mul_eval θ hst htT).integral_eq).trans integral_id_gaussianReal
  rw [hmean, integral_indicator hQA, setIntegral_const] at hi
  simp only [smul_eq_mul, mul_one] at hi
  dsimp only [Q] at hi
  rw [hW.tilted_mul_eval_eq_withDensity] at hi
  rw [integral_withDensity_eq_integral_toReal_smul
    ((hW.adapted.stronglyAdapted_exponentialMartingale θ T).measurable.mono (ℱ.le T) le_rfl
      |>.ennreal_ofReal) (by simp)] at hi
  simp only [ENNReal.toReal_ofReal (exponentialMartingale_pos θ W T _).le,
    smul_eq_mul, Pi.mul_apply, Pi.sub_apply] at hi
  rw [← hW.tilted_mul_eval_eq_withDensity, measureReal_def,
    hW.tilted_mul_eval_apply θ (hst.trans htT) hA, ENNReal.toReal_ofReal] at hi
  · simpa only [mul_comm] using hi
  · exact integral_nonneg (fun ω ↦ (exponentialMartingale_pos θ W s ω).le)

private theorem inner_exponential_rectangle
    (hW : IsFilteredPreBrownianReal ℱ W P) (θ : ℝ)
    {s t T : ℝ≥0} (hst : s ≤ t) (ht : t ≤ T) {A : Set Ω}
    (hA : MeasurableSet[ℱ s] A) :
    letI := (hW.hasLaw_eval 0).isProbabilityMeasure
    let g := (hW.memLp_exponentialMartingale θ T (by norm_num : (2 : ℝ≥0∞) ≠ ∞)).toLp
      (exponentialMartingale θ W T)
    ⟪g, hW.l2Integral T (indicatorConstLp 2
      (measurableSet_predictable_Ioc_prod s t hA) (measure_ne_top _ _) 1)⟫_ℝ =
      θ * ((t : ℝ) - s) * ∫ ω in A, exponentialMartingale θ W s ω ∂P := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  dsimp only
  rw [L2.inner_def]
  simp only [RCLike.inner_apply, conj_trivial]
  have heq := integral_congr_ae ((hW.coeFn_l2Integral_indicatorConstLp_Ioc_prod_of_le
    hst ht hA 1).mul
      (hW.memLp_exponentialMartingale θ T (by norm_num : (2 : ℝ≥0∞) ≠ ∞)).coeFn_toLp)
  simp only [Pi.mul_apply] at heq
  rw [heq]
  simp_rw [mul_comm _ (exponentialMartingale θ W T _)]
  exact hW.integral_exponentialMartingale_mul_indicator_sub θ hst ht hA

private theorem inner_exponential_l2Integral
    (hW : IsFilteredPreBrownianReal ℱ W P) (hpred : IsStronglyPredictable ℱ W)
    (θ : ℝ) (T : ℝ≥0) :
    letI := (hW.hasLaw_eval 0).isProbabilityMeasure
    let f := (hW.memLp_exponentialMartingale_predictableMeasure hpred θ T).toLp
      (fun p : ℝ≥0 × Ω ↦ exponentialMartingale θ W p.1 p.2)
    let g := (hW.memLp_exponentialMartingale θ T (by norm_num : (2 : ℝ≥0∞) ≠ ∞)).toLp
      (exponentialMartingale θ W T)
    (innerSL ℝ g).comp (hW.l2Integral T).toContinuousLinearMap = θ • innerSL ℝ f := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  let hF := hW.memLp_exponentialMartingale_predictableMeasure hpred θ T
  apply ContinuousLinearMap.ext_indicatorConstLp_Ioc_prod_predictableMeasure T
  intro s t hst ht A hA
  simp only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    innerSL_apply_apply, smul_apply, smul_eq_mul]
  rw [real_inner_comm (indicatorConstLp 2
    (measurableSet_predictable_Ioc_prod s t hA) (measure_ne_top _ _) 1) _,
    L2.inner_indicatorConstLp_one]
  rw [inner_exponential_rectangle hW θ hst.le ht hA]
  have hZ : StronglyMeasurable[ℱ.predictable]
      (fun p : ℝ≥0 × Ω ↦ exponentialMartingale θ W p.1 p.2) := by
    simp only [exponentialMartingale_def]
    exact (Real.measurable_exp.comp ((hpred.measurable.const_mul θ).sub
      ((measurable_subtype_coe.comp ℱ.measurable_fst_predictable).const_mul (θ ^ 2)
        |>.div_const 2))).stronglyMeasurable
  have hrect := measurableSet_predictable_Ioc_prod s t hA
  rw [setIntegral_congr_ae hrect (hF.coeFn_toLp.mono fun p hp _ ↦ hp)]
  rw [← integral_indicator hrect, ℱ.integral_predictableMeasure P (hZ.indicator hrect) T,
    integral_indicator ((measurableSet_Ioc).prod (ℱ.le s _ hA)),
    setIntegral_prod _ (((ℱ.memLp_predictableMeasure_iff P hZ T 2).mp hF).integrable
      (by norm_num)).integrableOn]
  have heq : (∫ u in Ioc s t, ∫ ω in A, exponentialMartingale θ W u ω ∂P ∂timeMeasure T) =
      ((t : ℝ) - s) * ∫ ω in A, exponentialMartingale θ W s ω ∂P := by
    rw [setIntegral_congr_fun measurableSet_Ioc (fun u hu ↦
      ((hW.martingale_exponentialMartingale θ).setIntegral_eq hu.1.le hA).symm),
      setIntegral_const]
    simp [measureReal_def, min_eq_left ht, ENNReal.toReal_ofReal (sub_nonneg.mpr
      (NNReal.coe_le_coe.mpr hst.le)), smul_eq_mul]
  rw [heq]
  ring

private theorem integral_time_exp (θ : ℝ) (T : ℝ≥0) :
    ∫ u, θ ^ 2 * exp (θ ^ 2 * u) ∂timeMeasure T = exp (θ ^ 2 * T) - 1 := by
  have hc := NNReal.isClosedEmbedding_coe.measurableEmbedding
  have hm : (timeMeasure T).map ((↑) : ℝ≥0 → ℝ) = volume.restrict (Ioc 0 (T : ℝ)) := by
    rw [timeMeasure_def, hc.restrict_comap, hc.map_comap,
      Measure.restrict_restrict hc.measurableSet_range,
      inter_eq_right.mpr (image_subset_range _ _), NNReal.image_coe_Ioc, NNReal.coe_zero]
  rw [← hc.integral_map (fun u : ℝ ↦ θ ^ 2 * exp (θ ^ 2 * u)), hm,
    ← intervalIntegral.integral_of_le T.coe_nonneg]
  have h : ∫ u in (0 : ℝ)..T, θ ^ 2 * exp (θ ^ 2 * u) =
      exp (θ ^ 2 * T) - exp (θ ^ 2 * 0) := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ ↦ (((hasDerivAt_id u).const_mul (θ ^ 2)).exp).congr_deriv (by simp; ring))
    ((by fun_prop : Continuous (fun u : ℝ ↦ θ ^ 2 * exp (θ ^ 2 * u))).intervalIntegrable 0 T)
  simpa only [mul_zero, exp_zero] using h

private theorem norm_sq_exponential_integrand
    (hW : IsFilteredPreBrownianReal ℱ W P) (hpred : IsStronglyPredictable ℱ W)
    (θ : ℝ) (T : ℝ≥0) :
    letI := (hW.hasLaw_eval 0).isProbabilityMeasure
    let f := (hW.memLp_exponentialMartingale_predictableMeasure hpred θ T).toLp
      (fun p : ℝ≥0 × Ω ↦ exponentialMartingale θ W p.1 p.2)
    ‖θ • f‖ ^ 2 = exp (θ ^ 2 * T) - 1 := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  let hF := hW.memLp_exponentialMartingale_predictableMeasure hpred θ T
  let f := hF.toLp (fun p : ℝ≥0 × Ω ↦ exponentialMartingale θ W p.1 p.2)
  dsimp only
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, ← Lp.integral_norm_sq_eq_norm_sq,
    ← integral_const_mul]
  have hZ : StronglyMeasurable[ℱ.predictable]
      (fun p : ℝ≥0 × Ω ↦ exponentialMartingale θ W p.1 p.2) := by
    simp only [exponentialMartingale_def]
    exact (Real.measurable_exp.comp ((hpred.measurable.const_mul θ).sub
      ((measurable_subtype_coe.comp ℱ.measurable_fst_predictable).const_mul (θ ^ 2)
        |>.div_const 2))).stronglyMeasurable
  have he : (fun p ↦ θ ^ 2 * ‖f p‖ ^ 2) =ᵐ[ℱ.predictableMeasure P T]
      fun p : ℝ≥0 × Ω ↦ θ ^ 2 * exponentialMartingale θ W p.1 p.2 ^ 2 := by
    filter_upwards [hF.coeFn_toLp] with p hp
    simp only [f, hp, Real.norm_eq_abs, sq_abs]
  rw [integral_congr_ae he]
  have hZZ : StronglyMeasurable[ℱ.predictable]
      (fun p : ℝ≥0 × Ω ↦ θ ^ 2 * exponentialMartingale θ W p.1 p.2 ^ 2) := by
    simpa only [Pi.pow_apply] using (hZ.pow 2).const_mul (θ ^ 2)
  rw [ℱ.integral_predictableMeasure P hZZ T]
  rw [integral_prod _
    ((((ℱ.memLp_predictableMeasure_iff P hZ T 2).mp hF).integrable_sq).const_mul _)]
  simp_rw [integral_const_mul, hW.integral_sq_exponentialMartingale]
  simpa only [integral_const_mul] using integral_time_exp θ T

/-- The constant-parameter Brownian exponential satisfies its stochastic integral equation
in the completed predictable L² integral: `∫₀ᵀ θ Z_u dW_u = Z_T - 1`.
The predictable Brownian version must be supplied explicitly on a raw filtration. -/
theorem coeFn_l2Integral_exponentialMartingale
    (hW : IsFilteredPreBrownianReal ℱ W P) (hpred : IsStronglyPredictable ℱ W)
    (θ : ℝ) (T : ℝ≥0) :
    letI := (hW.hasLaw_eval 0).isProbabilityMeasure
    hW.l2Integral T (θ • (hW.memLp_exponentialMartingale_predictableMeasure hpred θ T).toLp
      (fun p : ℝ≥0 × Ω ↦ exponentialMartingale θ W p.1 p.2)) =ᵐ[P]
      fun ω ↦ exponentialMartingale θ W T ω - 1 := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  let hF := hW.memLp_exponentialMartingale_predictableMeasure hpred θ T
  let hG := hW.memLp_exponentialMartingale θ T (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
  let f := hF.toLp (fun p : ℝ≥0 × Ω ↦ exponentialMartingale θ W p.1 p.2)
  let g := hG.toLp (exponentialMartingale θ W T)
  let one : Lp ℝ 2 P := indicatorConstLp 2 MeasurableSet.univ (measure_ne_top _ _) 1
  have hgnorm : ‖g‖ ^ 2 = exp (θ ^ 2 * T) := by
    rw [← Lp.integral_norm_sq_eq_norm_sq]
    simp only [Real.norm_eq_abs, sq_abs]
    exact (integral_congr_ae (hG.coeFn_toLp.mono fun ω hω ↦
      congrArg (fun x : ℝ ↦ x ^ 2) hω)).trans (hW.integral_sq_exponentialMartingale θ T)
  have hmean : ⟪one, g⟫_ℝ = 1 := by
    rw [L2.inner_indicatorConstLp_one, setIntegral_univ]
    exact (integral_congr_ae hG.coeFn_toLp).trans (hW.integral_exponentialMartingale θ T)
  have hzero : ⟪one, hW.l2Integral T (θ • f)⟫_ℝ = 0 := by
    rw [L2.inner_indicatorConstLp_one, setIntegral_univ, hW.integral_l2Integral]
  have hpair : ⟪g, hW.l2Integral T (θ • f)⟫_ℝ = ‖θ • f‖ ^ 2 := by
    have h := congrArg (fun J : Lp ℝ 2 (ℱ.predictableMeasure P T) →L[ℝ] ℝ ↦ J (θ • f))
      (inner_exponential_l2Integral hW hpred θ T)
    simp only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
      innerSL_apply_apply, smul_apply, inner_smul_right, smul_eq_mul] at h
    have hp : ⟪g, hW.l2Integral T (θ • f)⟫_ℝ = θ * (θ * ⟪f, f⟫_ℝ) := h
    rw [real_inner_self_eq_norm_sq] at hp
    rw [hp, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    ring
  have hfnorm : ‖θ • f‖ ^ 2 = exp (θ ^ 2 * T) - 1 :=
    norm_sq_exponential_integrand hW hpred θ T
  have hone : ‖one‖ ^ 2 = 1 := by
    simp [one, indicatorConstLp_univ, Lp.norm_const, measureReal_def]
  have heq : hW.l2Integral T (θ • f) = g - one := by
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    have hn := norm_sub_sq_real (g - one) (hW.l2Integral T (θ • f))
    have hcenter : ‖g - one‖ ^ 2 = exp (θ ^ 2 * T) - 1 := by
      rw [norm_sub_sq_real, real_inner_comm one g, hmean, hgnorm, hone]
      ring
    rw [inner_sub_left, hpair, hzero, sub_zero, (hW.l2Integral T).norm_map,
      hcenter, hfnorm] at hn
    have : ‖(g - one) - hW.l2Integral T (θ • f)‖ = 0 := by
      nlinarith [norm_nonneg ((g - one) - hW.l2Integral T (θ • f))]
    simpa only [norm_sub_rev] using this
  rw [heq]
  filter_upwards [Lp.coeFn_sub g one, hG.coeFn_toLp,
    indicatorConstLp_coeFn (p := 2) (hs := MeasurableSet.univ)
      (hμs := measure_ne_top P univ) (c := (1 : ℝ))] with ω hs hg ho
  rw [hs]
  dsimp only [Pi.sub_apply, g, one]
  rw [hg, ho]
  simp

end TauCeti.Probability.IsFilteredPreBrownianReal
