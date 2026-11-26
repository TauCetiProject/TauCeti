/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.ExponentialMartingale
public import TauCeti.Probability.BrownianMotion.Integral.L2
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.Probability.BrownianMotion.Tilted
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

`coeFn_l2Integral_smul_toLp_exponentialMartingale` gives the integral equation, including zero
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

open TauCeti.Probability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {ℱ : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}

namespace ProbabilityTheory.IsPreBrownianReal

/-- A predictable Brownian exponential belongs to every finite `Lᵖ` on a finite horizon.
Neither continuity of paths nor usual conditions on the filtration are needed. -/
theorem memLp_exponentialMartingale_predictableMeasure
    (hW : IsPreBrownianReal W P) (hpred : IsStronglyPredictable ℱ W)
    (θ : ℝ) (T : ℝ≥0) {p : ℝ≥0∞} (hp : p ≠ ∞) :
    MemLp (fun u : ℝ≥0 × Ω ↦ exponentialMartingale θ W u.1 u.2) p
      (ℱ.predictableMeasure P T) := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  have hZ : StronglyMeasurable[ℱ.predictable]
      (fun u : ℝ≥0 × Ω ↦ exponentialMartingale θ W u.1 u.2) := hpred.exponentialMartingale θ
  rw [ℱ.memLp_predictableMeasure_iff P hZ T p]
  have hm := (hZ.mono ℱ.predictable_le_prod).aestronglyMeasurable (μ := (timeMeasure T).prod P)
  rcases eq_or_ne p 0 with rfl | hp0
  · exact memLp_zero_iff_aestronglyMeasurable.2 hm
  refine (integrable_norm_rpow_iff hm hp0 hp).1 ?_
  have hr := (Real.continuous_rpow_const (q := p.toReal) ENNReal.toReal_nonneg)
    |>.comp_aestronglyMeasurable hm.norm
  refine (integrable_prod_iff hr).2 ⟨Eventually.of_forall fun t ↦ ?_, ?_⟩
  · exact (integrable_norm_rpow_iff (hW.integrable_exponentialMartingale θ t).aestronglyMeasurable
      hp0 hp).2 (hW.memLp_exponentialMartingale θ t hp)
  · let c := p.toReal * (p.toReal - 1) * θ ^ 2 / 2
    simp_rw [Real.norm_eq_abs, abs_of_pos (rpow_pos_of_pos (abs_pos.mpr
      (exponentialMartingale_pos θ W _ _).ne') _),
      abs_of_pos (exponentialMartingale_pos θ W _ _), hW.integral_rpow_exponentialMartingale]
    have h (t : ℝ≥0) : p.toReal * (p.toReal - 1) * θ ^ 2 * t / 2 = c * t := by
      dsimp [c]
      ring
    simp_rw [h]
    apply (integrable_const (exp (|c| * T))).mono'
      (by fun_prop : AEStronglyMeasurable (fun t : ℝ≥0 ↦ exp (c * t)) (timeMeasure T))
    filter_upwards [ae_mem_Ioc_timeMeasure T] with t ht
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    exact exp_le_exp.mpr (mul_le_mul (le_abs_self c) (NNReal.coe_le_coe.mpr ht.2)
      t.coe_nonneg (abs_nonneg c))

end ProbabilityTheory.IsPreBrownianReal

namespace TauCeti.Probability.IsFilteredPreBrownianReal

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
  simp_rw [← indicator_mul_left A (fun _ ↦ (1 : ℝ)) (fun ω ↦ W t ω - W s ω), one_mul,
    ← indicator_mul_left A (fun ω ↦ W t ω - W s ω), integral_indicator (ℱ.le s A hA),
    mul_comm (_ - _) (exponentialMartingale θ W T _)]
  exact hW.setIntegral_exponentialMartingale_mul_sub θ hst ht hA

private theorem inner_exponential_l2Integral
    (hW : IsFilteredPreBrownianReal ℱ W P) (hpred : IsStronglyPredictable ℱ W)
    (θ : ℝ) (T : ℝ≥0) :
    let f := (hW.toIsPreBrownianReal.memLp_exponentialMartingale_predictableMeasure hpred θ T
      (by simp : (2 : ℝ≥0∞) ≠ ∞)).toLp
      (fun p : ℝ≥0 × Ω ↦ exponentialMartingale θ W p.1 p.2)
    let g := (hW.memLp_exponentialMartingale θ T (by norm_num : (2 : ℝ≥0∞) ≠ ∞)).toLp
      (exponentialMartingale θ W T)
    (innerSL ℝ g).comp (hW.l2Integral T).toContinuousLinearMap = θ • innerSL ℝ f := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  let hF := hW.toIsPreBrownianReal.memLp_exponentialMartingale_predictableMeasure hpred θ T
    (by simp : (2 : ℝ≥0∞) ≠ ∞)
  apply ContinuousLinearMap.ext_indicatorConstLp_Ioc_prod_predictableMeasure T
  intro s t hst ht A hA
  simp only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    innerSL_apply_apply, smul_apply, smul_eq_mul]
  rw [real_inner_comm (indicatorConstLp 2
    (measurableSet_predictable_Ioc_prod s t hA) (measure_ne_top _ _) 1) _,
    L2.inner_indicatorConstLp_one]
  rw [inner_exponential_rectangle hW θ hst.le ht hA]
  have hZ : StronglyMeasurable[ℱ.predictable]
      (fun u : ℝ≥0 × Ω ↦ exponentialMartingale θ W u.1 u.2) := hpred.exponentialMartingale θ
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

private theorem norm_sq_exponential_integrand
    (hW : IsPreBrownianReal W P) (hpred : IsStronglyPredictable ℱ W)
    (θ : ℝ) (T : ℝ≥0) :
    let f := (hW.memLp_exponentialMartingale_predictableMeasure hpred θ T
      (by simp : (2 : ℝ≥0∞) ≠ ∞)).toLp
      (fun p : ℝ≥0 × Ω ↦ exponentialMartingale θ W p.1 p.2)
    ‖θ • f‖ ^ 2 = exp (θ ^ 2 * T) - 1 := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  let hF := hW.memLp_exponentialMartingale_predictableMeasure hpred θ T
    (by simp : (2 : ℝ≥0∞) ≠ ∞)
  have hZ : StronglyMeasurable[ℱ.predictable]
      (fun u : ℝ≥0 × Ω ↦ exponentialMartingale θ W u.1 u.2) := hpred.exponentialMartingale θ
  have hZZ : StronglyMeasurable[ℱ.predictable]
      (fun p : ℝ≥0 × Ω ↦ exponentialMartingale θ W p.1 p.2 ^ 2) := hZ.pow 2
  dsimp only
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, hF.norm_toLp_sq]
  simp_rw [Real.norm_eq_abs, sq_abs]
  rw [ℱ.integral_predictableMeasure P hZZ T,
    integral_prod _ ((ℱ.memLp_predictableMeasure_iff P hZ T 2).mp hF).integrable_sq]
  simp_rw [hW.integral_sq_exponentialMartingale]
  have htime : (∫ u, exp (θ ^ 2 * u) ∂timeMeasure T) = ∫ u in (0 : ℝ)..T, exp (θ ^ 2 * u) := by
    rw [integral_timeMeasure]
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le T.coe_nonneg] at hu
    simp only [Real.coe_toNNReal u hu.1]
  rw [htime, ← smul_eq_mul, intervalIntegral.smul_integral_comp_mul_left, integral_exp,
    mul_zero, exp_zero]

/-- The constant-parameter Brownian exponential satisfies its stochastic integral equation
in the completed predictable L² integral: `∫₀ᵀ θ Z_u dW_u = Z_T - 1`.
The predictable Brownian version must be supplied explicitly on a raw filtration. -/
theorem coeFn_l2Integral_smul_toLp_exponentialMartingale
    (hW : IsFilteredPreBrownianReal ℱ W P) (hpred : IsStronglyPredictable ℱ W)
    (θ : ℝ) (T : ℝ≥0) :
    hW.l2Integral T (θ • (hW.toIsPreBrownianReal.memLp_exponentialMartingale_predictableMeasure
      hpred θ T (by simp : (2 : ℝ≥0∞) ≠ ∞)).toLp
      (fun p : ℝ≥0 × Ω ↦ exponentialMartingale θ W p.1 p.2)) =ᵐ[P]
      fun ω ↦ exponentialMartingale θ W T ω - 1 := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  let hF := hW.toIsPreBrownianReal.memLp_exponentialMartingale_predictableMeasure hpred θ T
    (by simp : (2 : ℝ≥0∞) ≠ ∞)
  let hG := hW.memLp_exponentialMartingale θ T (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
  let f := hF.toLp (fun p : ℝ≥0 × Ω ↦ exponentialMartingale θ W p.1 p.2)
  let g := hG.toLp (exponentialMartingale θ W T)
  let one : Lp ℝ 2 P := indicatorConstLp 2 MeasurableSet.univ (measure_ne_top _ _) 1
  have hgnorm : ‖g‖ ^ 2 = exp (θ ^ 2 * T) := by
    simpa only [g, hG.norm_toLp_sq, Real.norm_eq_abs, sq_abs] using
      hW.integral_sq_exponentialMartingale θ T
  have hmean : ⟪one, g⟫_ℝ = 1 := by
    rw [L2.inner_indicatorConstLp_one, setIntegral_univ]
    exact (integral_congr_ae hG.coeFn_toLp).trans (hW.integral_exponentialMartingale θ T)
  have hzero : ⟪one, hW.l2Integral T (θ • f)⟫_ℝ = 0 := by
    rw [L2.inner_indicatorConstLp_one, setIntegral_univ, hW.integral_l2Integral]
  have hpair : ⟪g, hW.l2Integral T (θ • f)⟫_ℝ = ‖θ • f‖ ^ 2 := by
    have h := congrArg (fun J : Lp ℝ 2 (ℱ.predictableMeasure P T) →L[ℝ] ℝ ↦ J (θ • f))
      (inner_exponential_l2Integral hW hpred θ T)
    simp only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
      innerSL_apply_apply, smul_apply, inner_smul_right, smul_eq_mul, f, g] at h ⊢
    rw [h, real_inner_self_eq_norm_sq, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    ring
  have hfnorm : ‖θ • f‖ ^ 2 = exp (θ ^ 2 * T) - 1 :=
    norm_sq_exponential_integrand hW.toIsPreBrownianReal hpred θ T
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
