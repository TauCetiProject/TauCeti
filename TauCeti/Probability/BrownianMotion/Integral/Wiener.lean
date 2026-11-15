/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.TimeIntegral.Basic
public import TauCeti.Probability.Process.TimeMeasure
import Mathlib.Analysis.Normed.Operator.Extend
import TauCeti.Analysis.InnerProductSpace.LinearCombination
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import TauCeti.Probability.Distributions.Gaussian.Continuity
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import TauCeti.MeasureTheory.Function.Lp.Indicator
import TauCeti.MeasureTheory.Function.L2Space

/-!
# The deterministic Wiener integral

For a real pre-Brownian motion and a finite horizon `T`, `wienerIntegral` constructs
an isometric real linear map from `L²((0,T],dt)` to `L²(P)`. It sends the indicator of
an initial interval to the Brownian evaluation at its clipped endpoint. Thus the
construction needs only the finite-dimensional Brownian laws, not path regularity
or a filtration. It is an integral of deterministic integrands, not a construction
of integration for random predictable integrands.

The integrals form a jointly Gaussian family (`isGaussianProcess_wienerIntegral`),
with mean zero, covariance equal to the time-`L²` inner product, and variance equal to
the squared time-`L²` norm. Interval formulas and uniqueness among continuous linear
maps characterize the construction. Extension by zero to longer horizons and changes
of Brownian version almost surely at each time preserve the integral. Linearity,
isometry and preservation of inner products are provided by its bundled type.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second
  edition, Springer, 1991, §3.2, deterministic integrands and the Wiener integral.
* Central formal ingredients: `IsPreBrownianReal.toL2`,
  `TauCeti.topologicalClosure_span_indicatorConstLp_eq_top_of_isPiSystem`, and
  `LinearMap.extendOfIsometry`.
-/

public section
noncomputable section

open MeasureTheory Set Filter
open scoped NNReal InnerProductSpace Topology

namespace ProbabilityTheory.IsPreBrownianReal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

private def timeIndicator (T t : ℝ≥0) : Lp ℝ 2 (TauCeti.Probability.timeMeasure T) :=
  indicatorConstLp 2 (measurableSet_Iic (a := t)) (measure_ne_top _ _) 1

private theorem inner_timeIndicator (T s t : ℝ≥0) :
    ⟪timeIndicator T s, timeIndicator T t⟫_ℝ = (min (min s t) T : ℝ≥0) := by
  simp only [timeIndicator, L2.inner_indicatorConstLp_one_indicatorConstLp_one,
    Iic_inter_Iic, measureReal_def, TauCeti.Probability.timeMeasure_Iic, ENNReal.coe_toReal,
    RCLike.ofReal_real_eq_id, id_eq]

private def timeStep (T : ℝ≥0) :
    (ℝ≥0 →₀ ℝ) →ₗ[ℝ] Lp ℝ 2 (TauCeti.Probability.timeMeasure T) :=
  Finsupp.linearCombination ℝ (timeIndicator T)

private theorem denseRange_timeStep (T : ℝ≥0) : DenseRange (timeStep T) := by
  have hdense : (Submodule.span ℝ (range (timeIndicator T))).topologicalClosure = ⊤ :=
    TauCeti.topologicalClosure_span_indicatorConstLp_Iic_eq_top (fun _ ↦ measure_ne_top _ _)
  rw [denseRange_iff_closure_range, ← LinearMap.coe_range, timeStep,
    Finsupp.range_linearCombination, ← Submodule.topologicalClosure_coe, hdense]
  rfl

private def brownianStep (hB : IsPreBrownianReal B P) (T : ℝ≥0) :
    (ℝ≥0 →₀ ℝ) →ₗ[ℝ] Lp ℝ 2 P :=
  Finsupp.linearCombination ℝ (fun t ↦ hB.toL2 (min t T))

private theorem norm_brownianStep (hB : IsPreBrownianReal B P) (T : ℝ≥0) (v : ℝ≥0 →₀ ℝ) :
    ‖brownianStep hB T v‖ = ‖timeStep T v‖ := by
  have hinner (s t : ℝ≥0) :
      ⟪hB.toL2 (min s T), hB.toL2 (min t T)⟫_ℝ =
        ⟪timeIndicator T s, timeIndicator T t⟫_ℝ := by
    rw [hB.inner_toL2, inner_timeIndicator]
    congr 1
    exact min_min_min_comm s T t T |>.trans (by simp [min_assoc])
  exact v.norm_linearCombination_eq_of_inner_eq hinner

/-- The deterministic Wiener integral on `(0,T]`, as an isometric real linear map.
No filtration or sample-path regularity is needed. -/
def wienerIntegral (hB : IsPreBrownianReal B P) (T : ℝ≥0) :
    Lp ℝ 2 (TauCeti.Probability.timeMeasure T) →ₗᵢ[ℝ] Lp ℝ 2 P :=
  (brownianStep hB T).extendOfIsometry (denseRange_timeStep T) (norm_brownianStep hB T)

/-- Integrating an initial-interval indicator gives the Brownian evaluation at its
endpoint clipped to the horizon, scaled by the indicator height. -/
@[simp]
theorem wienerIntegral_indicatorConstLp_Iic (hB : IsPreBrownianReal B P) (T t : ℝ≥0)
    (c : ℝ) :
    hB.wienerIntegral T
        (indicatorConstLp 2 (measurableSet_Iic (a := t)) (measure_ne_top _ _) c) =
      c • hB.toL2 (min t T) := by
  have h := LinearMap.extendOfIsometry_eq (brownianStep hB T) (denseRange_timeStep T)
    (norm_brownianStep hB T) (Finsupp.single t c)
  simpa [wienerIntegral, timeStep, timeIndicator, brownianStep,
    ← TauCeti.indicatorConstLp_smul, smul_eq_mul] using h

/-- The deterministic Wiener integral is uniquely determined among continuous real
linear maps by its values on initial-interval indicators with endpoints up to the horizon. -/
theorem eq_wienerIntegral (hB : IsPreBrownianReal B P) (T : ℝ≥0)
    (A : Lp ℝ 2 (TauCeti.Probability.timeMeasure T) →L[ℝ] Lp ℝ 2 P)
    (hA : ∀ t ≤ T,
      A (indicatorConstLp 2 (measurableSet_Iic (a := t)) (measure_ne_top _ _) 1) =
        hB.toL2 t) : A = (hB.wienerIntegral T).toContinuousLinearMap := by
  have hA' (t : ℝ≥0) :
      A (indicatorConstLp 2 (measurableSet_Iic (a := t)) (measure_ne_top _ _) 1) =
        hB.toL2 (min t T) := by
    rw [← TauCeti.Probability.indicatorConstLp_Iic_min_timeMeasure,
      hA _ (min_le_right _ _)]
  rw [wienerIntegral, LinearMap.toContinuousLinearMap_extendOfIsometry]
  exact (LinearMap.extendOfNorm_unique (denseRange_timeStep T) 1
    (by simp [norm_brownianStep]) A (by
      ext v
      simp [timeStep, brownianStep, Finsupp.linearCombination_apply, Finsupp.sum,
        timeIndicator, hA'])).symm

/-- Extending a deterministic integrand by zero to a longer horizon does not change
its Wiener integral. -/
@[simp]
theorem wienerIntegral_timeMeasureExtendLp (hB : IsPreBrownianReal B P)
    {S T : ℝ≥0} (hST : S ≤ T) (f : Lp ℝ 2 (TauCeti.Probability.timeMeasure S)) :
    hB.wienerIntegral T (TauCeti.Probability.timeMeasureExtendLp ℝ hST f) =
      hB.wienerIntegral S f := by
  have hmap : (hB.wienerIntegral T).toContinuousLinearMap.comp
      (TauCeti.Probability.timeMeasureExtendLp ℝ hST).toContinuousLinearMap =
      (hB.wienerIntegral S).toContinuousLinearMap := by
    apply hB.eq_wienerIntegral S
    intro t ht
    simp only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
      TauCeti.Probability.timeMeasureExtendLp_indicatorConstLp_Iic, min_eq_left ht,
      wienerIntegral_indicatorConstLp_Iic, min_eq_left (ht.trans hST), one_smul]
  exact congrArg (fun A : Lp ℝ 2 (TauCeti.Probability.timeMeasure S) →L[ℝ] Lp ℝ 2 P ↦ A f) hmap

/-- Changing the Brownian version almost surely at each time up to the horizon does
not change the deterministic Wiener integral. -/
theorem wienerIntegral_congr (hB : IsPreBrownianReal B P) {B' : ℝ≥0 → Ω → ℝ}
    (hB' : IsPreBrownianReal B' P) (T : ℝ≥0)
    (h : ∀ t ≤ T, B t =ᵐ[P] B' t) : hB.wienerIntegral T = hB'.wienerIntegral T := by
  apply LinearIsometry.toContinuousLinearMap_injective
  apply hB'.eq_wienerIntegral T
  intro t ht
  simp only [LinearIsometry.coe_toContinuousLinearMap, wienerIntegral_indicatorConstLp_Iic,
    min_eq_left ht, one_smul]
  exact Lp.ext ((hB.coeFn_toL2 t).trans ((h t ht).trans (hB'.coeFn_toL2 t).symm))

/-- For `s ≤ t`, integrating a constant-height indicator of `(s,t]` gives the Brownian
increment with both endpoints clipped to the horizon, scaled by the height `c`. -/
@[simp]
theorem wienerIntegral_indicatorConstLp_Ioc (hB : IsPreBrownianReal B P) (T : ℝ≥0)
    {s t : ℝ≥0} (hst : s ≤ t) (c : ℝ) :
    hB.wienerIntegral T
        (indicatorConstLp 2 (measurableSet_Ioc (a := s) (b := t)) (measure_ne_top _ _) c) =
      c • (hB.toL2 (min t T) - hB.toL2 (min s T)) := by
  have h := indicatorConstLp_disjoint_union (μ := TauCeti.Probability.timeMeasure T)
    (p := 2) (c := c) (s := Iic s) (t := Ioc s t)
    measurableSet_Iic measurableSet_Ioc
    (measure_ne_top _ _) (measure_ne_top _ _) (Iic_disjoint_Ioc le_rfl)
  simp only [Iic_union_Ioc_eq_Iic hst] at h
  have hh := congrArg (hB.wienerIntegral T) h
  rw [map_add, wienerIntegral_indicatorConstLp_Iic, wienerIntegral_indicatorConstLp_Iic] at hh
  rw [smul_sub]
  exact (eq_sub_iff_add_eq').2 hh.symm

/-- Integrating a constant gives the terminal Brownian evaluation scaled by that constant. -/
@[simp]
theorem wienerIntegral_const (hB : IsPreBrownianReal B P) (T : ℝ≥0) (c : ℝ) :
    hB.wienerIntegral T (Lp.const 2 (TauCeti.Probability.timeMeasure T) c) =
      c • hB.toL2 T := by
  have hconst : Lp.const 2 (TauCeti.Probability.timeMeasure T) c =
      indicatorConstLp 2 (measurableSet_Iic (a := T)) (measure_ne_top _ _) c := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_const 2 (TauCeti.Probability.timeMeasure T) c,
      indicatorConstLp_coeFn (p := 2) (hs := measurableSet_Iic (a := T))
        (hμs := measure_ne_top _ _) (c := c),
      TauCeti.Probability.ae_mem_Ioc_timeMeasure T] with t hc hi ht
    rw [hc, hi, indicator_of_mem ht.2]
    rfl
  simp [hconst]

/-- On a zero-length horizon every deterministic Wiener integral is zero. -/
@[simp]
theorem wienerIntegral_zero (hB : IsPreBrownianReal B P)
    (f : Lp ℝ 2 (TauCeti.Probability.timeMeasure 0)) : hB.wienerIntegral 0 f = 0 := by
  have hf : f = 0 := Lp.eq_zero_iff_ae_eq_zero.2 (by
    simp only [TauCeti.Probability.timeMeasure_zero, ae_zero]
    exact Filter.eventually_bot)
  simp [hf]

/-- Every deterministic Wiener integral has mean zero. -/
@[simp]
theorem integral_wienerIntegral (hB : IsPreBrownianReal B P) (T : ℝ≥0)
    (f : Lp ℝ 2 (TauCeti.Probability.timeMeasure T)) :
    ∫ ω, hB.wienerIntegral T f ω ∂P = 0 := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  let one : Lp ℝ 2 P := Lp.const 2 P 1
  have hexpect (g : Lp ℝ 2 P) : ⟪one, g⟫_ℝ = ∫ ω, g ω ∂P := by
    dsimp only [one]
    rw [← indicatorConstLp_univ, L2.inner_indicatorConstLp_one, setIntegral_univ]
  have hz : ∀ t : ℝ≥0, ⟪one, hB.toL2 t⟫_ℝ = 0 := by
    intro t
    rw [hexpect, integral_congr_ae (hB.coeFn_toL2 t), hB.integral_eval]
  rw [← hexpect]
  refine (denseRange_timeStep T).induction_on f (isClosed_eq
    (continuous_const.inner (hB.wienerIntegral T).continuous) continuous_const) (fun v ↦ ?_)
  simp only [wienerIntegral, LinearMap.extendOfIsometry_eq, brownianStep,
    Finsupp.linearCombination_apply, Finsupp.sum, inner_sum, real_inner_smul_right, hz,
    mul_zero, Finset.sum_const_zero]

/-- Covariance of deterministic Wiener integrals is their time-`L²` inner product. -/
@[simp]
theorem covariance_wienerIntegral (hB : IsPreBrownianReal B P) (T : ℝ≥0)
    (f g : Lp ℝ 2 (TauCeti.Probability.timeMeasure T)) :
    cov[hB.wienerIntegral T f, hB.wienerIntegral T g; P] = ⟪f, g⟫_ℝ := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  rw [covariance_eq_sub (Lp.memLp _) (Lp.memLp _), integral_wienerIntegral,
    integral_wienerIntegral, zero_mul, sub_zero]
  simpa only [L2.inner_def, RCLike.inner_apply, conj_trivial, Pi.mul_apply, mul_comm] using
    (hB.wienerIntegral T).inner_map_map f g

/-- The variance of a deterministic Wiener integral is its squared time-`L²` norm. -/
@[simp]
theorem variance_wienerIntegral (hB : IsPreBrownianReal B P) (T : ℝ≥0)
    (f : Lp ℝ 2 (TauCeti.Probability.timeMeasure T)) :
    Var[hB.wienerIntegral T f; P] = ‖f‖ ^ 2 := by
  rw [← covariance_self (Lp.memLp _).aemeasurable, covariance_wienerIntegral,
    real_inner_self_eq_norm_sq]

private theorem hasLaw_brownianStep (hB : IsPreBrownianReal B P) (T : ℝ≥0)
    (v : ℝ≥0 →₀ ℝ) :
    HasLaw (brownianStep hB T v) (gaussianReal 0 (‖timeStep T v‖₊ ^ 2)) P := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hg : IsGaussianProcess (fun t ↦ ⇑(hB.toL2 (min t T))) P :=
    (hB.isGaussianProcess.comp_right (fun t ↦ min t T)).congr
      (fun t ↦ (hB.coeFn_toL2 _).symm)
  have hgauss : HasGaussianLaw (brownianStep hB T v) P := by
    apply ((hg.smul v).hasGaussianLaw_fun_sum (I := v.support)).congr
    filter_upwards [(Lp.coeFn_linearCombination v (fun t ↦ hB.toL2 (min t T))).symm]
      with ω hω
    simpa [brownianStep, Finsupp.linearCombination_apply, Finsupp.sum] using hω
  have hmean : ∫ ω, brownianStep hB T v ω ∂P = 0 := by
    simpa only [wienerIntegral, LinearMap.extendOfIsometry_eq] using
      hB.integral_wienerIntegral T (timeStep T v)
  refine ⟨hgauss.aemeasurable, ?_⟩
  rw [hgauss.map_eq_gaussianReal, hmean]
  congr 1
  have hvar : Var[brownianStep hB T v; P] = ‖timeStep T v‖ ^ 2 := by
    simpa only [wienerIntegral, LinearMap.extendOfIsometry_eq] using
      hB.variance_wienerIntegral T (timeStep T v)
  rw [hvar]
  exact (Real.toNNReal_pow (norm_nonneg _) 2).trans (by simp)

/-- The deterministic Wiener integral is centered Gaussian with variance equal to
the squared time-`L²` norm. This includes the Dirac law for the zero integrand. -/
theorem hasLaw_wienerIntegral (hB : IsPreBrownianReal B P) (T : ℝ≥0)
    (f : Lp ℝ 2 (TauCeti.Probability.timeMeasure T)) :
    HasLaw (hB.wienerIntegral T f) (gaussianReal 0 (‖f‖₊ ^ 2)) P := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨u, hu, huf⟩ := mem_closure_iff_seq_limit.mp (denseRange_timeStep T f)
  choose v hv using hu
  have hvlim : Tendsto (fun n ↦ timeStep T (v n)) atTop (𝓝 f) := by
    simpa only [hv] using huf
  have hw : Tendsto (fun n ↦ brownianStep hB T (v n)) atTop (𝓝 (hB.wienerIntegral T f)) := by
    simpa only [Function.comp_def, wienerIntegral, LinearMap.extendOfIsometry_eq] using
      (hB.wienerIntegral T).continuous.tendsto f |>.comp hvlim
  have hd := (tendstoInMeasure_of_tendsto_Lp hw).tendstoInDistribution
    (fun n ↦ (Lp.memLp (brownianStep hB T (v n))).aemeasurable)
  refine ⟨(Lp.memLp _).aemeasurable, ?_⟩
  have hlim := hd.tendsto
  have hlaw (n : ℕ) :
      (⟨P.map (brownianStep hB T (v n)), inferInstance⟩ : ProbabilityMeasure ℝ) =
        (gaussianReal 0 (‖timeStep T (v n)‖₊ ^ 2)).toProbabilityMeasure :=
    Subtype.ext (hasLaw_brownianStep hB T (v n)).map_eq
  simp only [hlaw] at hlim
  have hc : Continuous (fun g : Lp ℝ 2 (TauCeti.Probability.timeMeasure T) ↦
      (gaussianReal 0 (‖g‖₊ ^ 2)).toProbabilityMeasure) :=
    Continuous.gaussianReal continuous_const (continuous_nnNorm.pow 2)
  exact congrArg (fun μ : ProbabilityMeasure ℝ ↦ (μ : Measure ℝ))
    (tendsto_nhds_unique hlim (hc.tendsto f |>.comp hvlim))

/-- The Wiener integrals form a jointly Gaussian family indexed by deterministic
`L²` integrands. -/
theorem isGaussianProcess_wienerIntegral (hB : IsPreBrownianReal B P) (T : ℝ≥0) :
    IsGaussianProcess (fun f ↦ ⇑(hB.wienerIntegral T f)) P where
  hasGaussianLaw I := by
    classical
    have hmeas : AEMeasurable (fun ω ↦ I.restrict (fun f ↦ hB.wienerIntegral T f ω)) P :=
      AEMeasurable.of_eval (fun _ ↦ (Lp.memLp _).aemeasurable)
    refine ⟨hmeas, isGaussian_of_isGaussian_map (fun L ↦ ?_)⟩
    rw [AEMeasurable.map_map_of_aemeasurable (by fun_prop) hmeas]
    have hg := (hB.hasLaw_wienerIntegral T
      (∑ f : I, L (Pi.single f 1) • f.1)).hasGaussianLaw
    have heq : (fun ω ↦ hB.wienerIntegral T
        (∑ f : I, L (Pi.single f 1) • f.1) ω) =ᵐ[P]
        L ∘ (fun ω ↦ I.restrict (fun f ↦ hB.wienerIntegral T f ω)) := by
      simp only [map_sum, map_smul]
      filter_upwards [Lp.coeFn_finsetSum Finset.univ
        (fun f : I ↦ L (Pi.single f 1) • hB.wienerIntegral T f.1),
        ae_all_iff.2 (fun f : I ↦ Lp.coeFn_smul (L (Pi.single f 1))
          (hB.wienerIntegral T f.1))] with ω hsum hsmul
      rw [hsum]
      simp only [Finset.sum_apply, hsmul, Pi.smul_apply, smul_eq_mul]
      calc
        _ = ∑ f : I, L (hB.wienerIntegral T f.1 ω • Pi.single f 1) := by
          simp [mul_comm]
        _ = L (∑ f : I, hB.wienerIntegral T f.1 ω • Pi.single f 1) :=
          (map_sum L _ _).symm
        _ = _ := congrArg L (by ext f; simp [Pi.single_apply])
    exact (hg.congr heq).isGaussian_map

end ProbabilityTheory.IsPreBrownianReal
