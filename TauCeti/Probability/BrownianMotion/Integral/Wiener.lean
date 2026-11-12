/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.TimeIntegral
public import TauCeti.Probability.Process.TimeMeasure
import TauCeti.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# The deterministic Wiener integral

For a real pre-Brownian motion and a finite horizon `T`, `wienerIntegral` constructs
an isometric real linear map from `L²((0,T],dt)` to `L²(P)`. It sends the indicator of
an initial interval to the Brownian evaluation at its clipped endpoint. Thus the
construction needs only the finite-dimensional Brownian laws, not path regularity
or a filtration. It is an integral of deterministic integrands, not a construction
of integration for random predictable integrands.

The construction completes finite linear combinations of initial-interval indicators.
It uses `IsPreBrownianReal.toL2`, the generating-pi-system density theorem for `L²`,
and Mathlib's `LinearMap.extendOfIsometry`. Every resulting integral has the centered
Gaussian law with variance equal to the squared time-`L²` norm. The interval formulas
and uniqueness among continuous linear maps characterize the construction; linearity,
isometry and preservation of inner products are provided by its bundled type.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second
  edition, Springer, 1991, §3.2, deterministic integrands and the Wiener integral.
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
  have hgen : (inferInstance : MeasurableSpace ℝ≥0) =
      MeasurableSpace.generateFrom (range Iic) := by
    exact (BorelSpace.measurable_eq (α := ℝ≥0)).trans (borel_eq_generateFrom_Iic ℝ≥0)
  have hcover : IsCountablySpanning (range (Iic : ℝ≥0 → Set ℝ≥0)) := by
    refine ⟨fun n : ℕ ↦ Iic (n : ℝ≥0), fun n ↦ mem_range_self _, ?_⟩
    ext t
    simp only [mem_iUnion, mem_Iic, mem_univ, iff_true]
    exact exists_nat_ge t
  have hdense := TauCeti.topologicalClosure_span_indicatorConstLp_eq_top_of_isPiSystem
    (μ := TauCeti.Probability.timeMeasure T) hgen isPiSystem_Iic hcover
    (fun _ _ ↦ measure_ne_top _ _)
  have hset : {g : Lp ℝ 2 (TauCeti.Probability.timeMeasure T) |
      ∃ (s : Set ℝ≥0) (hs : s ∈ range Iic),
        g = indicatorConstLp 2 (hgen ▸ MeasurableSpace.measurableSet_generateFrom hs)
          (measure_ne_top _ _) 1} = range (timeIndicator T) := by
    ext g
    constructor
    · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
      exact mem_range_self t
    · rintro ⟨t, rfl⟩
      exact ⟨Iic t, mem_range_self t, rfl⟩
  rw [hset] at hdense
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
  have heq : ⟪brownianStep hB T v, brownianStep hB T v⟫_ℝ =
      ⟪timeStep T v, timeStep T v⟫_ℝ := by
    simp only [brownianStep, timeStep, Finsupp.linearCombination_apply, Finsupp.sum,
      sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right, hinner]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    (by simpa only [real_inner_self_eq_norm_sq] using heq)

/-- The deterministic Wiener integral on `(0,T]`, as an isometric real linear map.
No filtration or sample-path regularity is needed. -/
def wienerIntegral (hB : IsPreBrownianReal B P) (T : ℝ≥0) :
    Lp ℝ 2 (TauCeti.Probability.timeMeasure T) →ₗᵢ[ℝ] Lp ℝ 2 P :=
  (brownianStep hB T).extendOfIsometry (denseRange_timeStep T) (norm_brownianStep hB T)

/-- Integrating an initial-interval indicator gives the Brownian evaluation at its
endpoint clipped to the horizon. In particular the zero horizon gives the zero class. -/
@[simp]
theorem wienerIntegral_indicatorConstLp_Iic (hB : IsPreBrownianReal B P) (T t : ℝ≥0) :
    hB.wienerIntegral T
        (indicatorConstLp 2 (measurableSet_Iic (a := t)) (measure_ne_top _ _) 1) =
      hB.toL2 (min t T) := by
  have h := LinearMap.extendOfIsometry_eq (brownianStep hB T) (denseRange_timeStep T)
    (norm_brownianStep hB T) (Finsupp.single t 1)
  simpa [wienerIntegral, timeStep, timeIndicator, brownianStep] using h

/-- The deterministic Wiener integral is uniquely determined among continuous real
linear maps by its values on initial-interval indicators. -/
theorem eq_wienerIntegral (hB : IsPreBrownianReal B P) (T : ℝ≥0)
    (A : Lp ℝ 2 (TauCeti.Probability.timeMeasure T) →L[ℝ] Lp ℝ 2 P)
    (hA : ∀ t : ℝ≥0,
      A (indicatorConstLp 2 (measurableSet_Iic (a := t)) (measure_ne_top _ _) 1) =
        hB.toL2 (min t T)) : A = (hB.wienerIntegral T).toContinuousLinearMap := by
  apply DFunLike.coe_injective
  apply (denseRange_timeStep T).equalizer A.continuous
    (hB.wienerIntegral T).toContinuousLinearMap.continuous
  ext v
  simp [timeStep, Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul,
    timeIndicator, hA]

/-- Integrating an interval indicator gives the corresponding Brownian increment,
with both endpoints clipped to the horizon. -/
@[simp]
theorem wienerIntegral_indicatorConstLp_Ioc (hB : IsPreBrownianReal B P) (T : ℝ≥0)
    {s t : ℝ≥0} (hst : s ≤ t) :
    hB.wienerIntegral T
        (indicatorConstLp 2 (measurableSet_Ioc (a := s) (b := t)) (measure_ne_top _ _) 1) =
      hB.toL2 (min t T) - hB.toL2 (min s T) := by
  have h := indicatorConstLp_disjoint_union (μ := TauCeti.Probability.timeMeasure T)
    (p := 2) (c := (1 : ℝ)) (s := Iic s) (t := Ioc s t)
    measurableSet_Iic measurableSet_Ioc
    (measure_ne_top _ _) (measure_ne_top _ _) (Iic_disjoint_Ioc le_rfl)
  simp only [Iic_union_Ioc_eq_Iic hst] at h
  have hh := congrArg (hB.wienerIntegral T) h
  rw [map_add, wienerIntegral_indicatorConstLp_Iic, wienerIntegral_indicatorConstLp_Iic] at hh
  exact (eq_sub_iff_add_eq').2 hh.symm

/-- Every deterministic Wiener integral has mean zero. -/
@[simp]
theorem integral_wienerIntegral (hB : IsPreBrownianReal B P) (T : ℝ≥0)
    (f : Lp ℝ 2 (TauCeti.Probability.timeMeasure T)) :
    ∫ ω, hB.wienerIntegral T f ω ∂P = 0 := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  let one : Lp ℝ 2 P := Lp.const 2 P 1
  have hexpect (g : Lp ℝ 2 P) : ⟪one, g⟫_ℝ = ∫ ω, g ω ∂P := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_const (p := 2) P (1 : ℝ)] with ω hω
    dsimp only [one]
    rw [hω]
    simp
  have hz : ∀ t : ℝ≥0, ⟪one, hB.toL2 t⟫_ℝ = 0 := by
    intro t
    rw [hexpect, integral_congr_ae (hB.coeFn_toL2 t), hB.integral_eval]
  rw [← hexpect]
  refine (denseRange_timeStep T).induction_on f (isClosed_eq
    (continuous_const.inner (hB.wienerIntegral T).continuous) continuous_const) (fun v ↦ ?_)
  simp only [wienerIntegral, LinearMap.extendOfIsometry_eq, brownianStep,
    Finsupp.linearCombination_apply, Finsupp.sum, inner_sum, real_inner_smul_right, hz,
    mul_zero, Finset.sum_const_zero]

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
  rw [variance_eq_sub (Lp.memLp _), hmean, zero_pow two_ne_zero, sub_zero]
  have hsq := Lp.integral_norm_sq_eq_norm_sq (brownianStep hB T v)
  simp only [Real.norm_eq_abs, sq_abs] at hsq
  simp only [Pi.pow_apply]
  rw [hsq, norm_brownianStep]
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
  refine ⟨(Lp.memLp _).aemeasurable, Measure.ext_of_charFun (funext fun x ↦ ?_)⟩
  have hlim := hd.tendsto_charFun x
  simp only [(hasLaw_brownianStep hB T _).map_eq] at hlim
  have hc : Continuous (fun g : Lp ℝ 2 (TauCeti.Probability.timeMeasure T) ↦
      charFun (gaussianReal 0 (‖g‖₊ ^ 2)) x) := by
    simp only [charFun_gaussianReal]
    fun_prop
  exact tendsto_nhds_unique hlim (by
    simpa only [Function.comp_def] using hc.tendsto f |>.comp hvlim)

end ProbabilityTheory.IsPreBrownianReal
