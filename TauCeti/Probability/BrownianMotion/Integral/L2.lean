/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Integral.Covariance
public import TauCeti.Probability.Process.Predictable.Measure
import TauCeti.Probability.Process.ElementaryDensity
import Mathlib.Analysis.Normed.Operator.Extend
import TauCeti.Analysis.InnerProductSpace.LinearCombination
import TauCeti.MeasureTheory.Function.Lp.Indicator

/-!
# The finite-horizon predictable L² Brownian integral

For a Brownian motion relative to an arbitrary filtration, construct the terminal integral
as a real linear isometry from predictable time-product L² into sample-space L².
On a predictable rectangle `(s,t] × A` its value is `1_A (W_t − W_s)`, with clipping at
the declared horizon. The map is uniquely determined by these elementary values.
Linearity and the isometry are supplied by the bundled map, not separate operations on
chosen representatives. The result is a terminal-time map on L² classes, not a
time-indexed integral process.

The construction uses the overlapping-increment Gram identity and the density of predictable
rectangles, followed by Mathlib's `LinearMap.extendOfIsometry`.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal InnerProductSpace

namespace TauCeti.Probability.IsFilteredPreBrownianReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {ℱ : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}

private structure Rectangle (ℱ : Filtration ℝ≥0 mΩ) where
  s : ℝ≥0
  t : ℝ≥0
  event : Set Ω
  known : MeasurableSet[ℱ s] event

-- This abbreviation lets rectangle indices elaborate directly as their indicator L² classes.
private abbrev step [IsFiniteMeasure P] (T : ℝ≥0) (R : Rectangle ℱ) :
    Lp ℝ 2 (ℱ.predictableMeasure P T) :=
  indicatorConstLp 2 (measurableSet_predictable_Ioc_prod R.s R.t R.known) (measure_ne_top _ _) 1

private def Rectangle.height (R : Rectangle ℱ) : Ω → ℝ := R.event.indicator 1

private theorem Rectangle.height_measurable (R : Rectangle ℱ) :
    StronglyMeasurable[ℱ R.s] R.height :=
  stronglyMeasurable_const.indicator R.known

private theorem Rectangle.height_memLp [IsFiniteMeasure P] (R : Rectangle ℱ) : MemLp R.height 2 P :=
  (memLp_const (1 : ℝ)).indicator (ℱ.le _ _ R.known).nullMeasurableSet

private def increment (hW : IsFilteredPreBrownianReal ℱ W P) (T : ℝ≥0) (R : Rectangle ℱ) :
    Lp ℝ 2 P := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  exact (hW.memLp_mul_sub (le_max_left R.s (min R.t T)) R.height_measurable
    R.height_memLp).toLp (fun ω ↦ R.height ω * (W (max R.s (min R.t T)) ω - W R.s ω))

private theorem increment_ae (hW : IsFilteredPreBrownianReal ℱ W P)
    (T : ℝ≥0) (R : Rectangle ℱ) :
    increment hW T R =ᵐ[P]
      fun ω ↦ R.height ω * (W (max R.s (min R.t T)) ω - W R.s ω) := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  exact (hW.memLp_mul_sub (le_max_left R.s (min R.t T)) R.height_measurable
    R.height_memLp).coeFn_toLp

private theorem inner_increment [IsFiniteMeasure P] (hW : IsFilteredPreBrownianReal ℱ W P)
    (T : ℝ≥0) (R Q : Rectangle ℱ) :
    ⟪increment hW T R, increment hW T Q⟫_ℝ =
      ⟪step (P := P) T R, step (P := P) T Q⟫_ℝ := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  rw [real_inner_comm, L2.inner_def]
  have hi := integral_congr_ae ((increment_ae hW T R).mul (increment_ae hW T Q))
  simp only [RCLike.inner_apply, conj_trivial, Pi.mul_apply] at hi ⊢
  rw [hi, hW.integral_mul_sub_mul_mul_sub (le_max_left _ _) (le_max_left _ _)
    R.height_measurable Q.height_measurable R.height_memLp Q.height_memLp]
  have hevent : ∫ ω, R.height ω * Q.height ω ∂P = (P (R.event ∩ Q.event)).toReal := by
    simpa only [Set.inter_indicator_one, Pi.mul_apply, Rectangle.height, measureReal_def] using
      (integral_indicator_one (μ := P) ((ℱ.le _ _ R.known).inter (ℱ.le _ _ Q.known)))
  rw [hevent, step, step, L2.real_inner_indicatorConstLp_one_indicatorConstLp_one]
  have hset : (Ioc R.s R.t ×ˢ R.event) ∩ (Ioc Q.s Q.t ×ˢ Q.event) =
      Ioc (max R.s Q.s) (min R.t Q.t) ×ˢ (R.event ∩ Q.event) := by
    rw [prod_inter_prod, Ioc_inter_Ioc]
  rw [hset, measureReal_def, ℱ.predictableMeasure_Ioc_prod P T _ _
    (((ℱ.mono (le_max_left _ _)) _ R.known).inter
      ((ℱ.mono (le_max_right _ _)) _ Q.known)), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal']
  have hlength : (↑(min (max R.s (min R.t T)) (max Q.s (min Q.t T)) - max R.s Q.s) : ℝ) =
      max ((min (min R.t Q.t) T : ℝ≥0) - (max R.s Q.s : ℝ)) 0 := by
    simp only [NNReal.coe_sub_def, NNReal.coe_min, NNReal.coe_max]
    grind only [min_def, max_def]
  rw [hlength, NNReal.coe_max, mul_comm]

private theorem dense_step [IsFiniteMeasure P] (T : ℝ≥0) :
    DenseRange (Finsupp.linearCombination ℝ (step (ℱ := ℱ) (P := P) T)) := by
  rw [DenseRange, ← LinearMap.coe_range, Finsupp.range_linearCombination,
    Submodule.dense_iff_topologicalClosure_eq_top]
  have hd := ℱ.topologicalClosure_span_indicatorConstLp_Ioc_prod_eq_top
    (ℱ.predictableMeasure P T) (fun _ _ _ _ ↦ measure_ne_top _ _)
    (ℱ.predictableMeasure_singleton_zero_prod P T MeasurableSet.univ)
  convert hd using 2
  congr 1
  ext f
  constructor
  · rintro ⟨R, rfl⟩
    exact ⟨R.s, R.t, R.event, R.known, rfl⟩
  · rintro ⟨s, t, A, hA, rfl⟩
    exact ⟨⟨s, t, A, hA⟩, rfl⟩

/-- The Brownian integral at horizon `T`, as a linear isometry from predictable L² to L²(P).
It is defined on a.e. classes, so null-set changes in an integrand do not change its value. -/
def l2Integral (hW : IsFilteredPreBrownianReal ℱ W P) (T : ℝ≥0) :
    Lp ℝ 2 (ℱ.predictableMeasure P T) →ₗᵢ[ℝ] Lp ℝ 2 P := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  exact (Finsupp.linearCombination ℝ (increment hW T)).extendOfIsometry
    (dense_step T) (fun c ↦ c.norm_linearCombination_eq_of_inner_eq (inner_increment hW T))

private theorem l2Integral_step [IsFiniteMeasure P] (hW : IsFilteredPreBrownianReal ℱ W P)
    (T : ℝ≥0) (R : Rectangle ℱ) :
    hW.l2Integral T (step (P := P) T R) = increment hW T R := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  have h := (Finsupp.linearCombination ℝ (increment hW T)).extendOfIsometry_eq
    (dense_step (ℱ := ℱ) (P := P) T)
    (fun c ↦ c.norm_linearCombination_eq_of_inner_eq (inner_increment hW T)) (Finsupp.single R 1)
  simpa only [l2Integral, Finsupp.linearCombination_single, one_smul] using h

/-- The integral of a constant on a predictable rectangle, clipped at the horizon.
The maximum makes empty or reversed intervals contribute zero, including intervals after `T`. -/
theorem coeFn_l2Integral_indicatorConstLp_Ioc_prod (hW : IsFilteredPreBrownianReal ℱ W P)
    (T s t : ℝ≥0) {A : Set Ω} (hA : MeasurableSet[ℱ s] A) (c : ℝ) :
    letI := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
    hW.l2Integral T (indicatorConstLp 2 (measurableSet_predictable_Ioc_prod s t hA)
      (measure_ne_top _ _) c) =ᵐ[P]
      fun ω ↦ A.indicator (fun _ ↦ c) ω * (W (max s (min t T)) ω - W s ω) := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  have h := increment_ae hW T ⟨s, t, A, hA⟩
  rw [← l2Integral_step hW T] at h
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  have hc := TauCeti.indicatorConstLp_smul (p := 2) (μ := ℱ.predictableMeasure P T)
    (measurableSet_predictable_Ioc_prod s t hA) (measure_ne_top _ _) c (1 : ℝ)
  simp only [smul_eq_mul, mul_one] at hc
  rw [hc, map_smul]
  filter_upwards [Lp.coeFn_smul c (hW.l2Integral T (step T ⟨s, t, A, hA⟩)), h] with ω hsmul hω
  simp only [hsmul, Pi.smul_apply, smul_eq_mul, hω, Rectangle.height]
  by_cases hAω : ω ∈ A <;> simp [hAω]

/-- On an interval within the horizon, a constant rectangle's integral is its Brownian
increment multiplied by the constant and the indicator of the event known at its left endpoint. -/
theorem coeFn_l2Integral_indicatorConstLp_Ioc_prod_of_le
    (hW : IsFilteredPreBrownianReal ℱ W P)
    {T s t : ℝ≥0} (hst : s ≤ t) (ht : t ≤ T) {A : Set Ω}
    (hA : MeasurableSet[ℱ s] A) (c : ℝ) :
    letI := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
    hW.l2Integral T (indicatorConstLp 2 (measurableSet_predictable_Ioc_prod s t hA)
      (measure_ne_top _ _) c) =ᵐ[P]
      fun ω ↦ A.indicator (fun _ ↦ c) ω * (W t ω - W s ω) := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  simpa only [min_eq_left ht, max_eq_right hst] using
    hW.coeFn_l2Integral_indicatorConstLp_Ioc_prod T s t hA c

/-- The integral of a constant integrand is that constant times the Brownian value at
the horizon, almost everywhere. -/
theorem coeFn_l2Integral_const (hW : IsFilteredPreBrownianReal ℱ W P)
    (T : ℝ≥0) (c : ℝ) :
    letI := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
    hW.l2Integral T (Lp.const 2 (ℱ.predictableMeasure P T) c) =ᵐ[P]
      fun ω ↦ c * W T ω := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  have hb := ae_restrict_mem (μ := ℱ.predictableMeasure P T)
    (measurableSet_predictable_Ioc_prod 0 T (𝓕 := ℱ) MeasurableSet.univ)
  rw [ℱ.predictableMeasure_restrict, min_self] at hb
  have heq : indicatorConstLp 2
      (measurableSet_predictable_Ioc_prod 0 T (𝓕 := ℱ) MeasurableSet.univ)
      (measure_ne_top (ℱ.predictableMeasure P T) _) c =
      Lp.const 2 (ℱ.predictableMeasure P T) c := by
    apply Lp.ext
    filter_upwards [indicatorConstLp_coeFn (p := 2) (c := c)
      (hs := measurableSet_predictable_Ioc_prod 0 T (𝓕 := ℱ) MeasurableSet.univ)
      (hμs := measure_ne_top (ℱ.predictableMeasure P T) _),
      Lp.coeFn_const 2 (ℱ.predictableMeasure P T) c, hb] with p hp hc hmem
    simp only [hp, hc, Function.const_apply, indicator_of_mem hmem]
  rw [← heq]
  filter_upwards [hW.coeFn_l2Integral_indicatorConstLp_Ioc_prod_of_le
    (s := 0) (t := T) bot_le le_rfl MeasurableSet.univ c,
    hW.toIsPreBrownianReal.eval_zero_ae_eq_zero] with ω hω hzero
  simpa only [indicator_univ, hzero, sub_zero] using hω

/-- The integral is the unique continuous linear map with its values on nonempty predictable
rectangles within the horizon. No isometry hypothesis on the competing map is needed. -/
theorem l2Integral_unique (hW : IsFilteredPreBrownianReal ℱ W P) (T : ℝ≥0)
    (J : Lp ℝ 2 (ℱ.predictableMeasure P T) →L[ℝ] Lp ℝ 2 P)
    (hJ : ∀ ⦃s t : ℝ≥0⦄, s < t → t ≤ T → ∀ ⦃A : Set Ω⦄ (hA : MeasurableSet[ℱ s] A),
      letI := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
      J (indicatorConstLp 2 (measurableSet_predictable_Ioc_prod s t hA)
        (measure_ne_top _ _) 1) =ᵐ[P]
        fun ω ↦ A.indicator (fun _ ↦ (1 : ℝ)) ω * (W t ω - W s ω)) :
    J = (hW.l2Integral T).toContinuousLinearMap := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  apply ContinuousLinearMap.ext_indicatorConstLp_Ioc_prod_predictableMeasure T
  intro s t hst ht A hA
  apply Lp.ext
  exact (hJ hst ht hA).trans
    (hW.coeFn_l2Integral_indicatorConstLp_Ioc_prod_of_le hst.le ht hA 1).symm

/-- At horizon zero every predictable L² integral vanishes. -/
@[simp]
theorem l2Integral_zero (hW : IsFilteredPreBrownianReal ℱ W P)
    (f : Lp ℝ 2 (ℱ.predictableMeasure P 0)) : hW.l2Integral 0 f = 0 := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  have hz := hW.l2Integral_unique 0 0 (by
    intro s t hst ht A hA
    exact (not_lt_of_ge (ht.trans bot_le) hst).elim)
  exact congrArg (fun J : Lp ℝ 2 (ℱ.predictableMeasure P 0) →L[ℝ] Lp ℝ 2 P ↦ J f) hz.symm

/-- Replacing the integrator by an a.e.-equal process on the horizon preserves the integral. -/
theorem l2Integral_congr {B : ℝ≥0 → Ω → ℝ}
    (hB : IsFilteredPreBrownianReal ℱ B P) (hW : IsFilteredPreBrownianReal ℱ W P)
    {T : ℝ≥0} (h : ∀ t ≤ T, B t =ᵐ[P] W t) : hB.l2Integral T = hW.l2Integral T := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  apply LinearIsometry.toContinuousLinearMap_injective
  apply hW.l2Integral_unique
  intro s t hst ht A hA
  refine (hB.coeFn_l2Integral_indicatorConstLp_Ioc_prod_of_le hst.le ht hA 1).trans ?_
  filter_upwards [h t ht, h s (hst.le.trans ht)] with ω htω hsω
  simp only [htω, hsω]

/-- Every predictable L² Brownian integral has expectation zero. -/
@[simp]
theorem integral_l2Integral (hW : IsFilteredPreBrownianReal ℱ W P) (T : ℝ≥0)
    (f : Lp ℝ 2 (ℱ.predictableMeasure P T)) : ∫ ω, hW.l2Integral T f ω ∂P = 0 := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  let one : Lp ℝ 2 P := indicatorConstLp 2 MeasurableSet.univ (measure_ne_top _ _) 1
  have hz : (innerSL ℝ one).comp (hW.l2Integral T).toContinuousLinearMap = 0 := by
    apply ContinuousLinearMap.ext_indicatorConstLp_Ioc_prod_predictableMeasure T
    intro s t hst ht A hA
    simp only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
      innerSL_apply_apply, one, L2.inner_indicatorConstLp_one, setIntegral_univ, zero_apply]
    exact (integral_congr_ae
      (hW.coeFn_l2Integral_indicatorConstLp_Ioc_prod_of_le hst.le ht hA 1)).trans
      (hW.integral_mul_sub_eq_zero hst.le (stronglyMeasurable_const.indicator hA))
  have h := congrArg (fun J : Lp ℝ 2 (ℱ.predictableMeasure P T) →L[ℝ] ℝ ↦ J f) hz
  simpa only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    innerSL_apply_apply, one, L2.inner_indicatorConstLp_one, setIntegral_univ, zero_apply] using h

end TauCeti.Probability.IsFilteredPreBrownianReal
