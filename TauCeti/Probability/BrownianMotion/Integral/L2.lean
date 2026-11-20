/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Integral.Covariance
public import TauCeti.Probability.Finance.SimpleStrategy.Energy
public import TauCeti.Probability.Process.Predictable.Measure
import TauCeti.Probability.Process.ElementaryDensity
import Mathlib.Analysis.Normed.Operator.Extend
import TauCeti.Analysis.InnerProductSpace.LinearCombination
import TauCeti.MeasureTheory.Function.Lp.Basic
import TauCeti.MeasureTheory.Function.Lp.Indicator
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Function.SimpleFunc.Dense

/-!
# The finite-horizon predictable L² Brownian integral

For a Brownian motion relative to an arbitrary filtration, construct the terminal integral
as a real linear isometry from predictable time-product L² into sample-space L².
On a predictable rectangle `(s,t] × A` its value is `1_A (W_t − W_s)`, with clipping at
the declared horizon; for any square-integrable left-measurable height `ξ` on `(s, t]` it evaluates
to `ξ (W_{max s (min t T)} - W_s)` (`coeFn_l2Integral_indicator_Ioc`,
`coeFn_l2Integral_indicator_Ioc_of_le`), on any nondecreasing trading grid it agrees almost
everywhere with `Finance.simpleGains` (`coeFn_l2Integral_simpleHolding`), and elementary gains
converge in `L²(P)` along any filter of `L²`-approximating simple holdings
(`tendsto_eLpNorm_simpleGains_l2Integral`).
The map is uniquely determined by its elementary rectangle values.
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

open Filter MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal InnerProductSpace Topology

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

private theorem tendsto_of_tendsto_norm_sub_sq_zero {E : Type*} [SeminormedAddCommGroup E]
    {u : ℕ → E} {v : E} (h : Tendsto (fun n ↦ ‖u n - v‖ ^ 2) atTop (𝓝 0)) :
    Tendsto u atTop (𝓝 v) :=
  tendsto_iff_norm_sub_tendsto_zero.2 <| by
    simpa only [Real.sqrt_zero, Real.sqrt_sq (norm_nonneg _)] using h.sqrt

private theorem coeFn_l2Integral_sum_indicatorConstLp_Ioc (hW : IsFilteredPreBrownianReal ℱ W P)
    (T s t : ℝ≥0) (S : Finset ℝ) {A : ℝ → Set Ω} (hA : ∀ c, MeasurableSet[ℱ s] (A c)) :
    letI := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
    letI : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
    hW.l2Integral T (∑ c ∈ S, indicatorConstLp 2 (measurableSet_predictable_Ioc_prod s t (hA c))
      (measure_ne_top _ _) c) =ᵐ[P]
      fun ω ↦ (∑ c ∈ S, (A c).indicator (fun _ ↦ c) ω) * (W (max s (min t T)) ω - W s ω) := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  rw [map_sum]
  filter_upwards [Lp.coeFn_fun_finsetSum S fun c ↦ hW.l2Integral T (indicatorConstLp 2
      (measurableSet_predictable_Ioc_prod s t (hA c)) (measure_ne_top _ _) c),
    (ae_ball_iff S.countable_toSet).2 fun c _ ↦
      hW.coeFn_l2Integral_indicatorConstLp_Ioc_prod T s t (hA c) c] with ω hsum hc
  rw [hsum, Finset.sum_mul]; exact Finset.sum_congr rfl fun c hcS ↦ hc c hcS

/-- The predictable `L²` Brownian integral of a single-interval integrand with an `ℱ s`-measurable
square-integrable height `ξ` on `(s, t]` agrees almost everywhere with
`ξ * (W (max s (min t T)) - W s)`, clipping at the horizon `T`. -/
theorem coeFn_l2Integral_indicator_Ioc (hW : IsFilteredPreBrownianReal ℱ W P)
    (T s t : ℝ≥0) {ξ : Ω → ℝ} (hξ : StronglyMeasurable[ℱ s] ξ) (hξ₂ : MemLp ξ 2 P) :
    letI := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
    hW.l2Integral T ((ℱ.memLp_indicator_Ioc_predictableMeasure P T s t hξ hξ₂).toLp
      (fun p : ℝ≥0 × Ω ↦ (Ioc s t).indicator (fun _ ↦ ξ p.2) p.1)) =ᵐ[P]
      fun ω ↦ ξ ω * (W (max s (min t T)) ω - W s ω) := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  obtain ⟨S, A, hA, hlim_trim⟩ := hξ.exists_seq_finset_indicator_tendsto_eLpNorm
    ENNReal.ofNat_ne_top ((eLpNorm_trim (ℱ.le s) hξ).trans_lt hξ₂.eLpNorm_lt_top)
  let ξn (n : ℕ) (ω : Ω) : ℝ := ∑ c ∈ S n, (A n c).indicator (fun _ ↦ c) ω
  have hξn_m (n : ℕ) : StronglyMeasurable[ℱ s] (ξn n) :=
    Finset.stronglyMeasurable_fun_sum _ fun c _ ↦ stronglyMeasurable_const.indicator (hA n c)
  have hξn_Lp (n : ℕ) : MemLp (ξn n) 2 P :=
    memLp_finsetSum _ fun c _ ↦ (memLp_const c).indicator (ℱ.le s _ (hA n c)).nullMeasurableSet
  have hd_sq : Tendsto (fun n ↦ ∫ ω, (ξn n ω - ξ ω) ^ 2 ∂P) atTop (𝓝 0) := by
    simpa only [Pi.zero_apply, norm_zero, zero_pow two_ne_zero, integral_zero, Pi.sub_apply,
      Real.norm_eq_abs, sq_abs] using tendsto_integral_norm_sq_of_tendsto_eLpNorm_sub MemLp.zero
      (fun n ↦ (hξn_Lp n).sub hξ₂) (by
        simpa only [sub_zero] using
          hlim_trim.congr fun n ↦ eLpNorm_trim (ℱ.le s) ((hξn_m n).sub hξ))
  have hmem := ℱ.memLp_indicator_Ioc_predictableMeasure P T s t hξ hξ₂
  let g (n : ℕ) : Lp ℝ 2 (ℱ.predictableMeasure P T) := ∑ c ∈ S n, indicatorConstLp 2
    (measurableSet_predictable_Ioc_prod s t (hA n c)) (measure_ne_top _ _) c
  have hg_f : Tendsto g atTop (𝓝 (hmem.toLp _)) := tendsto_of_tendsto_norm_sub_sq_zero <| by
    simpa only [mul_zero] using (hd_sq.const_mul ((timeMeasure T).real (Ioc s t))).congr fun n ↦ by
      have hgn := ℱ.memLp_indicator_Ioc_predictableMeasure P T s t (hξn_m n) (hξn_Lp n)
      have hsub := ℱ.memLp_indicator_Ioc_predictableMeasure P T s t
        ((hξn_m n).sub hξ) ((hξn_Lp n).sub hξ₂)
      rw [(Lp.ext ((coeFn_sum_indicatorConstLp_prod (p := 2) (S n) (Ioc s t)
            (fun c ↦ measurableSet_predictable_Ioc_prod s t (hA n c)) (fun _ ↦ measure_ne_top _ _)
            id).trans hgn.coeFn_toLp.symm) : g n = hgn.toLp _), ← MemLp.toLp_sub hgn hmem,
        MemLp.toLp_congr (hgn.sub hmem) hsub
          (.of_forall fun p ↦ by by_cases hp : p.1 ∈ Ioc s t <;> simp [hp])]
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Pi.sub_apply, Real.norm_eq_abs, sq_abs]
        using (ℱ.norm_toLp_indicator_Ioc_rpow P two_ne_zero ENNReal.ofNat_ne_top T s t
          ((hξn_m n).sub hξ) ((hξn_Lp n).sub hξ₂)).symm
  have htar := hW.memLp_mul_sub (le_max_left s (min t T)) hξ hξ₂
  have hIg : Tendsto (fun n ↦ hW.l2Integral T (g n)) atTop (𝓝 (htar.toLp _)) :=
    tendsto_of_tendsto_norm_sub_sq_zero <| by
      simpa only [zero_mul] using
        (hd_sq.mul_const (((max s (min t T) : ℝ≥0) : ℝ) - s)).congr fun n ↦ by
          have hgn := hW.memLp_mul_sub (le_max_left s (min t T)) (hξn_m n) (hξn_Lp n)
          have hdiff := hW.memLp_mul_sub (le_max_left s (min t T))
            ((hξn_m n).sub hξ) ((hξn_Lp n).sub hξ₂)
          rw [(Lp.ext ((hW.coeFn_l2Integral_sum_indicatorConstLp_Ioc T s t (S n) (hA n)).trans
                hgn.coeFn_toLp.symm) : hW.l2Integral T (g n) = hgn.toLp _),
            ← MemLp.toLp_sub hgn htar,
            MemLp.toLp_congr (hgn.sub htar) hdiff (.of_forall fun ω ↦ by simp [sub_mul]),
            hdiff.norm_toLp_sq]
          simpa only [Real.norm_eq_abs, sq_abs, Pi.sub_apply] using
            (hW.integral_sq_mul_sub (le_max_left s (min t T)) ((hξn_m n).sub hξ)).symm
  exact tendsto_nhds_unique (((hW.l2Integral T).continuous.tendsto _).comp hg_f) hIg ▸
    htar.coeFn_toLp

/-- On an interval within the horizon, the predictable `L²` Brownian integral of an
`ℱ s`-measurable square-integrable height `ξ` on `(s, t]` is `ξ * (W t - W s)`. -/
theorem coeFn_l2Integral_indicator_Ioc_of_le (hW : IsFilteredPreBrownianReal ℱ W P)
    {T s t : ℝ≥0} (hst : s ≤ t) (ht : t ≤ T) {ξ : Ω → ℝ}
    (hξ : StronglyMeasurable[ℱ s] ξ) (hξ₂ : MemLp ξ 2 P) :
    letI := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
    hW.l2Integral T ((ℱ.memLp_indicator_Ioc_predictableMeasure P T s t hξ hξ₂).toLp
      (fun p : ℝ≥0 × Ω ↦ (Ioc s t).indicator (fun _ ↦ ξ p.2) p.1)) =ᵐ[P]
      fun ω ↦ ξ ω * (W t ω - W s ω) := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  simpa only [min_eq_left ht, max_eq_right hst] using hW.coeFn_l2Integral_indicator_Ioc T s t hξ hξ₂

/-- On any nondecreasing trading grid with square-integrable left-measurable heights, the
predictable `L²` Brownian integral at horizon `T` agrees almost everywhere with the elementary
gains `Finance.simpleGains`. Path continuity of `W` is not needed. -/
theorem coeFn_l2Integral_simpleHolding (hW : IsFilteredPreBrownianReal ℱ W P)
    {τ : ℕ → ℝ≥0} {n : ℕ} {a : ℕ → Ω → ℝ} (hτ : MonotoneOn τ (Iic n))
    (ha : ∀ i < n, StronglyMeasurable[ℱ (τ i)] (a i)) (ha₂ : ∀ i < n, MemLp (a i) 2 P) (T : ℝ≥0) :
    letI := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
    hW.l2Integral T ((Finance.memLp_simpleHolding_predictableMeasure ha ha₂ T).toLp
      (Function.uncurry (Finance.simpleHolding τ n a))) =ᵐ[P]
      Finance.simpleGains τ n a W T := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  let f (i : Fin n) (p : ℝ≥0 × Ω) := (Ioc (τ i) (τ (i + 1))).indicator (fun _ ↦ a i p.2) p.1
  have hmi (i : Fin n) := ℱ.memLp_indicator_Ioc_predictableMeasure P T (τ i) (τ (i + 1))
    (ha i i.isLt) (ha₂ i i.isLt)
  have hms' : MemLp (fun p ↦ ∑ i : Fin n, f i p) 2 (ℱ.predictableMeasure P T) :=
    memLp_finsetSum Finset.univ fun i _ ↦ hmi i
  rw [(MemLp.toLp_congr (Finance.memLp_simpleHolding_predictableMeasure ha ha₂ T) hms'
      (.of_forall fun ⟨s, ω⟩ ↦ by simp only [f, Function.uncurry_apply_pair,
        Finance.simpleHolding_def, ← Fin.sum_univ_eq_sum_range])).trans
      (hms'.toLp_finsetSum hmi), map_sum]
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ fun i : Fin n ↦ hW.l2Integral T
      ((hmi i).toLp (f i)),
    ae_all_iff.2 fun i : Fin n ↦
      hW.coeFn_l2Integral_indicator_Ioc T (τ i) (τ (i + 1)) (ha i i.isLt)
        (ha₂ i i.isLt)] with ω hfin hi
  rw [hfin, Finance.simpleGains_def, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ ↦ (hi i).trans ?_
  have hle : τ i ≤ τ (i + 1) := hτ i.isLt.le i.isLt (Nat.le_succ i)
  rcases le_total (τ i) T with hiT | hTi
  · rw [min_eq_left hiT, max_eq_right (le_min hle hiT)]
  · rw [min_eq_right hTi, min_eq_right (hTi.trans hle), max_eq_left hTi, sub_self, sub_self]

/-- Along any filter where left-measurable `L²` simple holdings converge in ambient
`(timeMeasure T).prod P`-`L²` norm to a predictable integrand `H` on `(0, T]`, their elementary
gains at `T` converge in `L²(P)` to `hW.l2Integral T`. Neither path continuity of `W` nor uniform
height bounds are needed. -/
theorem tendsto_eLpNorm_simpleGains_l2Integral (hW : IsFilteredPreBrownianReal ℱ W P)
    {ι : Type*} {l : Filter ι} {T : ℝ≥0} {H : ℝ≥0 → Ω → ℝ}
    (hH : IsStronglyPredictable ℱ H)
    (hH₂ : MemLp (Function.uncurry H) 2 ((timeMeasure T).prod P))
    {n : ι → ℕ} {τ : ι → ℕ → ℝ≥0} {a : ι → ℕ → Ω → ℝ}
    (hτ : ∀ m, MonotoneOn (τ m) (Iic (n m)))
    (ha : ∀ m i, i < n m → StronglyMeasurable[ℱ (τ m i)] (a m i))
    (ha₂ : ∀ m i, i < n m → MemLp (a m i) 2 P)
    (hlim : Tendsto (fun m ↦ eLpNorm
      (fun p ↦ Finance.simpleHolding (τ m) (n m) (a m) p.1 p.2 - H p.1 p.2) 2
        ((timeMeasure T).prod P)) l (𝓝 0)) :
    Tendsto (fun m ↦ eLpNorm
      (Finance.simpleGains (τ m) (n m) (a m) W T -
        ⇑(hW.l2Integral T (((ℱ.memLp_predictableMeasure_iff P hH T 2).2 hH₂).toLp
          (Function.uncurry H)))) 2 P) l (𝓝 0) := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  let hHT := (ℱ.memLp_predictableMeasure_iff P hH T 2).2 hH₂
  let g (m : ι) := (Finance.memLp_simpleHolding_predictableMeasure (ha m) (ha₂ m) T).toLp
    (Function.uncurry (Finance.simpleHolding (τ m) (n m) (a m)))
  exact ((Lp.tendsto_Lp_iff_tendsto_eLpNorm' (fun m ↦ hW.l2Integral T (g m)) _).1 <|
    ((hW.l2Integral T).continuous.tendsto _).comp <| (Lp.tendsto_Lp_iff_tendsto_eLpNorm' g _).2 <|
      hlim.congr fun m ↦ (eLpNorm_trim ℱ.predictable_le_prod
        ((Finance.isStronglyPredictable_simpleHolding (ha m)).sub hH)).symm.trans <| by
          rw [← ℱ.predictableMeasure_def]
          exact eLpNorm_congr_ae
            ((Finance.memLp_simpleHolding_predictableMeasure (ha m) (ha₂ m) T).coeFn_toLp.symm.sub
              hHT.coeFn_toLp.symm)).congr fun m ↦ eLpNorm_congr_ae
    ((hW.coeFn_l2Integral_simpleHolding (hτ m) (ha m) (ha₂ m) T).sub EventuallyEq.rfl)

end TauCeti.Probability.IsFilteredPreBrownianReal
