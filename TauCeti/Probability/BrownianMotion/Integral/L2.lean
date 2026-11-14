/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Integral.Covariance
public import TauCeti.Probability.Process.Predictable.Measure
public import Mathlib.Probability.Martingale.Basic
import TauCeti.Probability.Process.ElementaryDensity
import Mathlib.Analysis.Normed.Operator.Extend
import TauCeti.Analysis.InnerProductSpace.LinearCombination
import TauCeti.MeasureTheory.Function.Lp.Indicator
import TauCeti.Probability.BrownianMotion.Martingale
import TauCeti.Probability.Martingale.ContinuousLimit

/-!
# The finite-horizon predictable L² Brownian integral

For a Brownian motion relative to an arbitrary filtration, construct the terminal integral
as a real linear isometry from predictable time-product L² into sample-space L².
On a predictable rectangle `(s,t] × A` its value is `1_A (W_t − W_s)`, with clipping at
the declared horizon. The map is uniquely determined by these elementary values.
Linearity and the isometry are supplied by the bundled map, not separate operations on
chosen representatives. The result is a terminal-time map on L² classes, not a
time-indexed integral process by itself. With almost-surely continuous Brownian paths,
`exists_continuous_martingale_l2Integral` realizes every terminal integral as the final
value of a predictable, square-integrable, almost-surely continuous martingale, frozen after
the horizon and starting at zero. Continuity holds outside one common null set on the
original raw filtration; no usual conditions or everywhere-continuous raw version are assumed.

The construction uses the overlapping-increment Gram identity and the density of predictable
rectangles, followed by Mathlib's `LinearMap.extendOfIsometry`. The continuous realization
uses `MeasureTheory.exists_continuous_martingale_of_cauchySeq_Lp` on finite linear
combinations of rectangle integrals; conditional L² projection controls intermediate dates.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
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

/-! ## Continuous martingale realization -/

private def Rectangle.process (T : ℝ≥0) (R : Rectangle ℱ) (W : ℝ≥0 → Ω → ℝ)
    (u : ℝ≥0) (ω : Ω) : ℝ :=
  R.height ω * (W (min (max R.s (min R.t T)) u) ω - W (min R.s u) ω)

private theorem Rectangle.process_memLp (hW : IsFilteredPreBrownianReal ℱ W P)
    (T : ℝ≥0) (R : Rectangle ℱ) (u : ℝ≥0) : MemLp (R.process T W u) 2 P := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  unfold Rectangle.process
  by_cases hsu : R.s ≤ u
  · simpa only [min_eq_left hsu] using hW.memLp_mul_sub
      (le_min (le_max_left R.s (min R.t T)) hsu) R.height_measurable R.height_memLp
  · have hus := le_of_not_ge hsu
    have hue : u ≤ max R.s (min R.t T) := hus.trans (le_max_left _ _)
    simpa only [min_eq_right hus, min_eq_right hue, sub_self, mul_zero]
      using (MemLp.zero' : MemLp (fun _ : Ω ↦ (0 : ℝ)) 2 P)

private theorem Rectangle.process_martingale (hW : IsFilteredPreBrownianReal ℱ W P)
    (T : ℝ≥0) (R : Rectangle ℱ) : Martingale (R.process T W) ℱ P := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  have hM := (hW.martingale.const_min (max R.s (min R.t T))).sub
    (hW.martingale.const_min R.s)
  exact hM.mul_left_of_eq_zero (r := R.s)
    (fun u hu ↦ by
      ext ω
      simp [min_eq_right hu, min_eq_right (hu.trans (le_max_left _ _))])
    R.height_measurable (fun u ↦ (R.process_memLp hW T u).integrable (by norm_num))

private theorem Rectangle.process_terminal (hW : IsFilteredPreBrownianReal ℱ W P)
    (T : ℝ≥0) (R : Rectangle ℱ) : R.process T W T =ᵐ[P] increment hW T R := by
  apply EventuallyEq.trans _ (increment_ae hW T R).symm
  apply Eventually.of_forall
  intro ω
  by_cases hs : R.s ≤ T
  · simp only [Rectangle.process, min_eq_left hs,
      min_eq_left (max_le hs (min_le_right _ _))]
  · have hTs := le_of_not_ge hs
    simp [Rectangle.process, hTs]

private theorem Rectangle.process_frozen (T : ℝ≥0) (R : Rectangle ℱ)
    (u : ℝ≥0) (ω : Ω) : R.process T W (min T u) ω = R.process T W u ω := by
  by_cases hs : R.s ≤ T
  · have he : max R.s (min R.t T) ≤ T := max_le hs (min_le_right _ _)
    simp only [Rectangle.process, ← min_assoc, min_eq_left he, min_eq_left hs]
  · simp only [Rectangle.process, max_eq_left ((min_le_right _ _).trans (le_of_not_ge hs)),
      sub_self, mul_zero]

private theorem exists_approximating_martingales (hW : IsFilteredPreBrownianReal ℱ W P)
    (hc : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω)) (T : ℝ≥0)
    (f : Lp ℝ 2 (ℱ.predictableMeasure P T)) :
    ∃ (M : ℕ → ℝ≥0 → Ω → ℝ) (hmem : ∀ n u, MemLp (M n u) 2 P),
      (∀ n, Martingale (M n) ℱ P) ∧
      (∀ n, ∀ᵐ ω ∂P, Continuous (fun u ↦ M n u ω)) ∧
      (∀ n, M n 0 = 0) ∧ (∀ n u, M n (min T u) = M n u) ∧
      Tendsto (fun n ↦ (hmem n T).toLp (M n T)) atTop (𝓝 (hW.l2Integral T f)) := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  let L := Finsupp.linearCombination ℝ (step (ℱ := ℱ) (P := P) T)
  obtain ⟨a, ha, halim⟩ := mem_closure_iff_seq_limit.mp
    (dense_step (ℱ := ℱ) (P := P) T f)
  choose c hca using ha
  have hclim : Tendsto (fun n ↦ L (c n)) atTop (𝓝 f) := by
    simpa only [L, hca] using halim
  let M (n : ℕ) := Finsupp.linearCombination ℝ (fun R : Rectangle ℱ ↦ R.process T W) (c n)
  have hM (n : ℕ) : Martingale (M n) ℱ P := by
    classical
    dsimp only [M, Finsupp.linearCombination_apply, Finsupp.sum]
    exact Finset.sum_induction _ (fun X ↦ Martingale X ℱ P)
      (fun X Y hX hY ↦ hX.add hY) (martingale_zero ℝ ℱ P)
      (fun R _ ↦ (R.process_martingale hW T).smul ((c n) R))
  have hmem (n : ℕ) (u : ℝ≥0) : MemLp (M n u) 2 P := by
    classical
    simpa only [M, Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul] using memLp_finsetSum' (c n).support
        (fun R _ ↦ (R.process_memLp hW T u).const_smul ((c n) R))
  -- Identify the terminal L² classes before using any martingale completion theorem.
  have hterm (n : ℕ) : (hmem n T).toLp (M n T) = hW.l2Integral T (L (c n)) := by
    classical
    apply Lp.ext
    refine (hmem n T).coeFn_toLp.trans ?_
    have hlin := (hW.l2Integral T).toLinearMap.map_finsupp_linearCombination
      (g := step (ℱ := ℱ) (P := P) T) (c n)
    simp only [LinearIsometry.coe_toLinearMap] at hlin
    dsimp only [L]
    rw [hlin]
    have hi : ∀ R ∈ (c n).support, R.process T W T =ᵐ[P]
        hW.l2Integral T (step (P := P) T R) := fun R _ ↦ by
      rw [l2Integral_step]
      exact R.process_terminal hW T
    filter_upwards [(eventually_all_finset (c n).support).mpr hi,
      Lp.coeFn_linearCombination (c n) (fun R ↦ hW.l2Integral T (step T R))] with ω hω hs
    simp only [M, Finsupp.linearCombination_apply, Finsupp.sum, Pi.smul_apply,
      smul_eq_mul, Finset.sum_apply, Function.comp_apply] at hs ⊢
    rw [hs]
    exact Finset.sum_congr rfl fun R hR ↦ congrArg (((c n) R) * ·) (hω R hR)
  have hfrozen (n : ℕ) (u : ℝ≥0) : M n (min T u) = M n u := by
    classical
    ext ω
    simp only [M, Finsupp.linearCombination_apply, Finsupp.sum,
      Pi.smul_apply, Finset.sum_apply, Rectangle.process_frozen]
  have htermLim : Tendsto (fun n ↦ (hmem n T).toLp (M n T)) atTop
      (𝓝 (hW.l2Integral T f)) := by
    simpa only [Function.comp_def, hterm] using
      (hW.l2Integral T).continuous.continuousAt.tendsto.comp hclim
  refine ⟨M, hmem, hM, ?_, ?_, hfrozen, htermLim⟩
  · intro n
    filter_upwards [hc] with ω hω
    classical
    simp only [M, Finsupp.linearCombination_apply, Finsupp.sum,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Rectangle.process]
    exact continuous_finsetSum _ fun R _ ↦ continuous_const.mul
      (continuous_const.mul ((hω.comp (continuous_const.min continuous_id)).sub
        (hω.comp (continuous_const.min continuous_id))))
  · intro n
    classical
    ext ω
    simp [M, Finsupp.linearCombination_apply, Finsupp.sum, Rectangle.process]

/-- Every finite-horizon predictable L² Brownian integral is the terminal value of a
predictable square-integrable martingale with almost-surely continuous paths. The martingale
starts at zero and is frozen after the declared horizon. Path continuity uses one common
sample-full event and requires no completeness or right continuity of the filtration.
This is a continuous realization of the terminal map, not a cross-horizon identification
of separate L² representatives. -/
theorem exists_continuous_martingale_l2Integral (hW : IsFilteredPreBrownianReal ℱ W P)
    (hc : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω)) (T : ℝ≥0)
    (f : Lp ℝ 2 (ℱ.predictableMeasure P T)) :
    ∃ I : ℝ≥0 → Ω → ℝ, Martingale I ℱ P ∧ IsStronglyPredictable ℱ I ∧
      (∀ t, MemLp (I t) 2 P) ∧
      (∀ᵐ ω ∂P, Continuous (fun t ↦ I t ω) ∧ I 0 ω = 0 ∧
        ∀ t, I (min T t) ω = I t ω) ∧ I T =ᵐ[P] hW.l2Integral T f := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  obtain ⟨M, hmem, hM, hcont, hzero, hfrozen, htermLim⟩ :=
    exists_approximating_martingales hW hc T f
  -- Conditional expectation contracts terminal L² errors at every observation time.
  have hcond (n : ℕ) (u : ℝ≥0) : (hmem n u).toLp (M n u) =
      (condExpL2 ℝ ℝ (ℱ.le u) ((hmem n T).toLp (M n T)) : Lp ℝ 2 P) := by
    apply Lp.ext
    refine (hmem n u).coeFn_toLp.trans ?_
    apply EventuallyEq.trans _
      (MemLp.condExpL2_ae_eq_condExp (𝕜 := ℝ) (ℱ.le u) (hmem n T)).symm
    have hm := (hM n).condExp_ae_eq (le_max_right T u)
    have he : M n (max T u) = M n T := by
      rw [← hfrozen, min_eq_left (le_max_left _ _)]
    rw [he] at hm
    exact hm.symm
  have hcau (u : ℝ≥0) : CauchySeq (fun n ↦ (hmem n u).toLp (M n u)) := by
    have h := ((lpMeas ℝ ℝ (ℱ u) 2 P).subtypeL.comp
      (condExpL2 ℝ ℝ (ℱ.le u))).continuous
    have hlim := (h.tendsto (hW.l2Integral T f)).comp htermLim
    have heq : (fun n ↦ (hmem n u).toLp (M n u)) =
        fun n ↦ (condExpL2 ℝ ℝ (ℱ.le u) ((hmem n T).toLp (M n T)) : Lp ℝ 2 P) :=
      funext fun n ↦ hcond n u
    rw [heq]
    exact hlim.cauchySeq
  -- Complete the continuous martingales on the raw filtration, retaining a common path event.
  obtain ⟨I, hI, hp, hlim, -, φ, -, hpath⟩ :=
    exists_continuous_martingale_of_cauchySeq_Lp hM hcont hmem hcau
  refine ⟨I, hI, hp, fun u ↦ (hlim u).1, ?_, ?_⟩
  · filter_upwards [hpath] with ω hω
    refine ⟨hω.1, ?_, fun u ↦ ?_⟩
    · have hz := (hω.2 0).tendsto_at le_rfl
      simp only [hzero, Pi.zero_apply] at hz
      exact tendsto_nhds_unique hz tendsto_const_nhds
    · exact tendsto_nhds_unique ((hω.2 (min T u)).tendsto_at le_rfl)
        (by simpa only [hfrozen] using (hω.2 u).tendsto_at le_rfl)
  · exact tendstoInMeasure_ae_unique
      (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0) (hlim T).2)
      ((tendstoInMeasure_of_tendsto_Lp htermLim).congr
        (fun n ↦ (hmem n T).coeFn_toLp) EventuallyEq.rfl)

end TauCeti.Probability.IsFilteredPreBrownianReal
