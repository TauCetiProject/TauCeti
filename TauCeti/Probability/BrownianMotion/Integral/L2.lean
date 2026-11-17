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
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp

/-!
# The finite-horizon predictable L² Brownian integral

For a Brownian motion relative to an arbitrary filtration, construct the terminal integral
as a real linear isometry from predictable time-product L² into sample-space L².
On a predictable rectangle `(s,t] × A` its value is `1_A (W_t − W_s)`, with clipping at
the declared horizon. The map is uniquely determined by these elementary values.
Linearity and the isometry are supplied by the bundled map, not separate operations on
chosen representatives. The result is a terminal-time map on L² classes, not a
time-indexed integral process.

For general `L²` `ℱ s`-measurable heights on `(s, t]`, `coeFn_l2Integral_indicator_Ioc_mul` extends
the elementary formula, and `eLpNorm_l2Integral` / `eLpNorm_l2Integral_sub` record `eLpNorm` forms.

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

/-- For `s ≤ t`, `W (max s (min t T)) - W s = W (min t T) - W (min s T)`. -/
private theorem sub_max_min_eq_sub_min {s t : ℝ≥0} (hst : s ≤ t) (T : ℝ≥0) (ω : Ω) :
    W (max s (min t T)) ω - W s ω = W (min t T) ω - W (min s T) ω := by
  by_cases hsT : s ≤ T
  · rw [min_eq_left hsT, max_eq_right (le_min hst hsT)]
  · have hTs := le_of_not_ge hsT
    rw [min_eq_right hTs, min_eq_right (hTs.trans hst), max_eq_left hTs, sub_self, sub_self]

/-- The `L²` seminorm of a left-open interval indicator weighted by a predictable height is bounded
by `(timeMeasure T univ) ^ (1 / 2)` times the `L²(P)` seminorm of the height. -/
private theorem eLpNorm_indicator_Ioc_mul_le [IsFiniteMeasure P] (T s t : ℝ≥0) {g : Ω → ℝ}
    (hg : StronglyMeasurable[ℱ s] g) :
    eLpNorm (fun p : ℝ≥0 × Ω ↦ (Ioc s t).indicator (fun _ ↦ g p.2) p.1) 2
      ((timeMeasure T).prod P) ≤ (timeMeasure T Set.univ) ^ (2 : ℝ)⁻¹ * eLpNorm g 2 P :=
  calc eLpNorm (fun p : ℝ≥0 × Ω ↦ (Ioc s t).indicator (fun _ ↦ g p.2) p.1) 2
        ((timeMeasure T).prod P)
      ≤ eLpNorm (g ∘ Prod.snd) 2 ((timeMeasure T).prod P) :=
        eLpNorm_mono ((ℱ.stronglyMeasurable_predictable_indicator_Ioc_mul s t hg).mono
          ℱ.predictable_le_prod).aestronglyMeasurable
          fun p ↦ by by_cases h : p.1 ∈ Ioc s t <;> simp [h]
    _ = eLpNorm g 2 ((timeMeasure T Set.univ) • P) := by
        rw [← Measure.map_snd_prod,
          eLpNorm_map_measure (hg.mono (ℱ.le s)).aestronglyMeasurable measurable_snd.aemeasurable]
    _ ≤ (timeMeasure T Set.univ) ^ (2 : ℝ)⁻¹ * eLpNorm g 2 P := by
        simpa only [smul_eq_mul, one_div, ENNReal.toReal_inv, ENNReal.toReal_ofNat] using
          eLpNorm_smul_measure_le (timeMeasure T Set.univ) g 2 P

/-- For `s ≤ t'` and `g ∈ L²(P)` `ℱ s`-measurable, `‖g * (W t' - W s)‖₂ = √(t' - s) * ‖g‖₂`. -/
private theorem norm_toLp_mul_sub_eq (hW : IsFilteredPreBrownianReal ℱ W P)
    {s t' : ℝ≥0} (hst' : s ≤ t') {g : Ω → ℝ} (hg : StronglyMeasurable[ℱ s] g) (hg₂ : MemLp g 2 P) :
    ‖(hW.memLp_mul_sub hst' hg hg₂).toLp (fun ω ↦ g ω * (W t' ω - W s ω))‖ =
      √((t' : ℝ) - s) * ‖hg₂.toLp g‖ := by
  have hsq {u : Ω → ℝ} (hu : MemLp u 2 P) : ‖hu.toLp u‖ ^ 2 = ∫ ω, u ω ^ 2 ∂P := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    exact integral_congr_ae (hu.coeFn_toLp.mono fun ω hω ↦ by simp [hω, sq])
  rw [← Real.sqrt_sq (norm_nonneg _), ← Real.sqrt_sq (norm_nonneg (hg₂.toLp g)),
    ← Real.sqrt_mul (sub_nonneg.mpr (NNReal.coe_le_coe.mpr hst'))]
  exact congrArg Real.sqrt <| by rw [hsq, hW.integral_sq_mul_sub hst' hg, ← hsq hg₂, mul_comm]

/-- The predictable L² Brownian integral of a single left-open interval weighted by an arbitrary
square-integrable `ℱ s`-measurable height equals the height times the clipped Brownian increment. -/
theorem coeFn_l2Integral_indicator_Ioc_mul (hW : IsFilteredPreBrownianReal ℱ W P)
    (T : ℝ≥0) {s t : ℝ≥0} (hst : s ≤ t) {ξ : Ω → ℝ}
    (hξ : StronglyMeasurable[ℱ s] ξ) (hξ₂ : MemLp ξ 2 P)
    (hmem : MemLp (fun p : ℝ≥0 × Ω ↦ (Ioc s t).indicator (fun _ ↦ ξ p.2) p.1) 2
      (ℱ.predictableMeasure P T)) :
    hW.l2Integral T (hmem.toLp _) =ᵐ[P] fun ω ↦ ξ ω * (W (min t T) ω - W (min s T) ω) := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  let t' : ℝ≥0 := max s (min t T)
  have hst' : s ≤ t' := le_max_left _ _
  -- Step 1: reduce to `lpMeas ℝ ℝ (ℱ s) 2 P` using an `ℱ s`-measurable representative `mk f`
  -- and compare the `L²` integral `Φ` against the clipped Brownian increment `Ψ`.
  let mk (f : lpMeas ℝ ℝ (ℱ s) 2 P) : Ω → ℝ := (mem_lpMeas_iff_aestronglyMeasurable.mp f.2).mk f
  have hmk_meas (f) : StronglyMeasurable[ℱ s] (mk f) :=
    (mem_lpMeas_iff_aestronglyMeasurable.mp f.2).stronglyMeasurable_mk
  have hmk_ae (f : lpMeas ℝ ℝ (ℱ s) 2 P) : ((f : Lp ℝ 2 P) : Ω → ℝ) =ᵐ[P] mk f :=
    (mem_lpMeas_iff_aestronglyMeasurable.mp f.2).ae_eq_mk
  have hmk_memLp (f) : MemLp (mk f) 2 P := (Lp.memLp (f : Lp ℝ 2 P)).ae_eq (hmk_ae f)
  have hmk_add (f g) : mk (f + g) =ᵐ[P] fun ω ↦ mk f ω + mk g ω :=
    (hmk_ae (f + g)).symm.trans ((Lp.coeFn_add (f : Lp ℝ 2 P) g).trans ((hmk_ae f).add (hmk_ae g)))
  have htoP (f) := ℱ.memLp_predictableMeasure_indicator_Ioc_mul T s t (hmk_meas f) (hmk_memLp f)
  have hΨm (f) := hW.memLp_mul_sub hst' (hmk_meas f) (hmk_memLp f)
  let Φ (f : lpMeas ℝ ℝ (ℱ s) 2 P) : Lp ℝ 2 P := hW.l2Integral T ((htoP f).toLp _)
  let Ψ (f : lpMeas ℝ ℝ (ℱ s) 2 P) : Lp ℝ 2 P := (hΨm f).toLp _
  -- Step 2: additivity and operator bounds (hence continuity) of `Φ` and `Ψ`.
  have hΦ_add (f g) : Φ (f + g) = Φ f + Φ g := by
    dsimp only [Φ]; rw [← map_add]; congr 1; apply Lp.ext
    filter_upwards [(htoP (f + g)).coeFn_toLp, Lp.coeFn_add ((htoP f).toLp _) ((htoP g).toLp _),
      (htoP f).coeFn_toLp, (htoP g).coeFn_toLp,
      ℱ.ae_eq_predictableMeasure_indicator_Ioc_mul T s t (hmk_meas (f + g))
        ((hmk_meas f).add (hmk_meas g)) (hmk_add f g)] with p h1 h2 h3 h4 h5
    rw [h1, h2, Pi.add_apply, h3, h4, h5]; by_cases hp : p.1 ∈ Ioc s t <;> simp [hp]
  have hΨ_add (f g) : Ψ (f + g) = Ψ f + Ψ g := by
    apply Lp.ext
    filter_upwards [(hΨm (f + g)).coeFn_toLp, Lp.coeFn_add ((hΨm f).toLp _) ((hΨm g).toLp _),
      (hΨm f).coeFn_toLp, (hΨm g).coeFn_toLp, hmk_add f g] with ω h1 h2 h3 h4 h5
    rw [h1, h2, Pi.add_apply, h3, h4, h5, add_mul]
  have hΦ_bound (f) : ‖Φ f‖ ≤ ((timeMeasure T Set.univ) ^ (2 : ℝ)⁻¹).toReal * ‖f‖ := by
    rw [LinearIsometry.norm_map, Lp.norm_toLp, ℱ.predictableMeasure_def,
      eLpNorm_trim ℱ.predictable_le_prod
        (ℱ.stronglyMeasurable_predictable_indicator_Ioc_mul s t (hmk_meas f)),
      show ‖f‖ = (eLpNorm (mk f) 2 P).toReal by
        rw [← Submodule.norm_coe f, Lp.norm_def, eLpNorm_congr_ae (hmk_ae f)], ← ENNReal.toReal_mul]
    exact ENNReal.toReal_mono (ENNReal.mul_ne_top (by finiteness) (hmk_memLp f).eLpNorm_ne_top)
      (eLpNorm_indicator_Ioc_mul_le T s t (hmk_meas f))
  have hΨ_bound (f) : ‖Ψ f‖ ≤ √((t' : ℝ) - s) * ‖f‖ := le_of_eq <| by
    rw [hW.norm_toLp_mul_sub_eq hst' (hmk_meas f) (hmk_memLp f), ← Submodule.norm_coe f]
    exact congrArg (√((t' : ℝ) - s) * norm ·)
      (Lp.ext ((hmk_memLp f).coeFn_toLp.trans (hmk_ae f).symm))
  -- Step 3: verify `Φ = Ψ` on `ℱ s`-measurable indicators, then extend by additivity and closure.
  have hΦΨ : ∀ g : Lp ℝ 2 P, AEStronglyMeasurable[ℱ s] g P →
      ∀ hg : g ∈ lpMeas ℝ ℝ (ℱ s) 2 P, Φ ⟨g, hg⟩ = Ψ ⟨g, hg⟩ :=
    Lp.induction_stronglyMeasurable (ℱ.le s) (by norm_num)
      (fun g ↦ ∀ hg : g ∈ lpMeas ℝ ℝ (ℱ s) 2 P, Φ ⟨g, hg⟩ = Ψ ⟨g, hg⟩)
      (fun c A hA hμA hg ↦ by
        let fc : lpMeas ℝ ℝ (ℱ s) 2 P := ⟨_, hg⟩
        have hfc_ae : mk fc =ᵐ[P] A.indicator (fun _ ↦ c) := (hmk_ae fc).symm.trans <| by
          rw [show (fc : Lp ℝ 2 P) = indicatorConstLp 2 (ℱ.le s A hA) hμA.ne c from
            Lp.simpleFunc.coe_indicatorConst _ _ _]; exact indicatorConstLp_coeFn
        have hEq : (htoP fc).toLp _ = indicatorConstLp 2
            (measurableSet_predictable_Ioc_prod s t hA) (measure_ne_top _ _) c := by
          apply Lp.ext
          filter_upwards [(htoP fc).coeFn_toLp, indicatorConstLp_coeFn (p := 2) (c := c)
              (hs := measurableSet_predictable_Ioc_prod s t hA) (hμs := measure_ne_top _ _),
            ℱ.ae_eq_predictableMeasure_indicator_Ioc_mul T s t (hmk_meas fc)
              (stronglyMeasurable_const.indicator hA) hfc_ae] with p h1 h2 h3
          rw [h1, h2, h3]
          by_cases h1' : p.1 ∈ Ioc s t <;> by_cases h2' : p.2 ∈ A <;> simp [h1', h2']
        apply Lp.ext
        filter_upwards [Lp.ext_iff.mp (congrArg (hW.l2Integral T) hEq),
          hW.coeFn_l2Integral_indicatorConstLp_Ioc_prod T s t hA c, (hΨm fc).coeFn_toLp, hfc_ae]
          with ω h1 h2 h3 h4
        dsimp only [Φ, Ψ]; rw [h1, h2, h3, h4])
      (fun f g hf hg hfm hgm _ h1 h2 hfg ↦ by
        have hmem_lp {u : Ω → ℝ} (hu : MemLp u 2 P) (hum : StronglyMeasurable[ℱ s] u) :
            hu.toLp u ∈ lpMeas ℝ ℝ (ℱ s) 2 P := mem_lpMeas_iff_aestronglyMeasurable.mpr <|
          hum.aestronglyMeasurable.congr hu.coeFn_toLp.symm
        rw [show (⟨hf.toLp f + hg.toLp g, hfg⟩ : lpMeas ℝ ℝ (ℱ s) 2 P) =
            ⟨_, hmem_lp hf hfm⟩ + ⟨_, hmem_lp hg hgm⟩ from Subtype.ext rfl,
          hΦ_add, hΨ_add, h1 _, h2 _])
      (by
        convert isClosed_eq
          (AddMonoidHomClass.continuous_of_bound (AddMonoidHom.mk' Φ hΦ_add) _ hΦ_bound)
          (AddMonoidHomClass.continuous_of_bound (AddMonoidHom.mk' Ψ hΨ_add) _ hΨ_bound) using 1
        ext f; exact ⟨fun h ↦ h f.2, fun h _ ↦ h⟩)
  -- Step 4: apply `Φ = Ψ` to the class of `ξ` and rewrite the clipped Brownian increment.
  have hfξ_mem : hξ₂.toLp ξ ∈ lpMeas ℝ ℝ (ℱ s) 2 P :=
    mem_lpMeas_iff_aestronglyMeasurable.mpr (hξ.aestronglyMeasurable.congr hξ₂.coeFn_toLp.symm)
  let fξ : lpMeas ℝ ℝ (ℱ s) 2 P := ⟨hξ₂.toLp ξ, hfξ_mem⟩
  have hfξ_ae : mk fξ =ᵐ[P] ξ := (hmk_ae fξ).symm.trans hξ₂.coeFn_toLp
  have hL : hmem.toLp _ = (htoP fξ).toLp _ := Lp.ext (hmem.coeFn_toLp.trans
    ((ℱ.ae_eq_predictableMeasure_indicator_Ioc_mul T s t (hmk_meas fξ) hξ hfξ_ae).symm.trans
      (htoP fξ).coeFn_toLp.symm))
  filter_upwards [Lp.ext_iff.mp ((congrArg (hW.l2Integral T) hL).trans
      (hΦΨ _ (mem_lpMeas_iff_aestronglyMeasurable.mp hfξ_mem) hfξ_mem)),
    (hΨm fξ).coeFn_toLp, hfξ_ae] with ω h1 h2 h3
  dsimp only [Ψ] at h1; rw [h1, h2, h3, sub_max_min_eq_sub_min hst T ω]

/-- The `L²(P)` seminorm of a finite-horizon predictable L² Brownian integral equals the
time-product `L²` seminorm of its integrand on `(0, t]`. -/
theorem eLpNorm_l2Integral (hW : IsFilteredPreBrownianReal ℱ W P) (t : ℝ≥0)
    {f : ℝ≥0 × Ω → ℝ} (hf : StronglyMeasurable[ℱ.predictable] f)
    (hm : MemLp f 2 (ℱ.predictableMeasure P t)) :
    eLpNorm (hW.l2Integral t (hm.toLp f) : Ω → ℝ) 2 P = eLpNorm f 2 ((timeMeasure t).prod P) := by
  rw [← Lp.eNorm_def, LinearIsometry.eNorm_map, Lp.eNorm_def, eLpNorm_congr_ae hm.coeFn_toLp,
    ℱ.predictableMeasure_def, eLpNorm_trim ℱ.predictable_le_prod hf]

/-- The `L²(P)` distance between two finite-horizon predictable L² Brownian integrals equals the
time-product `L²` distance between their integrands on `(0, t]`. -/
theorem eLpNorm_l2Integral_sub (hW : IsFilteredPreBrownianReal ℱ W P) (t : ℝ≥0)
    {f₁ f₂ : ℝ≥0 × Ω → ℝ} (hf₁ : StronglyMeasurable[ℱ.predictable] f₁)
    (hf₂ : StronglyMeasurable[ℱ.predictable] f₂)
    (hm₁ : MemLp f₁ 2 (ℱ.predictableMeasure P t)) (hm₂ : MemLp f₂ 2 (ℱ.predictableMeasure P t)) :
    eLpNorm ((hW.l2Integral t (hm₁.toLp f₁) : Ω → ℝ) - (hW.l2Integral t (hm₂.toLp f₂) : Ω → ℝ))
      2 P = eLpNorm (f₁ - f₂) 2 ((timeMeasure t).prod P) := by
  rw [← Lp.edist_def, eDist_eq_eNorm_sub, ← map_sub, LinearIsometry.eNorm_map,
    ← eDist_eq_eNorm_sub, Lp.edist_def, eLpNorm_congr_ae (hm₁.coeFn_toLp.sub hm₂.coeFn_toLp),
    ℱ.predictableMeasure_def, eLpNorm_trim ℱ.predictable_le_prod (hf₁.sub hf₂)]

end TauCeti.Probability.IsFilteredPreBrownianReal
