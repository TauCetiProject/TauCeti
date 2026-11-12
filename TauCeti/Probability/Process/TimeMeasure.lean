/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import TauCeti.MeasureTheory.Function.Lp.ExtendByZero

/-!
# Lebesgue time measure on a finite nonnegative horizon

`TauCeti.Probability.timeMeasure T` is Lebesgue measure on `(0,T]` in nonnegative real
time, obtained by pulling back real Lebesgue measure along the coercion to `ℝ`.
The origin has zero mass. Interval masses and restriction to shorter horizons are
recorded explicitly for time-product measures used in stochastic integration.
-/

public section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace TauCeti.Probability

/-- Lebesgue measure on the finite time horizon `(0,T]`, with no atom at time zero. -/
noncomputable def timeMeasure (T : ℝ≥0) : Measure ℝ≥0 :=
  (Measure.comap ((↑) : ℝ≥0 → ℝ) volume).restrict (Ioc 0 T)

/-- The real-Lebesgue pullback defining the finite-horizon time measure. -/
theorem timeMeasure_def (T : ℝ≥0) :
    timeMeasure T = (Measure.comap ((↑) : ℝ≥0 → ℝ) volume).restrict (Ioc 0 T) :=
  (rfl)

/-- The mass of a measurable time set is its real Lebesgue mass within the horizon. -/
theorem timeMeasure_apply (T : ℝ≥0) {s : Set ℝ≥0} (hs : MeasurableSet s) :
    timeMeasure T s = volume (((↑) : ℝ≥0 → ℝ) '' (s ∩ Ioc 0 T)) := by
  rw [timeMeasure_def, Measure.restrict_apply hs,
    (NNReal.isClosedEmbedding_coe.measurableEmbedding).comap_apply]

/-- A time interval has its Lebesgue length, truncated at the horizon. -/
@[simp]
theorem timeMeasure_Ioc (T s t : ℝ≥0) :
    timeMeasure T (Ioc s t) = ENNReal.ofReal ((min t T : ℝ≥0) - (s : ℝ)) := by
  simp [timeMeasure_apply T measurableSet_Ioc, Ioc_inter_Ioc,
    NNReal.image_coe_Ioc, Real.volume_Ioc]

/-- An initial closed interval has its length clipped at the horizon; time zero is null. -/
@[simp]
theorem timeMeasure_Iic (T t : ℝ≥0) : timeMeasure T (Iic t) = (min t T : ℝ≥0) := by
  rw [timeMeasure_apply T measurableSet_Iic, inter_comm, Ioc_inter_Iic]
  simp [NNReal.image_coe_Ioc, Real.volume_Ioc, min_comm]

/-- The total time mass is the length of the horizon. -/
@[simp]
theorem timeMeasure_univ (T : ℝ≥0) : timeMeasure T univ = T := by
  calc
    timeMeasure T univ = timeMeasure T (Ioc 0 T) := by
      rw [timeMeasure_def, Measure.restrict_apply_univ, Measure.restrict_apply_self]
    _ = T := by simp

/-- Finite time horizons have finite time mass. -/
instance (T : ℝ≥0) : IsFiniteMeasure (timeMeasure T) :=
  ⟨by simp⟩

/-- Almost every time lies in the finite horizon, excluding the origin. -/
theorem ae_mem_Ioc_timeMeasure (T : ℝ≥0) : ∀ᵐ t ∂timeMeasure T, t ∈ Ioc 0 T := by
  rw [timeMeasure_def]
  exact ae_restrict_mem measurableSet_Ioc

/-- The horizon of length zero carries the zero measure. -/
@[simp]
theorem timeMeasure_zero : timeMeasure 0 = 0 := by
  simp [timeMeasure_def]

/-- The initial time carries no mass, independently of the horizon. -/
@[simp]
theorem timeMeasure_singleton_zero (T : ℝ≥0) : timeMeasure T {0} = 0 := by
  simp [timeMeasure_apply T (measurableSet_singleton 0)]

/-- Restricting time measure again clips the horizon to the smaller endpoint. -/
@[simp]
theorem timeMeasure_restrict (T S : ℝ≥0) :
    (timeMeasure T).restrict (Ioc 0 S) = timeMeasure (min S T) := by
  rw [timeMeasure_def, Measure.restrict_restrict measurableSet_Ioc, Ioc_inter_Ioc]
  simp [timeMeasure_def]

/-- Initial-interval indicator classes only depend on the endpoint clipped to the horizon. -/
theorem indicatorConstLp_Iic_min_timeMeasure {E : Type*} [NormedAddCommGroup E]
    (p : ℝ≥0∞) (T t : ℝ≥0) (c : E) :
    indicatorConstLp (μ := timeMeasure T) p (measurableSet_Iic (a := t))
        (measure_ne_top _ _) c =
      indicatorConstLp p (measurableSet_Iic (a := min t T)) (measure_ne_top _ _) c := by
  apply Lp.ext
  filter_upwards [indicatorConstLp_coeFn (μ := timeMeasure T) (p := p)
    (hs := measurableSet_Iic (a := t)) (hμs := measure_ne_top _ _) (c := c),
    indicatorConstLp_coeFn (μ := timeMeasure T) (p := p)
      (hs := measurableSet_Iic (a := min t T)) (hμs := measure_ne_top _ _) (c := c),
    ae_mem_Ioc_timeMeasure T] with u ht hm hu
  rw [ht, hm]
  simp only [indicator_apply, mem_Iic, le_min_iff, hu.2, and_true]

section ExtendLp

variable {𝕜 E : Type*} [NormedRing 𝕜] [NormedAddCommGroup E] [Module 𝕜 E]
  [IsBoundedSMul 𝕜 E] {p : ℝ≥0∞} [Fact (1 ≤ p)] {S T : ℝ≥0}

variable (𝕜) in
/-- Extend a finite-horizon `Lᵖ` function by zero to a longer horizon, isometrically. -/
noncomputable def timeMeasureExtendLp (hST : S ≤ T) :
    Lp E p (timeMeasure S) →ₗᵢ[𝕜] Lp E p (timeMeasure T) :=
  extendByZeroLpₗᵢ 𝕜 (Measure.comap ((↑) : ℝ≥0 → ℝ) volume)
    measurableSet_Ioc (Ioc_subset_Ioc_right hST)

/-- The horizon extension is represented by the indicator of the shorter horizon. -/
theorem coeFn_timeMeasureExtendLp (hST : S ≤ T) (f : Lp E p (timeMeasure S)) :
    ⇑(timeMeasureExtendLp 𝕜 hST f) =ᵐ[timeMeasure T] (Ioc 0 S).indicator ⇑f := by
  exact coeFn_extendByZeroLpₗᵢ 𝕜 measurableSet_Ioc (Ioc_subset_Ioc_right hST) f

/-- Extending an initial-interval indicator within the shorter horizon preserves it. -/
@[simp]
theorem timeMeasureExtendLp_indicatorConstLp_Iic (hST : S ≤ T) {t : ℝ≥0}
    (ht : t ≤ S) (c : E) :
    timeMeasureExtendLp 𝕜 hST
        (indicatorConstLp p (measurableSet_Iic (a := t)) (measure_ne_top _ _) c) =
      indicatorConstLp p (measurableSet_Iic (a := t)) (measure_ne_top _ _) c := by
  have hi : (Ioc 0 S).indicator ⇑(indicatorConstLp (μ := timeMeasure S) p
      (measurableSet_Iic (a := t)) (measure_ne_top _ _) c) =ᵐ[timeMeasure T]
      (Ioc 0 S).indicator ((Iic t).indicator (fun _ ↦ c)) :=
    ae_restrict_of_ae ((ae_eq_restrict_iff_indicator_ae_eq measurableSet_Ioc).mp
      (indicatorConstLp_coeFn (μ := timeMeasure S) (p := p)
        (hs := measurableSet_Iic (a := t)) (hμs := measure_ne_top _ _) (c := c)))
  apply Lp.ext
  filter_upwards [coeFn_timeMeasureExtendLp (𝕜 := 𝕜) hST
    (indicatorConstLp p (measurableSet_Iic (a := t)) (measure_ne_top _ _) c), hi,
    indicatorConstLp_coeFn (μ := timeMeasure T) (p := p)
      (hs := measurableSet_Iic (a := t)) (hμs := measure_ne_top _ _) (c := c),
    ae_mem_Ioc_timeMeasure T] with u he hi hc hu
  rw [he, hi, hc]
  by_cases hut : u ≤ t
  · simp [hut, hu.1, hut.trans ht]
  · simp [hut, indicator_apply]

end ExtendLp

end TauCeti.Probability
