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
The origin has zero mass. Interval masses, monotonicity in the horizon and restriction to
shorter horizons are recorded explicitly for time-product measures used in stochastic
integration.
The isometry `timeMeasureExtendLp` extends finite-horizon `Lᵖ` functions by zero to
longer horizons. Initial-interval indicator classes depend only on their endpoint
clipped to the horizon; the extension lemmas describe their images.
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

/-- Time measure on a shorter horizon is dominated by time measure on a longer one. -/
theorem timeMeasure_mono {S T : ℝ≥0} (hST : S ≤ T) : timeMeasure S ≤ timeMeasure T := by
  rw [← min_eq_left hST, ← timeMeasure_restrict]
  exact Measure.restrict_le_self

/-- Initial-interval indicator classes only depend on the endpoint clipped to the horizon. -/
theorem indicatorConstLp_Iic_min_timeMeasure {E : Type*} [NormedAddCommGroup E]
    (p : ℝ≥0∞) (T t : ℝ≥0) (c : E) :
    indicatorConstLp (μ := timeMeasure T) p (measurableSet_Iic (a := min t T))
        (measure_ne_top _ _) c =
      indicatorConstLp p (measurableSet_Iic (a := t)) (measure_ne_top _ _) c := by
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
  [IsBoundedSMul 𝕜 E] {p : ℝ≥0∞} [Fact (1 ≤ p)] {S T U : ℝ≥0}

variable (𝕜) in
/-- Extend a finite-horizon `Lᵖ` function by zero to a longer horizon, isometrically. -/
noncomputable def timeMeasureExtendLp (hST : S ≤ T) :
    Lp E p (timeMeasure S) →ₗᵢ[𝕜] Lp E p (timeMeasure T) :=
  extendByZeroLpₗᵢ 𝕜 (Measure.comap ((↑) : ℝ≥0 → ℝ) volume)
    measurableSet_Ioc (Ioc_subset_Ioc_right hST)

/-- The horizon extension agrees `timeMeasure T`-almost everywhere with `f` on
`(0,S]`, extended by zero outside that interval. -/
theorem coeFn_timeMeasureExtendLp (hST : S ≤ T) (f : Lp E p (timeMeasure S)) :
    ⇑(timeMeasureExtendLp 𝕜 hST f) =ᵐ[timeMeasure T] (Ioc 0 S).indicator ⇑f := by
  exact coeFn_extendByZeroLpₗᵢ 𝕜 measurableSet_Ioc (Ioc_subset_Ioc_right hST) f

/-- Extending to the same horizon is the identity. -/
@[simp]
theorem timeMeasureExtendLp_self (f : Lp E p (timeMeasure S)) :
    timeMeasureExtendLp 𝕜 le_rfl f = f :=
  extendByZeroLpₗᵢ_self 𝕜 measurableSet_Ioc f

/-- Two successive horizon extensions equal the direct extension. -/
@[simp]
theorem timeMeasureExtendLp_timeMeasureExtendLp (hST : S ≤ T) (hTU : T ≤ U)
    (f : Lp E p (timeMeasure S)) :
    timeMeasureExtendLp 𝕜 hTU (timeMeasureExtendLp 𝕜 hST f) =
      timeMeasureExtendLp 𝕜 (hST.trans hTU) f :=
  extendByZeroLpₗᵢ_extendByZeroLpₗᵢ 𝕜 measurableSet_Ioc measurableSet_Ioc
    (Ioc_subset_Ioc_right hST) (Ioc_subset_Ioc_right hTU) f

/-- The horizon extension restricts back to the original function almost everywhere. -/
theorem coeFn_timeMeasureExtendLp_restrict (hST : S ≤ T) (f : Lp E p (timeMeasure S)) :
    ⇑(timeMeasureExtendLp 𝕜 hST f) =ᵐ[timeMeasure S] ⇑f :=
  coeFn_extendByZeroLpₗᵢ_restrict 𝕜 measurableSet_Ioc (Ioc_subset_Ioc_right hST) f

/-- Any almost-everywhere representative can be used in the zero-extension formula. -/
theorem coeFn_timeMeasureExtendLp_of_ae_eq (hST : S ≤ T)
    {f : Lp E p (timeMeasure S)} {h : ℝ≥0 → E} (hf : ⇑f =ᵐ[timeMeasure S] h) :
    ⇑(timeMeasureExtendLp 𝕜 hST f) =ᵐ[timeMeasure T] (Ioc 0 S).indicator h :=
  (coeFn_timeMeasureExtendLp hST f).trans
    (ae_restrict_of_ae ((ae_eq_restrict_iff_indicator_ae_eq measurableSet_Ioc).mp hf))

/-- Extending an initial-interval indicator clips its endpoint to the shorter horizon. -/
@[simp]
theorem timeMeasureExtendLp_indicatorConstLp_Iic (hST : S ≤ T) (t : ℝ≥0) (c : E) :
    timeMeasureExtendLp 𝕜 hST
        (indicatorConstLp p (measurableSet_Iic (a := t)) (measure_ne_top _ _) c) =
      indicatorConstLp p (measurableSet_Iic (a := min t S)) (measure_ne_top _ _) c := by
  apply Lp.ext
  filter_upwards [coeFn_timeMeasureExtendLp_of_ae_eq (𝕜 := 𝕜) hST
    (indicatorConstLp_coeFn (p := p) (hs := measurableSet_Iic (a := t))
      (hμs := measure_ne_top _ _) (c := c)),
    indicatorConstLp_coeFn (μ := timeMeasure T) (p := p)
      (hs := measurableSet_Iic (a := min t S)) (hμs := measure_ne_top _ _) (c := c),
    ae_mem_Ioc_timeMeasure T] with u he hc hu
  rw [he, hc]
  simp only [indicator_apply, mem_Ioc, mem_Iic, le_min_iff, hu.1, true_and]
  by_cases hS : u ≤ S <;> by_cases ht : u ≤ t <;> simp [hS, ht]

/-- Extending an interval indicator clips its upper endpoint to the shorter horizon. -/
@[simp]
theorem timeMeasureExtendLp_indicatorConstLp_Ioc (hST : S ≤ T) (s t : ℝ≥0) (c : E) :
    timeMeasureExtendLp 𝕜 hST
        (indicatorConstLp p (measurableSet_Ioc (a := s) (b := t)) (measure_ne_top _ _) c) =
      indicatorConstLp p (measurableSet_Ioc (a := s) (b := min t S))
        (measure_ne_top _ _) c := by
  apply Lp.ext
  filter_upwards [coeFn_timeMeasureExtendLp_of_ae_eq (𝕜 := 𝕜) hST
    (indicatorConstLp_coeFn (p := p) (hs := measurableSet_Ioc (a := s) (b := t))
      (hμs := measure_ne_top _ _) (c := c)),
    indicatorConstLp_coeFn (μ := timeMeasure T) (p := p)
      (hs := measurableSet_Ioc (a := s) (b := min t S))
      (hμs := measure_ne_top _ _) (c := c)] with u he hc
  rw [he, hc, indicator_indicator, Ioc_inter_Ioc]
  simp [min_comm]

end ExtendLp

end TauCeti.Probability
