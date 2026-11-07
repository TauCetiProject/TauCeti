/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Lebesgue time measure on a finite nonnegative horizon

`TauCeti.Probability.timeMeasure T` is Lebesgue measure on `(0,T]` in nonnegative real
time, obtained by pulling back real Lebesgue measure along the coercion to `ℝ`.
The origin has zero mass. Interval masses and restriction to shorter horizons are
recorded explicitly for time-product measures used in stochastic integration.
-/

public section

open MeasureTheory Set
open scoped NNReal

namespace TauCeti.Probability

/-- Lebesgue measure on the finite time horizon `(0,T]`, with no atom at time zero. -/
noncomputable def timeMeasure (T : ℝ≥0) : Measure ℝ≥0 :=
  (Measure.comap ((↑) : ℝ≥0 → ℝ) volume).restrict (Ioc 0 T)

/-- The real-Lebesgue pullback defining the finite-horizon time measure. -/
theorem timeMeasure_def (T : ℝ≥0) :
    timeMeasure T = (Measure.comap ((↑) : ℝ≥0 → ℝ) volume).restrict (Ioc 0 T) :=
  (rfl)

/-- A time interval has its Lebesgue length, truncated at the horizon. -/
@[simp]
theorem timeMeasure_Ioc (T s t : ℝ≥0) :
    timeMeasure T (Ioc s t) = ENNReal.ofReal ((min t T : ℝ≥0) - (s : ℝ)) := by
  rw [timeMeasure_def, Measure.restrict_apply measurableSet_Ioc, Ioc_inter_Ioc,
    max_eq_left (zero_le : (0 : ℝ≥0) ≤ s),
    (NNReal.isClosedEmbedding_coe.measurableEmbedding).comap_apply,
    NNReal.image_coe_Ioc, Real.volume_Ioc]

/-- The total time mass is the length of the horizon. -/
@[simp]
theorem timeMeasure_univ (T : ℝ≥0) : timeMeasure T univ = T := by
  rw [timeMeasure_def, Measure.restrict_apply_univ,
    (NNReal.isClosedEmbedding_coe.measurableEmbedding).comap_apply,
    NNReal.image_coe_Ioc, Real.volume_Ioc]
  simp

/-- Finite time horizons have finite time mass. -/
instance (T : ℝ≥0) : IsFiniteMeasure (timeMeasure T) :=
  ⟨by simp⟩

/-- The horizon of length zero carries the zero measure. -/
@[simp]
theorem timeMeasure_zero : timeMeasure 0 = 0 := by
  simp [timeMeasure_def]

/-- The initial time carries no mass, independently of the horizon. -/
@[simp]
theorem timeMeasure_singleton_zero (T : ℝ≥0) : timeMeasure T {0} = 0 := by
  rw [timeMeasure_def, Measure.restrict_apply (measurableSet_singleton 0)]
  simp

/-- Restricting time measure again clips the horizon to the smaller endpoint. -/
@[simp]
theorem timeMeasure_restrict (T S : ℝ≥0) :
    (timeMeasure T).restrict (Ioc 0 S) = timeMeasure (min S T) := by
  rw [timeMeasure_def, Measure.restrict_restrict measurableSet_Ioc, Ioc_inter_Ioc]
  simp [timeMeasure_def]

end TauCeti.Probability
