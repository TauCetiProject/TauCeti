/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Process.TimeMeasure
public import TauCeti.Probability.Process.Predictable
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# The finite-horizon Brownian predictable measure

For a filtration `ℱ`, `ℱ.predictableMeasure P T` is the restriction of Lebesgue-time × `P`
to `(0,T]`, trimmed to the predictable sigma-algebra. No Brownian process, usual conditions,
or completion of the sample space are needed for this construction. Its native `Lp ℝ 2`
space is the expected-square-energy space for Brownian integrands.

The measure agrees with the ambient product measure on predictable sets. In particular,
`(s,t] × A`, with `A` known at `s` and `t ≤ T`, has mass `(t-s) P(A)`. The initial-time
slice has mass zero, and restricting to a shorter horizon commutes with trimming.
Native `lintegral_trim`, `integral_trim`, and `eLpNorm_trim` then identify predictable
integrands' energies and norms with their ambient time-product counterparts.

## References

* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2.
-/

public section

open MeasureTheory Set TauCeti.Probability
open scoped NNReal

namespace MeasureTheory.Filtration

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- The finite-horizon time-product measure on the predictable sigma-algebra.
It is the expected-energy measure for Brownian stochastic integrands. -/
noncomputable def predictableMeasure (ℱ : Filtration ℝ≥0 m) (P : Measure Ω) (T : ℝ≥0) :
    @Measure (ℝ≥0 × Ω) ℱ.predictable :=
  ((timeMeasure T).prod P).trim ℱ.predictable_le_prod

/-- The predictable measure is the trim of the finite-horizon time-product measure. -/
theorem predictableMeasure_def (ℱ : Filtration ℝ≥0 m) (P : Measure Ω) (T : ℝ≥0) :
    ℱ.predictableMeasure P T = ((timeMeasure T).prod P).trim ℱ.predictable_le_prod :=
  (rfl)

/-- On predictable sets, trimming does not change time-product mass. -/
theorem predictableMeasure_apply (ℱ : Filtration ℝ≥0 m) (P : Measure Ω) (T : ℝ≥0)
    {A : Set (ℝ≥0 × Ω)} (hA : MeasurableSet[ℱ.predictable] A) :
    ℱ.predictableMeasure P T A = (timeMeasure T).prod P A := by
  rw [predictableMeasure_def, trim_measurableSet_eq _ hA]

/-- Predictable rectangles have time length times event probability, clipped at the horizon. -/
@[simp]
theorem predictableMeasure_Ioc_prod (ℱ : Filtration ℝ≥0 m) (P : Measure Ω) [SFinite P]
    (T s t : ℝ≥0) {A : Set Ω} (hA : MeasurableSet[ℱ s] A) :
    ℱ.predictableMeasure P T (Ioc s t ×ˢ A) =
      ENNReal.ofReal ((min t T : ℝ≥0) - (s : ℝ)) * P A := by
  rw [predictableMeasure_apply _ _ _ (measurableSet_predictable_Ioc_prod _ _ hA),
    Measure.prod_prod, timeMeasure_Ioc]

/-- At a horizon beyond the right endpoint, a predictable rectangle has its full time length. -/
theorem predictableMeasure_Ioc_prod_of_le (ℱ : Filtration ℝ≥0 m) (P : Measure Ω) [SFinite P]
    {T s t : ℝ≥0} (ht : t ≤ T) {A : Set Ω} (hA : MeasurableSet[ℱ s] A) :
    ℱ.predictableMeasure P T (Ioc s t ×ˢ A) = ENNReal.ofReal ((t : ℝ) - s) * P A := by
  simp [predictableMeasure_Ioc_prod ℱ P T s t hA, min_eq_left ht]

/-- The total predictable mass is the horizon length times the total sample-space mass. -/
@[simp]
theorem predictableMeasure_univ (ℱ : Filtration ℝ≥0 m) (P : Measure Ω) [SFinite P]
    (T : ℝ≥0) : ℱ.predictableMeasure P T univ = T * P univ := by
  rw [predictableMeasure_apply _ _ _ MeasurableSet.univ, ← univ_prod_univ,
    Measure.prod_prod, timeMeasure_univ]

/-- A finite underlying measure gives a finite predictable measure on every finite horizon. -/
instance (ℱ : Filtration ℝ≥0 m) (P : Measure Ω) [IsFiniteMeasure P] (T : ℝ≥0) :
    IsFiniteMeasure (ℱ.predictableMeasure P T) := by
  rw [predictableMeasure_def]
  infer_instance

/-- At horizon zero the predictable measure is zero. -/
@[simp]
theorem predictableMeasure_zero (ℱ : Filtration ℝ≥0 m) (P : Measure Ω) :
    ℱ.predictableMeasure P 0 = 0 := by
  simp [predictableMeasure_def]

/-- There is no predictable mass at the initial time, even when the initial event is nontrivial. -/
@[simp]
theorem predictableMeasure_singleton_zero_prod (ℱ : Filtration ℝ≥0 m) (P : Measure Ω)
    [SFinite P] (T : ℝ≥0) {A : Set Ω} (hA : MeasurableSet[ℱ 0] A) :
    ℱ.predictableMeasure P T ({0} ×ˢ A) = 0 := by
  have hzero : MeasurableSet[ℱ.predictable] ({0} ×ˢ A) := by
    simpa only [NNReal.bot_eq_zero] using measurableSet_predictable_singleton_bot_prod hA
  rw [predictableMeasure_apply _ _ _ hzero, Measure.prod_prod,
    timeMeasure_singleton_zero, zero_mul]

/-- Restricting the predictable measure to `(0,S]` clips its horizon to `min S T`. -/
@[simp]
theorem predictableMeasure_restrict (ℱ : Filtration ℝ≥0 m) (P : Measure Ω) [SFinite P]
    (T S : ℝ≥0) :
    (ℱ.predictableMeasure P T).restrict (Ioc 0 S ×ˢ univ) =
      ℱ.predictableMeasure P (min S T) := by
  have hS : MeasurableSet[ℱ.predictable] (Ioc 0 S ×ˢ (univ : Set Ω)) :=
    measurableSet_predictable_Ioc_prod _ _ MeasurableSet.univ
  rw [predictableMeasure_def, restrict_trim ℱ.predictable_le_prod _ hS,
    ← Measure.restrict_prod_eq_prod_univ, timeMeasure_restrict, predictableMeasure_def]

end MeasureTheory.Filtration
