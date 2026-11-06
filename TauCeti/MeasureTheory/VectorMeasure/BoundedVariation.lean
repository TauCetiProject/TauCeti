/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.VectorMeasure.BoundedVariation
import Mathlib.MeasureTheory.VectorMeasure.IntegrationByParts

/-!
# Derivative vector measures of Stieltjes functions

For a right-continuous monotone function of bounded variation, Mathlib's derivative vector
measure agrees with the positive Stieltjes measure viewed as a signed measure. This identifies
the classical derivative measure of a distribution function, including its atoms and singular
continuous part, with the measure whose distribution function it is.

The comparison uses the existing interval formulas for both constructions and uniqueness of
vector measures from their values on closed intervals.
-/

public section

open MeasureTheory Set

/-- For a Stieltjes function of bounded variation, the classical derivative vector measure
is its positive Stieltjes measure, viewed as a signed measure. In particular this comparison
retains both the jump atoms and any singular continuous part. -/
theorem StieltjesFunction.vectorMeasure_eq_toSignedMeasure
    {α : Type*} [LinearOrder α] [DenselyOrdered α] [TopologicalSpace α] [OrderTopology α]
    [SecondCountableTopology α] [CompactIccSpace α] [MeasurableSpace α] [BorelSpace α]
    (f : StieltjesFunction α) [IsFiniteMeasure f.measure] (hf : BoundedVariationOn f univ) :
    hf.vectorMeasure = f.measure.toSignedMeasure := by
  apply VectorMeasure.ext_of_Icc
  intro a b hab
  rw [hf.vectorMeasure_Icc hab, f.rightLim_eq,
    Measure.toSignedMeasure_apply_measurable measurableSet_Icc, measureReal_def,
    f.measure_Icc, ENNReal.toReal_ofReal]
  exact sub_nonneg.mpr (f.mono.leftLim_le hab)
