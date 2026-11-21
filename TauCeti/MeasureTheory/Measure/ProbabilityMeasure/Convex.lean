/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Convex combinations of probability measures

Probability measures are closed under convex combinations: for nonnegative extended-real weights
`a + b = 1`, the measure `a • P + b • Q` again has total mass one.
`ProbabilityMeasure.convexComb` bundles this measure, allowing affinity of maps between
probability measures to be stated without rebuilding the probability-measure structure.

## Main results

* `TauCeti.MeasureTheory.isProbabilityMeasure_smul_add_smul` proves that the underlying measure
  has total mass one.
* `MeasureTheory.ProbabilityMeasure.toMeasure_convexComb` identifies the underlying measure.
* `MeasureTheory.ProbabilityMeasure.convexComb_apply` evaluates the combination on any set.
* `MeasureTheory.ProbabilityMeasure.convexComb_zero_left`,
  `MeasureTheory.ProbabilityMeasure.convexComb_zero_right`, and
  `MeasureTheory.ProbabilityMeasure.convexComb_self` simplify degenerate combinations.
* `MeasureTheory.ProbabilityMeasure.convexComb_comm` exchanges the measures and their weights.
-/

public section

noncomputable section

open MeasureTheory

open scoped ENNReal

namespace TauCeti

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α]

/-- **A convex combination of probability measures is a probability measure.** The weights are
arbitrary elements of `ℝ≥0∞` summing to `1`; no separate nonnegativity condition is needed, since
`ℝ≥0∞` has none to impose. -/
theorem isProbabilityMeasure_smul_add_smul {a b : ℝ≥0∞} (hab : a + b = 1) (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] : IsProbabilityMeasure (a • μ + b • ν) :=
  ⟨by simp [hab]⟩

end MeasureTheory

end TauCeti

namespace MeasureTheory

namespace ProbabilityMeasure

variable {α : Type*} [MeasurableSpace α]

/-- The **convex combination** `a • P + b • Q` of two probability measures, for weights summing
to `1`, bundled as a `ProbabilityMeasure`. Its underlying measure is `toMeasure_convexComb`. -/
def convexComb {a b : ℝ≥0∞} (hab : a + b = 1) (P Q : ProbabilityMeasure α) :
    ProbabilityMeasure α :=
  ⟨a • (P : Measure α) + b • (Q : Measure α),
    TauCeti.MeasureTheory.isProbabilityMeasure_smul_add_smul hab _ _⟩

/-- The underlying measure of a convex combination is the combination of the underlying
measures. -/
@[simp]
theorem toMeasure_convexComb {a b : ℝ≥0∞} (hab : a + b = 1) (P Q : ProbabilityMeasure α) :
    (convexComb hab P Q : Measure α) = a • (P : Measure α) + b • (Q : Measure α) :=
  (rfl)

/-- Evaluation of a convex combination on an arbitrary set, with values in `ℝ≥0`. -/
@[simp]
theorem convexComb_apply {a b : ℝ≥0∞} (hab : a + b = 1) (P Q : ProbabilityMeasure α)
    (s : Set α) : convexComb hab P Q s = a.toNNReal * P s + b.toNNReal * Q s := by
  have ha : a ≠ ∞ := (ENNReal.add_ne_top.mp (hab ▸ ENNReal.one_ne_top)).1
  have hb : b ≠ ∞ := (ENNReal.add_ne_top.mp (hab ▸ ENNReal.one_ne_top)).2
  apply ENNReal.coe_injective
  simp [ENNReal.coe_toNNReal ha, ENNReal.coe_toNNReal hb]

/-- A combination with zero weight on the first measure is the second measure. -/
@[simp]
theorem convexComb_zero_left {b : ℝ≥0∞} (hb : 0 + b = 1) (P Q : ProbabilityMeasure α) :
    convexComb hb P Q = Q := by
  have hb' : b = 1 := by simpa using hb
  apply toMeasure_injective
  simp [hb']

/-- A combination with zero weight on the second measure is the first measure. -/
@[simp]
theorem convexComb_zero_right {a : ℝ≥0∞} (ha : a + 0 = 1) (P Q : ProbabilityMeasure α) :
    convexComb ha P Q = P := by
  have ha' : a = 1 := by simpa using ha
  apply toMeasure_injective
  simp [ha']

/-- A convex combination of a probability measure with itself is that measure. -/
@[simp]
theorem convexComb_self {a b : ℝ≥0∞} (hab : a + b = 1) (P : ProbabilityMeasure α) :
    convexComb hab P P = P := by
  apply toMeasure_injective
  simp [← add_smul, hab]

/-- Exchanging both the measures and their weights preserves a convex combination. -/
theorem convexComb_comm {a b : ℝ≥0∞} (hab : a + b = 1) (P Q : ProbabilityMeasure α) :
    convexComb hab P Q = convexComb ((add_comm b a).trans hab) Q P := by
  apply toMeasure_injective
  simp [add_comm]

end ProbabilityMeasure

end MeasureTheory
