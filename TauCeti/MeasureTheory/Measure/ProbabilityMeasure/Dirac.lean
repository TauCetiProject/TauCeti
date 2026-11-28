/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.DiracProba

/-!
# Point masses as probability measures

Mathlib's `MeasureTheory.diracProba_toMeasure_apply'` evaluates the measure underlying the point
mass `diracProba x` on a measurable set. This file evaluates the `ℝ≥0`-valued point mass itself
and computes its push-forward along a measurable map.

## Main declarations

* `MeasureTheory.diracProba_apply'`: the mass of a measurable set under a point mass.
* `MeasureTheory.ProbabilityMeasure.map_diracProba`: the push-forward of a point mass is the
  point mass at the image point.
-/

public section

open scoped NNReal

namespace MeasureTheory

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- The point mass at `x` gives a measurable set `A` mass `1` if `x ∈ A`, and `0` otherwise. -/
@[simp]
theorem diracProba_apply' (x : X) {A : Set X} (hA : MeasurableSet A) :
    diracProba x A = A.indicator 1 x := by
  rw [← ENNReal.coe_inj, ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure,
    diracProba_toMeasure_apply' x hA]
  by_cases hx : x ∈ A <;> simp [hx]

/-- The push-forward of the point mass at `x` along a measurable map `f` is the point mass at
`f x`. -/
@[simp]
theorem ProbabilityMeasure.map_diracProba {f : X → Y} (hf : Measurable f) (x : X) :
    (diracProba x).map f = diracProba (f x) :=
  toMeasure_injective (Measure.map_dirac' hf x)

end MeasureTheory
