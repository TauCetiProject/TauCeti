/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.NNNorm
public import Mathlib.MeasureTheory.VectorMeasure.Variation.Basic
public import TauCeti.MeasureTheory.VectorMeasure.Operations

/-!
# Variation of vector measures under continuous linear maps

Applying a continuous linear map `φ` to the values of a vector measure multiplies its variation
by at most `‖φ‖₊`.

## Main declarations

* `MeasureTheory.VectorMeasure.variation_mapRangeL_le`: `|φ ∘ μ| ≤ ‖φ‖₊ • |μ|`.
-/

public section

open scoped NNReal

namespace MeasureTheory.VectorMeasure

variable {X F F' 𝕜 : Type*} [MeasurableSpace X] [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup F'] [NormedSpace 𝕜 F']

/-- Applying a continuous linear map to the values of a vector measure multiplies its variation
by at most the operator norm of the map. -/
theorem variation_mapRangeL_le (φ : F →L[𝕜] F') (μ : VectorMeasure X F) :
    (mapRangeL φ μ).variation ≤ ‖φ‖₊ • μ.variation := by
  refine variation_le_of_forall_enorm_le fun s _ => ?_
  rw [mapRangeL_apply, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  refine (φ.le_opENorm _).trans ?_
  rw [enorm_eq_nnnorm φ]
  gcongr
  exact enorm_measure_le_variation μ s

end MeasureTheory.VectorMeasure
