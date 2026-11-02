/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving

/-!
# Quasi-measure-preserving maps with dominated pushforward

A measurable map `f` with `μ.map f ≤ C • ν` is quasi-measure preserving from `μ` to `ν`, since
domination by a multiple implies absolute continuity
(`MeasureTheory.Measure.absolutelyContinuous_of_le_smul`).

## Main declarations

* `MeasureTheory.QuasiMeasurePreserving.of_map_le_smul`: a measurable map whose pushforward is
  dominated by a multiple of `ν` is quasi-measure preserving.
-/

public section

open scoped ENNReal

namespace MeasureTheory

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}
  {f : α → β} {C : ℝ≥0∞}

/-- A measurable map whose pushforward is dominated by a multiple of `ν` is quasi-measure
preserving. -/
theorem QuasiMeasurePreserving.of_map_le_smul (hf : Measurable f) (hmap : μ.map f ≤ C • ν) :
    QuasiMeasurePreserving f μ ν :=
  ⟨hf, Measure.absolutelyContinuous_of_le_smul hmap⟩

end MeasureTheory
