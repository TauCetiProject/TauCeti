/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Dynamics.Ergodic.MeasurePreserving

/-!
# Finiteness along measure-preserving maps

## Main results

* `MeasureTheory.MeasurePreserving.isFiniteMeasure` — a finite source measure makes the target of
  a measure-preserving map finite.
-/

public section

namespace MeasureTheory.MeasurePreserving

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure α} {ν : Measure β} {f : α → β}

/-- A finite source measure makes the target of a measure-preserving map finite. -/
theorem isFiniteMeasure [IsFiniteMeasure μ] (hf : MeasurePreserving f μ ν) : IsFiniteMeasure ν :=
  hf.map_eq ▸ Measure.isFiniteMeasure_map μ f

end MeasureTheory.MeasurePreserving
