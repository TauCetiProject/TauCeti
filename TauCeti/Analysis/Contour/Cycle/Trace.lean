/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Cycle.Basic
import TauCeti.Analysis.Contour.AbsolutelyContinuous
import TauCeti.MeasureTheory.Function.AbsolutelyContinuous.Trace
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Null traces of contour cycles

The trace of a contour cycle is a finite union of absolutely continuous curve images and
therefore is null for every additive Haar measure on the complex plane.
-/

public section

open MeasureTheory Set

namespace TauCeti.Contour.Cycle

/-- The trace of an existing contour cycle is null for every additive Haar measure. -/
theorem addHaar_trace_eq_zero (C : Cycle) (μ : Measure ℂ) [μ.IsAddHaarMeasure] :
    μ (trace C) = 0 := by
  have ht : trace C = ⋃ γ ∈ FreeAbelianGroup.support C, γ '' uIcc γ.a γ.b := by
    ext z
    simp only [mem_trace_iff, mem_iUnion, exists_prop]
  rw [ht]
  exact (measure_biUnion_null_iff (FreeAbelianGroup.support C).countable_toSet).mpr fun γ _ ↦
    γ.isPiecewiseC1On.absolutelyContinuousOnInterval.addHaar_image_uIcc_eq_zero μ (by simp)

end TauCeti.Contour.Cycle
