/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Functions continuous on a compact set are essentially bounded

A function continuous on a compact set `K` is bounded there, so it lies in `L^∞(μ.restrict s)` for
every measurable `s ⊆ K` (`ContinuousOn.memLp_top_restrict_of_subset_isCompact`). Allowing `s ⊊ K`
covers the usual case of an open interval `(a, b)` inside the compact interval `[a, b]`. This is the
continuous counterpart of Mathlib's `MonotoneOn.memLp_top`, and the restricted-measure counterpart
of `Continuous.memLp_top_of_hasCompactSupport`.
-/

public section

open MeasureTheory Set
open scoped ENNReal

variable {X E : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  [NormedAddCommGroup E]

/-- A function continuous on a compact set `K` is essentially bounded on every measurable
`s ⊆ K`. -/
theorem ContinuousOn.memLp_top_restrict_of_subset_isCompact {f : X → E} {K s : Set X}
    {μ : Measure X}
    (hf : ContinuousOn f K) (hK : IsCompact K) (hs : MeasurableSet s) (hsK : s ⊆ K) :
    MemLp f ∞ (μ.restrict s) := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hf
  refine memLp_top_of_bound (hf.aestronglyMeasurable_of_subset_isCompact hK hs hsK) C ?_
  filter_upwards [ae_restrict_mem hs] with x hx using hC x (hsK hx)
