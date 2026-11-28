/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Log
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Integrability of clipped logarithmic envelopes for `C₀` functions

When `f : C₀(Ω, E)`, `[R1Space Ω]`, `δ > 0`, and `μ` is finite on compact sets
(`IsFiniteMeasureOnCompacts μ`), the clipped logarithmic envelope `TauCeti.logMaxDiv f δ` has
compact support and is therefore `μ`-integrable (`ZeroAtInftyContinuousMap.integrable_logMaxDiv`).
-/

public section

open MeasureTheory
open scoped ZeroAtInfty

namespace ZeroAtInftyContinuousMap

/-- For `f : C₀(Ω, E)`, `δ > 0`, and `[R1Space Ω]`, the clipped logarithmic envelope
`TauCeti.logMaxDiv f δ` is integrable with respect to any measure `μ` finite on compact sets. -/
theorem integrable_logMaxDiv {Ω E : Type*} [TopologicalSpace Ω] [R1Space Ω] [MeasurableSpace Ω]
    [OpensMeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasureOnCompacts μ]
    [SeminormedAddCommGroup E] (f : C₀(Ω, E)) {δ : ℝ} (hδ : 0 < δ) :
    Integrable (TauCeti.logMaxDiv f δ) μ :=
  (TauCeti.continuous_logMaxDiv (map_continuous f) hδ).integrable_of_hasCompactSupport
    (hasCompactSupport_logMaxDiv f hδ)

end ZeroAtInftyContinuousMap
