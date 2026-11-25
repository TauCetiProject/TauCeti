/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.Topology.Connected.LocallyConnected
public import Mathlib.Topology.LocallyConstant.Basic

/-!
# Averages over connected components

Let `μ` be a measure on a topological space `X`. Replacing a function `f` by its average over the
connected component of each point,

`x ↦ ⨍ y in connectedComponent x, f y ∂μ`,

gives a function which is constant on every connected component, hence locally constant when `X`
is locally connected (`TauCeti.isLocallyConstant_setAverage_connectedComponent`). Subtracting it
normalizes `f` to have integral zero over every component of finite measure
(`TauCeti.setIntegral_connectedComponent_sub_setAverage`).

This normalization is unique among locally constant corrections: a locally constant function whose
integral over a component vanishes is zero there, provided that component has finite measure and
`μ` charges every nonempty open set
(`IsLocallyConstant.apply_eq_zero_of_setIntegral_connectedComponent_eq_zero`). So on a locally
connected space, for such `μ`, two functions which differ by a locally constant function and are
integrable on a component of finite measure agree on that component when their integrals over it
are equal.

These are the measure-theoretic steps in normalizing the primitive of an exact one-form on a
compact manifold, or a Hamiltonian, to have mean zero on each component.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace TauCeti

variable {X E : Type*} [TopologicalSpace X] [MeasurableSpace X] [NormedAddCommGroup E]
  [NormedSpace ℝ E] {μ : Measure X}

/-- The average of a function over the connected component of a point is locally constant in the
point, on a locally connected space. -/
theorem isLocallyConstant_setAverage_connectedComponent [LocallyConnectedSpace X] (f : X → E) :
    IsLocallyConstant fun x ↦ ⨍ y in connectedComponent x, f y ∂μ :=
  IsLocallyConstant.of_constant_on_connected_components fun _ _ hy ↦ by
    rw [connectedComponent_eq hy]

/-- Subtracting from `f` its average over the connected component of each point leaves a function
with integral zero over every connected component of finite measure. -/
theorem setIntegral_connectedComponent_sub_setAverage [OpensMeasurableSpace X] [CompleteSpace E]
    {x : X} (hx : μ (connectedComponent x) ≠ ∞) (f : X → E) :
    ∫ y in connectedComponent x, (f y - ⨍ z in connectedComponent y, f z ∂μ) ∂μ = 0 := by
  rw [setIntegral_congr_fun isClosed_connectedComponent.measurableSet fun y hy ↦ by
    rw [← connectedComponent_eq hy]]
  exact setAverage_sub_setAverage hx f

/-- A locally constant function whose integral over the connected component of `x` vanishes is
zero at `x`, when that component has finite measure and `μ` charges every nonempty open set. -/
theorem _root_.IsLocallyConstant.apply_eq_zero_of_setIntegral_connectedComponent_eq_zero
    [LocallyConnectedSpace X] [OpensMeasurableSpace X] [μ.IsOpenPosMeasure] [CompleteSpace E]
    {g : X → E} (hg : IsLocallyConstant g) {x : X} (hx : μ (connectedComponent x) ≠ ∞)
    (h : ∫ y in connectedComponent x, g y ∂μ = 0) : g x = 0 := by
  rw [setIntegral_congr_fun isClosed_connectedComponent.measurableSet fun y hy ↦
    hg.apply_eq_of_isPreconnected isPreconnected_connectedComponent hy mem_connectedComponent,
    setIntegral_const] at h
  refine (smul_eq_zero.mp h).resolve_left ?_
  exact ENNReal.toReal_ne_zero.mpr
    ⟨(isOpen_connectedComponent.measure_pos μ ⟨x, mem_connectedComponent⟩).ne', hx⟩

end TauCeti
