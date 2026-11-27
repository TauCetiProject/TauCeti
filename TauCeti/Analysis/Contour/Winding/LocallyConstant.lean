/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.Analysis.Contour.Winding.Number.Basic
public import Mathlib.Topology.LocallyConstant.Basic
import TauCeti.Analysis.Contour.Winding.Continuity

/-!
# The winding number is locally constant off a curve with integer indices

For a curve `γ`, continuous on `Set.uIcc a b` with interval-integrable derivative, whose winding
numbers about the points off its trace are integers, the generalized winding number
`fun w ↦ windingNumber γ a b w`, as a function on the points off the curve, is locally constant
(`ContinuousOn.isLocallyConstant_windingNumber_of_integer`), so it is constant on every connected
component of the curve complement
(`ContinuousOn.windingNumber_eq_of_mem_connectedComponentIn_of_integer`): the winding number is
continuous in the point there, and an integer-valued continuous function is locally constant.

A closed absolutely continuous curve has integer winding numbers off its trace, and the forms for
it, which also cover a piecewise-`C¹` curve and a curve differentiable off a countable set with
integrable derivative, are `AbsolutelyContinuousOnInterval.isLocallyConstant_windingNumber` and
`AbsolutelyContinuousOnInterval.windingNumber_eq_of_mem_connectedComponentIn`.

## Main results

* `ContinuousOn.isLocallyConstant_windingNumber_of_integer` — the winding number is locally
  constant on the complement of a curve with integer indices.
* `ContinuousOn.windingNumber_eq_of_mem_connectedComponentIn_of_integer` — it is constant on each
  connected component of the curve complement.

## Provenance

Adapted from `generalizedWindingNumber_locally_const_of_closed` in `WindingArgDiff.lean` of the
AINTLIB `LeanModularForms` development, restated for a raw `γ : ℝ → ℂ` on an oriented interval with
endpoints `a` and `b`.
-/

public section

open Complex MeasureTheory Set

open scoped Topology

namespace TauCeti.Contour

/-- A continuous curve with interval-integrable derivative and integer winding numbers off its
trace has locally constant winding number on the trace complement. -/
theorem _root_.ContinuousOn.isLocallyConstant_windingNumber_of_integer {γ : ℝ → ℂ} {a b : ℝ}
    (hγ_cont : ContinuousOn γ (uIcc a b))
    (hderiv_int : IntervalIntegrable (deriv γ) volume a b)
    (hint : ∀ z, z ∉ γ '' uIcc a b → ∃ n : ℤ, windingNumber γ a b z = n) :
    IsLocallyConstant
      (fun z : {z : ℂ // z ∉ γ '' uIcc a b} ↦ windingNumber γ a b z.val) := by
  classical
  choose n hn using fun z : {z : ℂ // z ∉ γ '' uIcc a b} ↦ hint z.val z.property
  have hc : Continuous
      (fun z : {z : ℂ // z ∉ γ '' uIcc a b} ↦ windingNumber γ a b z.val) := by
    refine continuous_iff_continuousAt.mpr fun z ↦ ?_
    have havoid : ∀ t ∈ uIcc a b, γ t ≠ z.val := by
      simpa only [mem_image, not_exists, not_and] using z.property
    exact (continuousAt_windingNumber_of_avoidance hγ_cont havoid
      (intervalIntegrable_inv_sub_mul_deriv hγ_cont havoid hderiv_int)).comp
        continuous_subtypeVal.continuousAt
  have hncont : Continuous n := Complex.isClosedEmbedding_intCast.isEmbedding.continuous_iff.mpr
    (by simpa only [Function.comp_def, ← hn] using hc)
  simpa only [Function.comp_def, ← hn] using
    ((IsLocallyConstant.iff_continuous n).mpr hncont).comp (fun k : ℤ ↦ (k : ℂ))

/-- A continuous curve with integrable derivative and integer indices has constant winding
number on every connected component of its trace complement. -/
theorem _root_.ContinuousOn.windingNumber_eq_of_mem_connectedComponentIn_of_integer
    {γ : ℝ → ℂ} {a b : ℝ} (hγ : ContinuousOn γ (uIcc a b))
    (hderiv : IntervalIntegrable (deriv γ) volume a b)
    (hint : ∀ z, z ∉ γ '' uIcc a b → ∃ n : ℤ, windingNumber γ a b z = n)
    {z w : ℂ} (hw : w ∈ connectedComponentIn ((γ '' uIcc a b)ᶜ) z) :
    windingNumber γ a b w = windingNumber γ a b z := by
  have hz : z ∈ (γ '' uIcc a b)ᶜ := by
    by_contra hz
    rw [connectedComponentIn_eq_empty hz] at hw
    exact hw
  rw [connectedComponentIn_eq_image hz] at hw
  obtain ⟨w, hw, rfl⟩ := hw
  exact (hγ.isLocallyConstant_windingNumber_of_integer hderiv hint).apply_eq_of_isPreconnected
    isPreconnected_connectedComponent hw mem_connectedComponent

end TauCeti.Contour
