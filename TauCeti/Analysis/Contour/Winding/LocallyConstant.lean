/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.Analysis.Contour.Winding.Number.Basic
public import Mathlib.Topology.LocallyConstant.Basic
public import TauCeti.Analysis.Calculus.ContDiff.PiecewiseC1On
import TauCeti.Analysis.Contour.Winding.Continuity
import TauCeti.Analysis.Contour.Winding.AbsolutelyContinuous.Basic

/-!
# The winding number is locally constant off a closed curve

For a closed curve `γ` (so `γ a = γ b`) that is continuous on `Set.uIcc a b`, differentiable off a
countable set, with interval-integrable derivative, the generalized winding number
`fun w ↦ windingNumber γ a b w`, viewed as a function on the points off the curve, is locally
constant (`isLocallyConstant_windingNumber_of_closed`). As a corollary, the winding number is
constant on every connected component of the curve complement.

This file gives the forms for a curve whose winding numbers off its trace are known to be
integers, for a curve with a countable exceptional set, and for a piecewise-`C¹` curve. The forms
for an absolutely continuous curve are in `Winding/AbsolutelyContinuous/LocallyConstant.lean`;
Dixon's argument for the homology form of Cauchy's theorem uses those, through
`AbsolutelyContinuousOnInterval.exists_ball_windingNumber_zero`.

## Main results

* `TauCeti.Contour.isLocallyConstant_windingNumber_of_closed` — the winding number is locally
  constant on the complement of a closed curve.
* `TauCeti.Contour.windingNumber_eq_of_mem_connectedComponentIn` — the winding number is constant
  on each connected component of the curve complement.
* `TauCeti.IsPiecewiseC1On.windingNumber_eq_of_mem_connectedComponentIn` — the direct
  piecewise-`C¹` form.

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

/-- **The winding number is locally constant off a closed curve.** Let `γ` be a closed curve
(`γ a = γ b`), differentiable off a countable set `P`, continuous on `Set.uIcc a b`, with
interval-integrable derivative. Then, as a function of the point ranging over the complement of the
curve, the generalized winding number `fun w ↦ windingNumber γ a b w` is locally constant. -/
theorem isLocallyConstant_windingNumber_of_closed {γ : ℝ → ℂ} {a b : ℝ} {P : Set ℝ}
    (hclosed : γ a = γ b) (hP : P.Countable) (hγ_cont : ContinuousOn γ (uIcc a b))
    (hγ_diff : ∀ t ∈ Ioo (min a b) (max a b) \ P, DifferentiableAt ℝ γ t)
    (hderiv_int : IntervalIntegrable (fun t ↦ deriv γ t) volume a b) :
    IsLocallyConstant
      (fun w : {w : ℂ // ∀ t ∈ uIcc a b, γ t ≠ w} ↦ windingNumber γ a b w.val) := by
  have hac := hγ_cont.absolutelyContinuousOnInterval_of_hasDerivAt_off_countable hP
    (fun t ht ↦ (hγ_diff t ht).hasDerivAt) hderiv_int
  have h := hγ_cont.isLocallyConstant_windingNumber_of_integer hderiv_int
    (fun _ hz ↦ hac.exists_int_windingNumber hclosed hz)
  -- Reindex by the same point with its equivalent trace-avoidance predicate.
  exact h.comp_continuous (continuous_subtypeVal.subtype_mk
    (fun z ↦ by simpa only [mem_image, not_exists, not_and] using z.property))

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

/-- **The winding number is constant on a connected component of the curve complement.**
For a closed curve that is continuous on `[[a, b]]`, differentiable away from a countable set,
and has interval-integrable derivative, two points in the same connected component of
`ℂ \ γ '' [[a, b]]` have the same winding number.

This is the connected-component form of homotopy invariance in the point: it follows from local
constancy of the integer-valued winding number off the curve. -/
theorem windingNumber_eq_of_mem_connectedComponentIn {γ : ℝ → ℂ} {a b : ℝ} {P : Set ℝ}
    (hclosed : γ a = γ b) (hP : P.Countable) (hγ_cont : ContinuousOn γ (uIcc a b))
    (hγ_diff : ∀ t ∈ Ioo (min a b) (max a b) \ P, DifferentiableAt ℝ γ t)
    (hderiv_int : IntervalIntegrable (fun t ↦ deriv γ t) volume a b)
    {w₀ w₁ : ℂ} (hw₁ : w₁ ∈ connectedComponentIn ((γ '' uIcc a b)ᶜ) w₀) :
    windingNumber γ a b w₁ = windingNumber γ a b w₀ := by
  have hac := hγ_cont.absolutelyContinuousOnInterval_of_hasDerivAt_off_countable hP
    (fun t ht ↦ (hγ_diff t ht).hasDerivAt) hderiv_int
  exact hγ_cont.windingNumber_eq_of_mem_connectedComponentIn_of_integer hderiv_int
    (fun _ hz ↦ hac.exists_int_windingNumber hclosed hz) hw₁

/-- **Piecewise-`C¹` form of componentwise constancy.** For a closed piecewise-`C¹` curve, two
points in the same connected component of the curve complement have the same winding number. -/
theorem _root_.TauCeti.IsPiecewiseC1On.windingNumber_eq_of_mem_connectedComponentIn
    {γ : ℝ → ℂ} {a b : ℝ} (hγ : IsPiecewiseC1On γ a b) (hclosed : γ a = γ b)
    {w₀ w₁ : ℂ} (hw₁ : w₁ ∈ connectedComponentIn ((γ '' uIcc a b)ᶜ) w₀) :
    windingNumber γ a b w₁ = windingNumber γ a b w₀ := by
  obtain ⟨P, hP, hγ_diff⟩ := hγ.exists_countable_differentiableAt
  exact TauCeti.Contour.windingNumber_eq_of_mem_connectedComponentIn hclosed hP
    hγ.continuousOn hγ_diff hγ.intervalIntegrable_deriv hw₁

end TauCeti.Contour
