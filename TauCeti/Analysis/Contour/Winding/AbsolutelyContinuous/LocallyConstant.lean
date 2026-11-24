/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Winding.AbsolutelyContinuous.Basic
public import Mathlib.Topology.LocallyConstant.Basic
import TauCeti.Analysis.Contour.Winding.LocallyConstant

/-!
# Local constancy of winding numbers for absolutely continuous curves

The winding number of a closed absolutely continuous curve is locally constant off its trace,
and is consequently constant on each connected component of the trace complement. In particular,
around an off-curve point where the winding number of an absolutely continuous curve vanishes, it
vanishes on a whole ball that stays off the curve
(`AbsolutelyContinuousOnInterval.exists_ball_windingNumber_zero`): this is the local matching data
that Dixon's argument for the homology form of Cauchy's theorem uses.
-/

public section

open Complex MeasureTheory Set

namespace TauCeti.Contour

/-- The winding number of a closed absolutely continuous curve is locally constant off its trace. -/
theorem _root_.AbsolutelyContinuousOnInterval.isLocallyConstant_windingNumber
    {γ : ℝ → ℂ} {a b : ℝ} (hγ : AbsolutelyContinuousOnInterval γ a b)
    (hclosed : γ a = γ b) :
    IsLocallyConstant (fun z : {z : ℂ // z ∉ γ '' uIcc a b} ↦ windingNumber γ a b z.val) := by
  exact hγ.continuousOn.isLocallyConstant_windingNumber_of_integer
    hγ.intervalIntegrable_deriv_of_finiteDimensional
    (fun _ hz ↦ hγ.exists_int_windingNumber hclosed hz)

/-- The winding number of a closed absolutely continuous curve is constant on each connected
component of the complement of its trace. -/
theorem _root_.AbsolutelyContinuousOnInterval.windingNumber_eq_of_mem_connectedComponentIn
    {γ : ℝ → ℂ} {a b : ℝ} (hγ : AbsolutelyContinuousOnInterval γ a b)
    (hclosed : γ a = γ b) {z w : ℂ}
    (hw : w ∈ connectedComponentIn ((γ '' uIcc a b)ᶜ) z) :
    windingNumber γ a b w = windingNumber γ a b z := by
  exact hγ.continuousOn.windingNumber_eq_of_mem_connectedComponentIn_of_integer
    hγ.intervalIntegrable_deriv_of_finiteDimensional
    (fun _ hz ↦ hγ.exists_int_windingNumber hclosed hz) hw

/-- **The winding number vanishes on a ball around an off-curve null point.** For an absolutely
continuous curve `γ`, if the winding number about an off-curve point `w` is `0`, then it is `0`
throughout a ball around `w` that stays off the curve. No closedness hypothesis is needed: a
vanishing winding number about an off-curve point forces `γ a = γ b`. -/
theorem _root_.AbsolutelyContinuousOnInterval.exists_ball_windingNumber_zero
    {γ : ℝ → ℂ} {w : ℂ} {a b : ℝ} (hγ : AbsolutelyContinuousOnInterval γ a b)
    (hoff : ∀ t ∈ uIcc a b, γ t ≠ w) (hw_zero : windingNumber γ a b w = 0) :
    ∃ ε > 0, ∀ w' ∈ Metric.ball w ε,
      (∀ t ∈ uIcc a b, γ t ≠ w') ∧ windingNumber γ a b w' = 0 := by
  have hw : w ∈ (γ '' uIcc a b)ᶜ := by
    simpa only [mem_compl_iff, mem_image, not_exists, not_and] using hoff
  -- The endpoint-ratio identity `exp (2πi · n) = (γ b - w) / (γ a - w)` at `n = 0`.
  have hclosed : γ a = γ b := by
    simpa [hw_zero, eq_div_iff (sub_ne_zero.mpr (hoff a left_mem_uIcc))] using
      hγ.exp_two_pi_I_mul_windingNumber hw
  -- A ball around `w` inside the open complement of the trace lies in one connected component.
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp
    (isCompact_uIcc.image_of_continuousOn hγ.continuousOn).isClosed.isOpen_compl w hw
  refine ⟨ε, hε, fun w' hw' ↦ ⟨fun t ht heq ↦ hball hw' ⟨t, ht, heq⟩, ?_⟩⟩
  rw [hγ.windingNumber_eq_of_mem_connectedComponentIn hclosed
    ((convex_ball w ε).isPreconnected.subset_connectedComponentIn (Metric.mem_ball_self hε)
      hball hw'), hw_zero]

end TauCeti.Contour
