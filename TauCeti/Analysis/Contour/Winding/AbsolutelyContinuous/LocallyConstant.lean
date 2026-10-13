/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Winding.AbsolutelyContinuous.Basic
public import Mathlib.Topology.LocallyConstant.Basic
import TauCeti.Analysis.Contour.Winding.Continuity

/-!
# Local constancy of winding numbers for absolutely continuous curves

The winding number of a closed absolutely continuous curve is locally constant off its trace,
and is consequently constant on each connected component of the trace complement.
-/

public section

open Complex MeasureTheory Set

namespace TauCeti.Contour

/-- The winding number of a closed absolutely continuous curve is locally constant off its trace. -/
theorem isLocallyConstant_windingNumber_of_absolutelyContinuousOnInterval
    {γ : ℝ → ℂ} {a b : ℝ} (hγ : AbsolutelyContinuousOnInterval γ a b)
    (hclosed : γ a = γ b) :
    IsLocallyConstant (fun z : {z : ℂ // z ∉ γ '' uIcc a b} ↦ windingNumber γ a b z.1) := by
  classical
  choose n hn using fun z : {z : ℂ // z ∉ γ '' uIcc a b} ↦
    exists_int_windingNumber_of_absolutelyContinuousOnInterval hγ hclosed z.2
  have hcont : Continuous (fun z : {z : ℂ // z ∉ γ '' uIcc a b} ↦ windingNumber γ a b z.1) := by
    refine continuous_iff_continuousAt.mpr fun z ↦ ?_
    exact (continuousAt_windingNumber_of_avoidance hγ.continuousOn
      (fun t ht heq ↦ z.2 ⟨t, ht, heq⟩)
      (intervalIntegrable_inv_sub_mul_deriv_of_absolutelyContinuousOnInterval hγ z.2)).comp
      continuous_subtype_val.continuousAt
  have hncont : Continuous n := Complex.isClosedEmbedding_intCast.isEmbedding.continuous_iff.mpr
    (by simpa only [Function.comp_def, ← hn] using hcont)
  simpa only [Function.comp_def, ← hn] using
    ((IsLocallyConstant.iff_continuous n).mpr hncont).comp (fun k : ℤ ↦ (k : ℂ))

/-- The winding number of a closed absolutely continuous curve is constant on each connected
component of the complement of its trace. -/
theorem windingNumber_eq_of_mem_connectedComponentIn_of_absolutelyContinuousOnInterval
    {γ : ℝ → ℂ} {a b : ℝ} (hγ : AbsolutelyContinuousOnInterval γ a b)
    (hclosed : γ a = γ b) {z w : ℂ}
    (hw : w ∈ connectedComponentIn ((γ '' uIcc a b)ᶜ) z) :
    windingNumber γ a b w = windingNumber γ a b z := by
  have hz : z ∈ (γ '' uIcc a b)ᶜ := by
    by_contra hz
    rw [connectedComponentIn_eq_empty hz] at hw
    exact hw
  rw [connectedComponentIn_eq_image hz] at hw
  obtain ⟨w, hw, rfl⟩ := hw
  have hlc := isLocallyConstant_windingNumber_of_absolutelyContinuousOnInterval hγ hclosed
  exact hlc.apply_eq_of_isPreconnected isPreconnected_connectedComponent hw mem_connectedComponent

end TauCeti.Contour
