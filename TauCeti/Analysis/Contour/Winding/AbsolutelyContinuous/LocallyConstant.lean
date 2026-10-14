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
and is consequently constant on each connected component of the trace complement.
-/

public section

open Complex MeasureTheory Set

namespace TauCeti.Contour

/-- The winding number of a closed absolutely continuous curve is locally constant off its trace. -/
theorem _root_.AbsolutelyContinuousOnInterval.isLocallyConstant_windingNumber
    {γ : ℝ → ℂ} {a b : ℝ} (hγ : AbsolutelyContinuousOnInterval γ a b)
    (hclosed : γ a = γ b) :
    IsLocallyConstant (fun z : {z : ℂ // z ∉ γ '' uIcc a b} ↦ windingNumber γ a b z.1) := by
  have h := ContinuousOn.isLocallyConstant_windingNumber_of_integer hγ.continuousOn
    hγ.intervalIntegrable_deriv_of_finiteDimensional fun z hz ↦
      hγ.exists_int_windingNumber hclosed
        (by rintro ⟨t, ht, heq⟩; exact hz t ht heq)
  have heq : (fun z : ℂ ↦ ∀ t ∈ uIcc a b, γ t ≠ z) =
      (fun z : ℂ ↦ z ∉ γ '' uIcc a b) := by
    funext z
    simp only [mem_image, not_exists, not_and]
  rw [heq] at h
  exact h

/-- The winding number of a closed absolutely continuous curve is constant on each connected
component of the complement of its trace. -/
theorem _root_.AbsolutelyContinuousOnInterval.windingNumber_eq_of_mem_connectedComponentIn
    {γ : ℝ → ℂ} {a b : ℝ} (hγ : AbsolutelyContinuousOnInterval γ a b)
    (hclosed : γ a = γ b) {z w : ℂ}
    (hw : w ∈ connectedComponentIn ((γ '' uIcc a b)ᶜ) z) :
    windingNumber γ a b w = windingNumber γ a b z := by
  exact hγ.continuousOn.windingNumber_eq_of_mem_connectedComponentIn_of_integer
    hγ.intervalIntegrable_deriv_of_finiteDimensional
    (fun _ hz ↦ hγ.exists_int_windingNumber hclosed
      (by rintro ⟨t, ht, heq⟩; exact hz t ht heq)) hw

end TauCeti.Contour
