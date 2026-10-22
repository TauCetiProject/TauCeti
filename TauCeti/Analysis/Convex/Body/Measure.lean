/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Body
public import TauCeti.MeasureTheory.Measure.Lebesgue.OrthogonalSlices

/-!
# Volume and projections of convex bodies

`ConvexBody.exists_image_inner_eq_Icc` states that the heights of a positive-volume convex
body along a unit vector form a nondegenerate compact interval.
-/

public section

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace ConvexBody

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The heights of a positive-volume convex body along a unit vector form a nondegenerate
compact interval. -/
theorem exists_image_inner_eq_Icc (K : ConvexBody E) (hK : 0 < volume (K : Set E))
    {e : E} (he : ‖e‖ = 1) :
    ∃ a b : ℝ, a < b ∧ (fun x ↦ ⟪e, x⟫) '' (K : Set E) = Icc a b := by
  have hcont : Continuous fun x : E ↦ ⟪e, x⟫ := by fun_prop
  have hI := eq_Icc_of_connected_compact
    ⟨K.nonempty.image _, K.convex.isPreconnected.image _ hcont.continuousOn⟩
    (K.isCompact.image hcont)
  refine ⟨_, _, lt_of_not_ge fun hle ↦ hK.ne' ?_, hI⟩
  -- Otherwise `K` lies in a hyperplane, which is null.
  have hsub : (K : Set E) ⊆ {x ∈ (K : Set E) | ⟪e, x⟫ = sInf ((fun x ↦ ⟪e, x⟫) '' K)} :=
    fun x hx ↦ by
      have hx' : ⟪e, x⟫ ∈ Icc _ _ := hI ▸ mem_image_of_mem _ hx
      exact ⟨hx, le_antisymm (hx'.2.trans hle) hx'.1⟩
  exact measure_mono_null hsub
    (TauCeti.volume_sep_inner_eq K.isCompact.measurableSet.nullMeasurableSet he _)

end ConvexBody
