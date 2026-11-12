/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
public import TauCeti.Analysis.Normed.Module.Normalize

/-!
# Measurability of radial projection

This file proves that normalization `x ↦ ‖x‖⁻¹ • x` and the direction map
`TauCeti.sphereDirection e` to the unit sphere are measurable.

## Main results

* `TauCeti.measurable_normalize`: normalization is measurable.
* `TauCeti.measurable_sphereDirection`: the direction map is measurable.
-/

public section

open Metric

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Normalization `x ↦ ‖x‖⁻¹ • x` is measurable. -/
@[fun_prop]
theorem measurable_normalize : Measurable (NormedSpace.normalize : E → E) := by
  unfold NormedSpace.normalize
  fun_prop

/-- The direction map is measurable. -/
@[fun_prop]
theorem measurable_sphereDirection (e : sphere (0 : E) 1) : Measurable (sphereDirection e) := by
  classical
  have h : ((↑) ∘ sphereDirection e : E → E) =
      fun x ↦ if x = 0 then ↑e else NormedSpace.normalize x := by
    ext1 x
    split_ifs with hx
    · simp [hx]
    · exact coe_sphereDirection_of_ne_zero e hx
  rw [← (MeasurableEmbedding.subtype_coe isClosed_sphere.measurableSet).measurable_comp_iff, h]
  exact Measurable.ite (measurableSet_singleton 0) measurable_const measurable_normalize

end TauCeti
