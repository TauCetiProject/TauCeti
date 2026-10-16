/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Icc
public import Mathlib.Topology.UnitInterval
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition

import Mathlib.Geometry.Manifold.Algebra.LieGroup

/-!
# Smooth time maps into the unit interval

The reflection `t ↦ 1 - t` is smooth for the manifold-with-boundary structure of the
unit interval. The smooth transition function also gives smooth interval-valued
maps. These support reversal and stationary-time concatenation of smooth isotopies.

The constructions reuse Mathlib’s interval immersion and `Real.smoothTransition`.
-/

public section

open scoped Manifold ContDiff

namespace unitInterval

/-- Time reversal is smooth, including at both endpoints of the unit interval. -/
theorem contMDiff_symm {n : ℕ∞ω} : ContMDiff (𝓡∂ 1) (𝓡∂ 1) n symm := by
  apply contMDiff_iff_comp_subtypeVal_Icc.mpr
  refine ⟨continuous_symm, ?_⟩
  simpa only [Function.comp_def, coe_symm_eq] using
    (contMDiff_const.sub (contMDiff_subtypeVal_Icc (x := 0) (y := 1) (n := n)))

end unitInterval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞ω} {f : M → ℝ}

/-- Applying the smooth transition function gives a smooth map into the unit interval.
This applies to finite regularity and `C^∞`, without asserting analyticity. -/
theorem ContMDiff.smoothTransition (hf : ContMDiff I 𝓘(ℝ) n f) (hn : n ≤ ∞) :
    ContMDiff I (𝓡∂ 1) n (fun x => (⟨Real.smoothTransition (f x),
      Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩ : unitInterval)) := by
  apply contMDiff_iff_comp_subtypeVal_Icc.mpr
  refine ⟨(Real.smoothTransition.continuous.comp hf.continuous).subtype_mk _, ?_⟩
  exact ((Real.smoothTransition.contDiff (n := ⊤)).contMDiff.of_le hn).comp hf

