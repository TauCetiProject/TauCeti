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
The preferred interval charts also expose their actual affine coordinate formulas and the
within-range derivatives of the inclusion composed with their inverses.
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

open Set Filter WithLp
open scoped Topology

namespace TauCeti

variable {a b : ℝ} [hab : Fact (a < b)]

/-- Mathlib's actual preferred interval chart is translation on the left and reflection on
the right. This formula holds for every input, independently of chart-source membership. -/
theorem extChartAt_Icc_apply (α x : Icc a b) :
    extChartAt (𝓡∂ 1) α x =
      if (α : ℝ) < b then toLp 2 (fun _ : Fin 1 ↦ (x : ℝ) - a)
      else toLp 2 (fun _ : Fin 1 ↦ b - (x : ℝ)) := by
  rw [extChartAt, Icc_chartedSpaceChartAt]
  split_ifs <;> rfl

/-- Both preferred interval charts have the actual half-open coordinate target `[0,b-a)`. -/
theorem extChartAt_Icc_target (α : Icc a b) :
    (extChartAt (𝓡∂ 1) α).target =
      (fun z : EuclideanSpace ℝ (Fin 1) ↦ z 0) ⁻¹' Ico 0 (b - a) := by
  rw [extChartAt, OpenPartialHomeomorph.extend_target, Icc_chartedSpaceChartAt]
  ext z
  have hab' : 0 < b - a := sub_pos.mpr hab.out
  split_ifs <;> simp [IccLeftChart, IccRightChart,
    modelWithCornersEuclideanHalfSpace_symm_apply, range_modelWithCornersEuclideanHalfSpace,
    max_lt_iff, hab', and_comm]

/-- On the actual coordinate target, the inverse interval chart composed with inclusion is
affine; the model retraction and interval clamps do not alter these values. -/
theorem subtypeVal_extChartAt_Icc_symm (α : Icc a b)
    {z : EuclideanSpace ℝ (Fin 1)} (hz : z ∈ (extChartAt (𝓡∂ 1) α).target) :
    ((extChartAt (𝓡∂ 1) α).symm z : ℝ) =
      if (α : ℝ) < b then z 0 + a else b - z 0 := by
  have hz' : z 0 ∈ Ico 0 (b - a) := by rwa [extChartAt_Icc_target] at hz
  have hnonneg : 0 ≤ z 0 := hz'.1
  have hsmall : z 0 ≤ b - a := hz'.2.le
  rw [extChartAt, OpenPartialHomeomorph.extend_coe_symm, Icc_chartedSpaceChartAt]
  simp only [Function.comp_apply, modelWithCornersEuclideanHalfSpace_symm_apply_of_le hnonneg]
  split_ifs
  · rw [IccLeftChart_symm_apply_of_le hsmall]
  · rw [IccRightChart_symm_apply_of_le hsmall]

/-- The actual inverse interval chart has derivative `+eval₀` in the left chart and
`-eval₀` in the right chart, including derivatives within the half-line at its endpoint. -/
theorem hasFDerivWithinAt_subtypeVal_extChartAt_Icc_symm (α : Icc a b)
    {z : EuclideanSpace ℝ (Fin 1)} (hz : z ∈ (extChartAt (𝓡∂ 1) α).target) :
    HasFDerivWithinAt (fun w ↦ ((extChartAt (𝓡∂ 1) α).symm w : ℝ))
      ((if (α : ℝ) < b then (1 : ℝ) else -1) • EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 1) 0)
      (range (𝓡∂ 1)) z := by
  have heq : (fun w ↦ ((extChartAt (𝓡∂ 1) α).symm w : ℝ)) =ᶠ[𝓝[range (𝓡∂ 1)] z]
      fun w ↦ if (α : ℝ) < b then w 0 + a else b - w 0 := by
    filter_upwards [extChartAt_target_mem_nhdsWithin_of_mem hz] with w hw
    exact subtypeVal_extChartAt_Icc_symm α hw
  have hx := subtypeVal_extChartAt_Icc_symm α hz
  by_cases hα : (α : ℝ) < b
  · simp only [ite_eq_left hα, one_smul] at heq hx ⊢
    exact ((EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 1) 0).hasFDerivAt.add_const a).hasFDerivWithinAt
      |>.congr_of_eventuallyEq heq hx
  · simp only [ite_eq_right hα, neg_smul, one_smul] at heq hx ⊢
    exact ((EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 1) 0).hasFDerivAt.const_sub b).hasFDerivWithinAt
      |>.congr_of_eventuallyEq heq hx

/-- The interval inclusion has its actual signed own-chart derivative. At the right endpoint
the inward half-line coordinate points in the negative real direction. -/
theorem mfderiv_subtypeVal_Icc (x : Icc a b) :
    mfderiv (𝓡∂ 1) 𝓘(ℝ) (Subtype.val : Icc a b → ℝ) x =
      (if (x : ℝ) < b then (1 : ℝ) else -1) •
        EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 1) 0 := by
  apply HasMFDerivAt.mfderiv
  refine ⟨continuous_subtype_val.continuousAt, ?_⟩
  simp only [writtenInExtChartAt, extChartAt_model_space_eq_id, PartialEquiv.refl_coe,
    Function.id_comp]
  convert! hasFDerivWithinAt_subtypeVal_extChartAt_Icc_symm x (mem_extChartAt_target x) using 1

open Fact.Manifold in
/-- Every intrinsic interior point of the interval belongs to its bottom preferred chart. -/
theorem interior_Icc_subset_extChartAt_bot_source :
    (𝓡∂ 1).interior (Icc a b) ⊆ (extChartAt (𝓡∂ 1) (⊥ : Icc a b)).source := by
  intro x hx
  have ht : (x : ℝ) < b := by
    by_contra hn
    have hxb : (x : ℝ) = b := le_antisymm x.property.2 (le_of_not_gt hn)
    have htop : x = (⊤ : Icc a b) := Subtype.ext hxb
    have hnot := ((𝓡∂ 1).isInteriorPoint_iff_not_isBoundaryPoint x).mp hx
    exact hnot (htop ▸ Icc_isBoundaryPoint_top)
  rw [extChartAt_source, Icc_chartedSpaceChartAt_of_le_top (z := (⊥ : Icc a b))
    (by simpa only [Icc.coe_bot] using hab.out)]
  exact ht

end TauCeti
