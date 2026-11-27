/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic

/-!
# Strong measurability from distance tests

A function with separable range is strongly measurable if its distance from every
fixed point is measurable. This criterion allows norming scalar evaluations to detect
strong measurability without assuming completeness of the target.
-/

public section

open MeasureTheory Set Metric TopologicalSpace

namespace TauCeti

/-- Strong measurability is equivalent to separability of the range and measurability of
all distance functions. The target need not carry a chosen measurable structure. -/
theorem stronglyMeasurable_iff_measurable_dist {α E : Type*} [MeasurableSpace α]
    [PseudoMetricSpace E] (f : α → E) :
    StronglyMeasurable f ↔ IsSeparable (range f) ∧
      ∀ x, Measurable (fun a ↦ dist (f a) x) := by
  refine ⟨fun hf ↦ ⟨hf.isSeparable_range, fun x ↦ ?_⟩, fun ⟨hs, hd⟩ ↦ ?_⟩
  · exact ((continuous_id.dist continuous_const).comp_stronglyMeasurable hf).measurable
  · have := hs.secondCountableTopology
    let g : α → range f := rangeFactorization f
    borelize ↥(range f)
    have hg : Measurable g := by
      refine measurable_of_isOpen fun U hU ↦ ?_
      let I := {p : range f × ℝ // ball p.1 p.2 ⊆ U}
      have hcover : (⋃ p : I, ball p.val.1 p.val.2) = U := by
        refine Subset.antisymm (iUnion_subset fun p ↦ p.property) ?_
        intro x hx
        obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU x hx
        exact mem_iUnion.mpr ⟨⟨(x, r), hball⟩, mem_ball_self hr⟩
      obtain ⟨t, ht, htc⟩ := eq_open_union_countable
        (fun p : I ↦ ball p.val.1 p.val.2) (fun _ ↦ isOpen_ball)
      simp only [← hcover, ← htc, preimage_iUnion]
      refine MeasurableSet.biUnion ht fun p _ ↦ ?_
      exact measurableSet_lt (hd p.val.1) measurable_const
    exact continuous_subtypeVal.comp_stronglyMeasurable hg.stronglyMeasurable

end TauCeti
