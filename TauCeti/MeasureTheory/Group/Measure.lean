/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.Measure

/-!
# Measures invariant under addition

This file records measure formulas for finite families of disjoint additive translates.  In
lattice-point counting, the formula turns disjoint translates of a fundamental-domain cell into
measure bounds that can be compared with the number of cells. For a subgroup of finite index in a
larger subgroup, the same count reads off the measure of the smaller subgroup from that of the
larger one and the relative index; over a nonarchimedean local field this computes the Haar
measure of a box of ideals inside the box of integers.

## Main results

* `Measure.measure_biUnion_sub_mem`: a finite disjoint union of translates has measure
  equal to the number of translates times the measure of the original set.
* `Subgroup.relIndex_mul_measure`: for `H ≤ K` of finite relative index, the relative index
  times the measure of `H` is the measure of `K`, for any left-invariant measure.
-/

public section

open MeasureTheory Set

namespace TauCeti

variable {E : Type*} [AddGroup E] [MeasurableSpace E] [MeasurableAdd E]

/-- The union of finitely many pairwise disjoint translates of a measurable set has measure equal
to the number of translates times the measure of the set. -/
theorem _root_.MeasureTheory.Measure.measure_biUnion_sub_mem
    (mu : Measure E) [mu.IsAddRightInvariant]
    {G F : Set E} (hFm : MeasurableSet F)
    (hdisj : ∀ w₁ ∈ G, ∀ w₂ ∈ G, w₁ ≠ w₂ →
      Disjoint {y : E | y - w₁ ∈ F} {y : E | y - w₂ ∈ F})
    {T : Finset E} (hT : ↑T ⊆ G) :
    mu (⋃ w ∈ T, {y : E | y - w ∈ F}) = T.card * mu F := by
  rw [measure_biUnion_finset (fun w₁ h₁ w₂ h₂ h ↦ hdisj w₁ (hT h₁) w₂ (hT h₂) h)
    fun w _ ↦ by
      have h : {y : E | y - w ∈ F} = (fun y : E ↦ y + -w) ⁻¹' F := by
        ext y
        simp only [Set.mem_ofPred_eq, Set.mem_preimage, sub_eq_add_neg]
      rw [h]
      exact measurableSet_preimage (measurable_id.add_const (-w)) hFm]
  have htranslate (w : E) : mu {y : E | y - w ∈ F} = mu F := by
    have h : {y : E | y - w ∈ F} = (fun y : E ↦ y + -w) ⁻¹' F := by
      ext y
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, sub_eq_add_neg]
    rw [h, measure_preimage_add_right]
  simp_rw [htranslate]
  simp

end TauCeti

namespace Subgroup

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]

/-- For subgroups `H ≤ K` of finite relative index, the relative index times the measure of `H` is
the measure of `K`, for any left-invariant measure: `K` is the disjoint union of `H.relIndex K`
left translates of `H`. This is `Subgroup.index_mul_measure` relative to `K`. -/
@[to_additive AddSubgroup.relIndex_mul_measure /-- For additive subgroups `H ≤ K` of finite
relative index, the relative index times the measure of `H` is the measure of `K`, for any
left-invariant measure: `K` is the disjoint union of `H.relIndex K` translates of `H`. This is
`AddSubgroup.index_mul_measure` relative to `K`. -/]
theorem relIndex_mul_measure {H K : Subgroup G} (hHK : H ≤ K) (hindex : H.relIndex K ≠ 0)
    (hH : MeasurableSet (H : Set G)) (hK : MeasurableSet (K : Set G)) (μ : Measure G)
    [μ.IsMulLeftInvariant] : H.relIndex K * μ H = μ K := by
  -- Apply `Subgroup.index_mul_measure` in the group `K`, to the pullback of `μ` along `K ↪ G`.
  have : MeasurableMul K :=
    ⟨fun c ↦ ((measurable_const_mul (c : G)).comp measurable_subtype_coe).subtype_mk,
      fun c ↦ ((measurable_mul_const (c : G)).comp measurable_subtype_coe).subtype_mk⟩
  have he : MeasurableEmbedding K.subtype := MeasurableEmbedding.subtype_coe hK
  have := Measure.IsMulLeftInvariant.comap μ he
  have : (H.subgroupOf K).FiniteIndex := ⟨hindex⟩
  have h := (H.subgroupOf K).index_mul_measure (measurable_subtype_coe hH) (μ.comap K.subtype)
  rwa [he.comap_apply, he.comap_apply, image_univ, coe_subgroupOf, coe_subtype,
    image_preimage_eq_inter_range, Subtype.range_coe, inter_eq_left.2 hHK, ← relIndex,
    Subtype.range_coe] at h

end Subgroup
