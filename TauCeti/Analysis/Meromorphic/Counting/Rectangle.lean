/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Meromorphic.Counting.Basic
public import Mathlib.Analysis.Complex.Basic
import TauCeti.Topology.Order.Interval
import Mathlib.Topology.Algebra.Group.Order

/-!
# Height additivity, monotonicity, and right-continuity of rectangle counts

For height additivity, rectangles are closed in their real coordinate and half open in their
imaginary coordinate. A splitting edge above the bottom height belongs to precisely one of the
two pieces, so its divisor multiplicity is counted once, in the lower piece. The counts use
`MeromorphicOn.divisor f U`, which is identically zero unless `f` is meromorphic on `U`: for a
function that is not meromorphic on `U` every count is zero by convention, and no actual zeros are
counted. The containing closed rectangle is compact, which supplies finite divisor support,
including at its edges.

As the upper height increases, the zero count is monotone and locally constant from the
right, even at a height carrying zeros. The symmetric closed-rectangle count has the same
properties as both height bounds expand. In particular both counts are right-continuous.
These facts allow an asymptotic zero-counting formula to pass from heights avoiding zeros to
all heights.
-/

public section

open Set Complex Filter Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {f : ℂ → E} {U : Set ℂ} {σ₁ σ₂ t₁ t₂ t₃ : ℝ}

/-- Divisor support is finite on any region contained in a closed rectangle in its domain. -/
theorem inter_divisor_support_finite_of_subset_reProdIm_Icc {R : Set ℂ}
    (hU : Icc σ₁ σ₂ ×ℂ Icc t₁ t₂ ⊆ U) (hR : R ⊆ Icc σ₁ σ₂ ×ℂ Icc t₁ t₂) :
    (R ∩ Function.support (MeromorphicOn.divisor f U)).Finite :=
  MeromorphicOn.divisor_finite_inter_support_of_isCompact
    (isCompact_Icc.reProdIm isCompact_Icc) hU hR

/-- The positive multiplicities defining a zero count have finite support on any region
contained in a closed rectangle in the divisor domain. -/
theorem zeroCount_support_finite_of_subset_reProdIm_Icc {R : Set ℂ}
    (hU : Icc σ₁ σ₂ ×ℂ Icc t₁ t₂ ⊆ U) (hR : R ⊆ Icc σ₁ σ₂ ×ℂ Icc t₁ t₂) :
    (R ∩ Function.support (fun z ↦ (MeromorphicOn.divisor f U z).toNat)).Finite :=
  zeroCount_support_finite (inter_divisor_support_finite_of_subset_reProdIm_Icc hU hR)

/-- A closed rectangle in the divisor domain has a vertically larger rectangle with finite
support, even when the larger rectangle is not contained in the domain. -/
theorem exists_lt_gt_reProdIm_inter_divisor_support_finite
    (hU : Icc σ₁ σ₂ ×ℂ Icc t₁ t₂ ⊆ U) :
    ∃ a < t₁, ∃ b > t₂,
      ((Icc σ₁ σ₂ ×ℂ Icc a b) ∩ Function.support (MeromorphicOn.divisor f U)).Finite := by
  classical
  by_cases ht : t₁ ≤ t₂
  swap
  · obtain ⟨a, ha₂, ha₁⟩ := exists_between (lt_of_not_ge ht)
    obtain ⟨b, hb₂, hba⟩ := exists_between ha₂
    refine ⟨a, ha₁, b, hb₂, ?_⟩
    rw [reProdIm_eq_empty.mpr (Or.inr (Icc_eq_empty_of_lt hba)), empty_inter]
    exact finite_empty
  choose V hV hfin using fun z hz ↦
    (MeromorphicOn.divisor f U).supportLocallyFiniteWithinDomain z (hU hz)
  obtain ⟨s, hs⟩ := (isCompact_Icc.reProdIm isCompact_Icc).elim_nhds_subcover_nhdsSet'
    (fun z hz ↦ V z hz) hV
  let N := ⋃ z ∈ s, V z.1 z.2
  have hN : (N ∩ Function.support (MeromorphicOn.divisor f U)).Finite := by
    simp only [N, iUnion_inter]
    exact s.finite_toSet.biUnion fun z _ ↦ hfin z.1 z.2
  have hprod : equivRealProdCLM.symm ⁻¹' N ∈
      𝓝ˢ (Icc σ₁ σ₂ ×ˢ Icc t₁ t₂) :=
    equivRealProdCLM.symm.continuous.tendsto_nhdsSet
      (by rintro _ ⟨h₁, h₂⟩; simp [mem_reProdIm, h₁, h₂]) hs
  rw [isCompact_Icc.nhdsSet_prod_eq isCompact_Icc] at hprod
  obtain ⟨A, hA, B, hB, hAB⟩ := Filter.mem_prod_iff.mp hprod
  have hBI : uIcc t₁ t₂ ⊆ interior B := by
    rw [uIcc_of_le ht]
    exact subset_interior_iff_mem_nhdsSet.mpr hB
  obtain ⟨c, d, hcd, hcdB⟩ := isOpen_interior.exists_Ioo_subset_of_uIcc_subset hBI
  rw [uIcc_of_le ht] at hcd
  obtain ⟨a, b, hab, habcd⟩ := isCompact_Icc.exists_Icc_between
    ⟨t₁, left_mem_Icc.mpr ht⟩ hcd
  refine ⟨a, (hab (left_mem_Icc.mpr ht)).1, b, (hab (right_mem_Icc.mpr ht)).2,
    hN.subset fun z hz ↦ ⟨?_, hz.2⟩⟩
  suffices equivRealProdCLM z ∈ equivRealProdCLM.symm ⁻¹' N by
    simpa only [mem_preimage, ContinuousLinearEquiv.symm_apply_apply] using this
  apply hAB
  rw [equivRealProdCLM_apply]
  exact ⟨subset_of_mem_nhdsSet hA hz.1.1, interior_subset (hcdB (habcd hz.1.2))⟩

private theorem rectangle_partition
    (ht12 : t₁ ≤ t₂) (ht23 : t₂ ≤ t₃)
    (hU : Icc σ₁ σ₂ ×ℂ Icc t₁ t₃ ⊆ U) :
    ((Icc σ₁ σ₂ ×ℂ Ioc t₁ t₂) ∪ (Icc σ₁ σ₂ ×ℂ Ioc t₂ t₃) =
      Icc σ₁ σ₂ ×ℂ Ioc t₁ t₃) ∧
    Disjoint (Icc σ₁ σ₂ ×ℂ Ioc t₁ t₂) (Icc σ₁ σ₂ ×ℂ Ioc t₂ t₃) ∧
    ((Icc σ₁ σ₂ ×ℂ Ioc t₁ t₂) ∩ Function.support (MeromorphicOn.divisor f U)).Finite ∧
    ((Icc σ₁ σ₂ ×ℂ Ioc t₂ t₃) ∩ Function.support (MeromorphicOn.divisor f U)).Finite := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp_rw [← preimage_equivRealProd_prod, ← preimage_union, ← prod_union,
      Ioc_union_Ioc_eq_Ioc ht12 ht23]
  · exact disjoint_left.mpr fun z hz hz' ↦
      disjoint_left.mp (Ioc_disjoint_Ioc_of_le le_rfl) hz.2 hz'.2
  · exact inter_divisor_support_finite_of_subset_reProdIm_Icc hU
      (fun z hz ↦ ⟨hz.1, hz.2.1.le, hz.2.2.trans ht23⟩)
  · exact inter_divisor_support_finite_of_subset_reProdIm_Icc hU
      (fun z hz ↦ ⟨hz.1, ht12.trans hz.2.1.le, hz.2.2⟩)

/-- Splitting a half-open rectangle in imaginary height adds the signed counts exactly.
Neither meromorphy nor boundary nonvanishing is required. -/
theorem divisorCount_reProdIm_Ioc_eq_add
    (ht12 : t₁ ≤ t₂) (ht23 : t₂ ≤ t₃)
    (hU : Icc σ₁ σ₂ ×ℂ Icc t₁ t₃ ⊆ U) :
    divisorCount f U (Icc σ₁ σ₂ ×ℂ Ioc t₁ t₃) =
      divisorCount f U (Icc σ₁ σ₂ ×ℂ Ioc t₁ t₂) +
        divisorCount f U (Icc σ₁ σ₂ ×ℂ Ioc t₂ t₃) := by
  obtain ⟨hsplit, hdisjoint, hfirst, hsecond⟩ := rectangle_partition (f := f) ht12 ht23 hU
  rw [← hsplit]
  exact divisorCount_union hdisjoint hfirst hsecond

/-- Splitting a half-open rectangle in imaginary height adds the natural zero counts exactly.
Positive divisor multiplicities on the splitting edge are assigned to the lower piece and counted
only once. If `f` is not meromorphic on `U` the divisor vanishes, so all counts are zero by
convention. -/
theorem zeroCount_reProdIm_Ioc_eq_add
    (ht12 : t₁ ≤ t₂) (ht23 : t₂ ≤ t₃)
    (hU : Icc σ₁ σ₂ ×ℂ Icc t₁ t₃ ⊆ U) :
    zeroCount f U (Icc σ₁ σ₂ ×ℂ Ioc t₁ t₃) =
      zeroCount f U (Icc σ₁ σ₂ ×ℂ Ioc t₁ t₂) +
        zeroCount f U (Icc σ₁ σ₂ ×ℂ Ioc t₂ t₃) := by
  obtain ⟨hsplit, hdisjoint, hfirst, hsecond⟩ := rectangle_partition (f := f) ht12 ht23 hU
  rw [← hsplit]
  exact zeroCount_union hdisjoint (zeroCount_support_finite hfirst)
    (zeroCount_support_finite hsecond)

/-- Increasing the upper height cannot decrease the zero count. Only inclusion of the
closed rectangle up to the larger height in `U` is required. -/
theorem zeroCount_reProdIm_Ioc_le (ht : t₂ ≤ t₃)
    (hU : Icc σ₁ σ₂ ×ℂ Icc t₁ t₃ ⊆ U) :
    zeroCount f U (Icc σ₁ σ₂ ×ℂ Ioc t₁ t₂) ≤
      zeroCount f U (Icc σ₁ σ₂ ×ℂ Ioc t₁ t₃) := by
  refine zeroCount_mono (S := Icc σ₁ σ₂ ×ℂ Ioc t₁ t₃)
    (fun z hz ↦ ⟨hz.1, hz.2.1, hz.2.2.trans ht⟩) ?_
  exact zeroCount_support_finite_of_subset_reProdIm_Icc hU
    (fun z hz ↦ ⟨hz.1, hz.2.1.le, hz.2.2⟩)

/-- A half-open rectangle's zero count is locally constant as its top edge moves to the
right in height. Zeros at height `T` remain counted when `t₁ < T`, and remain excluded
when `T ≤ t₁`. Only the closed rectangle up to `T` must lie in the divisor domain. -/
theorem eventuallyEq_zeroCount_reProdIm_Ioc_nhdsGE (T : ℝ)
    (hU : Icc σ₁ σ₂ ×ℂ Icc t₁ T ⊆ U) :
    (fun t ↦ zeroCount f U (Icc σ₁ σ₂ ×ℂ Ioc t₁ t)) =ᶠ[𝓝[≥] T]
      fun _ ↦ zeroCount f U (Icc σ₁ σ₂ ×ℂ Ioc t₁ T) := by
  obtain ⟨a, ha, b, hb, hfin⟩ :=
    exists_lt_gt_reProdIm_inter_divisor_support_finite (f := f) hU
  apply eventuallyEq_zeroCount_of_eventually_subset (zeroCount_support_finite hfin)
  · filter_upwards [Ico_mem_nhdsGE hb] with t ht
    exact ⟨fun z hz ↦ ⟨hz.1, hz.2.1, hz.2.2.trans ht.1⟩,
      fun z hz ↦ ⟨hz.1, ha.le.trans hz.2.1.le, hz.2.2.trans ht.2.le⟩⟩
  · intro z _
    by_cases hz : z.im ≤ T
    · exact Eventually.of_forall fun _ hzt ↦ ⟨hzt.1, hzt.2.1, hz⟩
    · filter_upwards [Ico_mem_nhdsGE (lt_of_not_ge hz)] with t ht hzt
      exact False.elim ((not_le.mpr ht.2) hzt.2.2)

/-- The natural zero count with its top edge included is right-continuous in height. -/
theorem continuousWithinAt_zeroCount_reProdIm_Ioc_Ici (T : ℝ)
    (hU : Icc σ₁ σ₂ ×ℂ Icc t₁ T ⊆ U) :
    ContinuousWithinAt (fun t ↦ zeroCount f U (Icc σ₁ σ₂ ×ℂ Ioc t₁ t)) (Ici T) T :=
  continuousWithinAt_const.congr_of_eventuallyEq
    (eventuallyEq_zeroCount_reProdIm_Ioc_nhdsGE T hU) rfl

/-- Moving both height bounds of a closed rectangle outward cannot decrease its zero count. -/
theorem zeroCount_reProdIm_Icc_le {s₁ s₂ : ℝ} (h₁ : s₁ ≤ t₁) (h₂ : t₂ ≤ s₂)
    (hU : Icc σ₁ σ₂ ×ℂ Icc s₁ s₂ ⊆ U) :
    zeroCount f U (Icc σ₁ σ₂ ×ℂ Icc t₁ t₂) ≤
      zeroCount f U (Icc σ₁ σ₂ ×ℂ Icc s₁ s₂) :=
  zeroCount_mono (fun _ hz ↦ ⟨hz.1, h₁.trans hz.2.1, hz.2.2.trans h₂⟩)
    (zeroCount_support_finite_of_subset_reProdIm_Icc hU Subset.rfl)

/-- A closed rectangle's zero count stabilizes as its lower and upper height bounds move
outward, with no ordering assumption on the heights. When `t₁ ≤ t₂`, zeros on the original
bottom and top edges remain included. -/
theorem eventuallyEq_zeroCount_reProdIm_Icc_nhdsLE_nhdsGE
    (hU : Icc σ₁ σ₂ ×ℂ Icc t₁ t₂ ⊆ U) :
    (fun p : ℝ × ℝ ↦ zeroCount f U (Icc σ₁ σ₂ ×ℂ Icc p.1 p.2))
      =ᶠ[𝓝[≤] t₁ ×ˢ 𝓝[≥] t₂]
        fun _ ↦ zeroCount f U (Icc σ₁ σ₂ ×ℂ Icc t₁ t₂) := by
  obtain ⟨a, ha, b, hb, hfin⟩ :=
    exists_lt_gt_reProdIm_inter_divisor_support_finite (f := f) hU
  apply eventuallyEq_zeroCount_of_eventually_subset (zeroCount_support_finite hfin)
  · filter_upwards [Filter.Eventually.prod_mk (Ioc_mem_nhdsLE ha) (Ico_mem_nhdsGE hb)] with p hp
    exact ⟨fun z hz ↦ ⟨hz.1, hp.1.2.trans hz.2.1, hz.2.2.trans hp.2.1⟩,
      fun z hz ↦ ⟨hz.1, hp.1.1.le.trans hz.2.1, hz.2.2.trans hp.2.2.le⟩⟩
  · intro z _
    by_cases hlow : t₁ ≤ z.im
    · by_cases hhigh : z.im ≤ t₂
      · exact Eventually.of_forall fun _ hzp ↦ ⟨hzp.1, hlow, hhigh⟩
      · filter_upwards [Filter.Eventually.prod_inr (Ico_mem_nhdsGE (lt_of_not_ge hhigh)) (𝓝[≤] t₁)]
          with p hp hzp
        exact False.elim ((not_le.mpr hp.2) hzp.2.2)
    · filter_upwards [Filter.Eventually.prod_inl (Ioc_mem_nhdsLE (lt_of_not_ge hlow)) (𝓝[≥] t₂)]
        with p hp hzp
      exact False.elim ((not_le.mpr hp.1) hzp.2.1)

/-- The closed-rectangle count is continuous as its bottom and top edges move outward. -/
theorem continuousWithinAt_zeroCount_reProdIm_Icc_Iic_prod_Ici
    (hU : Icc σ₁ σ₂ ×ℂ Icc t₁ t₂ ⊆ U) :
    ContinuousWithinAt (fun p : ℝ × ℝ ↦ zeroCount f U (Icc σ₁ σ₂ ×ℂ Icc p.1 p.2))
      (Iic t₁ ×ˢ Ici t₂) (t₁, t₂) := by
  apply continuousWithinAt_const.congr_of_eventuallyEq _ rfl
  rw [nhdsWithin_prod_eq]
  exact eventuallyEq_zeroCount_reProdIm_Icc_nhdsLE_nhdsGE hU

/-- The symmetric closed-rectangle count stabilizes immediately to the right of every
height. At negative heights the region is empty; at height zero real zeros are retained. -/
theorem eventuallyEq_zeroCount_reProdIm_Icc_neg_nhdsGE (T : ℝ)
    (hU : Icc σ₁ σ₂ ×ℂ Icc (-T) T ⊆ U) :
    (fun t ↦ zeroCount f U (Icc σ₁ σ₂ ×ℂ Icc (-t) t)) =ᶠ[𝓝[≥] T]
      fun _ ↦ zeroCount f U (Icc σ₁ σ₂ ×ℂ Icc (-T) T) :=
  (eventuallyEq_zeroCount_reProdIm_Icc_nhdsLE_nhdsGE hU).comp_tendsto
    (tendsto_neg_nhdsGE.prodMk tendsto_id)

/-- The symmetric closed-rectangle zero count is right-continuous at every height. -/
theorem continuousWithinAt_zeroCount_reProdIm_Icc_neg_Ici (T : ℝ)
    (hU : Icc σ₁ σ₂ ×ℂ Icc (-T) T ⊆ U) :
    ContinuousWithinAt (fun t ↦ zeroCount f U (Icc σ₁ σ₂ ×ℂ Icc (-t) t)) (Ici T) T :=
  continuousWithinAt_const.congr_of_eventuallyEq
    (eventuallyEq_zeroCount_reProdIm_Icc_neg_nhdsGE T hU) rfl

end TauCeti
