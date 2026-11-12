/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Meromorphic.Counting.Basic
public import Mathlib.Analysis.Complex.Basic

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
theorem reProdIm_inter_divisor_support_finite {R : Set ℂ}
    (hU : Icc σ₁ σ₂ ×ℂ Icc t₁ t₂ ⊆ U) (hR : R ⊆ Icc σ₁ σ₂ ×ℂ Icc t₁ t₂) :
    (R ∩ Function.support (MeromorphicOn.divisor f U)).Finite :=
  MeromorphicOn.divisor_finite_inter_support_of_isCompact
    (isCompact_Icc.reProdIm isCompact_Icc) hU hR

/-- The positive multiplicities defining a zero count have finite support on any region
contained in a closed rectangle in the divisor domain. -/
theorem reProdIm_inter_zeroCount_support_finite {R : Set ℂ}
    (hU : Icc σ₁ σ₂ ×ℂ Icc t₁ t₂ ⊆ U) (hR : R ⊆ Icc σ₁ σ₂ ×ℂ Icc t₁ t₂) :
    (R ∩ Function.support (fun z ↦ (MeromorphicOn.divisor f U z).toNat)).Finite :=
  zeroCount_support_finite (reProdIm_inter_divisor_support_finite hU hR)

/-- A closed rectangle in the divisor domain has a vertically larger rectangle with finite
support, even when the larger rectangle is not contained in the domain. -/
theorem exists_lt_gt_reProdIm_inter_divisor_support_finite (ht : t₁ ≤ t₂)
    (hU : Icc σ₁ σ₂ ×ℂ Icc t₁ t₂ ⊆ U) :
    ∃ a < t₁, ∃ b > t₂,
      ((Icc σ₁ σ₂ ×ℂ Icc a b) ∩ Function.support (MeromorphicOn.divisor f U)).Finite := by
  classical
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
    equivRealProdCLM.symm.continuous.tendsto_nhdsSet (fun z hz ↦ hz) hs
  rw [isCompact_Icc.nhdsSet_prod_eq isCompact_Icc] at hprod
  obtain ⟨A, hA, B, hB, hAB⟩ := Filter.mem_prod_iff.mp hprod
  have hB₁ := mem_nhdsSet_iff_forall.mp hB t₁ (left_mem_Icc.mpr ht)
  have hB₂ := mem_nhdsSet_iff_forall.mp hB t₂ (right_mem_Icc.mpr ht)
  obtain ⟨a, ha, haB⟩ := exists_Ioc_subset_of_mem_nhds hB₁ ⟨t₁ - 1, sub_one_lt _⟩
  obtain ⟨b, hb, hbB⟩ := exists_Ico_subset_of_mem_nhds hB₂ ⟨t₂ + 1, lt_add_one _⟩
  obtain ⟨a', haa', ha'⟩ := exists_between ha
  obtain ⟨b', hb', hb'b⟩ := exists_between hb
  refine ⟨a', ha', b', hb', hN.subset fun z hz ↦ ⟨?_, hz.2⟩⟩
  suffices equivRealProdCLM z ∈ equivRealProdCLM.symm ⁻¹' N by
    simpa only [mem_preimage, ContinuousLinearEquiv.symm_apply_apply] using this
  apply hAB
  refine ⟨subset_of_mem_nhdsSet hA hz.1.1, ?_⟩
  by_cases hlow : z.im < t₁
  · exact haB ⟨haa'.trans_le hz.1.2.1, hlow.le⟩
  by_cases hhigh : t₂ < z.im
  · exact hbB ⟨hhigh.le, hz.1.2.2.trans_lt hb'b⟩
  exact subset_of_mem_nhdsSet hB ⟨le_of_not_gt hlow, le_of_not_gt hhigh⟩

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
  · exact reProdIm_inter_divisor_support_finite hU
      (fun z hz ↦ ⟨hz.1, hz.2.1.le, hz.2.2.trans ht23⟩)
  · exact reProdIm_inter_divisor_support_finite hU
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
  exact reProdIm_inter_zeroCount_support_finite hU
    (fun z hz ↦ ⟨hz.1, hz.2.1.le, hz.2.2⟩)

/-- A half-open rectangle's zero count is locally constant as its top edge moves to the
right in height. Zeros at height `T` remain counted when `t₁ < T`, and remain excluded
when `T ≤ t₁`. Only the closed rectangle up to `T` must lie in the divisor domain. -/
theorem eventuallyEq_zeroCount_reProdIm_Ioc_nhdsGE (T : ℝ)
    (hU : Icc σ₁ σ₂ ×ℂ Icc t₁ T ⊆ U) :
    (fun t ↦ zeroCount f U (Icc σ₁ σ₂ ×ℂ Ioc t₁ t)) =ᶠ[𝓝[≥] T]
      fun _ ↦ zeroCount f U (Icc σ₁ σ₂ ×ℂ Ioc t₁ T) := by
  classical
  by_cases hT : T < t₁
  · filter_upwards [(eventually_lt_nhds hT).filter_mono nhdsWithin_le_nhds] with t ht
    simp [Ioc_eq_empty_of_le ht.le, Ioc_eq_empty_of_le hT.le]
  obtain ⟨a, ha, b, hb, hfin⟩ :=
    exists_lt_gt_reProdIm_inter_divisor_support_finite (f := f) (le_of_not_gt hT) hU
  let K := Icc σ₁ σ₂ ×ℂ Icc a b
  -- Finitely many divisor points give a common right neighborhood with no new heights.
  have hheight : ∀ᶠ t in 𝓝[≥] T, ∀ z ∈ K ∩ Function.support (MeromorphicOn.divisor f U),
      z.im ≤ t ↔ z.im ≤ T := by
    apply hfin.eventually_all.mpr
    intro z _
    by_cases hz : z.im ≤ T
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact iff_of_true (hz.trans ht) hz
    · filter_upwards [eventually_lt_nhds (lt_of_not_ge hz) |>.filter_mono nhdsWithin_le_nhds]
        with t ht
      exact iff_of_false (not_le.mpr ht) hz
  filter_upwards [hheight, self_mem_nhdsWithin,
    (eventually_lt_nhds hb).filter_mono nhdsWithin_le_nhds] with t ht hbottom htop
  have hK : Icc σ₁ σ₂ ×ℂ Ioc t₁ t ⊆ K :=
    fun z hz ↦ ⟨hz.1, ha.le.trans hz.2.1.le, hz.2.2.trans htop.le⟩
  have hsub : Icc σ₁ σ₂ ×ℂ Ioc t₁ T ⊆ Icc σ₁ σ₂ ×ℂ Ioc t₁ t :=
    fun z hz ↦ ⟨hz.1, hz.2.1, hz.2.2.trans hbottom⟩
  have hfin' : ((Icc σ₁ σ₂ ×ℂ Ioc t₁ t) ∩
      Function.support (fun z ↦ (MeromorphicOn.divisor f U z).toNat)).Finite :=
    zeroCount_support_finite (hfin.subset fun z hz ↦
      ⟨hK hz.1, hz.2⟩)
  refine ((zeroCount_eq_iff_of_subset hsub hfin').2 ?_).symm
  intro z hz
  by_contra hne
  have hd : z ∈ Function.support (MeromorphicOn.divisor f U) := by
    intro heq
    exact hne (by simp [heq])
  have him := ht z ⟨hK hz.1, hd⟩
  exact hz.2 ⟨hz.1.1, hz.1.2.1, him.mp hz.1.2.2⟩

/-- The natural zero count with its top edge included is right-continuous in height. -/
theorem continuousWithinAt_zeroCount_reProdIm_Ioc_Ici (T : ℝ)
    (hU : Icc σ₁ σ₂ ×ℂ Icc t₁ T ⊆ U) :
    ContinuousWithinAt (fun t ↦ zeroCount f U (Icc σ₁ σ₂ ×ℂ Ioc t₁ t)) (Ici T) T :=
  continuousWithinAt_const.congr_of_eventuallyEq
    (eventuallyEq_zeroCount_reProdIm_Ioc_nhdsGE T hU) rfl

/-- Expanding both vertical edges of a closed rectangle cannot decrease its zero count. -/
theorem zeroCount_reProdIm_Icc_le {s₁ s₂ : ℝ} (h₁ : s₁ ≤ t₁) (h₂ : t₂ ≤ s₂)
    (hU : Icc σ₁ σ₂ ×ℂ Icc s₁ s₂ ⊆ U) :
    zeroCount f U (Icc σ₁ σ₂ ×ℂ Icc t₁ t₂) ≤
      zeroCount f U (Icc σ₁ σ₂ ×ℂ Icc s₁ s₂) :=
  zeroCount_mono (fun _ hz ↦ ⟨hz.1, h₁.trans hz.2.1, hz.2.2.trans h₂⟩)
    (reProdIm_inter_zeroCount_support_finite hU Subset.rfl)

/-- The symmetric closed-rectangle count stabilizes immediately to the right of every
height. At negative heights the region is empty; at height zero real zeros are retained. -/
theorem eventuallyEq_zeroCount_reProdIm_Icc_neg_nhdsGE (T : ℝ)
    (hU : Icc σ₁ σ₂ ×ℂ Icc (-T) T ⊆ U) :
    (fun t ↦ zeroCount f U (Icc σ₁ σ₂ ×ℂ Icc (-t) t)) =ᶠ[𝓝[≥] T]
      fun _ ↦ zeroCount f U (Icc σ₁ σ₂ ×ℂ Icc (-T) T) := by
  classical
  by_cases hT : T < 0
  · filter_upwards [(eventually_lt_nhds hT).filter_mono nhdsWithin_le_nhds] with t ht
    have ht' : t < -t := by linarith
    have hT' : T < -T := by linarith
    simp [Icc_eq_empty_of_lt ht', Icc_eq_empty_of_lt hT']
  have hT' : -T ≤ T := by linarith
  obtain ⟨a, ha, b, hb, hfin⟩ :=
    exists_lt_gt_reProdIm_inter_divisor_support_finite (f := f) hT' hU
  let K := Icc σ₁ σ₂ ×ℂ Icc a b
  have hheight : ∀ᶠ t in 𝓝[≥] T, ∀ z ∈ K ∩ Function.support (MeromorphicOn.divisor f U),
      |z.im| ≤ t ↔ |z.im| ≤ T := by
    apply hfin.eventually_all.mpr
    intro z _
    by_cases hz : |z.im| ≤ T
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact iff_of_true (hz.trans ht) hz
    · filter_upwards [eventually_lt_nhds (lt_of_not_ge hz) |>.filter_mono nhdsWithin_le_nhds]
        with t ht
      exact iff_of_false (not_le.mpr ht) hz
  have hTa : T < -a := by linarith
  -- A common right neighborhood avoids new absolute heights on either moving edge.
  filter_upwards [hheight, self_mem_nhdsWithin,
    (eventually_lt_nhds hb).filter_mono nhdsWithin_le_nhds,
    (eventually_lt_nhds hTa).filter_mono nhdsWithin_le_nhds]
    with t ht hbottom htop hlow
  have hat : a ≤ -t := by linarith
  have hK : Icc σ₁ σ₂ ×ℂ Icc (-t) t ⊆ K :=
    fun z hz ↦ ⟨hz.1, hat.trans hz.2.1, hz.2.2.trans htop.le⟩
  have hsub : Icc σ₁ σ₂ ×ℂ Icc (-T) T ⊆ Icc σ₁ σ₂ ×ℂ Icc (-t) t :=
    fun z hz ↦ ⟨hz.1, (neg_le_neg hbottom).trans hz.2.1, hz.2.2.trans hbottom⟩
  have hfin' : ((Icc σ₁ σ₂ ×ℂ Icc (-t) t) ∩
      Function.support (fun z ↦ (MeromorphicOn.divisor f U z).toNat)).Finite :=
    zeroCount_support_finite (hfin.subset fun z hz ↦ ⟨hK hz.1, hz.2⟩)
  refine ((zeroCount_eq_iff_of_subset hsub hfin').2 ?_).symm
  intro z hz
  by_contra hne
  have hd : z ∈ Function.support (MeromorphicOn.divisor f U) := by
    intro heq
    exact hne (by simp [heq])
  have him := ht z ⟨hK hz.1, hd⟩
  exact hz.2 ⟨hz.1.1, abs_le.mp (him.mp (abs_le.mpr hz.1.2))⟩

/-- The symmetric closed-rectangle zero count is right-continuous at every height. -/
theorem continuousWithinAt_zeroCount_reProdIm_Icc_neg_Ici (T : ℝ)
    (hU : Icc σ₁ σ₂ ×ℂ Icc (-T) T ⊆ U) :
    ContinuousWithinAt (fun t ↦ zeroCount f U (Icc σ₁ σ₂ ×ℂ Icc (-t) t)) (Ici T) T :=
  continuousWithinAt_const.congr_of_eventuallyEq
    (eventuallyEq_zeroCount_reProdIm_Icc_neg_nhdsGE T hU) rfl

end TauCeti
