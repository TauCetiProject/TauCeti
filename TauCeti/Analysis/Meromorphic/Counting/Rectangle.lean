/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Meromorphic.Counting.Basic
public import Mathlib.Analysis.Complex.Basic

/-!
# Exact additivity of counts in imaginary height

Rectangles are closed in their real coordinate and half open in their imaginary coordinate.
Thus a point on a splitting edge belongs to precisely one of the two pieces, so its divisor
multiplicity is counted once, in the lower piece. The counts are those of the divisor
`MeromorphicOn.divisor f U`, which is identically zero unless `f` is meromorphic on `U`: for a
function that is not meromorphic on `U` every count is zero by convention, and no actual zeros are
counted. The containing closed rectangle is compact, which supplies finite divisor support,
including at its edges.

As the upper height increases, the zero count is monotone and locally constant from the
right, even at a height carrying zeros. In particular it is right-continuous. These facts
allow an asymptotic zero-counting formula to pass from heights avoiding zeros to all heights.
-/

public section

open Set Complex Filter Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {f : ℂ → E} {U : Set ℂ} {σ₁ σ₂ t₁ t₂ t₃ : ℝ}

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
  · apply MeromorphicOn.divisor_finite_inter_support_of_isCompact
      (isCompact_Icc.reProdIm isCompact_Icc) hU
    intro z hz
    exact ⟨hz.1, le_of_lt hz.2.1, hz.2.2.trans ht23⟩
  · apply MeromorphicOn.divisor_finite_inter_support_of_isCompact
      (isCompact_Icc.reProdIm isCompact_Icc) hU
    intro z hz
    exact ⟨hz.1, ht12.trans (le_of_lt hz.2.1), hz.2.2⟩

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

/-- Increasing the upper height cannot decrease the zero count. The containing closed
rectangle guarantees that neither sum takes the infinite-support default value. -/
theorem zeroCount_reProdIm_Ioc_le (ht : t₂ ≤ t₃)
    (hU : Icc σ₁ σ₂ ×ℂ Icc t₁ t₃ ⊆ U) :
    zeroCount f U (Icc σ₁ σ₂ ×ℂ Ioc t₁ t₂) ≤
      zeroCount f U (Icc σ₁ σ₂ ×ℂ Ioc t₁ t₃) := by
  refine zeroCount_mono (S := Icc σ₁ σ₂ ×ℂ Ioc t₁ t₃)
    (fun z hz ↦ ⟨hz.1, hz.2.1, hz.2.2.trans ht⟩) ?_
  apply zeroCount_support_finite
  exact MeromorphicOn.divisor_finite_inter_support_of_isCompact
    (isCompact_Icc.reProdIm isCompact_Icc) hU
    (fun z hz ↦ ⟨hz.1, hz.2.1.le, hz.2.2⟩)

/-- A half-open rectangle's zero count is locally constant as its top edge moves to the
right in height. Zeros on the original top edge remain counted. Only inclusion of a compact
rectangle in the divisor domain is required; without meromorphy the divisor is zero. -/
theorem eventuallyEq_zeroCount_reProdIm_Ioc (T : ℝ) (hT : T < t₃)
    (hU : Icc σ₁ σ₂ ×ℂ Icc t₁ t₃ ⊆ U) :
    (fun t ↦ zeroCount f U (Icc σ₁ σ₂ ×ℂ Ioc t₁ t)) =ᶠ[𝓝[≥] T]
      fun _ ↦ zeroCount f U (Icc σ₁ σ₂ ×ℂ Ioc t₁ T) := by
  classical
  let K := Icc σ₁ σ₂ ×ℂ Icc t₁ t₃
  have hfin : (K ∩ Function.support (MeromorphicOn.divisor f U)).Finite :=
    MeromorphicOn.divisor_finite_inter_support_of_isCompact
      (isCompact_Icc.reProdIm isCompact_Icc) hU Subset.rfl
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
    (eventually_lt_nhds hT).filter_mono nhdsWithin_le_nhds] with t ht hbottom htop
  have hsub : Icc σ₁ σ₂ ×ℂ Ioc t₁ T ⊆ Icc σ₁ σ₂ ×ℂ Ioc t₁ t :=
    fun z hz ↦ ⟨hz.1, hz.2.1, hz.2.2.trans hbottom⟩
  have hfin' : ((Icc σ₁ σ₂ ×ℂ Ioc t₁ t) ∩
      Function.support (fun z ↦ (MeromorphicOn.divisor f U z).toNat)).Finite :=
    zeroCount_support_finite (hfin.subset fun z hz ↦
      ⟨⟨hz.1.1, hz.1.2.1.le, hz.1.2.2.trans htop.le⟩, hz.2⟩)
  refine ((zeroCount_eq_iff_of_subset hsub hfin').2 ?_).symm
  intro z hz
  by_contra hne
  have hd : z ∈ Function.support (MeromorphicOn.divisor f U) := by
    intro heq
    exact hne (by simp [heq])
  have him := ht z ⟨⟨hz.1.1, hz.1.2.1.le, hz.1.2.2.trans htop.le⟩, hd⟩
  exact hz.2 ⟨hz.1.1, hz.1.2.1, him.mp hz.1.2.2⟩

/-- The natural zero count with its top edge included is right-continuous in height. -/
theorem continuousWithinAt_zeroCount_reProdIm_Ioc (T : ℝ) (hT : T < t₃)
    (hU : Icc σ₁ σ₂ ×ℂ Icc t₁ t₃ ⊆ U) :
    ContinuousWithinAt (fun t ↦ zeroCount f U (Icc σ₁ σ₂ ×ℂ Ioc t₁ t)) (Ici T) T :=
  continuousWithinAt_const.congr_of_eventuallyEq
    (eventuallyEq_zeroCount_reProdIm_Ioc T hT hU) rfl

end TauCeti
