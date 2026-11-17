/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Filter
public import Mathlib.Topology.Order.Cadlag
import Mathlib.Topology.Order.Basic

/-!
# Simultaneous almost-sure monotonicity of right-continuous processes

If a process `X : ι → Ω → β` on a densely ordered separable linear order is almost surely
nondecreasing between each fixed pair of times `s ≤ t` and has almost surely right-continuous paths
into an order-closed topological preorder `β`, then almost surely the entire sample path `X · ω` is
monotone simultaneously across all times.
-/

public section

open Filter MeasureTheory Set
open scoped Topology

namespace TauCeti.Probability

/-- On a densely ordered separable linear order, pairwise almost-sure monotonicity together with
almost-sure right-continuity implies almost-sure pathwise monotonicity into any order-closed
preorder. -/
theorem ae_monotone_of_ae_le_of_isRightContinuous {Ω ι β : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [LinearOrder ι] [TopologicalSpace ι] [OrderTopology ι] [DenselyOrdered ι]
    [TopologicalSpace.SeparableSpace ι]
    [Preorder β] [TopologicalSpace β] [OrderClosedTopology β]
    {X : ι → Ω → β} (hle : ∀ ⦃s t : ι⦄, s ≤ t → ∀ᵐ ω ∂P, X s ω ≤ X t ω)
    (hrc : ∀ᵐ ω ∂P, IsRightContinuous (X · ω)) :
    ∀ᵐ ω ∂P, Monotone (X · ω) := by
  cases isEmpty_or_nonempty ι
  · exact ae_of_all _ fun _ s ↦ (IsEmpty.false s).elim
  · let q : ℕ → ι := TopologicalSpace.denseSeq ι
    have hdense : DenseRange q := TopologicalSpace.denseRange_denseSeq ι
    have hqmono : ∀ᵐ ω ∂P, ∀ i j : ℕ, q i ≤ q j → X (q i) ω ≤ X (q j) ω :=
      ae_all_iff.mpr fun i ↦ ae_all_iff.mpr fun j ↦ by
        by_cases hqij : q i ≤ q j
        · exact (hle hqij).mono fun _ hω _ ↦ hω
        · exact ae_of_all _ fun _ hbad ↦ False.elim (hqij hbad)
    have htop : ∀ᵐ ω ∂P, ∀ m : ι, IsTop m → ∀ i : ℕ, X (q i) ω ≤ X m ω := by
      by_cases h : ∃ m : ι, IsTop m
      · obtain ⟨m, hm⟩ := h
        filter_upwards [ae_all_iff.mpr fun i ↦ hle (hm (q i))] with ω hω m' hm'
        rwa [le_antisymm (hm m') (hm' m)]
      · exact ae_of_all _ fun _ m hm ↦ (h ⟨m, hm⟩).elim
    filter_upwards [hrc, hqmono, htop] with ω hrcω hq hm s t hst
    rcases hst.eq_or_lt with rfl | hst
    · exact le_rfl
    · have hle_of_dense {b : ι} (hsb : s < b)
          (hIoo : ∀ i, s < q i → q i < b → X (q i) ω ≤ X b ω) : X s ω ≤ X b ω := by
        refine isClosed_Iic.mem_of_frequently_of_tendsto ?_ (hrcω s)
        rw [Filter.frequently_iff]
        intro U hU
        obtain ⟨s', hs', hss'⟩ := (mem_nhdsGT_iff_exists_Ioo_subset' hsb).mp hU
        obtain ⟨i, hi⟩ := hdense.exists_mem_open isOpen_Ioo (nonempty_Ioo.mpr (lt_min hs' hsb))
        exact ⟨q i, hss' ⟨hi.1, hi.2.trans_le (min_le_left _ _)⟩,
          hIoo i hi.1 (hi.2.trans_le (min_le_right _ _))⟩
      by_cases ht : ∃ t₁, t < t₁
      · obtain ⟨t₁, htt₁⟩ := ht
        refine isClosed_Ici.mem_of_frequently_of_tendsto ?_ (hrcω t)
        rw [Filter.frequently_iff]
        intro V hV
        obtain ⟨t', ht', htt'⟩ := (mem_nhdsGT_iff_exists_Ioo_subset' htt₁).mp hV
        obtain ⟨j, hj⟩ := hdense.exists_mem_open isOpen_Ioo (nonempty_Ioo.mpr ht')
        exact ⟨q j, htt' hj, hle_of_dense (hst.trans hj.1) fun i _ hib ↦ hq i j hib.le⟩
      · exact hle_of_dense hst fun i _ _ ↦ hm t (fun x ↦ not_lt.mp fun htx ↦ ht ⟨x, htx⟩) i

end TauCeti.Probability
