/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Regular

/-!
# Regularity under almost everywhere continuous maps and finite sums

A measurable map that is continuous on a measurable set of full measure sends an inner regular
measure to an inner regular measure. Global continuity is unnecessary: compact approximation
can be performed inside the set where the map is continuous. This applies, for example, to
spectral character assignments whose exceptional set has measure zero.

Outer regularity and weak regularity are preserved by finite sums of measures, complementing
Mathlib's finite-sum instances for inner regularity. An open set approximating a sum from outside
is the intersection of open sets approximating the summands, and a set approximating it from
inside is the union of sets approximating the summands. Weak regularity of a finite sum is what
lets one approximate a function in `L¹` of several finite measures at once by approximating it in
`L¹` of their sum.
-/

public section

open MeasureTheory Set

namespace TauCeti

variable {α β : Type*} [MeasurableSpace α] [TopologicalSpace α]
  [MeasurableSpace β] [TopologicalSpace β]

/-- A measurable map continuous on a measurable set of full measure preserves inner regularity.
No separation, countability or finiteness assumption is required. -/
theorem innerRegular_map_of_continuousOn {μ : Measure α} [μ.InnerRegular]
    {f : α → β} {s : Set α} (hf : Measurable f) (hs : MeasurableSet s)
    (hcont : ContinuousOn f s) (hmem : ∀ᵐ x ∂μ, x ∈ s) :
    (Measure.map f μ).InnerRegular := by
  have hreg : μ.InnerRegularWRT (fun K ↦ IsCompact K ∧ K ⊆ s) MeasurableSet := by
    intro t ht r hr
    rw [← μ.measure_inter_eq_of_ae hmem, inter_comm] at hr
    obtain ⟨K, hKsub, hK, hrK⟩ := (ht.inter hs).exists_lt_isCompact hr
    exact ⟨K, hKsub.trans inter_subset_left, ⟨hK, hKsub.trans inter_subset_right⟩, hrK⟩
  exact ⟨hreg.map hf.aemeasurable (fun _ ht ↦ hf ht)
    (fun _ hK ↦ hK.1.image_of_continuousOn (hcont.mono hK.2)) (fun _ ht ↦ ht)⟩

end TauCeti

namespace MeasureTheory.Measure

variable {α : Type*} [MeasurableSpace α] {μ ν : Measure α}

/-- If two measures are inner regular for a property `p` of sets stable under binary unions, then
so is their sum. -/
theorem InnerRegularWRT.add {p q : Set α → Prop} (hp : ∀ s t, p s → p t → p (s ∪ t))
    (hμ : μ.InnerRegularWRT p q) (hν : ν.InnerRegularWRT p q) : (μ + ν).InnerRegularWRT p q := by
  intro U hU r hr
  rw [add_apply] at hr
  rcases eq_or_ne (μ U) 0 with h | h
  · rw [h, zero_add] at hr
    obtain ⟨K, hKU, hK, hrK⟩ := hν hU r hr
    exact ⟨K, hKU, hK, hrK.trans_le (by simp)⟩
  rcases eq_or_ne (ν U) 0 with h' | h'
  · rw [h', add_zero] at hr
    obtain ⟨K, hKU, hK, hrK⟩ := hμ hU r hr
    exact ⟨K, hKU, hK, hrK.trans_le (by simp)⟩
  obtain ⟨a, ha, b, hb, hab⟩ := ENNReal.exists_lt_add_of_lt_add hr h h'
  obtain ⟨K, hKU, hK, haK⟩ := hμ hU a ha
  obtain ⟨L, hLU, hL, hbL⟩ := hν hU b hb
  refine ⟨K ∪ L, union_subset hKU hLU, hp K L hK hL, hab.trans_le ?_⟩
  rw [add_apply]
  calc a + b ≤ μ K + ν L := add_le_add haK.le hbL.le
    _ ≤ μ (K ∪ L) + ν (K ∪ L) := by gcongr <;> simp

variable [TopologicalSpace α]

/-- The sum of two outer regular measures is outer regular. -/
instance OuterRegular.add [OuterRegular μ] [OuterRegular ν] : OuterRegular (μ + ν) where
  outerRegular s _ r hr := by
    rw [gt_iff_lt, add_apply] at hr
    obtain ⟨a, ha, b, hb, hab⟩ := ENNReal.exists_add_lt_of_add_lt hr
    obtain ⟨U, hsU, hU, hμU⟩ := s.exists_isOpen_lt_of_lt a ha
    obtain ⟨V, hsV, hV, hνV⟩ := s.exists_isOpen_lt_of_lt b hb
    refine ⟨U ∩ V, subset_inter hsU hsV, hU.inter hV, ?_⟩
    rw [add_apply]
    calc μ (U ∩ V) + ν (U ∩ V) ≤ μ U + ν V := by gcongr <;> simp
      _ < r := (ENNReal.add_lt_add hμU hνV).trans hab

/-- The sum of two weakly regular measures is weakly regular. -/
instance WeaklyRegular.add [WeaklyRegular μ] [WeaklyRegular ν] : WeaklyRegular (μ + ν) where
  innerRegular := WeaklyRegular.innerRegular.add (fun _ _ ↦ IsClosed.union)
    WeaklyRegular.innerRegular

/-- A finite sum of outer regular measures is outer regular. -/
instance OuterRegular.finsetSum {ι : Type*} {μ : ι → Measure α} [∀ i, OuterRegular (μ i)]
    (s : Finset ι) : OuterRegular (∑ i ∈ s, μ i) := by
  classical
  induction s using Finset.induction with
  | empty => rw [Finset.sum_empty]; infer_instance
  | insert a s ha ih => rw [Finset.sum_insert ha]; infer_instance

/-- A finite sum of weakly regular measures is weakly regular. -/
instance WeaklyRegular.finsetSum {ι : Type*} {μ : ι → Measure α} [∀ i, WeaklyRegular (μ i)]
    (s : Finset ι) : WeaklyRegular (∑ i ∈ s, μ i) := by
  classical
  induction s using Finset.induction with
  | empty => rw [Finset.sum_empty]; infer_instance
  | insert a s ha ih => rw [Finset.sum_insert ha]; infer_instance

end MeasureTheory.Measure
