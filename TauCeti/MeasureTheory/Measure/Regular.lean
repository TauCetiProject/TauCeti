/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Regular

/-!
# Inner regularity under almost everywhere continuous maps

A measurable map that is continuous on a measurable set of full measure sends an inner regular
measure to an inner regular measure. Global continuity is unnecessary: compact approximation
can be performed inside the set where the map is continuous. This applies, for example, to
spectral character assignments whose exceptional set has measure zero.

For a σ-finite measure that is inner regular for compact sets on sets of finite measure, such as
an additive Haar measure, every null measurable set contains a σ-compact subset of full measure
(`MeasureTheory.NullMeasurableSet.exists_isSigmaCompact_subset_ae_eq`). This reduces statements
about measurable sets to statements about compact sets, up to a null set.
-/

public section

open MeasureTheory Set
open scoped ENNReal

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

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] [TopologicalSpace α]

/-- **Null measurable sets are σ-compact up to a null set.** For a σ-finite measure that is inner
regular for compact sets on sets of finite measure, every null measurable set `s` contains a
σ-compact set `t` that is almost everywhere equal to `s`. -/
theorem NullMeasurableSet.exists_isSigmaCompact_subset_ae_eq [OpensMeasurableSpace α] [T2Space α]
    {μ : Measure α} [SigmaFinite μ] [μ.InnerRegularCompactLTTop] {s : Set α}
    (hs : NullMeasurableSet s μ) : ∃ t ⊆ s, IsSigmaCompact t ∧ t =ᵐ[μ] s := by
  obtain ⟨u, hus, hu, hsu⟩ := hs.exists_measurable_subset_ae_eq
  -- Approximate `u ∩ spanningSets μ n` from inside by a compact set up to measure `k⁻¹`.
  have h (n k : ℕ) : ∃ K ⊆ u ∩ spanningSets μ n, IsCompact K ∧
      μ ((u ∩ spanningSets μ n) \ K) < (k : ℝ≥0∞)⁻¹ :=
    (hu.inter (measurableSet_spanningSets μ n)).exists_isCompact_sdiff_lt
      ((measure_mono inter_subset_right).trans_lt (measure_spanningSets_lt_top μ n)).ne
      (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top k))
  choose K hKu hK hKμ using h
  set t := ⋃ p : ℕ × ℕ, K p.1 p.2
  have htu : t ⊆ u := iUnion_subset fun p ↦ (hKu p.1 p.2).trans inter_subset_left
  have hnull : μ (u \ t) = 0 := by
    refine measure_mono_null (t := ⋃ n, (u ∩ spanningSets μ n) \ t) (fun x hx ↦ ?_)
      (measure_iUnion_null fun n ↦ ?_)
    · obtain ⟨n, hn⟩ := mem_iUnion.1 ((iUnion_spanningSets μ).symm ▸ mem_univ x)
      exact mem_iUnion.2 ⟨n, ⟨hx.1, hn⟩, hx.2⟩
    · refine nonpos_iff_eq_zero.1 (ge_of_tendsto' ENNReal.tendsto_inv_nat_nhds_zero fun k ↦ ?_)
      exact (measure_mono (sdiff_subset_sdiff_right
        (subset_iUnion (fun p : ℕ × ℕ ↦ K p.1 p.2) (n, k)))).trans (hKμ n k).le
  refine ⟨t, htu.trans hus, isSigmaCompact_iUnion_of_isCompact _ fun p ↦ hK p.1 p.2, ?_⟩
  exact (ae_eq_set.2 ⟨by simp [sdiff_eq_empty.2 htu], hnull⟩).trans hsu

end MeasureTheory
