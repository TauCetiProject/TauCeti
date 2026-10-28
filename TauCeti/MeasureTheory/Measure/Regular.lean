/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Regular
public import TauCeti.MeasureTheory.Measure.AbsolutelyContinuous

/-!
# Regularity under almost everywhere continuous maps and under absolute continuity

A measurable map that is continuous on a measurable set of full measure sends an inner regular
measure to an inner regular measure. Global continuity is unnecessary: compact approximation
can be performed inside the set where the map is continuous. This applies, for example, to
spectral character assignments whose exceptional set has measure zero.

A finite measure `ν` absolutely continuous with respect to a finite measure `μ` inherits the
regularity of `μ`. By the `ε`–`δ` form of absolute continuity
(`MeasureTheory.Measure.AbsolutelyContinuous.exists_pos_measure_lt_of_measure_lt`), a set `K ⊆ U`
or `U ⊇ A` approximating in `μ`-measure leaves a difference of small `ν`-measure. So every
compact or closed inner approximation, and every open outer approximation, for `μ` is one for
`ν`. In particular, on a compact Hausdorff space with its Borel σ-algebra, a finite measure
absolutely continuous with respect to a finite regular measure is regular. Since `ν ≤ c • μ`
implies `ν ≪ μ` (`MeasureTheory.Measure.absolutelyContinuous_of_le_smul`), the same holds for a
measure dominated by a multiple of a finite regular measure. This is how regularity is checked for
measures given only through a domination bound, such as the variation of a sum of scalar measures.

## Main results

* `TauCeti.innerRegular_map_of_continuousOn`: pushforward of an inner regular measure along a
  map continuous on a set of full measure.
* `MeasureTheory.Measure.AbsolutelyContinuous.innerRegularWRT`: transfer of inner regularity with
  respect to measurable approximating sets.
* `MeasureTheory.Measure.AbsolutelyContinuous.outerRegular`,
  `MeasureTheory.Measure.AbsolutelyContinuous.weaklyRegular`,
  `MeasureTheory.Measure.AbsolutelyContinuous.innerRegularCompactLTTop`,
  `MeasureTheory.Measure.AbsolutelyContinuous.innerRegular`,
  `MeasureTheory.Measure.AbsolutelyContinuous.regular`: a finite measure absolutely continuous
  with respect to a finite measure inherits each regularity property.

## References

* W. Rudin, *Real and Complex Analysis*, 3rd ed., McGraw-Hill (1987), §2.18 and Theorem 6.11.
* G. B. Folland, *Real Analysis: Modern Techniques and Their Applications*, 2nd ed., Wiley
  (1999), Theorem 3.5 and §7.1.
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

namespace MeasureTheory.Measure.AbsolutelyContinuous

variable {α : Type*} [MeasurableSpace α] {μ ν : Measure α}

/-- A finite measure absolutely continuous with respect to `μ` inherits inner regularity of `μ`
with respect to `p` on sets satisfying `q`, provided the approximating `p`-sets are `μ`-null
measurable and `q`-sets have finite `μ`-measure. -/
theorem innerRegularWRT [IsFiniteMeasure ν] (h : ν ≪ μ) {p q : Set α → Prop}
    (H : μ.InnerRegularWRT p q) (hp : ∀ K, p K → NullMeasurableSet K μ)
    (hq : ∀ U, q U → μ U ≠ ∞) : ν.InnerRegularWRT p q := by
  intro U hU r hr
  obtain ⟨δ, hδ, hδν⟩ := h.exists_pos_measure_lt_of_measure_lt (tsub_pos_of_lt hr).ne'
  have hμU : μ U ≠ 0 := fun h0 ↦ (pos_of_gt hr).ne' (h h0)
  obtain ⟨K, hKU, hpK, hK⟩ := H hU _ (ENNReal.sub_lt_self (hq U hU) hμU hδ.ne')
  have hdiff : ν (U \ K) < ν U - r := hδν _ <| measure_sdiff_lt_of_lt_add (hp K hpK) hKU
    (ne_top_of_le_ne_top (hq U hU) (measure_mono hKU))
    (ENNReal.lt_add_of_sub_lt_right (Or.inl (hq U hU)) hK)
  refine ⟨K, hKU, hpK, ?_⟩
  calc r = ν U - (ν U - r) := (ENNReal.sub_sub_cancel (measure_ne_top _ _) hr.le).symm
    _ < ν K := by
      rw [ENNReal.sub_lt_iff_lt_right (by finiteness) tsub_le_self]
      calc ν U ≤ ν (U ∩ K) + ν (U \ K) := measure_le_inter_add_sdiff ν U K
        _ < ν K + (ν U - r) := by
          rw [inter_eq_right.2 hKU]
          exact ENNReal.add_lt_add_left (measure_ne_top _ _) hdiff

variable [TopologicalSpace α] [IsFiniteMeasure μ] [IsFiniteMeasure ν]

/-- A finite measure absolutely continuous with respect to a finite outer regular measure is
outer regular. -/
theorem outerRegular [μ.OuterRegular] (h : ν ≪ μ) : ν.OuterRegular := by
  refine ⟨fun A hA r hr ↦ ?_⟩
  obtain ⟨δ, hδ, hδν⟩ := h.exists_pos_measure_lt_of_measure_lt (tsub_pos_of_lt hr).ne'
  obtain ⟨U, hAU, hU, -, hμU⟩ := hA.exists_isOpen_sdiff_lt (measure_ne_top μ A) hδ.ne'
  refine ⟨U, hAU, hU, ?_⟩
  calc ν U ≤ ν (U ∩ A) + ν (U \ A) := measure_le_inter_add_sdiff ν U A
    _ < ν A + (r - ν A) := by
      rw [inter_eq_right.2 hAU]
      exact ENNReal.add_lt_add_left (measure_ne_top _ _) (hδν _ hμU)
    _ = r := add_tsub_cancel_of_le hr.le

/-- A finite measure absolutely continuous with respect to a finite weakly regular measure is
weakly regular. -/
theorem weaklyRegular [OpensMeasurableSpace α] [μ.WeaklyRegular] (h : ν ≪ μ) :
    ν.WeaklyRegular where
  __ := h.outerRegular
  innerRegular := h.innerRegularWRT WeaklyRegular.innerRegular
    (fun _ hK ↦ hK.measurableSet.nullMeasurableSet) fun U _ ↦ measure_ne_top μ U

/-- On an `R₁` space with its Borel σ-algebra, a finite measure absolutely continuous with
respect to a finite measure that is inner regular for compact sets is inner regular for compact
sets. -/
theorem innerRegularCompactLTTop [BorelSpace α] [R1Space α] [μ.InnerRegularCompactLTTop]
    (h : ν ≪ μ) : ν.InnerRegularCompactLTTop := by
  -- Closures of compact sets are compact and closed, so measurable, approximating sets.
  have H : μ.InnerRegularWRT (fun K ↦ IsCompact K ∧ IsClosed K) MeasurableSet :=
    fun U hU _ hr ↦
      let ⟨K, hKU, hK, hrK⟩ := hU.exists_lt_isCompact_of_ne_top (measure_ne_top μ U) hr
      ⟨closure K, hK.closure_subset_measurableSet hU hKU, ⟨hK.closure, isClosed_closure⟩,
        hrK.trans_le (measure_mono subset_closure)⟩
  exact ⟨(h.innerRegularWRT H
    (fun _ hK ↦ hK.2.measurableSet.nullMeasurableSet) fun U _ ↦ measure_ne_top μ U).mono
      (fun _ hU ↦ hU.1) fun _ hK ↦ hK.1⟩

/-- On an `R₁` space with its Borel σ-algebra, a finite measure absolutely continuous with
respect to a finite inner regular measure is inner regular. -/
theorem innerRegular [BorelSpace α] [R1Space α] [μ.InnerRegular] (h : ν ≪ μ) :
    ν.InnerRegular :=
  have := h.innerRegularCompactLTTop
  inferInstance

/-- On an `R₁` space with its Borel σ-algebra, for example a compact Hausdorff space, a finite
measure absolutely continuous with respect to a finite regular measure is regular. -/
theorem regular [BorelSpace α] [R1Space α] [μ.Regular] (h : ν ≪ μ) : ν.Regular :=
  have := h.innerRegularCompactLTTop
  inferInstance

end MeasureTheory.Measure.AbsolutelyContinuous
