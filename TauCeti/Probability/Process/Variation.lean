/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.BoundedVariation
public import TauCeti.Probability.Process.Predictable.Basic
public import Mathlib.Topology.EMetricSpace.VariationOnFromTo

/-!
# Adapted variation processes

The accumulated total variation of a continuous adapted process is adapted. If its paths
have locally bounded variation, the real-valued variation process is continuous and predictable,
even on a raw filtration. Thus taking variation does not introduce future information. These
facts provide measurable increasing integrators for pathwise finite-variation calculus.

Continuity here is required for every path; an arbitrary modification on a null set need not
remain adapted to an incomplete filtration.

## References

* Philip Protter, *Stochastic Integration and Differential Equations*, second edition, Chapter I.
-/

public section

open MeasureTheory Set Filter
open scoped NNReal Topology

namespace MeasureTheory.StronglyAdapted

variable {Ω E : Type*} {m : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 m}
  [PseudoMetricSpace E] [SecondCountableTopology E]
  {X : ℝ≥0 → Ω → E}

/-- Extended accumulated variation of a continuous adapted process is adapted, without any
finiteness assumption on the variation. -/
theorem eVariationOn_Icc (hX : StronglyAdapted ℱ X)
    (hc : ∀ ω, Continuous (fun t => X t ω)) :
    StronglyAdapted ℱ (fun t ω => eVariationOn (fun s => X s ω) (Icc 0 t)) := by
  borelize E
  intro t
  let : MeasurableSpace Ω := ℱ t
  have hm : Measurable[ℱ t]
      (fun ω => eVariationOn (fun s => X s ω) (Icc 0 t)) :=
    Measurable.eVariationOn_Icc
      (fun s hs => ((hX s).mono (ℱ.mono hs.2)).measurable)
      (fun ω => (hc ω).continuousOn)
  exact hm.stronglyMeasurable

/-- The real accumulated variation of a continuous adapted process is adapted. For paths
of locally bounded variation this is the finite total variation, not an infinite-value fallback. -/
theorem variationOnFromTo (hX : StronglyAdapted ℱ X)
    (hc : ∀ ω, Continuous (fun t => X t ω)) :
    StronglyAdapted ℱ (fun t ω => variationOnFromTo (fun s => X s ω) univ 0 t) := by
  intro t
  let : MeasurableSpace Ω := ℱ t
  have ht : (0 : ℝ≥0) ≤ t := bot_le
  simpa only [_root_.variationOnFromTo.eq_of_le _ _ ht, univ_inter] using
    ((hX.eVariationOn_Icc hc t).measurable.ennreal_toReal).stronglyMeasurable

/-- The variation clock of a continuous locally bounded-variation adapted process is
predictable on the original filtration. No usual-conditions hypothesis is needed. -/
theorem isStronglyPredictable_variationOnFromTo (hX : StronglyAdapted ℱ X)
    (hc : ∀ ω, Continuous (fun t => X t ω))
    (hv : ∀ ω, LocallyBoundedVariationOn (fun t => X t ω) univ) :
    IsStronglyPredictable ℱ
      (fun t ω => _root_.variationOnFromTo (fun s => X s ω) univ 0 t) := by
  apply (hX.variationOnFromTo hc).isStronglyPredictable_of_continuous
  intro ω
  apply continuous_iff_continuousAt.mpr
  intro t
  let T := t + 1
  have hT : t < T := lt_add_one t
  have hnb : Icc 0 T ∈ 𝓝 t :=
    Filter.mem_of_superset (Iio_mem_nhds hT) (fun s hs => ⟨bot_le, hs.le⟩)
  have hb : BoundedVariationOn (fun s => X s ω) (Icc 0 T) := by
    simpa only [univ_inter] using hv ω 0 T (mem_univ _) (mem_univ _)
  have hl := hb.continuousWithinAt_variationOnFromTo_iff
    (left_mem_Icc.mpr bot_le) (⟨bot_le, hT.le⟩ : t ∈ Icc 0 T)
  have hlocal := (hl.mpr (hc ω |>.continuousAt.continuousWithinAt)).continuousAt hnb
  apply hlocal.congr_of_eventuallyEq
  filter_upwards [hnb] with s hs
  have hs0 : (0 : ℝ≥0) ≤ s := bot_le
  rw [_root_.variationOnFromTo.eq_of_le _ _ hs0,
    _root_.variationOnFromTo.eq_of_le _ _ hs0, univ_inter,
    inter_eq_right.mpr (Icc_subset_Icc le_rfl hs.2)]

end MeasureTheory.StronglyAdapted
