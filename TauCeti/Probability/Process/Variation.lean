/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.BoundedVariation
public import TauCeti.Probability.Process.Predictable.Basic
public import Mathlib.MeasureTheory.Measure.Stieltjes
public import Mathlib.Topology.EMetricSpace.VariationOnFromTo
import TauCeti.Topology.EMetricSpace.VariationOnFromTo

/-!
# Adapted variation processes

The accumulated total variation of a continuous adapted process is adapted. If its paths
have locally bounded variation, the real-valued variation process is continuous and predictable,
even on a raw filtration. Thus taking variation does not introduce future information. These
facts provide measurable increasing integrators for pathwise finite-variation calculus.

Continuity here is required for every path; an arbitrary modification on a null set need not
remain adapted to an incomplete filtration.

A continuous adapted real process with locally bounded variation also decomposes, after
subtracting its initial value, as the difference of two continuous increasing predictable
processes starting at zero. Their sum is the accumulated variation. The construction uses
Mathlib's `variationOnFromTo.add_self_monotoneOn` and `variationOnFromTo.sub_self_monotoneOn`.

## References

* Philip Protter, *Stochastic Integration and Differential Equations*, second edition, Chapter I.
-/

public section

open MeasureTheory Set Filter
open scoped NNReal Topology

namespace MeasureTheory.StronglyAdapted

section Variation

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

end Variation

variable {Ω : Type*} {m : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 m}
  {X : ℝ≥0 → Ω → ℝ}

/-- The positive and negative variation parts of a continuous adapted locally BV process can
be chosen continuously and predictably on its raw filtration. Both start at zero; their sum
is the accumulated variation, and their difference is the process minus its initial value. -/
theorem exists_stieltjesFunction_sub_stieltjesFunction (hX : StronglyAdapted ℱ X)
    (hc : ∀ ω, Continuous (fun t => X t ω))
    (hv : ∀ ω, LocallyBoundedVariationOn (fun t => X t ω) univ) :
    ∃ p q : Ω → StieltjesFunction ℝ≥0,
      (∀ ω, Continuous (p ω)) ∧ (∀ ω, Continuous (q ω)) ∧
      IsStronglyPredictable ℱ (fun t ω => p ω t) ∧
      IsStronglyPredictable ℱ (fun t ω => q ω t) ∧
      (∀ ω, p ω 0 = 0 ∧ q ω 0 = 0) ∧
      (∀ t ω, X t ω - X 0 ω = p ω t - q ω t) ∧
      ∀ t ω, p ω t + q ω t = _root_.variationOnFromTo (fun s => X s ω) univ 0 t := by
  let V := fun t ω => _root_.variationOnFromTo (fun s => X s ω) univ 0 t
  have hVc (ω) : Continuous (fun t => V t ω) :=
    continuous_iff_continuousAt.mpr fun t =>
      ((hv ω).continuousWithinAt_variationOnFromTo_iff (mem_univ 0) (mem_univ t)).mpr
        (hc ω |>.continuousAt.continuousWithinAt) |>.continuousAt (by simp)
  -- The canonical signed-variation parts preserve adaptation, unlike arbitrary pathwise choices.
  have hpc (ω) : Continuous (fun t => (V t ω + X t ω - X 0 ω) / 2) :=
    (((hVc ω).add (hc ω)).sub continuous_const).div_const 2
  have hqc (ω) : Continuous (fun t => (V t ω - X t ω + X 0 ω) / 2) :=
    (((hVc ω).sub (hc ω)).add continuous_const).div_const 2
  let p : Ω → StieltjesFunction ℝ≥0 := fun ω =>
    { toFun := fun t => (V t ω + X t ω - X 0 ω) / 2
      mono' := fun s t hst => by
        have h := variationOnFromTo.add_self_monotoneOn (hv ω) (mem_univ 0)
          (mem_univ s) (mem_univ t) hst
        dsimp only [Pi.add_apply] at h
        dsimp only [V]
        linarith
      right_continuous' := fun _ => (hpc ω).continuousAt.continuousWithinAt }
  let q : Ω → StieltjesFunction ℝ≥0 := fun ω =>
    { toFun := fun t => (V t ω - X t ω + X 0 ω) / 2
      mono' := fun s t hst => by
        have h := variationOnFromTo.sub_self_monotoneOn (hv ω) (mem_univ 0)
          (mem_univ s) (mem_univ t) hst
        dsimp only [Pi.sub_apply] at h
        dsimp only [V]
        linarith
      right_continuous' := fun _ => (hqc ω).continuousAt.continuousWithinAt }
  -- Transfer the fixed-time variation measurability to the parts, then use their continuity.
  have hVa := hX.variationOnFromTo hc
  have hp : StronglyAdapted ℱ (fun t ω => p ω t) := fun t =>
    ((((hVa t).add (hX t)).sub ((hX 0).mono (ℱ.mono (bot_le : 0 ≤ t)))).measurable.div_const
      2).stronglyMeasurable
  have hq : StronglyAdapted ℱ (fun t ω => q ω t) := fun t =>
    ((((hVa t).sub (hX t)).add ((hX 0).mono (ℱ.mono (bot_le : 0 ≤ t)))).measurable.div_const
      2).stronglyMeasurable
  refine ⟨p, q, hpc, hqc, hp.isStronglyPredictable_of_continuous hpc,
    hq.isStronglyPredictable_of_continuous hqc, ?_, ?_, ?_⟩
  · intro ω
    simp [p, q, V, variationOnFromTo.self]
  · intro t ω
    dsimp [p, q]
    ring
  · intro t ω
    dsimp [p, q]
    ring

end MeasureTheory.StronglyAdapted
