/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Process.Variation
public import TauCeti.Probability.Process.Stieltjes
public import TauCeti.MeasureTheory.VectorMeasure.FiniteHorizon
import TauCeti.Topology.EMetricSpace.VariationOnFromTo

/-!
# Adapted signed finite-variation measures

A continuous adapted real process of locally bounded variation decomposes into two continuous
adapted increasing processes starting at zero. Their sum is the accumulated variation and their
difference is the original process minus its initial value. In particular the parts are
predictable on the original filtration; no moment bounds or usual conditions are needed.

This decomposition identifies the finite-horizon derivative signed measure with the difference
of two measurable random Stieltjes measures. Its evaluation on any Borel set is therefore
measurable in the sigma algebra at the horizon. This supplies signed finite-variation
integrators without assuming that the original path is increasing or globally BV.
The open initial endpoint excludes an initial atom.

The construction uses Mathlib's signed-variation formulas
`variationOnFromTo.add_self_monotoneOn` and `variationOnFromTo.sub_self_monotoneOn`, and the
adaptation of accumulated variation from `TauCeti.Probability.Process.Variation`.

## References

* P. Protter, *Stochastic Integration and Differential Equations*, second edition, Chapter I.
-/

public section

open MeasureTheory Set
open scoped NNReal

namespace MeasureTheory.StronglyAdapted

variable {Ω : Type*} {m : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 m}
  {X : ℝ≥0 → Ω → ℝ}

/-- The positive and negative variation parts of a continuous adapted locally BV process can
be chosen continuously and predictably on its raw filtration. Both start at zero; their sum
is the accumulated variation, and their difference is the centered process. -/
theorem exists_stieltjesFunction_sub (hX : StronglyAdapted ℱ X)
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
  have hVc (ω) : Continuous (fun t => V t ω) := by
    exact continuous_iff_continuousAt.mpr fun t =>
      ((hv ω).continuousWithinAt_variationOnFromTo_iff (mem_univ 0) (mem_univ t)).mpr
        (hc ω |>.continuousAt.continuousWithinAt) |>.continuousAt (by simp)
  -- The canonical signed-variation parts preserve adaptation, unlike arbitrary pathwise choices.
  let p : Ω → StieltjesFunction ℝ≥0 := fun ω =>
    { toFun := fun t => (V t ω + X t ω - X 0 ω) / 2
      mono' := fun s t hst => by
        have h := variationOnFromTo.add_self_monotoneOn (hv ω) (mem_univ 0)
          (mem_univ s) (mem_univ t) hst
        dsimp only [Pi.add_apply] at h
        dsimp only [V]
        linarith
      right_continuous' := fun t =>
        (((hVc ω).add (hc ω)).sub continuous_const).div_const 2
          |>.continuousAt.continuousWithinAt }
  let q : Ω → StieltjesFunction ℝ≥0 := fun ω =>
    { toFun := fun t => (V t ω - X t ω + X 0 ω) / 2
      mono' := fun s t hst => by
        have h := variationOnFromTo.sub_self_monotoneOn (hv ω) (mem_univ 0)
          (mem_univ s) (mem_univ t) hst
        dsimp only [Pi.sub_apply] at h
        dsimp only [V]
        linarith
      right_continuous' := fun t =>
        (((hVc ω).sub (hc ω)).add continuous_const).div_const 2
          |>.continuousAt.continuousWithinAt }
  have hpc (ω) : Continuous (p ω) :=
    (((hVc ω).add (hc ω)).sub continuous_const).div_const 2
  have hqc (ω) : Continuous (q ω) :=
    (((hVc ω).sub (hc ω)).add continuous_const).div_const 2
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

/-- Every Borel-set evaluation of the finite-horizon signed Stieltjes measure of an adapted
process with continuous BV paths on that horizon is measurable at the horizon. No moments or
path regularity outside the horizon are required. -/
theorem measurable_vectorMeasureIcc (hX : StronglyAdapted ℱ X)
    (T : ℝ≥0) (hc : ∀ ω, ContinuousOn (fun t => X t ω) (Icc 0 T))
    (hv : ∀ ω, BoundedVariationOn (fun t => X t ω) (Icc 0 T))
    {s : Set ℝ≥0} (hs : MeasurableSet s) :
    Measurable[ℱ T] (fun ω => (hv ω).vectorMeasureIcc bot_le s) := by
  -- Extend constantly after T so that the decomposition uses no future path regularity.
  let Y := fun t ω => X (min t T) ω
  have hY : StronglyAdapted ℱ Y := fun t => (hX (min t T)).mono (ℱ.mono (min_le_left _ _))
  have hYc (ω) : Continuous (fun t => Y t ω) :=
    (hc ω).comp_continuous (continuous_id.min continuous_const)
      (fun t => ⟨bot_le, min_le_right t T⟩)
  have hYv (ω) : LocallyBoundedVariationOn (fun t => Y t ω) univ := by
    have hext : IccExtend (bot_le : 0 ≤ T) ((fun t => X t ω) ∘ Subtype.val) =
        (fun t => Y t ω) := by
      ext t
      simp [IccExtend_apply, Y, min_comm]
    exact (hext ▸ (hv ω).IccExtend bot_le).locallyBoundedVariationOn
  obtain ⟨p, q, _, _, hp, hq, hzero, hsub, _⟩ := hY.exists_stieltjesFunction_sub hYc hYv
  have hpM := hp.isStronglyProgressive.stronglyAdapted.adapted.measurable_restrict_measure_Ioc 0 T
  have hqM := hq.isStronglyProgressive.stronglyAdapted.adapted.measurable_restrict_measure_Ioc 0 T
  have heq (ω) :=
    (hv ω).vectorMeasureIcc_eq_sub_toSignedMeasure bot_le (p ω) (q ω)
      (fun t ht => by
        simpa [Y, min_eq_left ht.2, (hzero ω).1, (hzero ω).2] using hsub t ω)
  simp_rw [heq, _root_.sub_apply, Measure.toSignedMeasure_apply_measurable hs,
    measureReal_def]
  exact ((Measure.measurable_coe hs).comp hpM).ennreal_toReal.sub
    ((Measure.measurable_coe hs).comp hqM).ennreal_toReal

end MeasureTheory.StronglyAdapted
