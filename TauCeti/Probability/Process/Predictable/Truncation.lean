/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Process.Predictable.Measure
import TauCeti.MeasureTheory.Function.Lp.DominatedConvergence
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# Continuous time truncation of predictable integrands

On a fixed finite horizon, the predictable `Lᵖ` class of `1_(0,t] H` depends continuously
on `t` for every `1 ≤ p < ∞`. In particular, applying a continuous linear stochastic-integral
map to these truncations gives a mean-square continuous family when `p = 2`. This is
continuity in the space of random variables, not a selection of continuous sample paths.

The general result applies to any predictable measure whose time slices have zero mass.
For the time-product measure, continuity holds for every truncation time `t : ℝ≥0` and horizon
`T : ℝ≥0`, including `T = 0`; the horizon measure clips truncations past `T`.
No finiteness of the sample measure, path regularity, Brownian process, completion, or
usual-filtration assumption is needed.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2.B.
-/

public section

noncomputable section

open Filter Set MeasureTheory
open scoped Topology NNReal ENNReal symmDiff

namespace MeasureTheory.Filtration

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- Truncating a predictable finite-exponent `Lᵖ` integrand to `(0,t]` is continuous in
the truncation time whenever every time slice has zero mass. -/
theorem continuous_toLp_indicator_Ioc (ℱ : Filtration ℝ≥0 m)
    (μ : @Measure (ℝ≥0 × Ω) ℱ.predictable)
    (hμ : ∀ t : ℝ≥0, μ ({t} ×ˢ (univ : Set Ω)) = 0)
    {E : Type*} [NormedAddCommGroup E] {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    {f : ℝ≥0 × Ω → E} (hf : MemLp f p μ) :
    Continuous (fun t : ℝ≥0 ↦
      (hf.indicator (measurableSet_predictable_Ioc_prod 0 t
        (MeasurableSet.univ : MeasurableSet[ℱ 0] (univ : Set Ω))).nullMeasurableSet).toLp
          ((Ioc 0 t ×ˢ univ).indicator f)) := by
  let _ : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  have hm (t : ℝ≥0) := hf.indicator
    (measurableSet_predictable_Ioc_prod 0 t MeasurableSet.univ).nullMeasurableSet
  apply continuous_iff_continuousAt.mpr
  intro t
  rw [ContinuousAt, Lp.tendsto_Lp_iff_tendsto_eLpNorm'']
  refine TauCeti.tendsto_eLpNorm_sub_of_ae_tendsto hp
    (.of_forall fun s ↦ (hm s).aestronglyMeasurable) hf (C := 2) ?_ ?_
  · filter_upwards [] with s
    filter_upwards [] with x
    calc
      ‖(Ioc 0 s ×ˢ univ).indicator f x - (Ioc 0 t ×ˢ univ).indicator f x‖ₑ ≤
          ‖(Ioc 0 s ×ˢ univ).indicator f x‖ₑ + ‖(Ioc 0 t ×ˢ univ).indicator f x‖ₑ :=
        eNorm_sub_le
      _ ≤ ‖f x‖ₑ + ‖f x‖ₑ :=
        add_le_add (eNorm_indicator_le_eNorm_self f x) (eNorm_indicator_le_eNorm_self f x)
      _ = (2 : ℝ≥0) * ‖f x‖ₑ := by simp [two_mul]
  · have hnull : ∀ᵐ x ∂μ, x ∉ ({t} ×ˢ (univ : Set Ω)) :=
      measure_eq_zero_iff_ae_notMem.mp (hμ t)
    filter_upwards [hnull] with x hx
    have hxt : x.1 ≠ t := by simpa using hx
    have heq : ∀ᶠ s in 𝓝 t,
        (Ioc 0 s ×ˢ univ).indicator f x = (Ioc 0 t ×ˢ univ).indicator f x := by
      rcases lt_or_gt_of_ne hxt with hlt | hgt
      · filter_upwards [eventually_gt_nhds hlt] with s hs
        simp [Set.indicator, mem_Ioc, hlt.le, hs.le]
      · filter_upwards [eventually_lt_nhds hgt] with s hs
        simp [Set.indicator, mem_Ioc, not_le.mpr hgt, not_le.mpr hs]
    exact tendsto_const_nhds.congr' (heq.mono fun _ h ↦ h.symm)

/-- Time truncation is continuous for the finite-horizon predictable time-product measure,
without a finiteness assumption on the sample measure. -/
theorem continuous_toLp_indicator_Ioc_predictableMeasure (ℱ : Filtration ℝ≥0 m)
    (P : Measure Ω) (T : ℝ≥0)
    {E : Type*} [NormedAddCommGroup E] {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    {f : ℝ≥0 × Ω → E} (hf : MemLp f p (ℱ.predictableMeasure P T)) :
    Continuous (fun t : ℝ≥0 ↦
      (hf.indicator (measurableSet_predictable_Ioc_prod 0 t
        (MeasurableSet.univ : MeasurableSet[ℱ 0] (univ : Set Ω))).nullMeasurableSet).toLp
          ((Ioc 0 t ×ˢ univ).indicator f)) := by
  refine ℱ.continuous_toLp_indicator_Ioc (ℱ.predictableMeasure P T) (fun t ↦ ?_) hp hf
  have hmeas : MeasurableSet[ℱ.predictable] ({t} ×ˢ (univ : Set Ω)) :=
    by simpa only [← prod_univ] using
      ℱ.measurable_fst_predictable (measurableSet_singleton t)
  rw [predictableMeasure_apply _ _ _ hmeas]
  by_cases hP : SFinite P
  · let := hP
    rw [Measure.prod_prod]
    have ht : TauCeti.Probability.timeMeasure T {t} = 0 := by
      by_cases ht : t ∈ Ioc 0 T
      · simp [TauCeti.Probability.timeMeasure_apply T (measurableSet_singleton t),
          singleton_inter_of_mem ht]
      · simp [TauCeti.Probability.timeMeasure_apply T (measurableSet_singleton t),
          singleton_inter_of_notMem ht]
    rw [ht, zero_mul]
  · simp [Measure.prod_eq_zero_of_not_sfinite hP]

end MeasureTheory.Filtration
