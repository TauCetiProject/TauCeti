/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Process.Predictable.Measure
import TauCeti.MeasureTheory.Function.Lp.Indicator

/-!
# Continuous time truncation of predictable integrands

On a fixed finite horizon, the predictable `Lᵖ` class of `1_(0,t] H` depends continuously
on `t` for every `1 ≤ p < ∞`. In particular, applying a continuous linear stochastic-integral
map to these truncations gives a mean-square continuous family when `p = 2`. This is
continuity in the space of random variables, not a selection of continuous sample paths.

The symmetric-difference mass formula includes clipping at the horizon and the zero horizon.
No path regularity, Brownian process, completion, or usual-filtration assumption is needed.
The sample measure is finite, but need not be a probability measure.

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
the truncation time, as a class on the original fixed horizon. -/
theorem continuous_toLp_indicator_Ioc (ℱ : Filtration ℝ≥0 m)
    (P : Measure Ω) [IsFiniteMeasure P] (T : ℝ≥0)
    {E : Type*} [NormedAddCommGroup E] {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    {f : ℝ≥0 × Ω → E} (hf : MemLp f p (ℱ.predictableMeasure P T)) :
    Continuous (fun t : ℝ≥0 ↦
      (hf.indicator (measurableSet_predictable_Ioc_prod 0 t
        (MeasurableSet.univ : MeasurableSet[ℱ 0] (univ : Set Ω))).nullMeasurableSet).toLp
          ((Ioc 0 t ×ˢ univ).indicator f)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  refine hf.tendsto_toLp_indicator hp
    (fun s ↦ (measurableSet_predictable_Ioc_prod 0 s MeasurableSet.univ).nullMeasurableSet)
    (measurableSet_predictable_Ioc_prod 0 t MeasurableSet.univ).nullMeasurableSet ?_
  simp_rw [predictableMeasure_symmDiff_Ioc_prod_univ]
  have h : Tendsto (fun s : ℝ≥0 ↦
      ENNReal.ofReal |(min s T : ℝ≥0) - (min t T : ℝ≥0)|) (𝓝 t) (𝓝 0) := by
    have hc : Continuous (fun s : ℝ≥0 ↦
        ENNReal.ofReal |(min s T : ℝ≥0) - (min t T : ℝ≥0)|) :=
      ENNReal.continuous_ofReal.comp (by fun_prop)
    simpa using hc.tendsto t
  simpa using ENNReal.Tendsto.mul_const h (Or.inr (measure_ne_top P univ))

end MeasureTheory.Filtration
