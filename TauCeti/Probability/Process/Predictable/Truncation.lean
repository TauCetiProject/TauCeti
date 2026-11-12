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

/-- The symmetric difference of two initial predictable time strips has mass equal to
their clipped endpoint distance times the total sample mass. -/
@[simp]
theorem predictableMeasure_symmDiff_Ioc_prod_univ (ℱ : Filtration ℝ≥0 m)
    (P : Measure Ω) [SFinite P] (T s t : ℝ≥0) :
    ℱ.predictableMeasure P T ((Ioc 0 s ×ˢ univ) ∆ (Ioc 0 t ×ˢ univ)) =
      ENNReal.ofReal |(min s T : ℝ≥0) - (min t T : ℝ≥0)| * P univ := by
  have hstrip (s t : ℝ≥0) (hst : s ≤ t) :
      (Ioc 0 s ×ˢ (univ : Set Ω)) ∆ (Ioc 0 t ×ˢ univ) = Ioc s t ×ˢ univ := by
    ext p
    simp only [mem_symmDiff, mem_prod, mem_Ioc, mem_univ, and_true]
    have : (0 : ℝ≥0) ≤ s := bot_le
    grind
  rcases le_total s t with hst | hts
  · rw [hstrip s t hst, predictableMeasure_Ioc_prod _ _ _ _ _ MeasurableSet.univ,
      abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast min_le_min_right T hst))]
    congr 1
    by_cases hsT : s ≤ T
    · rw [min_eq_left hsT]
      congr 1
      ring
    · have htT : T ≤ t := (le_of_not_ge hsT).trans hst
      simp only [min_eq_right (le_of_not_ge hsT), min_eq_right htT, sub_self,
        neg_zero, ENNReal.ofReal_zero]
      exact ENNReal.ofReal_eq_zero.mpr (sub_nonpos.mpr (by exact_mod_cast (le_of_not_ge hsT)))
  · rw [symmDiff_comm, hstrip t s hts,
      predictableMeasure_Ioc_prod _ _ _ _ _ MeasurableSet.univ,
      abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast min_le_min_right T hts))]
    congr 1
    by_cases htT : t ≤ T
    · rw [min_eq_left htT]
    · have hsT : T ≤ s := (le_of_not_ge htT).trans hts
      simp only [min_eq_right (le_of_not_ge htT), min_eq_right hsT, sub_self,
        ENNReal.ofReal_zero]
      exact ENNReal.ofReal_eq_zero.mpr (sub_nonpos.mpr (by exact_mod_cast (le_of_not_ge htT)))

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
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
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
