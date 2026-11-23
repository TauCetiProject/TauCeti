/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Integral.Ito.Isometry
import TauCeti.MeasureTheory.Function.Lp.DominatedConvergence

/-!
# `L²(P)` time continuity and zero expectation of the continuous Brownian Itô integral

Extending `TauCeti.Probability.BrownianMotion.Integral.Ito.Isometry`, this module establishes
`L²(P)` continuity in time and zero expectation for any continuous Itô integral of a
`BrownianIntegrable` integrand, without assuming path continuity of the integrator `W`.

## Main results

* `TauCeti.Probability.IsItoIntegral.continuous_toLp`: `L²(P)` continuity in time.
* `TauCeti.Probability.IsItoIntegral.integral_eq_zero`: zero expectation at every horizon.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology

namespace TauCeti.Probability.IsItoIntegral

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {W H : ℝ≥0 → Ω → ℝ} {I : ℝ≥0 → Ω → ℝ}

/-- **`L²(P)` time continuity**: the `L²(P)` class `t ↦ (hI.memLp hW hH t).toLp (I t)` of a
continuous Itô integral of a `BrownianIntegrable` integrand varies continuously in `t`, without
assuming path continuity of `W`. -/
theorem continuous_toLp (hW : IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I) :
    Continuous fun t : ℝ≥0 ↦ (hI.memLp hW hH t).toLp (I t) := by
  let := (hW.hasLaw_eval 0).isProbabilityMeasure
  refine continuous_iff_continuousAt.2 fun t₀ ↦ tendsto_iff_edist_tendsto_0.2 ?_
  have hne_fst : ∀ᵐ t ∂timeMeasure (t₀ + 1), t ≠ t₀ := by
    simp only [ae_iff, ne_eq, not_not, ofPred_eq_eq_singleton,
      timeMeasure_apply _ (measurableSet_singleton t₀)]
    by_cases h0 : t₀ ∈ Ioc 0 (t₀ + 1) <;> simp [h0]
  have hne : ∀ᵐ p ∂(timeMeasure (t₀ + 1)).prod P, p.1 ≠ t₀ :=
    (Measure.quasiMeasurePreserving_fst (μ := timeMeasure (t₀ + 1)) (ν := P)).ae hne_fst
  have hlim : Tendsto (fun t ↦ eLpNorm
      (fun p : ℝ≥0 × Ω ↦ (uIoc t₀ t).indicator (H · p.2) p.1 - 0) 2
        ((timeMeasure (t₀ + 1)).prod P)) (𝓝 t₀) (𝓝 0) := by
    refine tendsto_eLpNorm_sub_of_ae_tendsto (C := 1) (by norm_num)
      (.of_forall fun t ↦ (hH.memLp_timeMeasure (t₀ + 1)).aestronglyMeasurable.indicator
        ((measurableSet_uIoc (a := t₀) (b := t)).prod MeasurableSet.univ) |>.congr
          (.of_forall fun p ↦ by
            by_cases hp : p.1 ∈ uIoc t₀ t <;> simp [Function.uncurry_def, hp]))
      (hH.memLp_timeMeasure (t₀ + 1))
      (.of_forall fun t ↦ .of_forall fun p ↦ by
        simpa only [Pi.zero_apply, sub_zero, ENNReal.coe_one, one_mul, Function.uncurry_def] using
          eNorm_indicator_le_eNorm_self (H · p.2) p.1)
      (hne.mono fun p hp ↦ tendsto_const_nhds.congr' <| by
        rcases lt_or_gt_of_ne hp with hlt | hgt
        · filter_upwards [eventually_gt_nhds hlt] with t ht
          rw [Set.indicator_of_notMem (by simp [Set.mem_uIoc, hlt.not_gt, ht.not_gt])]
        · filter_upwards [eventually_lt_nhds hgt] with t ht
          rw [Set.indicator_of_notMem (by simp [Set.mem_uIoc, hgt.not_ge, ht.not_ge])])
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (.of_forall fun _ ↦ zero_le)
    (Eventually.mono (Iio_mem_nhds (lt_add_one t₀)) fun t (ht : t < t₀ + 1) ↦ ?_)
  rw [Lp.edist_toLp_toLp]
  simp only [sub_zero]
  rcases le_total t₀ t with hle | hle
  · rw [hI.eLpNorm_sub_eq hW hH hle, uIoc_of_le hle]
    exact eLpNorm_mono_measure _ (Measure.prod_mono (timeMeasure_mono ht.le) le_rfl)
  · rw [← eLpNorm_neg, neg_sub, hI.eLpNorm_sub_eq hW hH hle, uIoc_of_ge hle]
    exact eLpNorm_mono_measure _ (Measure.prod_mono (timeMeasure_mono le_self_add) le_rfl)

/-- Every continuous Itô integral of a `BrownianIntegrable` integrand has expectation zero at every
horizon, without assuming path continuity of `W` or adaptation of `I`. -/
theorem integral_eq_zero (hW : IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I) (T : ℝ≥0) :
    ∫ ω, I T ω ∂P = 0 :=
  (integral_congr_ae (hI.ae_eq_l2Integral hW hH T)).trans (hW.integral_l2Integral T _)

end TauCeti.Probability.IsItoIntegral
