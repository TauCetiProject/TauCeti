/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.GeneralizedPareto.Basic
public import TauCeti.Probability.HasLaw

/-!
# Threshold stability of generalized Pareto laws

If `X` has generalized Pareto scale `s > 0` and shape `ξ`, then the excess `X - v`,
conditional on `X > v`, has scale `s + ξ * v` and the same shape. The threshold must satisfy
`v ≥ 0` and `s + ξ * v > 0`; for negative shape this excludes the finite upper endpoint.

The measure identity is accompanied by its `HasLaw` form for arbitrary random variables.
The exponential construction turns a threshold into elapsed exponential time, so its
memorylessness gives the conditional excess law without a density calculation.

## References

* S. Coles, *An Introduction to Statistical Modeling of Extreme Values*, Springer (2001),
  Chapter 4.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace TauCeti.Probability

private theorem exists_generalizedParetoMap_eq {s ξ v : ℝ} (hs : 0 < s) (hv : 0 ≤ v)
    (hw : 0 < s + ξ * v) :
    ∃ a : ℝ, 0 ≤ a ∧ generalizedParetoMap s ξ a = v := by
  by_cases hξ : ξ = 0
  · refine ⟨v / s, div_nonneg hv hs.le, ?_⟩
    rw [hξ, generalizedParetoMap_zero]
    field_simp
  have hw' : 0 < 1 + ξ * v / s := by
    have := div_pos hw hs
    simpa [add_div, hs.ne'] using this
  have hinv := generalizedParetoMap_log_div hs.ne' hξ hw'
  refine ⟨_, ?_, hinv⟩
  rwa [← generalizedParetoMap_nonneg_iff hs ξ, hinv]

private theorem generalizedParetoMap_sub_threshold (s ξ a e : ℝ) :
    generalizedParetoMap s ξ e - generalizedParetoMap s ξ a =
      generalizedParetoMap (s + ξ * generalizedParetoMap s ξ a) ξ (e - a) := by
  by_cases hξ : ξ = 0
  · simp only [hξ, generalizedParetoMap_zero, zero_mul, add_zero]
    ring
  simp only [generalizedParetoMap_of_shape_ne_zero hξ]
  rw [mul_sub ξ e a, Real.exp_sub]
  field_simp
  ring

/-- Conditional excesses of a generalized Pareto law have the same shape and scale `s + ξ * v`.
For negative shape, the admissibility condition keeps the threshold below the upper endpoint. -/
theorem map_sub_cond_generalizedParetoMeasure {s ξ v : ℝ} (hs : 0 < s) (hv : 0 ≤ v)
    (hw : 0 < s + ξ * v) :
    (cond (generalizedParetoMeasure s ξ) (Ioi v)).map (fun x => x - v) =
      generalizedParetoMeasure (s + ξ * v) ξ := by
  obtain ⟨a, ha, hav⟩ := exists_generalizedParetoMap_eq hs hv hw
  have hpre : generalizedParetoMap s ξ ⁻¹' Ioi v = Ioi a := by
    ext e
    simp only [mem_preimage, mem_Ioi, ← hav]
    exact (strictMono_generalizedParetoMap hs ξ).lt_iff_lt
  have hG : HasLaw (generalizedParetoMap s ξ) (generalizedParetoMeasure s ξ)
      (expMeasure 1) :=
    ⟨(measurable_generalizedParetoMap_right s ξ).aemeasurable,
      (generalizedParetoMeasure_of_pos hs ξ).symm⟩
  have hcond := (hG.cond (s := Ioi v) measurableSet_Ioi).map_eq
  rw [hpre] at hcond
  rw [← hcond, Measure.map_map (by fun_prop) (measurable_generalizedParetoMap_right s ξ)]
  calc
    (cond (expMeasure 1) (Ioi a)).map
        ((fun x => x - v) ∘ generalizedParetoMap s ξ) =
        (cond (expMeasure 1) (Ioi a)).map
          (generalizedParetoMap (s + ξ * v) ξ ∘ (fun e => e - a)) := by
      congr 1
      funext e
      simpa only [Function.comp_apply, hav] using generalizedParetoMap_sub_threshold s ξ a e
    _ = ((cond (expMeasure 1) (Ioi a)).map (fun e => e - a)).map
        (generalizedParetoMap (s + ξ * v) ξ) := by
      rw [Measure.map_map (measurable_generalizedParetoMap_right _ _) (by fun_prop)]
    _ = generalizedParetoMeasure (s + ξ * v) ξ := by
      rw [map_sub_cond_expMeasure one_pos ha, generalizedParetoMeasure_of_pos hw]

/-- If `X` has a generalized Pareto law, its excess above an admissible threshold has the
updated generalized Pareto law under the source measure conditioned on exceeding that threshold.
Only almost-everywhere measurability of `X`, supplied by `HasLaw`, is required. -/
theorem hasLaw_sub_cond_generalizedParetoMeasure
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}
    {s ξ v : ℝ} (hs : 0 < s) (hv : 0 ≤ v) (hw : 0 < s + ξ * v)
    (hX : HasLaw X (generalizedParetoMeasure s ξ) P) :
    HasLaw (fun ω => X ω - v) (generalizedParetoMeasure (s + ξ * v) ξ)
      (cond P {ω | v < X ω}) := by
  have h := (hasLaw_map (by fun_prop : Measurable fun x : ℝ => x - v).aemeasurable).comp
    (hX.cond (s := Ioi v) measurableSet_Ioi)
  rwa [map_sub_cond_generalizedParetoMeasure hs hv hw] at h

end TauCeti.Probability
