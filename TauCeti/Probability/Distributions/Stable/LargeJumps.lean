/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Stable.Approximation.Basic
public import TauCeti.Probability.Distributions.CompoundPoisson.Moments
public import TauCeti.Probability.Distributions.Pareto.Basic
import TauCeti.Probability.Distributions.Affine

/-!
# Absolute moments of large stable jumps

The absolute size of a stable Lévy jump conditioned to exceed a positive cutoff has a
Pareto law, independently of skewness. Consequently its absolute real-power moments exist
exactly below the stable shape. The compound Poisson law of these large jumps has the same
positive-order moment threshold, including at full skewness and at the critical exponent.

These results isolate the large-jump contribution to the moment theory of stable laws.
They concern the finite-intensity component, before combining it with the small-jump remainder.

## References

* J. P. Nolan, *Univariate Stable Distributions: Models for Heavy Tailed Data*, Springer,
  2020, chapter 1.

The jump-size identification uses the two Pareto restrictions of `stableLevyMeasure`;
the compound Poisson criterion uses its Poisson-mixture moment API.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal

namespace TauCeti.Probability

variable {α β ε q : ℝ}

/-- The normalized large-jump law has a finite absolute real-power moment exactly below
the stable shape. Negative orders are allowed because the cutoff is positive. -/
@[simp]
theorem integrable_abs_rpow_cond_stableLevyMeasure_iff (hα : α ∈ Ioo 0 2)
    (hβ : |β| ≤ 1) (hε : 0 < ε) :
    Integrable (fun x : ℝ ↦ |x| ^ q)
      (cond (stableLevyMeasure α β) {x : ℝ | ε < |x|}) ↔ q < α := by
  have h := integrable_map_measure
    (μ := cond (stableLevyMeasure α β) {x : ℝ | ε < |x|})
    (f := abs) (g := fun x : ℝ ↦ x ^ q) (by fun_prop) continuous_abs.measurable.aemeasurable
  rw [map_abs_cond_stableLevyMeasure hα hβ hε] at h
  exact h.symm.trans (integrable_rpow_paretoMeasure_iff hε hα.1 q)

/-- Below the shape, the normalized absolute jump moment is the Pareto moment. -/
theorem integral_abs_rpow_cond_stableLevyMeasure (hα : α ∈ Ioo 0 2) (hβ : |β| ≤ 1)
    (hε : 0 < ε) (hq : q < α) :
    ∫ x, |x| ^ q ∂cond (stableLevyMeasure α β) {x : ℝ | ε < |x|} =
      α * ε ^ q / (α - q) := by
  rw [← integral_map continuous_abs.measurable.aemeasurable (by fun_prop :
    AEStronglyMeasurable (fun x : ℝ ↦ x ^ q)
      ((cond (stableLevyMeasure α β) {x : ℝ | ε < |x|}).map abs)),
    map_abs_cond_stableLevyMeasure hα hβ hε, integral_rpow_paretoMeasure hε hα.1 hq]

/-- The compound Poisson component of stable jumps larger than a positive cutoff has a
finite absolute moment exactly below the stable shape. The critical exponent diverges. -/
@[simp]
theorem integrable_abs_rpow_compoundPoissonMeasure_stableLevyMeasure_iff
    (hα : α ∈ Ioo 0 2) (hβ : |β| ≤ 1) (hε : 0 < ε) (hq : 0 < q) :
    Integrable (fun x : ℝ ↦ |x| ^ q)
      (compoundPoissonMeasure
        ((stableLevyMeasure α β) {x : ℝ | ε < |x|}).toNNReal
        (cond (stableLevyMeasure α β) {x : ℝ | ε < |x|})) ↔ q < α := by
  let _ := isProbabilityMeasure_cond_stableLevyMeasure hα hβ hε
  have hrate : ((stableLevyMeasure α β) {x : ℝ | ε < |x|}).toNNReal ≠ 0 := by
    exact (ENNReal.toNNReal_pos (stableLevyMeasure_abs_gt_pos hα hβ hε).ne'
      (stableLevyMeasure_abs_gt_ne_top hε)).ne'
  have hmem := memLp_id_compoundPoissonMeasure_iff
    (μ := cond (stableLevyMeasure α β) {x : ℝ | ε < |x|})
    (p := ENNReal.ofReal q) (by positivity) ENNReal.ofReal_ne_top hrate
  rw [← integrable_norm_rpow_iff (by fun_prop) (by positivity) ENNReal.ofReal_ne_top,
    ← integrable_norm_rpow_iff (by fun_prop) (by positivity) ENNReal.ofReal_ne_top] at hmem
  simpa only [id_eq, Real.norm_eq_abs, ENNReal.toReal_ofReal hq.le] using
    hmem.trans (integrable_abs_rpow_cond_stableLevyMeasure_iff hα hβ hε)

/-- Sine compensation does not change the large-jump moment threshold. Thus every
positive-cutoff compensated stable approximation has finite absolute `q`th moment exactly
when `q < α`. -/
@[simp]
theorem integrable_abs_rpow_stableCompensatedPoissonMeasure_iff
    (hα : α ∈ Ioo 0 2) (hβ : |β| ≤ 1) (hε : 0 < ε) (hq : 0 < q) :
    Integrable (fun x : ℝ ↦ |x| ^ q) (stableCompensatedPoissonMeasure α β ε) ↔ q < α := by
  let μ := compoundPoissonMeasure
    ((stableLevyMeasure α β) {x : ℝ | ε < |x|}).toNNReal
    (cond (stableLevyMeasure α β) {x : ℝ | ε < |x|})
  let c := ∫ x in {x : ℝ | ε < |x|}, sin x ∂stableLevyMeasure α β
  let _ := isProbabilityMeasure_cond_stableLevyMeasure hα hβ hε
  have h := memLp_id_map_affine_iff (μ := μ) (a := -c) (b := 1) (p := ENNReal.ofReal q)
    one_ne_zero
  rw [← integrable_norm_rpow_iff (by fun_prop) (by positivity) ENNReal.ofReal_ne_top,
    ← integrable_norm_rpow_iff (by fun_prop) (by positivity) ENNReal.ofReal_ne_top] at h
  simp only [id_eq, Real.norm_eq_abs, ENNReal.toReal_ofReal hq.le] at h
  rw [stableCompensatedPoissonMeasure_def]
  simpa only [one_mul, sub_eq_add_neg, add_comm] using h.trans
    (integrable_abs_rpow_compoundPoissonMeasure_stableLevyMeasure_iff hα hβ hε hq)

end TauCeti.Probability
