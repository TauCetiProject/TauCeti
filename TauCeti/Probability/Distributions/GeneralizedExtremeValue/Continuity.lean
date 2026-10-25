/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.GeneralizedExtremeValue.Basic
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import TauCeti.MeasureTheory.Measure.ProbabilityMeasure.Map
import Mathlib.Analysis.Calculus.DSlope

/-!
# Weak continuity of generalized extreme-value laws

Generalized extreme-value laws depend jointly weakly continuously on location, positive scale,
and real shape. In particular, the nonzero-shape laws converge to the Gumbel law as the shape
tends to zero, from either side. The topology here is that of `ProbabilityMeasure ℝ`.

The apparent singularity of the defining exponential transformation at shape zero is removable:
the divided difference of the exponential extends there by its derivative. A common rate-one
exponential variable therefore realizes the parameter limits pointwise, and its pushforward laws
converge weakly. No moment hypotheses are needed, even when the shapes cross moment thresholds.

## Main results

* `TauCeti.Probability.continuous_generalizedExtremeValueMeasure` gives joint weak continuity.
* `TauCeti.Probability.tendsto_generalizedExtremeValueMeasure_nhds_zero_gumbelMeasure`
  gives the Gumbel limit.

## References

* S. Coles, *An Introduction to Statistical Modeling of Extreme Values*, Springer (2001),
  Chapter 3.
-/

public section

open Filter MeasureTheory ProbabilityTheory Set Topology

namespace TauCeti.Probability

private theorem generalizedExtremeValueMap_eq_dslope (m s ξ e : ℝ) :
    generalizedExtremeValueMap m s ξ e =
      m - s * Real.log e * dslope Real.exp 0 (-ξ * Real.log e) := by
  by_cases hξ : ξ = 0
  · simp [hξ, Real.deriv_exp]
  · rw [generalizedExtremeValueMap_of_shape_ne_zero hξ]
    have h := sub_smul_dslope Real.exp 0 (-ξ * Real.log e)
    simp only [sub_zero, smul_eq_mul, Real.exp_zero, neg_mul] at h
    field_simp
    linear_combination -s * h

private theorem continuous_generalizedExtremeValueMap_left (e : ℝ) :
    Continuous fun p : (ℝ × ℝ) × ℝ =>
      generalizedExtremeValueMap p.1.1 p.1.2 p.2 e := by
  have hd : Continuous (dslope Real.exp 0) := by
    exact continuousOn_univ.1
      ((continuousOn_dslope (s := Set.univ) Filter.univ_mem).2
        ⟨Real.continuous_exp.continuousOn, Real.differentiable_exp 0⟩)
  simp_rw [generalizedExtremeValueMap_eq_dslope]
  exact (continuous_fst.fst).sub
    ((continuous_fst.snd.mul_const _).mul
      (hd.comp (continuous_snd.neg.mul_const _)))

/-- Generalized extreme-value laws depend jointly weakly continuously on location, positive
scale, and shape, including shape zero where the law is Gumbel. -/
theorem continuous_generalizedExtremeValueMeasure :
    Continuous (Y := ProbabilityMeasure ℝ) (fun p : (ℝ × Ioi (0 : ℝ)) × ℝ =>
      (⟨generalizedExtremeValueMeasure p.1.1 p.1.2 p.2,
        isProbabilityMeasure_generalizedExtremeValueMeasure p.1.2.2 p.1.1 p.2⟩ :
        ProbabilityMeasure ℝ)) := by
  let P : ProbabilityMeasure ℝ := ⟨expMeasure 1, isProbabilityMeasure_expMeasure one_pos⟩
  have h := P.continuous_map_of_forall_continuous
    (f := fun p : (ℝ × Ioi (0 : ℝ)) × ℝ =>
      generalizedExtremeValueMap p.1.1 p.1.2 p.2)
    (fun p => (measurable_generalizedExtremeValueMap_right _ _ _).aemeasurable)
    (fun e => (continuous_generalizedExtremeValueMap_left e).comp
      ((continuous_fst.fst.prodMk
        (continuous_subtype_val.comp continuous_fst.snd)).prodMk continuous_snd))
  refine h.congr fun p => ?_
  apply ProbabilityMeasure.toMeasure_injective
  rw [ProbabilityMeasure.toMeasure_map]
  exact (generalizedExtremeValueMeasure_of_pos p.1.2.2 p.1.1 p.2).symm

/-- As the shape tends to zero from either side, a fixed-location, positive-scale generalized
extreme-value law converges weakly to the Gumbel law with that location and scale. -/
theorem tendsto_generalizedExtremeValueMeasure_nhds_zero_gumbelMeasure
    {s : ℝ} (hs : 0 < s) (m : ℝ) :
    Tendsto (β := ProbabilityMeasure ℝ) (fun ξ : ℝ =>
      (⟨generalizedExtremeValueMeasure m s ξ,
        isProbabilityMeasure_generalizedExtremeValueMeasure hs m ξ⟩ : ProbabilityMeasure ℝ))
      (𝓝 0) (𝓝 (⟨gumbelMeasure m s,
        isProbabilityMeasure_gumbelMeasure hs m⟩ : ProbabilityMeasure ℝ)) := by
  have h := (continuous_generalizedExtremeValueMeasure.comp
    (continuous_const.prodMk continuous_id :
      Continuous fun ξ : ℝ => ((m, (⟨s, hs⟩ : Ioi (0 : ℝ))), ξ))).tendsto 0
  have hzero : (⟨generalizedExtremeValueMeasure m s 0,
      isProbabilityMeasure_generalizedExtremeValueMeasure hs m 0⟩ : ProbabilityMeasure ℝ) =
      ⟨gumbelMeasure m s, isProbabilityMeasure_gumbelMeasure hs m⟩ :=
    Subtype.ext (generalizedExtremeValueMeasure_zero m s)
  rw [← hzero]
  exact h

end TauCeti.Probability
