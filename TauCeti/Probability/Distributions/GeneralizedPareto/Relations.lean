/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.GeneralizedPareto.Cdf
public import TauCeti.Probability.Distributions.Pareto.Basic
public import TauCeti.Probability.Distributions.Uniform.Basic
import TauCeti.Probability.Distributions.Affine

/-!
# Special cases of the generalized Pareto distribution

The generalized Pareto family contains the uniform law at shape `-1`. At positive shape, adding
the lower endpoint `s / ξ` turns the law into a Pareto law with threshold `s / ξ` and shape
`1 / ξ`. Equivalently, subtracting the threshold from a Pareto variable gives a generalized
Pareto variable.

These measure identities are accompanied by random-variable forms so that the specializations can
be used without manually rewriting pushforwards.

## References

* S. Coles, *An Introduction to Statistical Modeling of Extreme Values*, Springer (2001),
  Chapter 4.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace TauCeti.Probability

/-- A generalized Pareto law of shape `-1` is uniform on the interval from zero to its scale.
For a nonpositive scale, both sides are the zero measure. -/
@[simp]
theorem generalizedParetoMeasure_neg_one (s : ℝ) :
    generalizedParetoMeasure s (-1) = uniformMeasure 0 s := by
  rcases le_or_gt s 0 with hs | hs
  · rw [generalizedParetoMeasure_of_nonpos hs, uniformMeasure_eq_zero_of_le hs]
  let _ := isProbabilityMeasure_generalizedParetoMeasure hs (-1)
  let _ := isProbabilityMeasure_uniformMeasure hs
  apply Measure.eq_of_cdf
  ext x
  by_cases hx : x ≤ 0
  · rw [cdf_generalizedParetoMeasure_eq hs, cdf_uniformMeasure hs]
    simp [hx]
  by_cases hxs : s ≤ x
  · have hsupport : ¬0 < 1 + -x / s := by
      have hrewrite : 1 + -x / s = (s - x) / s := by
        field_simp
        ring
      rw [hrewrite]
      exact not_lt.mpr (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hxs) hs.le)
    rw [cdf_generalizedParetoMeasure_eq hs, cdf_uniformMeasure hs]
    norm_num [hx, hxs, hsupport]
  · have hsupport : 0 < 1 + -x / s := by
      have hrewrite : 1 + -x / s = (s - x) / s := by
        field_simp
        ring
      rw [hrewrite]
      exact div_pos (sub_pos.mpr (lt_of_not_ge hxs)) hs
    rw [cdf_generalizedParetoMeasure_eq hs, cdf_uniformMeasure hs]
    norm_num [hx, hxs, hsupport]
    field_simp

/-- A random variable with generalized Pareto shape `-1` is uniform from zero to its scale. -/
theorem HasLaw.generalizedPareto_neg_one {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} {s : ℝ} (hX : HasLaw X (generalizedParetoMeasure s (-1)) P) :
    HasLaw X (uniformMeasure 0 s) P := by
  rwa [generalizedParetoMeasure_neg_one] at hX

/-- Translating a positive-shape generalized Pareto law by `s / ξ` gives a Pareto law with
threshold `s / ξ` and shape `1 / ξ`. -/
theorem map_add_generalizedParetoMeasure_eq_paretoMeasure {s ξ : ℝ} (hs : 0 < s)
    (hξ : 0 < ξ) :
    (generalizedParetoMeasure s ξ).map (fun x => s / ξ + x) =
      paretoMeasure (s / ξ) (1 / ξ) := by
  let _ := isProbabilityMeasure_generalizedParetoMeasure hs ξ
  let _ := isProbabilityMeasure_paretoMeasure (div_pos hs hξ) (one_div_pos.mpr hξ)
  apply Measure.eq_of_cdf
  ext x
  have hfun : (fun y : ℝ => s / ξ + y) = fun y => s / ξ + 1 * y := by
    funext y
    ring
  rw [hfun, cdf_map_affine_of_pos (a := s / ξ) (b := 1) one_pos,
    cdf_generalizedParetoMeasure_eq hs,
    cdf_paretoMeasure_eq (div_pos hs hξ) (one_div_pos.mpr hξ)]
  simp only [div_one]
  by_cases hx : x < s / ξ
  · have hdiff : x - s / ξ ≤ 0 := by linarith
    simp only [hdiff, hx, ↓reduceIte]
  · have htx : s / ξ ≤ x := not_lt.mp hx
    rcases htx.eq_or_lt with rfl | htx
    · have hratio : s / ξ / (s / ξ) = 1 := div_self (div_ne_zero hs.ne' hξ.ne')
      simp [hratio]
    have hxpos : 0 < x := (div_pos hs hξ).trans htx
    have hdiff : ¬x - s / ξ ≤ 0 := by linarith
    have hbase : 0 < 1 + ξ * (x - s / ξ) / s := by
      have hrewrite : 1 + ξ * (x - s / ξ) / s = ξ * x / s := by
        field_simp
        ring
      rw [hrewrite]
      positivity
    simp only [hdiff, hξ.ne', hbase, hx, ↓reduceIte]
    congr 1
    have hrewrite : 1 + ξ * (x - s / ξ) / s = ξ * x / s := by
      field_simp
      ring
    calc
      (1 + ξ * (x - s / ξ) / s) ^ (-1 / ξ) =
          (ξ * x / s) ^ (-(1 / ξ)) := by
        rw [hrewrite]
        congr 1
        ring
      _ = (ξ * x / s)⁻¹ ^ (1 / ξ) := Real.rpow_neg_eq_inv_rpow _ _
      _ = (s / ξ / x) ^ (1 / ξ) := by
        congr 1
        field_simp

/-- Adding the threshold to a generalized Pareto random variable of positive shape produces a
Pareto random variable. -/
theorem HasLaw.add_generalizedPareto {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} {s ξ : ℝ} (hX : HasLaw X (generalizedParetoMeasure s ξ) P)
    (hs : 0 < s) (hξ : 0 < ξ) :
    HasLaw (fun ω => s / ξ + X ω) (paretoMeasure (s / ξ) (1 / ξ)) P := by
  rw [← map_add_generalizedParetoMeasure_eq_paretoMeasure hs hξ]
  exact (hasLaw_map (by fun_prop : Measurable fun x : ℝ => s / ξ + x).aemeasurable).comp hX

/-- Subtracting the threshold from a Pareto law gives a generalized Pareto law whose scale is
the threshold divided by the Pareto shape and whose shape is the reciprocal Pareto shape. -/
theorem map_sub_paretoMeasure_eq_generalizedParetoMeasure {t r : ℝ} (ht : 0 < t)
    (hr : 0 < r) :
    (paretoMeasure t r).map (fun x => x - t) = generalizedParetoMeasure (t / r) (1 / r) := by
  have hscale : 0 < t / r := div_pos ht hr
  have hshape : 0 < 1 / r := one_div_pos.mpr hr
  have hadd := map_add_generalizedParetoMeasure_eq_paretoMeasure hscale hshape
  have hthreshold : (t / r) / (1 / r) = t := by field_simp
  have hshapeinv : 1 / (1 / r) = r := by field_simp
  rw [hthreshold, hshapeinv] at hadd
  rw [← hadd, Measure.map_map (by fun_prop) (by fun_prop)]
  have hcomp : (fun x => x - t) ∘ (fun x => t + x) = id := by
    funext x
    simp only [Function.comp_apply, id_eq]
    ring
  rw [hcomp, Measure.map_id]

/-- Subtracting the threshold from a Pareto random variable produces the corresponding
generalized Pareto random variable. -/
theorem HasLaw.sub_pareto {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} {t r : ℝ} (hX : HasLaw X (paretoMeasure t r) P)
    (ht : 0 < t) (hr : 0 < r) :
    HasLaw (fun ω => X ω - t) (generalizedParetoMeasure (t / r) (1 / r)) P := by
  rw [← map_sub_paretoMeasure_eq_generalizedParetoMeasure ht hr]
  exact (hasLaw_map (by fun_prop : Measurable fun x : ℝ => x - t).aemeasurable).comp hX

end TauCeti.Probability
