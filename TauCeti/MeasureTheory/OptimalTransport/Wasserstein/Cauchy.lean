/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Basic
public import Mathlib.Probability.Distributions.Cauchy
import TauCeti.Probability.Distributions.Cauchy.Quantile
import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Convolution
import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Rearrangement

/-!
# Wasserstein distances between Cauchy laws

For every `1 ≤ p ≤ ∞`, two Cauchy laws have finite `p`-Wasserstein distance exactly when
their scales agree. In that case their distance is the distance between their locations.
This includes zero scale, where the laws are Dirac masses.

A positive-scale Cauchy law has no finite `p`-moment in this range. Thus its finite-distance
component is not the usual finite-moment space: it contains all translates of the law,
although none of those translates has finite moment. The distance formula exercises the
extended Wasserstein and quantile APIs without imposing moment hypotheses.

The unequal-scale case follows from the quantile formula: the difference of the quantiles
contains a nonzero multiple of the standard Cauchy quantile, which is not integrable.
The equal-scale case uses the moment-free distance-to-a-translate theorem.

## References

* C. Villani, *Optimal Transport: Old and New*, Springer, 2009, Chapter 6,
  for Wasserstein distances and their finite-distance components.
-/

public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace TauCeti

/-- A Cauchy law and a translate of it are at distance equal to the change of location,
even when neither has any finite first moment. -/
@[simp]
theorem wassersteinEDist_cauchyMeasure_same_scale {p : ℝ≥0∞} (hp : 1 ≤ p)
    (m n : ℝ) (γ : ℝ≥0) :
    wassersteinEDist p (cauchyMeasure m γ) (cauchyMeasure n γ) = edist m n := by
  have h := wassersteinEDist_map_add_right_eq_enorm measurable_edist hp
    (cauchyMeasure m γ) (n - m)
  rw [Probability.cauchyMeasure_map_add_const, add_sub_cancel] at h
  simpa [eDist_eq_eNorm_sub, eNorm_sub_rev] using h

/-- Distinct scales force infinite Wasserstein distance, including at exponent `∞`.
No moment condition is placed on either law. -/
theorem wassersteinEDist_cauchyMeasure_eq_top_of_scale_ne {p : ℝ≥0∞} (hp : 1 ≤ p)
    (m n : ℝ) {γ δ : ℝ≥0} (hscale : γ ≠ δ) :
    wassersteinEDist p (cauchyMeasure m γ) (cauchyMeasure n δ) = ∞ := by
  by_contra hfin
  let U := volume.restrict (Ioo (0 : ℝ) 1)
  have hU : IsProbabilityMeasure U := ⟨by simp [U]⟩
  let Q := (cauchyMeasure 0 1).quantile
  let D := fun t ↦ (cauchyMeasure m γ).quantile t - (cauchyMeasure n δ).quantile t
  have hD : Integrable D U := by
    exact memLp_one_iff_integrable.mp <|
      lt_of_le_of_lt (eLpNorm_le_eLpNorm_of_exponent_le hp)
        (by simpa [D, U, wassersteinEDist_eq_eLpNorm_quantile_sub hp] using
          (lt_top_iff_ne_top.mpr hfin))
  have hcoeff : (γ : ℝ) - δ ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hscale)
  have hQ : Integrable Q U := by
    have h := ((hD.sub (integrable_const (m - n))).const_mul ((γ : ℝ) - δ)⁻¹)
    apply h.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    dsimp [D, Q]
    rw [Probability.quantile_cauchyMeasure m γ ht,
      Probability.quantile_cauchyMeasure n δ ht,
      Probability.quantile_cauchyMeasure 0 1 ht]
    simp only [NNReal.coe_one, one_mul, zero_add]
    field_simp; ring
  have hbad : Integrable id (cauchyMeasure 0 1) :=
    (Measure.integrableOn_quantile_iff (cauchyMeasure 0 1)).mp hQ
  exact Probability.not_integrable_id_cauchyMeasure 0 one_ne_zero hbad

/-- The exact extended Wasserstein distance between any two Cauchy laws, for every
`1 ≤ p ≤ ∞`. The zero-scale Dirac boundary is included. -/
theorem wassersteinEDist_cauchyMeasure {p : ℝ≥0∞} (hp : 1 ≤ p)
    (m n : ℝ) (γ δ : ℝ≥0) :
    wassersteinEDist p (cauchyMeasure m γ) (cauchyMeasure n δ) =
      if γ = δ then edist m n else ∞ := by
  split_ifs with h
  · subst δ
    exact wassersteinEDist_cauchyMeasure_same_scale hp m n γ
  · exact wassersteinEDist_cauchyMeasure_eq_top_of_scale_ne hp m n h

/-- Among Cauchy laws, the finite-distance components are exactly the fixed-scale families. -/
theorem wassersteinEDist_cauchyMeasure_ne_top_iff {p : ℝ≥0∞} (hp : 1 ≤ p)
    (m n : ℝ) (γ δ : ℝ≥0) :
    wassersteinEDist p (cauchyMeasure m γ) (cauchyMeasure n δ) ≠ ∞ ↔ γ = δ := by
  rw [wassersteinEDist_cauchyMeasure hp]
  split_ifs <;> simp_all

/-- For `1 ≤ p ≤ ∞`, a Cauchy law has finite `p`-moment exactly at zero scale.
In particular, a positive-scale Cauchy law is not in the finite-moment Wasserstein space,
although its translates are at finite Wasserstein distance from it. -/
@[simp]
theorem hasFiniteMoment_cauchyMeasure_iff {p : ℝ≥0∞} (hp : 1 ≤ p)
    (m : ℝ) (γ : ℝ≥0) :
    HasFiniteMoment p (cauchyMeasure m γ) ↔ γ = 0 := by
  rw [hasFiniteMoment_iff_wassersteinEDist_dirac_ne_top measurable_edist m,
    ← cauchyMeasure_zero_scale m, wassersteinEDist_cauchyMeasure_ne_top_iff hp]
  exact eq_comm

end TauCeti
