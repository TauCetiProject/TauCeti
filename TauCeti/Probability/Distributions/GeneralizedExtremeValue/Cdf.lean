/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.GeneralizedExtremeValue.Basic

/-!
# Cumulative distribution function of the generalized extreme-value law

For positive scale, the generalized extreme-value cdf is

`exp (-((1 + ξ * ((x - m) / s)) ^ (-1 / ξ)))`

where the parenthesized term is positive. At the finite endpoint it extends by zero for positive
shape and by one for negative shape. At shape zero the law is Gumbel and uses the corresponding
Gumbel cdf.

The comparison theorem for `generalizedExtremeValueMap` records the inverse relation used both by
the cdf here and by quantiles of the law.

## References

* S. Coles, *An Introduction to Statistical Modeling of Extreme Values*, Springer (2001),
  Chapter 3.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set

namespace TauCeti.Probability

variable {m s ξ x e : ℝ}

/-- For positive shape, comparison with the generalized extreme-value transformation reduces to
comparison with a negative real power of the positive exponential input. -/
theorem generalizedExtremeValueMap_le_iff_of_shape_pos (hs : 0 < s) (hξ : 0 < ξ)
    (he : 0 < e) :
    generalizedExtremeValueMap m s ξ e ≤ x ↔
      e ^ (-ξ) ≤ 1 + ξ * ((x - m) / s) := by
  rw [generalizedExtremeValueMap_of_shape_ne_zero hξ.ne']
  have hrpow : exp (-ξ * log e) = e ^ (-ξ) := by
    rw [rpow_def_of_pos he]
    congr 1
    ring
  rw [hrpow]
  have halgebra :
      m + s * (e ^ (-ξ) - 1) / ξ ≤ x ↔
        e ^ (-ξ) ≤ 1 + ξ * ((x - m) / s) := by
    constructor
    · intro h
      have hmul : s * (e ^ (-ξ) - 1) ≤ (x - m) * ξ :=
        (div_le_iff₀ hξ).mp (by linarith)
      have hdiv : e ^ (-ξ) - 1 ≤ (x - m) * ξ / s :=
        (le_div_iff₀ hs).2 (by simpa [mul_comm] using hmul)
      calc
        e ^ (-ξ) ≤ 1 + (x - m) * ξ / s := by linarith
        _ = 1 + ξ * ((x - m) / s) := by ring
    · intro h
      have hdiv : e ^ (-ξ) - 1 ≤ (x - m) * ξ / s := by
        rw [show 1 + ξ * ((x - m) / s) = 1 + (x - m) * ξ / s by ring] at h
        linarith
      have hmul : s * (e ^ (-ξ) - 1) ≤ (x - m) * ξ := by
        simpa [mul_comm] using (le_div_iff₀ hs).mp hdiv
      have := (div_le_iff₀ hξ).2 hmul
      linarith
  exact halgebra

/-- For negative shape, comparison with the generalized extreme-value transformation reverses the
algebraic comparison before reducing to a positive real power of the exponential input. -/
theorem generalizedExtremeValueMap_le_iff_of_shape_neg (hs : 0 < s) (hξ : ξ < 0)
    (he : 0 < e) :
    generalizedExtremeValueMap m s ξ e ≤ x ↔
      1 + ξ * ((x - m) / s) ≤ e ^ (-ξ) := by
  rw [generalizedExtremeValueMap_of_shape_ne_zero hξ.ne]
  have hrpow : exp (-ξ * log e) = e ^ (-ξ) := by
    rw [rpow_def_of_pos he]
    congr 1
    ring
  rw [hrpow]
  constructor
  · intro h
    have hmul : (x - m) * ξ ≤ s * (e ^ (-ξ) - 1) :=
      (div_le_iff_of_neg hξ).mp (by linarith)
    have hdiv : (x - m) * ξ / s ≤ e ^ (-ξ) - 1 :=
      (div_le_iff₀ hs).2 (by simpa [mul_comm] using hmul)
    calc
      1 + ξ * ((x - m) / s) = 1 + (x - m) * ξ / s := by ring
      _ ≤ e ^ (-ξ) := by linarith
  · intro h
    have hdiv : (x - m) * ξ / s ≤ e ^ (-ξ) - 1 := by
      rw [show 1 + ξ * ((x - m) / s) = 1 + (x - m) * ξ / s by ring] at h
      linarith
    have hmul : (x - m) * ξ ≤ s * (e ^ (-ξ) - 1) := by
      simpa [mul_comm] using (div_le_iff₀ hs).mp hdiv
    have := (div_le_iff_of_neg hξ).2 hmul
    linarith

/-- On the interior of its support, the generalized extreme-value transformation is at most `x`
exactly when the source exponential variable exceeds the inverse threshold. -/
theorem generalizedExtremeValueMap_le_iff (hs : 0 < s) (hξ : ξ ≠ 0) (he : 0 < e)
    (hx : 0 < 1 + ξ * ((x - m) / s)) :
    generalizedExtremeValueMap m s ξ e ≤ x ↔
      (1 + ξ * ((x - m) / s)) ^ (-1 / ξ) ≤ e := by
  rcases lt_or_gt_of_ne hξ with hξ | hξ
  · rw [generalizedExtremeValueMap_le_iff_of_shape_neg hs hξ he]
    convert (Real.rpow_inv_le_iff_of_pos hx.le he.le (neg_pos.mpr hξ)).symm using 1
    field_simp
  · rw [generalizedExtremeValueMap_le_iff_of_shape_pos hs hξ he]
    convert (Real.rpow_inv_le_iff_of_neg hx he (neg_neg_of_pos hξ)).symm using 1
    field_simp

/-- The cdf of a positive-scale, nonzero-shape generalized extreme-value law. The formula includes
the zero or one extension beyond its finite support endpoint. -/
theorem cdf_generalizedExtremeValueMeasure_eq (hs : 0 < s) (hξ : ξ ≠ 0) (m x : ℝ) :
    cdf (generalizedExtremeValueMeasure m s ξ) x =
      if 0 < 1 + ξ * ((x - m) / s) then
        exp (-((1 + ξ * ((x - m) / s)) ^ (-1 / ξ)))
      else if 0 < ξ then 0 else 1 := by
  let _ := isProbabilityMeasure_generalizedExtremeValueMeasure hs m ξ
  let _ : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure one_pos
  rw [cdf_eq_real, generalizedExtremeValueMeasure_of_pos hs, Measure.real, Measure.map_apply
    (measurable_generalizedExtremeValueMap_right m s ξ) measurableSet_Iic]
  by_cases hx : 0 < 1 + ξ * ((x - m) / s)
  · rw [ite_eq_left hx]
    have hpre :
        generalizedExtremeValueMap m s ξ ⁻¹' Iic x =ᵐ[expMeasure 1]
          Ici ((1 + ξ * ((x - m) / s)) ^ (-1 / ξ)) := by
      filter_upwards [ae_pos_expMeasure 1] with e he
      apply propext
      exact generalizedExtremeValueMap_le_iff hs hξ he hx
    have ht : 0 < (1 + ξ * ((x - m) / s)) ^ (-1 / ξ) :=
      rpow_pos_of_pos hx _
    have hsingleton :
        expMeasure 1 {(1 + ξ * ((x - m) / s)) ^ (-1 / ξ)} = 0 := by
      rw [expMeasure_eq_withDensity]
      exact withDensity_absolutelyContinuous volume _ (measure_singleton _)
    rw [measure_congr hpre, ← measure_congr (Ioi_ae_eq_Ici' hsingleton),
      measure_Ioi_expMeasure one_pos, ite_eq_left ht.le,
      one_mul, ENNReal.toReal_ofReal (exp_nonneg _)]
  · rw [ite_eq_right hx]
    rcases lt_or_gt_of_ne hξ with hξ | hξ
    · rw [ite_eq_right (not_lt.mpr hξ.le)]
      have hpre : generalizedExtremeValueMap m s ξ ⁻¹' Iic x =ᵐ[expMeasure 1] univ := by
        filter_upwards [ae_pos_expMeasure 1] with e he
        apply propext
        simp only [mem_preimage, mem_Iic, mem_univ, iff_true]
        exact (generalizedExtremeValueMap_le_iff_of_shape_neg hs hξ he).2
          ((le_of_not_gt hx).trans (rpow_pos_of_pos he _).le)
      rw [measure_congr hpre, measure_univ, ENNReal.toReal_one]
    · rw [ite_eq_left hξ]
      have hpre : generalizedExtremeValueMap m s ξ ⁻¹' Iic x =ᵐ[expMeasure 1] ∅ := by
        filter_upwards [ae_pos_expMeasure 1] with e he
        apply propext
        simp only [mem_preimage, mem_Iic, mem_empty_iff_false, iff_false]
        exact fun hle ↦ (not_le_of_gt (rpow_pos_of_pos he _))
          ((generalizedExtremeValueMap_le_iff_of_shape_pos hs hξ he).1 hle |>.trans
            (le_of_not_gt hx))
      rw [measure_congr hpre, measure_empty, ENNReal.toReal_zero]

/-- At shape zero, the generalized extreme-value cdf is the Gumbel cdf. -/
theorem cdf_generalizedExtremeValueMeasure_zero (hs : 0 < s) (m x : ℝ) :
    cdf (generalizedExtremeValueMeasure m s 0) x =
      exp (-exp (-((x - m) / s))) := by
  rw [generalizedExtremeValueMeasure_zero, cdf_gumbelMeasure_eq hs]

end TauCeti.Probability
