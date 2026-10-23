/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.AsymmetricLaplace.Basic

/-!
# Exponential moments of asymmetric Laplace laws

For positive left and right rates `l` and `r`, the exponential-integrability domain is
exactly `(-l, r)`. On this interval the moment-generating function is
`exp (m * t) * r * l / ((r - t) * (l + t))`, and its logarithm separates into a location
term and two exponential cumulants. Both boundary points are excluded.

The formulas use the existing construction as a translated difference of independent
exponential variables, so no further integration against the density is needed.

## Reference

* S. Kotz, T. J. Kozubowski, K. Podgórski, *The Laplace Distribution and Generalizations*,
  Birkhäuser (2001), ch. 3.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set

namespace TauCeti.Probability

variable {m l r t : ℝ}

private theorem mgf_id_asymmetricLaplaceMeasure_eq_mul (hl : 0 < l) (hr : 0 < r) :
    mgf id (asymmetricLaplaceMeasure m l r) t =
      exp (t * m) * (mgf id (expMeasure r) t * mgf id (expMeasure l) (-t)) := by
  have := isProbabilityMeasure_expMeasure hl
  have := isProbabilityMeasure_expMeasure hr
  have hfactor : ∀ z : ℝ × ℝ, exp (t * (m + z.1 - z.2)) =
      exp (t * m) * (exp (t * z.1) * exp (-t * z.2)) := by
    intro z
    rw [← exp_add, ← exp_add]
    congr 1
    ring
  rw [asymmetricLaplaceMeasure_of_pos hl hr, mgf_id_map (by fun_prop), mgf]
  simp_rw [hfactor]
  rw [integral_const_mul, integral_prod_mul (fun x : ℝ ↦ exp (t * x))
    (fun y : ℝ ↦ exp (-t * y))]
  simp only [mgf, id_eq]

/-- Exponential moments of an asymmetric Laplace law exist exactly between the negative
left rate and the right rate, with neither endpoint included. -/
@[simp]
theorem integrableExpSet_id_asymmetricLaplaceMeasure (hl : 0 < l) (hr : 0 < r) :
    integrableExpSet id (asymmetricLaplaceMeasure m l r) = Ioo (-l) r := by
  have := isProbabilityMeasure_expMeasure hl
  have := isProbabilityMeasure_expMeasure hr
  have := isProbabilityMeasure_asymmetricLaplaceMeasure hl hr m
  ext t
  rw [mem_Ioo]
  have hright : 0 < mgf id (expMeasure r) t ↔ t < r := by
    rw [mgf_pos_iff]
    exact Set.ext_iff.mp (integrableExpSet_id_expMeasure hr) t
  have hleft : 0 < mgf id (expMeasure l) (-t) ↔ -l < t := by
    rw [mgf_pos_iff]
    have h : Integrable (fun x : ℝ ↦ exp (-t * x)) (expMeasure l) ↔ -t < l :=
      Set.ext_iff.mp (integrableExpSet_id_expMeasure hl) (-t)
    exact h.trans neg_lt
  have hdomain : t ∈ integrableExpSet id (asymmetricLaplaceMeasure m l r) ↔
      0 < mgf id (asymmetricLaplaceMeasure m l r) t := mgf_pos_iff.symm
  rw [hdomain, mgf_id_asymmetricLaplaceMeasure_eq_mul hl hr,
    mul_pos_iff_of_pos_left (exp_pos _), mul_pos_iff]
  simp only [hright, hleft, not_lt_of_ge (mgf_nonneg (X := id)), and_false, or_false]
  exact and_comm

/-- The moment-generating function of an asymmetric Laplace law on its exact domain. -/
@[simp]
theorem mgf_id_asymmetricLaplaceMeasure (hl : 0 < l) (hr : 0 < r)
    (htl : -l < t) (htr : t < r) :
    mgf id (asymmetricLaplaceMeasure m l r) t =
      exp (m * t) * r * l / ((r - t) * (l + t)) := by
  rw [mgf_id_asymmetricLaplaceMeasure_eq_mul hl hr, mgf_id_expMeasure hr htr,
    mgf_id_expMeasure hl (by linarith), sub_neg_eq_add]
  rw [mul_comm t m]
  field_simp

/-- The cumulant-generating function separates the location and the two exponential tails. -/
@[simp]
theorem cgf_id_asymmetricLaplaceMeasure (hl : 0 < l) (hr : 0 < r)
    (htl : -l < t) (htr : t < r) :
    cgf id (asymmetricLaplaceMeasure m l r) t =
      m * t - log (1 - t / r) - log (1 + t / l) := by
  have hrt : 0 < r - t := sub_pos.mpr htr
  have hlt : 0 < l + t := by linarith
  have hright : r / (r - t) = (1 - t / r)⁻¹ := by
    simp only [one_sub_div hr.ne', inv_div]
  have hleft : l / (l + t) = (1 + t / l)⁻¹ := by
    simp only [one_add_div hl.ne', inv_div]
  rw [cgf, mgf_id_asymmetricLaplaceMeasure_eq_mul hl hr,
    mgf_id_expMeasure hr htr, mgf_id_expMeasure hl (by linarith), sub_neg_eq_add,
    log_mul (exp_pos _).ne' (mul_pos (div_pos hr hrt) (div_pos hl hlt)).ne', log_exp,
    log_mul (div_pos hr hrt).ne' (div_pos hl hlt).ne']
  simp only [hright, hleft, log_inv]
  ring

end TauCeti.Probability
