/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.InverseGamma.Basic
public import Mathlib.Probability.Moments.Variance

import TauCeti.Probability.Moments.IntegrableExpMul

/-!
# Moments of the inverse-gamma distribution

This file proves the natural moments, mean, variance, sharp moment thresholds, and exact
exponential-integrability domain of the inverse-gamma distribution.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal Topology

namespace TauCeti

namespace Probability

variable {a r t : ℝ}

/-! ### Moments -/

/-- A natural power is integrable under a valid inverse-gamma law exactly below the shape. -/
@[simp]
theorem integrable_pow_inverseGammaMeasure_iff (ha : 0 < a) (hr : 0 < r) (n : ℕ) :
    Integrable (fun x : ℝ ↦ x ^ n) (inverseGammaMeasure a r) ↔ (n : ℝ) < a := by
  rw [inverseGammaMeasure_of_pos ha hr,
    integrable_map_measure (by fun_prop) measurable_inv.aemeasurable]
  simpa only [Function.comp_def, inv_pow] using
    TauCeti.Probability.integrable_inv_pow_gammaMeasure_iff ha hr n

/-- **Natural moments of a valid inverse-gamma law.**  The `n`th moment exists for `n < a` and
equals `r ^ n * Gamma (a - n) / Gamma a`. -/
@[simp]
theorem integral_pow_inverseGammaMeasure (hr : 0 < r) (n : ℕ)
    (hn : (n : ℝ) < a) :
    ∫ x, x ^ n ∂inverseGammaMeasure a r =
      r ^ n * Real.Gamma (a - n) / Real.Gamma a := by
  have ha : 0 < a := lt_of_le_of_lt (Nat.cast_nonneg n) hn
  rw [inverseGammaMeasure_of_pos ha hr,
    integral_map measurable_inv.aemeasurable (by fun_prop)]
  simpa only [inv_pow] using TauCeti.Probability.integral_inv_pow_gammaMeasure hr n hn

/-- The mean of an inverse-gamma law is `r / (a - 1)` when `1 < a`. -/
@[simp]
theorem integral_id_inverseGammaMeasure (hr : 0 < r) (ha : 1 < a) :
    ∫ x, x ∂inverseGammaMeasure a r = r / (a - 1) := by
  have h := integral_pow_inverseGammaMeasure hr 1 (by simpa using ha)
  have hgamma : Real.Gamma a = (a - 1) * Real.Gamma (a - 1) := by
    simpa using Real.Gamma_add_one (by linarith : a - 1 ≠ 0)
  simp only [pow_one, Nat.cast_one] at h
  rw [h, hgamma]
  field_simp [(Real.Gamma_pos_of_pos (by linarith : 0 < a - 1)).ne']

/-- The second raw moment of an inverse-gamma law is
`r² / ((a - 1) * (a - 2))` when `2 < a`. -/
@[simp high]
theorem integral_sq_inverseGammaMeasure (hr : 0 < r) (ha : 2 < a) :
    ∫ x, x ^ 2 ∂inverseGammaMeasure a r = r ^ 2 / ((a - 1) * (a - 2)) := by
  have h := integral_pow_inverseGammaMeasure hr 2 (by simpa using ha)
  have hgamma : Real.Gamma a = (a - 1) * Real.Gamma (a - 1) := by
    simpa using Real.Gamma_add_one (by linarith : a - 1 ≠ 0)
  have hshift : a - 2 + 1 = a - 1 := by ring
  have hgamma' : Real.Gamma (a - 1) = (a - 2) * Real.Gamma (a - 2) := by
    simpa [hshift] using Real.Gamma_add_one (by linarith : a - 2 ≠ 0)
  norm_num only [Nat.cast_ofNat] at h
  rw [h, hgamma, hgamma']
  field_simp [(Real.Gamma_pos_of_pos (by linarith : 0 < a - 2)).ne']

/-- The variance of an inverse-gamma law is
`r² / ((a - 1)² * (a - 2))` when `2 < a`. -/
@[simp]
theorem variance_id_inverseGammaMeasure (hr : 0 < r) (ha : 2 < a) :
    variance id (inverseGammaMeasure a r) = r ^ 2 / ((a - 1) ^ 2 * (a - 2)) := by
  let _ := isProbabilityMeasure_inverseGammaMeasure (by linarith : 0 < a) hr
  have hint2 : Integrable (fun x : ℝ ↦ x ^ 2) (inverseGammaMeasure a r) :=
    (integrable_pow_inverseGammaMeasure_iff (by linarith : 0 < a) hr 2).2 (by
      norm_num
      exact ha)
  have hLp : MemLp id 2 (inverseGammaMeasure a r) :=
    (memLp_two_iff_integrable_sq aestronglyMeasurable_id).2
      (by simpa using hint2)
  rw [variance_eq_sub hLp]
  simp only [Pi.pow_apply, id_eq]
  rw [integral_sq_inverseGammaMeasure hr ha, integral_id_inverseGammaMeasure hr (by linarith)]
  have ha1 : a - 1 ≠ 0 := by linarith
  have ha2 : a - 2 ≠ 0 := by linarith
  field_simp [ha1, ha2]
  ring

/-- The identity is integrable under a valid inverse-gamma law exactly above shape one. -/
@[simp]
theorem integrable_id_inverseGammaMeasure_iff (ha : 0 < a) (hr : 0 < r) :
    Integrable id (inverseGammaMeasure a r) ↔ 1 < a := by
  simpa only [Function.id_def, pow_one, Nat.cast_one] using
    integrable_pow_inverseGammaMeasure_iff ha hr 1

/-- At and below shape one, the identity is not integrable under a valid inverse-gamma law. -/
theorem not_integrable_id_inverseGammaMeasure (ha : 0 < a) (hr : 0 < r) (h : a ≤ 1) :
    ¬ Integrable id (inverseGammaMeasure a r) :=
  (integrable_id_inverseGammaMeasure_iff ha hr).not.mpr (not_lt.mpr h)

/-- At and below shape two, the square is not integrable under a valid inverse-gamma law. -/
theorem not_integrable_sq_inverseGammaMeasure (ha : 0 < a) (hr : 0 < r) (h : a ≤ 2) :
    ¬ Integrable (fun x : ℝ ↦ x ^ 2) (inverseGammaMeasure a r) :=
  (integrable_pow_inverseGammaMeasure_iff ha hr 2).not.mpr (by simpa using h)

/-! ### Exponential moments -/

/-- Every nonpositive exponential moment of a valid inverse-gamma law exists. -/
theorem integrable_exp_mul_inverseGammaMeasure (ha : 0 < a) (hr : 0 < r) (ht : t ≤ 0) :
    Integrable (fun x : ℝ ↦ Real.exp (t * x)) (inverseGammaMeasure a r) := by
  let _ := isProbabilityMeasure_inverseGammaMeasure ha hr
  exact integrable_exp_mul_of_ge t 0 ht measurable_id.aemeasurable
    ((ae_pos_inverseGammaMeasure a r).mono fun _ hx ↦ hx.le)

/-- **Positive exponential moments of a valid inverse-gamma law do not exist.** -/
theorem not_integrable_exp_mul_inverseGammaMeasure (ha : 0 < a) (hr : 0 < r) (ht : 0 < t) :
    ¬ Integrable (fun x : ℝ ↦ Real.exp (t * x)) (inverseGammaMeasure a r) := by
  let _ := isProbabilityMeasure_inverseGammaMeasure ha hr
  refine not_integrable_exp_mul_of_not_integrable_pow ⌈a⌉₊ measurable_id.aemeasurable
    ((ae_pos_inverseGammaMeasure a r).mono fun _ hx ↦ hx.le) (fun hpow ↦ ?_) ht
  exact not_lt_of_ge (Nat.le_ceil a)
    ((integrable_pow_inverseGammaMeasure_iff ha hr ⌈a⌉₊).1 hpow)

/-- **The exact exponential-integrability domain of a valid inverse-gamma law** is the
nonpositive half-line. -/
@[simp]
theorem integrableExpSet_id_inverseGammaMeasure (ha : 0 < a) (hr : 0 < r) :
    integrableExpSet id (inverseGammaMeasure a r) = Iic 0 := by
  ext u
  simp only [integrableExpSet, Set.mem_ofPred_eq, id_eq, mem_Iic]
  exact ⟨fun h ↦ not_lt.mp fun hu ↦ not_integrable_exp_mul_inverseGammaMeasure ha hr hu h,
    integrable_exp_mul_inverseGammaMeasure ha hr⟩


end Probability

end TauCeti
