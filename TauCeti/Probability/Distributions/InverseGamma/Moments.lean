/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.InverseGamma.Basic
public import Mathlib.Probability.Moments.Variance

import TauCeti.Probability.HasLaw
import TauCeti.Probability.Moments.IntegrableExpMul

/-!
# Moments of the inverse-gamma distribution

This file proves the real and natural moments, mean, variance, sharp moment thresholds, and exact
exponential-integrability domain of the inverse-gamma distribution. The results in
`ProbabilityTheory.HasLaw` transfer this elementary observable theory to random variables with an
inverse-gamma law.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal Topology

namespace TauCeti

namespace Probability

variable {a r t : ℝ}

/-! ### Moments -/

/-- A real power is integrable under a valid inverse-gamma law exactly when its exponent is below
the shape parameter. -/
@[simp]
theorem integrable_rpow_inverseGammaMeasure_iff (ha : 0 < a) (hr : 0 < r) (q : ℝ) :
    Integrable (fun x : ℝ ↦ x ^ q) (inverseGammaMeasure a r) ↔ q < a := by
  rw [inverseGammaMeasure_of_pos ha hr,
    integrable_map_measure (by fun_prop) measurable_inv.aemeasurable]
  have h_inv : (fun x : ℝ ↦ x⁻¹ ^ q) =ᵐ[gammaMeasure a r] fun x ↦ x ^ (-q) :=
    .of_forall fun x ↦ (Real.rpow_neg_eq_inv_rpow x q).symm
  simp only [Function.comp_def]
  rw [integrable_congr h_inv, integrable_rpow_gammaMeasure_iff ha hr]
  constructor <;> intro h <;> linarith

/-- **Real-power moments of a valid inverse-gamma law.** The `q`th moment exists for `q < a` and
equals `r ^ q * Gamma (a - q) / Gamma a`. -/
@[simp]
theorem integral_rpow_inverseGammaMeasure (ha : 0 < a) (hr : 0 < r) (hq : q < a) :
    ∫ x, x ^ q ∂inverseGammaMeasure a r =
      r ^ q * Real.Gamma (a - q) / Real.Gamma a := by
  rw [inverseGammaMeasure_of_pos ha hr,
    integral_map measurable_inv.aemeasurable (by fun_prop)]
  have h_inv : (fun x : ℝ ↦ x⁻¹ ^ q) =ᵐ[gammaMeasure a r] fun x ↦ x ^ (-q) :=
    .of_forall fun x ↦ (Real.rpow_neg_eq_inv_rpow x q).symm
  rw [integral_congr_ae h_inv,
    integral_rpow_gammaMeasure ha hr (q := -q) (by linarith)]
  simp only [neg_neg, sub_eq_add_neg]

/-- A natural power is integrable under a valid inverse-gamma law exactly below the shape. -/
@[simp]
theorem integrable_pow_inverseGammaMeasure_iff (ha : 0 < a) (hr : 0 < r) (n : ℕ) :
    Integrable (fun x : ℝ ↦ x ^ n) (inverseGammaMeasure a r) ↔ (n : ℝ) < a := by
  simpa only [Real.rpow_natCast] using
    integrable_rpow_inverseGammaMeasure_iff ha hr (n : ℝ)

/-- **Natural moments of a valid inverse-gamma law.**  The `n`th moment exists for `n < a` and
equals `r ^ n * Gamma (a - n) / Gamma a`. -/
@[simp]
theorem integral_pow_inverseGammaMeasure (hr : 0 < r) (n : ℕ)
    (hn : (n : ℝ) < a) :
    ∫ x, x ^ n ∂inverseGammaMeasure a r =
      r ^ n * Real.Gamma (a - n) / Real.Gamma a := by
  have ha : 0 < a := lt_of_le_of_lt (Nat.cast_nonneg n) hn
  simpa only [Real.rpow_natCast] using
    integral_rpow_inverseGammaMeasure ha hr hn

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

/-- Every nonpositive exponential moment of an inverse-gamma law exists. Invalid parameters give the
zero measure. -/
theorem integrable_exp_mul_inverseGammaMeasure (ht : t ≤ 0) :
    Integrable (fun x : ℝ ↦ Real.exp (t * x)) (inverseGammaMeasure a r) := by
  by_cases hv : 0 < a ∧ 0 < r
  · let _ := isProbabilityMeasure_inverseGammaMeasure hv.1 hv.2
    exact integrable_exp_mul_of_ge t 0 ht measurable_id.aemeasurable
      ((ae_pos_inverseGammaMeasure a r).mono fun _ hx ↦ hx.le)
  · rw [inverseGammaMeasure_of_not_pos hv]
    exact integrable_zero_measure

/-- **Positive exponential moments of a valid inverse-gamma law do not exist.** -/
theorem not_integrable_exp_mul_inverseGammaMeasure (ha : 0 < a) (hr : 0 < r) (ht : 0 < t) :
    ¬ Integrable (fun x : ℝ ↦ Real.exp (t * x)) (inverseGammaMeasure a r) := by
  let _ := isProbabilityMeasure_inverseGammaMeasure ha hr
  refine not_integrable_exp_mul_of_not_integrable_pow ⌈a⌉₊
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
    integrable_exp_mul_inverseGammaMeasure⟩


end Probability

end TauCeti

namespace ProbabilityTheory.HasLaw

open MeasureTheory TauCeti.Probability

variable {a r : ℝ} {n : ℕ} {q : ℝ} {Ω : Type*} [MeasurableSpace Ω]
  {P : Measure Ω} {X : Ω → ℝ}

/-- A real power of an inverse-gamma random variable is integrable exactly when its exponent is
below the shape parameter. -/
theorem integrable_rpow_inverseGammaMeasure_iff
    (hX : HasLaw X (inverseGammaMeasure a r) P) (ha : 0 < a) (hr : 0 < r) (q : ℝ) :
    Integrable (fun ω ↦ X ω ^ q) P ↔ q < a := by
  simpa only [Function.comp_def] using
    (hX.integrable_comp_iff (f := fun x : ℝ ↦ x ^ q) (by fun_prop)).trans
      (TauCeti.Probability.integrable_rpow_inverseGammaMeasure_iff ha hr q)

/-- The real-power moment of an inverse-gamma random variable below the shape parameter. -/
theorem integral_rpow_inverseGammaMeasure
    (hX : HasLaw X (inverseGammaMeasure a r) P) (ha : 0 < a) (hr : 0 < r) (hq : q < a) :
    ∫ ω, X ω ^ q ∂P = r ^ q * Real.Gamma (a - q) / Real.Gamma a := by
  rw [← Function.comp_def (f := fun x : ℝ ↦ x ^ q), hX.integral_comp (by fun_prop),
    TauCeti.Probability.integral_rpow_inverseGammaMeasure ha hr hq]

/-- A natural power of an inverse-gamma random variable is integrable exactly when its exponent is
below the shape parameter. -/
theorem integrable_pow_inverseGammaMeasure_iff
    (hX : HasLaw X (inverseGammaMeasure a r) P) (ha : 0 < a) (hr : 0 < r) (n : ℕ) :
    Integrable (fun ω ↦ X ω ^ n) P ↔ (n : ℝ) < a := by
  simpa only [Real.rpow_natCast] using
    hX.integrable_rpow_inverseGammaMeasure_iff ha hr (n : ℝ)

/-- The natural moments of an inverse-gamma random variable below the shape parameter. -/
theorem integral_pow_inverseGammaMeasure
    (hX : HasLaw X (inverseGammaMeasure a r) P) (hr : 0 < r) (hn : (n : ℝ) < a) :
    ∫ ω, X ω ^ n ∂P = r ^ n * Real.Gamma (a - n) / Real.Gamma a := by
  rw [← Function.comp_def (f := fun x : ℝ ↦ x ^ n), hX.integral_comp (by fun_prop),
    TauCeti.Probability.integral_pow_inverseGammaMeasure hr n hn]

/-- An inverse-gamma random variable is integrable exactly when the shape exceeds one. -/
theorem integrable_inverseGammaMeasure_iff
    (hX : HasLaw X (inverseGammaMeasure a r) P) (ha : 0 < a) (hr : 0 < r) :
    Integrable X P ↔ 1 < a := by
  simpa only [pow_one, Nat.cast_one] using hX.integrable_pow_inverseGammaMeasure_iff ha hr 1

/-- The expectation of an inverse-gamma random variable above shape one. -/
theorem integral_inverseGammaMeasure
    (hX : HasLaw X (inverseGammaMeasure a r) P) (hr : 0 < r) (ha : 1 < a) :
    ∫ ω, X ω ∂P = r / (a - 1) := by
  rw [hX.integral_eq, TauCeti.Probability.integral_id_inverseGammaMeasure hr ha]

/-- The variance of an inverse-gamma random variable above shape two. -/
theorem variance_inverseGammaMeasure
    (hX : HasLaw X (inverseGammaMeasure a r) P) (hr : 0 < r) (ha : 2 < a) :
    variance X P = r ^ 2 / ((a - 1) ^ 2 * (a - 2)) := by
  rw [hX.variance_eq, TauCeti.Probability.variance_id_inverseGammaMeasure hr ha]

/-- An inverse-gamma random variable has a finite exponential moment exactly at nonpositive
rates. -/
theorem integrable_exp_mul_inverseGammaMeasure_iff
    (hX : HasLaw X (inverseGammaMeasure a r) P) (ha : 0 < a) (hr : 0 < r) (t : ℝ) :
    Integrable (fun ω ↦ Real.exp (t * X ω)) P ↔ t ≤ 0 := by
  have hmeasure :
      Integrable (fun x : ℝ ↦ Real.exp (t * x)) (inverseGammaMeasure a r) ↔ t ≤ 0 := by
    constructor
    · intro h
      exact not_lt.mp fun ht ↦
        TauCeti.Probability.not_integrable_exp_mul_inverseGammaMeasure ha hr ht h
    · exact TauCeti.Probability.integrable_exp_mul_inverseGammaMeasure
  simpa only [Function.comp_def] using
    (hX.integrable_comp_iff (f := fun x : ℝ ↦ Real.exp (t * x)) (by fun_prop)).trans hmeasure

/-- The exponential-integrability domain of an inverse-gamma random variable is the nonpositive
half-line. -/
theorem integrableExpSet_inverseGammaMeasure
    (hX : HasLaw X (inverseGammaMeasure a r) P) (ha : 0 < a) (hr : 0 < r) :
    integrableExpSet X P = Set.Iic 0 := by
  ext t
  simpa only [integrableExpSet, Set.mem_ofPred_eq, Set.mem_Iic] using
    hX.integrable_exp_mul_inverseGammaMeasure_iff ha hr t

end ProbabilityTheory.HasLaw
