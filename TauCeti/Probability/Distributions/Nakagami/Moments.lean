/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Nakagami.Basic
public import TauCeti.Probability.Distributions.Chi.Moments

/-!
# Nakagami moments

The real-power moment of a Nakagami law is finite exactly when the exponent exceeds minus
twice its shape. This gives all natural moments, the mean and variance, and identifies the
spread parameter with the second moment. Every exponential moment is finite, inherited
from the chi law.

## References

* M. Nakagami, *The m-distribution — A general formula of intensity distribution of
  rapid fading*, Statistical Methods in Radio Wave Propagation, Pergamon, 1960, pp. 3–36.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set

namespace TauCeti.Probability

variable {m Ω q : ℝ}

/-- A Nakagami real-power moment is finite exactly above minus twice the shape. -/
@[simp]
theorem integrable_rpow_nakagamiMeasure_iff (hm : 0 < m) (hΩ : 0 < Ω) (q : ℝ) :
    Integrable (fun x : ℝ ↦ x ^ q) (nakagamiMeasure m Ω) ↔ -2 * m < q := by
  rw [nakagamiMeasure_eq_chiMeasure hm hΩ]
  simpa only [neg_mul] using
    integrable_rpow_chiMeasure_iff (by positivity : 0 < 2 * m) (by positivity) q

/-- Real-power moments on the exact domain of integrability. -/
theorem integral_rpow_nakagamiMeasure (hm : 0 < m) (hΩ : 0 < Ω) (hq : -2 * m < q) :
    ∫ x, x ^ q ∂nakagamiMeasure m Ω =
      (Ω / m) ^ (q / 2) * Real.Gamma (m + q / 2) / Real.Gamma m := by
  rw [nakagamiMeasure_of_pos hm hΩ, integral_map (by fun_prop) (by fun_prop)]
  have heq : (fun x : ℝ ↦ √x ^ q) =ᵐ[gammaMeasure m (m / Ω)] fun x ↦ x ^ (q / 2) := by
    filter_upwards [ae_pos_gammaMeasure m (m / Ω)] with x hx
    exact (rpow_div_two_eq_sqrt q hx.le).symm
  rw [integral_congr_ae heq,
    integral_rpow_gammaMeasure hm (div_pos hm hΩ) (by linarith : -m < q / 2),
    rpow_neg_eq_inv_rpow, inv_div]

/-- Every natural power is integrable, including at invalid parameters where the law is zero. -/
theorem integrable_pow_nakagamiMeasure (m Ω : ℝ) (n : ℕ) :
    Integrable (fun x : ℝ ↦ x ^ n) (nakagamiMeasure m Ω) := by
  by_cases h : 0 < m ∧ 0 < Ω
  · rw [nakagamiMeasure_eq_chiMeasure h.1 h.2]
    exact integrable_pow_chiMeasure _ _ n
  · simp [nakagamiMeasure_of_not_pos h]

/-- Natural moments of a Nakagami law, including order zero. -/
@[simp]
theorem integral_pow_nakagamiMeasure (hm : 0 < m) (hΩ : 0 < Ω) (n : ℕ) :
    ∫ x, x ^ n ∂nakagamiMeasure m Ω =
      (Ω / m) ^ ((n : ℝ) / 2) * Real.Gamma (m + (n : ℝ) / 2) / Real.Gamma m := by
  simpa only [rpow_natCast] using
    integral_rpow_nakagamiMeasure hm hΩ (q := (n : ℝ)) (by
      linarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n])

/-- The Nakagami mean. -/
@[simp]
theorem integral_id_nakagamiMeasure (hm : 0 < m) (hΩ : 0 < Ω) :
    ∫ x, x ∂nakagamiMeasure m Ω =
      √(Ω / m) * Real.Gamma (m + 1 / 2) / Real.Gamma m := by
  simpa only [pow_one, Nat.cast_one, ← sqrt_eq_rpow] using
    integral_pow_nakagamiMeasure hm hΩ 1

/-- The spread parameter is the second moment. -/
@[simp high]
theorem integral_sq_nakagamiMeasure (hm : 0 < m) (hΩ : 0 < Ω) :
    ∫ x, x ^ 2 ∂nakagamiMeasure m Ω = Ω := by
  rw [nakagamiMeasure_eq_chiMeasure hm hΩ, integral_sq_chiMeasure (by positivity) (by positivity),
    sq_sqrt (by positivity)]
  field_simp

/-- The Nakagami variance. -/
@[simp]
theorem variance_id_nakagamiMeasure (hm : 0 < m) (hΩ : 0 < Ω) :
    variance id (nakagamiMeasure m Ω) =
      Ω * (1 - (Real.Gamma (m + 1 / 2) / Real.Gamma m) ^ 2 / m) := by
  let _ := isProbabilityMeasure_nakagamiMeasure hm hΩ
  have hLp : MemLp id 2 (nakagamiMeasure m Ω) :=
    (memLp_two_iff_integrable_sq aestronglyMeasurable_id).2
      (integrable_pow_nakagamiMeasure m Ω 2)
  rw [variance_eq_sub hLp]
  simp only [Pi.pow_apply, id_eq, integral_sq_nakagamiMeasure hm hΩ,
    integral_id_nakagamiMeasure hm hΩ]
  rw [div_pow, mul_pow, sq_sqrt (by positivity)]
  ring

/-- Every exponential moment of a Nakagami law is finite, in all parameter regimes. -/
theorem integrable_exp_mul_id_nakagamiMeasure (m Ω t : ℝ) :
    Integrable (fun x : ℝ ↦ exp (t * x)) (nakagamiMeasure m Ω) := by
  by_cases h : 0 < m ∧ 0 < Ω
  · rw [nakagamiMeasure_eq_chiMeasure h.1 h.2]
    exact integrable_exp_mul_id_chiMeasure _ _ t
  · simp [nakagamiMeasure_of_not_pos h]

/-- The exact exponential-integrability domain is the entire real line. -/
@[simp]
theorem integrableExpSet_id_nakagamiMeasure (m Ω : ℝ) :
    integrableExpSet id (nakagamiMeasure m Ω) = univ := by
  ext t
  simp only [integrableExpSet, id_eq, mem_ofPred_eq, mem_univ, iff_true]
  exact integrable_exp_mul_id_nakagamiMeasure m Ω t

end TauCeti.Probability
