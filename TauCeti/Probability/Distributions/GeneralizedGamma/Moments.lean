/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.GeneralizedGamma.Basic

/-!
# Real-power moments of generalized gamma laws

The `q`th real-power moment exists exactly when `a + q / c > 0`, and equals
`s ^ q * Gamma (a + q / c) / Gamma a`. This criterion covers negative power parameters
as well as positive ones. Natural moments, the mean, and variance follow on their
respective exact integrability domains.

These results transfer the Gamma real-power moment criterion and formula through the
power pushforward; no new improper-integral calculation is needed.

## References

* E. W. Stacy, *A Generalization of the Gamma Distribution*, Annals of Mathematical
  Statistics 33 (1962), 1187–1192. We also allow negative power parameters.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real

namespace TauCeti.Probability

variable {a c s q : ℝ}

private theorem generalizedGamma_rpow_ae (hs : 0 < s) (q : ℝ) :
    (fun x : ℝ ↦ (s * x ^ c⁻¹) ^ q) =ᵐ[gammaMeasure a 1]
      fun x ↦ s ^ q * x ^ (q / c) := by
  filter_upwards [ae_pos_gammaMeasure a 1] with x hx
  rw [mul_rpow hs.le (rpow_nonneg hx.le _), ← rpow_mul hx.le]
  congr 2
  ring

/-- A real power is integrable exactly when its shifted Gamma shape is positive. -/
@[simp]
theorem integrable_rpow_generalizedGammaMeasure_iff
    (ha : 0 < a) (hc : c ≠ 0) (hs : 0 < s) (q : ℝ) :
    Integrable (fun x : ℝ ↦ x ^ q) (generalizedGammaMeasure a c s) ↔ 0 < a + q / c := by
  rw [generalizedGammaMeasure_of_valid ha hc hs,
    integrable_map_measure (by fun_prop) (by fun_prop)]
  simp only [Function.comp_def]
  rw [integrable_congr (generalizedGamma_rpow_ae hs q),
    integrable_const_mul_iff (isUnit_iff_ne_zero.2 (rpow_pos_of_pos hs q).ne'),
    integrable_rpow_gammaMeasure_iff ha zero_lt_one]
  constructor <;> intro h <;> linarith

/-- The real-power moment on its exact domain of integrability. -/
theorem integral_rpow_generalizedGammaMeasure
    (ha : 0 < a) (hc : c ≠ 0) (hs : 0 < s) (hq : 0 < a + q / c) :
    ∫ x, x ^ q ∂generalizedGammaMeasure a c s =
      s ^ q * Real.Gamma (a + q / c) / Real.Gamma a := by
  rw [generalizedGammaMeasure_of_valid ha hc hs,
    integral_map (by fun_prop) (by fun_prop),
    integral_congr_ae (generalizedGamma_rpow_ae hs q), integral_const_mul,
    integral_rpow_gammaMeasure ha zero_lt_one (by linarith : -a < q / c)]
  simp [mul_div_assoc]

/-- The sharp criterion for absolute integrability of a natural power, including order zero. -/
@[simp]
theorem integrable_pow_generalizedGammaMeasure_iff
    (ha : 0 < a) (hc : c ≠ 0) (hs : 0 < s) (n : ℕ) :
    Integrable (fun x : ℝ ↦ x ^ n) (generalizedGammaMeasure a c s) ↔
      0 < a + (n : ℝ) / c := by
  simpa only [rpow_natCast] using integrable_rpow_generalizedGammaMeasure_iff ha hc hs (n : ℝ)

/-- Natural moments whenever the corresponding absolute moment is finite. -/
@[simp]
theorem integral_pow_generalizedGammaMeasure
    (ha : 0 < a) (hc : c ≠ 0) (hs : 0 < s) (n : ℕ) (hn : 0 < a + (n : ℝ) / c) :
    ∫ x, x ^ n ∂generalizedGammaMeasure a c s =
      s ^ n * Real.Gamma (a + (n : ℝ) / c) / Real.Gamma a := by
  simpa only [rpow_natCast] using integral_rpow_generalizedGammaMeasure ha hc hs hn

/-- The mean exists exactly when the first shifted shape is positive. -/
@[simp]
theorem integrable_id_generalizedGammaMeasure_iff
    (ha : 0 < a) (hc : c ≠ 0) (hs : 0 < s) :
    Integrable id (generalizedGammaMeasure a c s) ↔ 0 < a + c⁻¹ := by
  simpa only [Function.id_def, pow_one, Nat.cast_one, one_div] using
    integrable_pow_generalizedGammaMeasure_iff ha hc hs 1

/-- The generalized gamma mean on its domain of integrability. -/
@[simp]
theorem integral_id_generalizedGammaMeasure
    (ha : 0 < a) (hc : c ≠ 0) (hs : 0 < s) (h : 0 < a + c⁻¹) :
    ∫ x, x ∂generalizedGammaMeasure a c s =
      s * Real.Gamma (a + c⁻¹) / Real.Gamma a := by
  simpa only [pow_one, Nat.cast_one, one_div] using
    integral_pow_generalizedGammaMeasure ha hc hs 1 (by simpa using h)

/-- The generalized gamma variance when the second moment is finite. -/
@[simp]
theorem variance_id_generalizedGammaMeasure
    (ha : 0 < a) (hc : c ≠ 0) (hs : 0 < s) (h : 0 < a + 2 / c) :
    variance id (generalizedGammaMeasure a c s) =
      s ^ 2 * (Real.Gamma (a + 2 / c) / Real.Gamma a -
        (Real.Gamma (a + c⁻¹) / Real.Gamma a) ^ 2) := by
  let _ := isProbabilityMeasure_generalizedGammaMeasure ha hc hs
  have hfirst : 0 < a + c⁻¹ := by
    have htwo : 2 / c = 2 * c⁻¹ := by ring
    linarith
  have hLp : MemLp id 2 (generalizedGammaMeasure a c s) :=
    (memLp_two_iff_integrable_sq aestronglyMeasurable_id).2
      ((integrable_pow_generalizedGammaMeasure_iff ha hc hs 2).2 (by simpa using h))
  rw [variance_eq_sub hLp]
  simp only [Pi.pow_apply, id_eq,
    integral_pow_generalizedGammaMeasure ha hc hs 2 (by simpa using h),
    Nat.cast_ofNat, integral_id_generalizedGammaMeasure ha hc hs hfirst]
  ring

end TauCeti.Probability
