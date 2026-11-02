/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.NoncentralT.Basic
public import Mathlib.Probability.Moments.Variance
import TauCeti.Probability.Distributions.Gaussian.PolynomialMemLp
import TauCeti.Probability.Distributions.NoncentralF.Moments

/-!
# Moments of noncentral t laws

The natural moment of order `n` of a noncentral t law with positive degree `ν` exists exactly
when `n < ν`, independently of its noncentrality. This file computes the mean, second raw
moment, and variance on their respective integrability domains. In particular, the second
moment differs from the variance when the noncentrality is nonzero.

The defining independent ratio separates powers into a Gaussian factor and a negative
half-power of a chi-squared variable. The Gamma moment criterion gives both finiteness and
sharp divergence. The square-law identification with noncentral F supplies the second moment.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2,
  second edition, Wiley, 1995, chapter 31.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal

namespace TauCeti.Probability

variable {ν δ : ℝ}

private theorem inv_sqrt_div_rpow_ae (hν : 0 < ν) (q : ℝ) :
    (fun x : ℝ ↦ (√(x / ν))⁻¹ ^ q) =ᵐ[chiSquaredMeasure ν]
      fun x ↦ ν ^ (q / 2) * x ^ (-q / 2) := by
  filter_upwards [ae_pos_chiSquaredMeasure hν] with x hx
  have hq : -q / 2 = -(q / 2) := by ring
  rw [inv_rpow (sqrt_nonneg _), ← rpow_div_two_eq_sqrt q (div_pos hx hν).le,
    div_rpow hx.le hν.le, inv_div,
    hq, rpow_neg hx.le]
  exact div_eq_mul_inv _ _

/-- A natural power is integrable under a noncentral t law exactly below its degrees of
freedom. Integrability includes absolute integrability and includes order zero. -/
@[simp]
theorem integrable_pow_noncentralTMeasure_iff (hν : 0 < ν) (δ : ℝ) (n : ℕ) :
    Integrable (fun x : ℝ ↦ x ^ n) (noncentralTMeasure ν δ) ↔ (n : ℝ) < ν := by
  let _ := isProbabilityMeasure_chiSquaredMeasure hν.le
  let _ := nullSingletonClass_gaussianReal (μ := δ) one_ne_zero
  have hden : Integrable (fun x : ℝ ↦ (√(x / ν))⁻¹ ^ n) (chiSquaredMeasure ν) ↔
      (n : ℝ) < ν := by
    simp_rw [← rpow_natCast]
    rw [integrable_congr (inv_sqrt_div_rpow_ae hν n),
      integrable_const_mul_iff (isUnit_iff_ne_zero.2 (rpow_pos_of_pos hν _).ne'),
      chiSquaredMeasure_eq_gammaMeasure hν,
      integrable_rpow_gammaMeasure_iff (half_pos hν) one_half_pos]
    constructor <;> intro h <;> linarith
  rw [noncentralTMeasure_eq_map_gaussianReal hν,
    integrable_map_measure (by fun_prop) (by fun_prop)]
  simp only [Function.comp_def, div_eq_mul_inv, mul_pow, inv_pow]
  constructor
  · intro h
    obtain ⟨x, hx, hx0⟩ := (h.prod_right_ae.and ((gaussianReal δ 1).ae_ne 0)).exists
    apply hden.1
    simp only [inv_pow]
    exact (integrable_const_mul_iff (isUnit_iff_ne_zero.2 (pow_ne_zero n hx0)) _).1 hx
  · intro hn
    simpa only [inv_pow, div_eq_mul_inv] using
      (integrable_pow_gaussianReal δ 1 n).mul_prod (hden.2 hn)

/-- The noncentral t mean exists exactly when the degrees of freedom exceed one. -/
@[simp]
theorem integrable_id_noncentralTMeasure_iff (hν : 0 < ν) (δ : ℝ) :
    Integrable id (noncentralTMeasure ν δ) ↔ 1 < ν := by
  simpa only [pow_one, Function.id_def, Nat.cast_one] using
    integrable_pow_noncentralTMeasure_iff hν δ 1

/-- The noncentral t second moment exists exactly when the degrees of freedom exceed two. -/
theorem integrable_sq_noncentralTMeasure_iff (hν : 0 < ν) (δ : ℝ) :
    Integrable (fun x : ℝ ↦ x ^ 2) (noncentralTMeasure ν δ) ↔ 2 < ν := by
  simpa only [Nat.cast_ofNat] using integrable_pow_noncentralTMeasure_iff hν δ 2

/-- The mean of a noncentral t law on its exact integrability domain. -/
@[simp]
theorem integral_id_noncentralTMeasure (hν : 1 < ν) (δ : ℝ) :
    ∫ x, x ∂noncentralTMeasure ν δ =
      δ * √(ν / 2) * Real.Gamma ((ν - 1) / 2) / Real.Gamma (ν / 2) := by
  have hν0 : 0 < ν := by linarith
  let _ := isProbabilityMeasure_chiSquaredMeasure hν0.le
  rw [noncentralTMeasure_eq_map_gaussianReal hν0,
    integral_map (by fun_prop) (by fun_prop)]
  have hprod := integral_prod_mul (μ := gaussianReal δ 1) (ν := chiSquaredMeasure ν)
    (fun x : ℝ ↦ x) (fun x : ℝ ↦ (√(x / ν))⁻¹)
  simp_rw [← div_eq_mul_inv] at hprod
  rw [hprod, integral_id_gaussianReal]
  have hden : (fun x : ℝ ↦ (√(x / ν))⁻¹) =ᵐ[chiSquaredMeasure ν]
      fun x ↦ ν ^ (1 / 2 : ℝ) * x ^ (-1 / 2 : ℝ) := by
    simpa only [rpow_one] using inv_sqrt_div_rpow_ae hν0 1
  rw [integral_congr_ae hden, integral_const_mul, chiSquaredMeasure_eq_gammaMeasure hν0,
    integral_rpow_gammaMeasure (half_pos hν0) one_half_pos (by linarith : -(ν / 2) < -1 / 2)]
  have hshape : ν / 2 + (-1 / 2) = (ν - 1) / 2 := by ring
  rw [hshape]
  norm_num only [neg_div, neg_neg]
  rw [← sqrt_eq_rpow, ← sqrt_eq_rpow, sqrt_div hν0.le, sqrt_div zero_le_one, sqrt_one]
  ring

/-- The second raw moment of a noncentral t law is `ν * (1 + δ ^ 2) / (ν - 2)`. -/
@[simp]
theorem integral_sq_noncentralTMeasure (hν : 2 < ν) (δ : ℝ) :
    ∫ x, x ^ 2 ∂noncentralTMeasure ν δ = ν * (1 + δ ^ 2) / (ν - 2) := by
  have h := congrArg (fun μ : Measure ℝ ↦ ∫ x, x ∂μ) (noncentralTMeasure_map_sq ν δ)
  rw [integral_map (by fun_prop) (by fun_prop),
    integral_id_noncentralFMeasure one_pos hν] at h
  simpa using h

/-- The variance of a noncentral t law is its second raw moment minus its squared mean. -/
@[simp]
theorem variance_id_noncentralTMeasure (hν : 2 < ν) (δ : ℝ) :
    variance id (noncentralTMeasure ν δ) = ν * (1 + δ ^ 2) / (ν - 2) -
      (δ * √(ν / 2) * Real.Gamma ((ν - 1) / 2) / Real.Gamma (ν / 2)) ^ 2 := by
  let _ := isProbabilityMeasure_noncentralTMeasure (by linarith : 0 < ν) δ
  have hLp : MemLp id 2 (noncentralTMeasure ν δ) :=
    (memLp_two_iff_integrable_sq aestronglyMeasurable_id).2
      ((integrable_sq_noncentralTMeasure_iff (by linarith) δ).2 hν)
  rw [variance_eq_sub hLp]
  simp only [Pi.pow_apply, id_eq, integral_sq_noncentralTMeasure hν,
    integral_id_noncentralTMeasure (by linarith : 1 < ν)]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}

/-- A random variable with noncentral t law has a finite natural moment exactly below its
degrees of freedom. -/
theorem integrable_pow_of_hasLaw_noncentralTMeasure_iff (hν : 0 < ν)
    (hX : HasLaw X (noncentralTMeasure ν δ) P) (n : ℕ) :
    Integrable (fun ω ↦ X ω ^ n) P ↔ (n : ℝ) < ν := by
  rw [← integrable_pow_noncentralTMeasure_iff hν δ n, ← hX.map_eq,
    integrable_map_measure (by fun_prop) hX.aemeasurable]
  rfl

/-- A variable with noncentral t law has the stated mean above one degree of freedom. -/
theorem integral_of_hasLaw_noncentralTMeasure (hν : 1 < ν)
    (hX : HasLaw X (noncentralTMeasure ν δ) P) :
    ∫ ω, X ω ∂P = δ * √(ν / 2) * Real.Gamma ((ν - 1) / 2) / Real.Gamma (ν / 2) := by
  rw [hX.integral_eq, integral_id_noncentralTMeasure hν]

/-- A variable with noncentral t law has the stated variance above two degrees of freedom. -/
theorem variance_of_hasLaw_noncentralTMeasure (hν : 2 < ν)
    (hX : HasLaw X (noncentralTMeasure ν δ) P) :
    variance X P = ν * (1 + δ ^ 2) / (ν - 2) -
      (δ * √(ν / 2) * Real.Gamma ((ν - 1) / 2) / Real.Gamma (ν / 2)) ^ 2 := by
  rw [hX.variance_eq, variance_id_noncentralTMeasure hν]

end TauCeti.Probability
