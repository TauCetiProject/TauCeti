/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.ProductMeasure
public import TauCeti.InformationTheory.Hellinger.Basic
import TauCeti.InformationTheory.Hellinger.Product

/-!
# Hellinger affinity of Gaussian distributions

This file computes the Hellinger affinity between one-dimensional real Gaussian laws and between
infinite product Gaussian sequence laws differing on finitely many coordinates:

* General nonzero variances (`TauCeti.hellingerAffinity_gaussianReal`):
  $$\rho\bigl(\mathcal{N}(a, v_1), \mathcal{N}(b, v_2)\bigr) =
    \sqrt{\frac{2\sqrt{v_1 v_2}}{v_1 + v_2}}
    \exp\!\Bigl(-\frac{(a - b)^2}{4(v_1 + v_2)}\Bigr).$$
* Equal nonzero variance (`TauCeti.hellingerAffinity_gaussianReal_same_var`):
  $$\rho\bigl(\mathcal{N}(a, v), \mathcal{N}(b, v)\bigr) =
    \exp\!\Bigl(-\frac{(a - b)^2}{8v}\Bigr).$$
* Infinite product Gaussian sequence laws (`TauCeti.hellingerAffinity_infinitePi_gaussianReal`):
  when `θ` and `θ'` agree outside a finite index set `s`,
  $$\rho\Bigl(\bigotimes_i \mathcal{N}(\theta_i, v), \bigotimes_i \mathcal{N}(\theta'_i, v)\Bigr) =
    \exp\!\Bigl(-\frac{1}{8v}\sum_{i \in s} (\theta_i - \theta'_i)^2\Bigr).$$
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

namespace TauCeti

private lemma sqrt_gaussianPDFReal_mul (a b : ℝ) {v₁ v₂ : ℝ≥0}
    (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0) (x : ℝ) :
    let w : ℝ≥0 := 2 * v₁ * v₂ / (v₁ + v₂)
    let m : ℝ := ((v₂ : ℝ) * a + (v₁ : ℝ) * b) / ((v₁ : ℝ) + v₂)
    √(gaussianPDFReal a v₁ x * gaussianPDFReal b v₂ x) =
      (√(2 * √((v₁ : ℝ) * v₂) / ((v₁ : ℝ) + v₂)) *
          Real.exp (-(a - b) ^ 2 / (4 * ((v₁ : ℝ) + v₂)))) *
        gaussianPDFReal m w x := by
  intro w m
  have hw_coe : (w : ℝ) = 2 * (v₁ : ℝ) * v₂ / ((v₁ : ℝ) + v₂) := by simp [w]
  simp only [gaussianPDFReal]
  have hcoeff :
      √((√(2 * π * v₁))⁻¹ * (√(2 * π * v₂))⁻¹) =
        √(2 * √((v₁ : ℝ) * v₂) / ((v₁ : ℝ) + v₂)) * (√(2 * π * w))⁻¹ := by
    have hsq_eq :
        (√(2 * π * v₁))⁻¹ * (√(2 * π * v₂))⁻¹ =
          (2 * √((v₁ : ℝ) * v₂) / ((v₁ : ℝ) + v₂)) * (2 * π * w)⁻¹ := by
      have hprod_eq : 2 * π * v₁ * (2 * π * v₂) = (2 * π) ^ 2 * ((v₁ : ℝ) * v₂) := by ring
      rw [← mul_inv, ← Real.sqrt_mul (by positivity), hprod_eq,
        Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity), hw_coe]
      have hsq : √((v₁ : ℝ) * v₂) * √((v₁ : ℝ) * v₂) = (v₁ : ℝ) * v₂ :=
        Real.mul_self_sqrt (by positivity)
      field_simp
      nlinarith [hsq]
    rw [hsq_eq, Real.sqrt_mul (by positivity), Real.sqrt_inv]
  have hexp :
      √(Real.exp (-(x - a) ^ 2 / (2 * v₁)) * Real.exp (-(x - b) ^ 2 / (2 * v₂))) =
        Real.exp (-(a - b) ^ 2 / (4 * ((v₁ : ℝ) + v₂))) *
          Real.exp (-(x - m) ^ 2 / (2 * w)) := by
    rw [← Real.exp_add, Real.sqrt_eq_rpow, ← Real.exp_mul, ← Real.exp_add]
    congr 1
    simp only [m, hw_coe]
    field_simp
    ring
  calc
    √((√(2 * π * v₁))⁻¹ * Real.exp (-(x - a) ^ 2 / (2 * v₁)) *
          ((√(2 * π * v₂))⁻¹ * Real.exp (-(x - b) ^ 2 / (2 * v₂))))
      = √(((√(2 * π * v₁))⁻¹ * (√(2 * π * v₂))⁻¹) *
          (Real.exp (-(x - a) ^ 2 / (2 * v₁)) * Real.exp (-(x - b) ^ 2 / (2 * v₂)))) := by
        congr 1; ring
    _ = √((√(2 * π * v₁))⁻¹ * (√(2 * π * v₂))⁻¹) *
          √(Real.exp (-(x - a) ^ 2 / (2 * v₁)) * Real.exp (-(x - b) ^ 2 / (2 * v₂))) :=
        Real.sqrt_mul (by positivity) _
    _ = (√(2 * √((v₁ : ℝ) * v₂) / ((v₁ : ℝ) + v₂)) * (√(2 * π * w))⁻¹) *
          (Real.exp (-(a - b) ^ 2 / (4 * ((v₁ : ℝ) + v₂))) *
            Real.exp (-(x - m) ^ 2 / (2 * w))) := by
        rw [hcoeff, hexp]
    _ = √(2 * √((v₁ : ℝ) * v₂) / ((v₁ : ℝ) + v₂)) *
          Real.exp (-(a - b) ^ 2 / (4 * ((v₁ : ℝ) + v₂))) *
          ((√(2 * π * w))⁻¹ * Real.exp (-(x - m) ^ 2 / (2 * w))) := by
        ring

/-- **Hellinger affinity of two real Gaussian laws** with nonzero variances `v₁` and `v₂`. -/
theorem hellingerAffinity_gaussianReal (a b : ℝ) {v₁ v₂ : ℝ≥0}
    (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0) :
    hellingerAffinity (gaussianReal a v₁) (gaussianReal b v₂) =
      √(2 * √((v₁ : ℝ) * v₂) / ((v₁ : ℝ) + v₂)) *
        Real.exp (-(a - b) ^ 2 / (4 * ((v₁ : ℝ) + v₂))) := by
  let w : ℝ≥0 := 2 * v₁ * v₂ / (v₁ + v₂)
  have hw : w ≠ 0 := by
    simp only [w, ne_eq, div_eq_zero_iff, mul_eq_zero, OfNat.ofNat_ne_zero, hv₁, hv₂,
      add_eq_zero, and_self, or_self, not_false_eq_true]
  let m : ℝ := ((v₂ : ℝ) * a + (v₁ : ℝ) * b) / ((v₁ : ℝ) + v₂)
  have hfin₁ : IsFiniteMeasure (volume.withDensity (gaussianPDF a v₁)) := by
    rw [← gaussianReal_of_var_ne_zero a hv₁]; infer_instance
  have hfin₂ : IsFiniteMeasure (volume.withDensity (gaussianPDF b v₂)) := by
    rw [← gaussianReal_of_var_ne_zero b hv₂]; infer_instance
  rw [gaussianReal_of_var_ne_zero a hv₁, gaussianReal_of_var_ne_zero b hv₂,
    hellingerAffinity_eq_integral_of_withDensity (measurable_gaussianPDF a v₁).aemeasurable
      (measurable_gaussianPDF b v₂).aemeasurable]
  simp_rw [toReal_gaussianPDF, sqrt_gaussianPDFReal_mul a b hv₁ hv₂]
  rw [integral_const_mul, integral_gaussianPDFReal_eq_one m hw, mul_one]

/-- **Hellinger affinity of two real Gaussian laws** with equal nonzero variance `v`. -/
theorem hellingerAffinity_gaussianReal_same_var (a b : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    hellingerAffinity (gaussianReal a v) (gaussianReal b v) =
      Real.exp (-(a - b) ^ 2 / (8 * (v : ℝ))) := by
  have hvpos : (0 : ℝ) < v := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
  rw [hellingerAffinity_gaussianReal a b hv hv, Real.sqrt_mul_self hvpos.le]
  have hratio : 2 * (v : ℝ) / ((v : ℝ) + v) = 1 := by field_simp; ring
  have hdenom : 4 * ((v : ℝ) + v) = 8 * (v : ℝ) := by ring
  rw [hratio, Real.sqrt_one, one_mul, hdenom]

/-- **Hellinger affinity of infinite product Gaussian sequence laws** whose mean vectors agree
outside a finite index set `s`. -/
theorem hellingerAffinity_infinitePi_gaussianReal {ι : Type*} (θ θ' : ι → ℝ) {v : ℝ≥0}
    (hv : v ≠ 0) {s : Finset ι} (hθ : ∀ i, i ∉ s → θ i = θ' i) :
    hellingerAffinity (Measure.infinitePi fun i => gaussianReal (θ i) v)
        (Measure.infinitePi fun i => gaussianReal (θ' i) v) =
      Real.exp (-(∑ i ∈ s, (θ i - θ' i) ^ 2) / (8 * (v : ℝ))) := by
  rw [hellingerAffinity_infinitePi _ _ (s := s) fun i hi => by rw [hθ i hi]]
  simp_rw [hellingerAffinity_gaussianReal_same_var _ _ hv, ← Real.exp_sum]
  congr 1
  rw [← Finset.sum_div, ← Finset.sum_neg_distrib]

end TauCeti
