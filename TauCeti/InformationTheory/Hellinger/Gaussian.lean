/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import TauCeti.InformationTheory.Hellinger.Basic

/-!
# Hellinger affinity of Gaussian distributions and Gaussian sequence laws

This file evaluates the Hellinger affinity (`TauCeti.hellingerAffinity`) for one-dimensional
Gaussian distributions `ProbabilityTheory.gaussianReal` and for infinite product Gaussian sequence
laws `Measure.infinitePi (fun j => gaussianReal (θ j) v)` whose means differ in finitely many
coordinates.

## Main statements

* `TauCeti.hellingerAffinity_gaussianReal`: closed-form Hellinger affinity of `N(a, v₁)` and
  `N(b, v₂)` whenever at least one variance is nonzero:
  `√(2 * √(v₁ * v₂) / (v₁ + v₂)) * exp (-(a - b)² / (4 * (v₁ + v₂)))`.
* `TauCeti.hellingerAffinity_gaussianReal_same_var`: the common-variance specialization
  `exp (-(a - b)² / (8 * v))` for `v ≠ 0`.
* `TauCeti.hellingerAffinity_infinitePi_gaussianReal`: the Hellinger affinity of two infinite
  product Gaussian sequence laws with common nonzero variance `v` whose means differ on a finite
  set `s = hθ.toFinset` is `exp (-(∑ j ∈ s, (θ j - θ' j)²) / (8 * v))`.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal

namespace TauCeti

private theorem sqrt_mul_gaussianPDFReal (a b : ℝ) {v₁ v₂ : ℝ≥0} (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0)
    (x : ℝ) :
    let m : ℝ := ((v₂ : ℝ) * a + (v₁ : ℝ) * b) / ((v₁ : ℝ) + v₂)
    let w : ℝ≥0 := ⟨2 * (v₁ : ℝ) * v₂ / ((v₁ : ℝ) + v₂), by positivity⟩
    √(gaussianPDFReal a v₁ x * gaussianPDFReal b v₂ x) =
      √(2 * √((v₁ : ℝ) * v₂) / ((v₁ : ℝ) + v₂)) *
        Real.exp (-(a - b) ^ 2 / (4 * ((v₁ : ℝ) + v₂))) *
        gaussianPDFReal m w x := by
  intro m w
  have hv₁' : (0 : ℝ) < v₁ := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hv₁)
  have hv₂' : (0 : ℝ) < v₂ := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hv₂)
  have hsum : (0 : ℝ) < (v₁ : ℝ) + v₂ := add_pos hv₁' hv₂'
  have hw_val : (w : ℝ) = 2 * (v₁ : ℝ) * v₂ / ((v₁ : ℝ) + v₂) := NNReal.coe_mk _ _
  have hw : (0 : ℝ) < w := by rw [hw_val]; positivity
  have hpref : √((√(2 * π * v₁))⁻¹ * (√(2 * π * v₂))⁻¹) =
      √(2 * √((v₁ : ℝ) * v₂) / ((v₁ : ℝ) + v₂)) * (√(2 * π * w))⁻¹ := by
    rw [← sq_eq_sq₀ (by positivity) (by positivity), Real.sq_sqrt (by positivity), mul_pow,
      Real.sq_sqrt (by positivity), inv_pow, Real.sq_sqrt (by positivity), ← mul_inv,
      ← Real.sqrt_mul (by positivity)]
    have hprod : 2 * π * v₁ * (2 * π * v₂) = (2 * π) ^ 2 * ((v₁ : ℝ) * v₂) := by ring
    rw [hprod, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity), hw_val]
    have hsqrt_ne : √((v₁ : ℝ) * v₂) ≠ 0 := (Real.sqrt_pos.2 (mul_pos hv₁' hv₂')).ne'
    field_simp [hsum.ne', hv₁'.ne', hv₂'.ne', hsqrt_ne, pi_ne_zero]
    linarith [Real.sq_sqrt (mul_nonneg hv₁'.le hv₂'.le)]
  have hexp : √(Real.exp (-(x - a) ^ 2 / (2 * v₁)) * Real.exp (-(x - b) ^ 2 / (2 * v₂))) =
      Real.exp (-(a - b) ^ 2 / (4 * ((v₁ : ℝ) + v₂))) * Real.exp (-(x - m) ^ 2 / (2 * w)) := by
    rw [← Real.exp_add, ← Real.exp_add, Real.sqrt_eq_iff_eq_sq (Real.exp_nonneg _)
      (Real.exp_nonneg _), ← Real.exp_nat_mul]
    congr 1
    rw [hw_val]
    dsimp only [m]
    field_simp [hv₁'.ne', hv₂'.ne', hsum.ne']
    ring
  rw [gaussianPDFReal, gaussianPDFReal, gaussianPDFReal]
  have hrearr : ((√(2 * π * v₁))⁻¹ * Real.exp (-(x - a) ^ 2 / (2 * v₁))) *
      ((√(2 * π * v₂))⁻¹ * Real.exp (-(x - b) ^ 2 / (2 * v₂))) =
      ((√(2 * π * v₁))⁻¹ * (√(2 * π * v₂))⁻¹) *
      (Real.exp (-(x - a) ^ 2 / (2 * v₁)) * Real.exp (-(x - b) ^ 2 / (2 * v₂))) := by ring
  rw [hrearr, Real.sqrt_mul (by positivity), hpref, hexp]
  ring

/-- **Hellinger affinity of two real Gaussian laws.** For arbitrary real means `a`, `b` and
variances `v₁`, `v₂` not both zero, `hellingerAffinity (gaussianReal a v₁) (gaussianReal b v₂)`
equals `√(2 * √(v₁ * v₂) / (v₁ + v₂)) * exp (-(a - b)² / (4 * (v₁ + v₂)))`. -/
theorem hellingerAffinity_gaussianReal (a b : ℝ) {v₁ v₂ : ℝ≥0} (hv : v₁ ≠ 0 ∨ v₂ ≠ 0) :
    hellingerAffinity (gaussianReal a v₁) (gaussianReal b v₂) =
      √(2 * √((v₁ : ℝ) * v₂) / ((v₁ : ℝ) + v₂)) *
        Real.exp (-(a - b) ^ 2 / (4 * ((v₁ : ℝ) + v₂))) := by
  rw [hellingerAffinity_eq_integral _ _ volume
    (hv.imp (gaussianReal_absolutelyContinuous a) (gaussianReal_absolutelyContinuous b))]
  have hcongr : (fun x => √(((gaussianReal a v₁).rnDeriv volume x).toReal *
      ((gaussianReal b v₂).rnDeriv volume x).toReal)) =ᵐ[volume]
      fun x => √(gaussianPDFReal a v₁ x * gaussianPDFReal b v₂ x) := by
    filter_upwards [rnDeriv_gaussianReal a v₁, rnDeriv_gaussianReal b v₂] with x hx₁ hx₂
    rw [hx₁, hx₂, toReal_gaussianPDF, toReal_gaussianPDF]
  rw [integral_congr_ae hcongr]
  by_cases hv₁ : v₁ = 0
  · subst hv₁; simp
  by_cases hv₂ : v₂ = 0
  · subst hv₂; simp
  let m : ℝ := ((v₂ : ℝ) * a + (v₁ : ℝ) * b) / ((v₁ : ℝ) + v₂)
  let w : ℝ≥0 := ⟨2 * (v₁ : ℝ) * v₂ / ((v₁ : ℝ) + v₂), by positivity⟩
  have hw : w ≠ 0 := by
    have : (0 : ℝ) < v₁ := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hv₁)
    have : (0 : ℝ) < v₂ := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hv₂)
    have hw_val : (w : ℝ) = 2 * (v₁ : ℝ) * v₂ / ((v₁ : ℝ) + v₂) := NNReal.coe_mk _ _
    have hpos : (0 : ℝ) < (w : ℝ) := by rw [hw_val]; positivity
    exact NNReal.coe_ne_zero.1 hpos.ne'
  simp_rw [sqrt_mul_gaussianPDFReal a b hv₁ hv₂]
  rw [integral_const_mul, integral_gaussianPDFReal_eq_one m hw, mul_one]

/-- **Hellinger affinity of two real Gaussian laws with common nonzero variance.**
`hellingerAffinity (gaussianReal a v) (gaussianReal b v) = exp (-(a - b)² / (8 * v))`. -/
theorem hellingerAffinity_gaussianReal_same_var (a b : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    hellingerAffinity (gaussianReal a v) (gaussianReal b v) =
      Real.exp (-(a - b) ^ 2 / (8 * v)) := by
  have hv' : (0 : ℝ) < v := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hv)
  have hadd : (v : ℝ) + v = 2 * v := by ring
  have hmul : 4 * (2 * (v : ℝ)) = 8 * v := by ring
  rw [hellingerAffinity_gaussianReal a b (Or.inl hv), Real.sqrt_mul_self hv'.le, hadd,
    div_self (by positivity), Real.sqrt_one, one_mul, hmul]

/-- **Hellinger affinity of Gaussian sequence laws.** For any index type `ι`, common nonzero
variance `v`, and mean vectors `θ`, `θ' : ι → ℝ` differing on a finite set `hθ.toFinset`, the
Hellinger affinity of `Measure.infinitePi fun j => gaussianReal (θ j) v` and
`Measure.infinitePi fun j => gaussianReal (θ' j) v` equals
`exp (-(∑ j ∈ hθ.toFinset, (θ j - θ' j)²) / (8 * v))`. -/
theorem hellingerAffinity_infinitePi_gaussianReal {ι : Type*} (θ θ' : ι → ℝ) {v : ℝ≥0}
    (hv : v ≠ 0) (hθ : (Function.support (θ - θ')).Finite) :
    hellingerAffinity (Measure.infinitePi fun j => gaussianReal (θ j) v)
        (Measure.infinitePi fun j => gaussianReal (θ' j) v) =
      Real.exp (-(∑ j ∈ hθ.toFinset, (θ j - θ' j) ^ 2) / (8 * v)) := by
  have hagree : ∀ j ∉ hθ.toFinset, gaussianReal (θ j) v = gaussianReal (θ' j) v := by
    intro j hj
    have hsub : θ j - θ' j = 0 := by
      by_contra hne
      exact hj (hθ.mem_toFinset.2 hne)
    rw [sub_eq_zero.1 hsub]
  rw [hellingerAffinity_infinitePi _ _ hagree]
  simp_rw [hellingerAffinity_gaussianReal_same_var _ _ hv, ← Real.exp_sum, ← Finset.sum_div,
    ← Finset.sum_neg_distrib]

end TauCeti
