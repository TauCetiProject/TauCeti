/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.TorusIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Pi

/-! # Finite operations and monomials under torus integration

Torus integration commutes with finite sums of integrable functions and with multiplying
a scalar integrand by a constant vector. These operations allow polynomial expansions to
be integrated term by term. Products in separate coordinates factor into circle integrals;
the resulting monomial orthogonality formula extracts multivariate Cauchy coefficients.
-/

public section

open Complex MeasureTheory Metric Set
open scoped Real

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {n : ℕ}

/-- A finite sum of torus-integrable functions can be integrated term by term. -/
theorem torusIntegral_finsetSum {ι : Type*} (s : Finset ι)
    {f : ι → (Fin n → ℂ) → E} {c : Fin n → ℂ} {R : Fin n → ℝ}
    (hf : ∀ i ∈ s, TorusIntegrable (f i) c R) :
    (∯ z in T(c, R), ∑ i ∈ s, f i z) = ∑ i ∈ s, ∯ z in T(c, R), f i z := by
  simp only [torusIntegral, Finset.smul_sum]
  exact integral_finsetSum s fun i hi => (hf i hi).function_integrable

/-- A constant vector factors out of a scalar torus integral. -/
theorem torusIntegral_smul_const [CompleteSpace E] (f : (Fin n → ℂ) → ℂ) (v : E)
    (c : Fin n → ℂ) (R : Fin n → ℝ) :
    (∯ z in T(c, R), f z • v) = (∯ z in T(c, R), f z) • v := by
  simp only [torusIntegral, smul_smul, smul_eq_mul, integral_smul_const]

/-- A product in separate coordinates integrates as the product of the circle integrals.
No integrability hypothesis is required. -/
theorem torusIntegral_prod {n : ℕ} (f : Fin n → ℂ → ℂ)
    (c : Fin n → ℂ) (R : Fin n → ℝ) :
    (∯ z in T(c, R), ∏ i, f i (z i)) = ∏ i, ∮ z in C(c i, R i), f i z := by
  simp only [torusIntegral, smul_eq_mul, ← Finset.prod_mul_distrib, torusMap,
    volume_pi, ← Set.pi_univ_Icc, Measure.restrict_pi_pi]
  rw [integral_fintype_prod_eq_prod
    (fun i (θ : ℝ) => (R i * Complex.exp (θ * I) * I : ℂ) *
      f i (c i + R i * Complex.exp (θ * I)))]
  congr 1
  ext i
  rw [circleIntegral_def_Icc]
  simp [deriv_circleMap, circleMap, mul_comm]

/-- Orthogonality of coordinate monomials against the multivariate Cauchy kernel. -/
theorem torusIntegral_prod_pow_div_pow {n : ℕ} (a b : Fin n → ℕ)
    {R : Fin n → ℝ} (hR : ∀ i, 0 < R i) :
    (∯ z in T(0, R), ∏ i, z i ^ b i / z i ^ (a i + 1)) =
      if b = a then (2 * π * I) ^ n else 0 := by
  classical
  have hcircle {a b : ℕ} {R : ℝ} (hR : 0 < R) :
      (∮ z in C(0, R), z ^ b / z ^ (a + 1)) = if b = a then 2 * π * I else 0 := by
    have heq : (∮ z in C(0, R), z ^ b / z ^ (a + 1)) =
        ∮ z in C(0, R), (z - 0) ^ ((b : ℤ) - (a + 1)) := by
      apply circleIntegral.integral_congr hR.le
      intro z hz
      have hz0 : z ≠ 0 := ne_of_mem_sphere hz hR.ne'
      simp only [sub_zero]
      rw [show (b : ℤ) - (a + 1) = (b : ℤ) - ((a + 1 : ℕ) : ℤ) by omega,
        zpow_sub₀ hz0]
      norm_cast
    rw [heq]
    split_ifs with h
    · subst b
      simpa using circleIntegral.integral_sub_inv_of_mem_ball (mem_ball_self (x := (0 : ℂ)) hR)
    · exact circleIntegral.integral_sub_zpow_of_ne (by omega) _ _ _
  rw [torusIntegral_prod (fun i z => z ^ b i / z ^ (a i + 1))]
  simp only [Pi.zero_apply]
  simp_rw [hcircle (hR _)]
  by_cases h : b = a
  · simp [h]
  · obtain ⟨i, hi⟩ := Function.ne_iff.1 h
    simp only [h, ↓reduceIte]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

end TauCeti
