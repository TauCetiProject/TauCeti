/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars

/-!
# Complex Gaussians as Schwartz functions

On a real inner product space `E`, the complex Gaussian `x ↦ exp (-b ‖x‖²)` with `0 < re b` is a
Schwartz function. This file packages it as `TauCeti.gaussianSchwartzMap`, so that results about
Schwartz functions, such as Poisson summation over a lattice, apply to it; its translates are then
Schwartz by `SchwartzMap.compSubConstCLM`.

The Gaussians `x ↦ exp (π i τ ‖x‖²)` with `0 < im τ` are the case `b = -π i τ`; summed over a
lattice they give its theta series. Mathlib's `fourier_gaussian_innerProductSpace` computes their
Fourier transform. In the shape used for the inversion law of theta series, for
`n = finrank ℝ E`,

`𝓕 (x ↦ exp (π i τ ‖x‖²)) y = (τ / i) ^ (-n / 2) * exp (π i (-1 / τ) ‖y‖²)`,

with the complex power `cpow`, and for even `n = 2k` the factor is the integer power
`((-i) ^ k * τ ^ k)⁻¹`.

## Main declarations

* `TauCeti.gaussianSchwartzMap`: the Gaussian `x ↦ exp (-b ‖x‖²)` as a Schwartz function, for
  `0 < re b`.
* `TauCeti.fourier_cexp_pi_mul_I_mul_norm_sq_mul`: the Fourier transform of
  `x ↦ exp (π i τ ‖x‖²)`, with the factor `(τ / i) ^ (-n / 2)`.
* `TauCeti.fourier_cexp_pi_mul_I_mul_norm_sq_mul_of_finrank_eq`: the same in even rank `2k`, with
  the factor `((-i) ^ k * τ ^ k)⁻¹`.

## Implementation notes

The Schwartz decay estimate is adapted from the Faà di Bruno argument of
`TauCeti.exists_one_add_norm_pow_mul_norm_iteratedFDeriv_heatKernel_le` in
`TauCeti/Analysis/PDE/HeatKernel/Bounds.lean`: write the Gaussian as `exp ∘ q` with an exponent
`q` of temperate growth, and bound its iterated derivatives with `norm_iteratedFDeriv_comp_le`.

## References

* J.-P. Serre, *A Course in Arithmetic*, Ch. VII §6.
-/

public section

open Complex Module
open scoped Real Nat SchwartzMap FourierTransform ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace TauCeti

/-- The complex Gaussian `x ↦ exp (-b ‖x‖²)` on a real inner product space, as a Schwartz
function, for `0 < re b`. -/
noncomputable def gaussianSchwartzMap {b : ℂ} (hb : 0 < b.re) : 𝓢(E, ℂ) where
  toFun x := cexp (-b * ‖x‖ ^ 2)
  smooth' := by
    simpa using (contDiff_const (c := -b)).mul
      (Complex.ofRealCLM.contDiff.comp (Function.hasTemperateGrowth_norm_sq E).1) |>.cexp
  decay' k n := by
    -- Write the Gaussian as `exp ∘ q`, with an exponent `q` of temperate growth.
    set q : E → ℂ := fun x ↦ -b * ((‖x‖ ^ 2 : ℝ) : ℂ)
    have hq : q.HasTemperateGrowth := (Function.HasTemperateGrowth.const (-b)).mul
      (Complex.hasTemperateGrowth_ofReal.comp (Function.hasTemperateGrowth_norm_sq E))
    have hfun : (fun x : E ↦ cexp (-b * ‖x‖ ^ 2)) = cexp ∘ q := by
      ext x
      simp [q]
    -- The real iterated derivatives of `exp` have the norm of `exp`.
    have hexp (i : ℕ) (z : ℂ) : ‖iteratedFDeriv ℝ i cexp z‖ = ‖cexp z‖ := by
      rw [← (Complex.contDiff_exp (𝕜 := ℂ) (n := i)).contDiffAt.restrictScalars_iteratedFDeriv
        (𝕜 := ℝ), Function.comp_apply, ContinuousMultilinearMap.norm_restrictScalars,
        norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate, iter_deriv_exp]
    obtain ⟨j, C₀, hC₀, hj⟩ := hq.norm_iteratedFDeriv_le_uniform n
    set m := j * n + k
    set c := b.re
    refine ⟨n ! * (1 + C₀) ^ n * (m ! * Real.exp (1 + (4 * c)⁻¹)), fun x ↦ ?_⟩
    rw [hfun]
    -- Faà di Bruno: `‖D^n (exp ∘ q) x‖ ≤ n! ‖exp (q x)‖ D^n` with `D = (1 + C₀) (1 + ‖x‖) ^ j`.
    set D : ℝ := (1 + C₀) * (1 + ‖x‖) ^ j
    have hD₁ : 1 ≤ D := one_le_mul_of_one_le_of_one_le (by linarith) (one_le_pow₀ (by simp))
    have hcomp : ‖iteratedFDeriv ℝ n (cexp ∘ q) x‖ ≤ n ! * ‖cexp (q x)‖ * D ^ n := by
      refine norm_iteratedFDeriv_comp_le Complex.contDiff_exp hq.1 (by exact_mod_cast le_top) x
        (fun i _ ↦ (hexp i (q x)).le) (fun i hi hin ↦ ?_)
      exact (hj i hin x).trans ((mul_le_mul_of_nonneg_right (by linarith) (by positivity) :
        C₀ * (1 + ‖x‖) ^ j ≤ D).trans (le_self_pow₀ hD₁ (by omega)))
    have hnorm : ‖cexp (q x)‖ = Real.exp (-c * ‖x‖ ^ 2) := by
      rw [Complex.norm_exp]
      simp only [q, c, neg_mul, neg_re, Complex.re_mul_ofReal]
    -- The weight `(1 + r) ^ m` is at most `m! exp (1 + r)`, and `1 + r - c r² ≤ 1 + 1 / (4c)`.
    set r := ‖x‖
    have hpow : (1 + r) ^ m ≤ m ! * Real.exp (1 + r) := by
      have := Real.pow_div_factorial_le_exp (1 + r) (by positivity) m
      rwa [div_le_iff₀ (by positivity), mul_comm] at this
    have hquad : 1 + r + -c * r ^ 2 ≤ 1 + (4 * c)⁻¹ := by
      have h : 1 + (4 * c)⁻¹ - (1 + r + -c * r ^ 2) = c * (r - (2 * c)⁻¹) ^ 2 := by
        field_simp
        ring
      nlinarith [mul_nonneg hb.le (sq_nonneg (r - (2 * c)⁻¹))]
    have hx : r ^ k ≤ (1 + r) ^ k := pow_le_pow_left₀ (norm_nonneg x) (by linarith) k
    calc r ^ k * ‖iteratedFDeriv ℝ n (cexp ∘ q) x‖
        ≤ (1 + r) ^ k * (n ! * ‖cexp (q x)‖ * D ^ n) := by gcongr
      _ = n ! * (1 + C₀) ^ n * ((1 + r) ^ m * Real.exp (-c * r ^ 2)) := by
          rw [hnorm, pow_add, pow_mul]
          simp only [D, mul_pow]
          ring
      _ ≤ n ! * (1 + C₀) ^ n * (m ! * Real.exp (1 + r) * Real.exp (-c * r ^ 2)) := by gcongr
      _ = n ! * (1 + C₀) ^ n * (m ! * Real.exp (1 + r + -c * r ^ 2)) := by
          rw [Real.exp_add (1 + r)]
          ring
      _ ≤ n ! * (1 + C₀) ^ n * (m ! * Real.exp (1 + (4 * c)⁻¹)) := by gcongr

/-- The value of the Schwartz Gaussian: `gaussianSchwartzMap hb x = exp (-b ‖x‖²)`. -/
@[simp]
theorem gaussianSchwartzMap_apply {b : ℂ} (hb : 0 < b.re) (x : E) :
    gaussianSchwartzMap hb x = cexp (-b * ‖x‖ ^ 2) :=
  (rfl)

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- **The Fourier transform of the Gaussian `x ↦ exp (π i τ ‖x‖²)`**: for `0 < im τ` and
`n = finrank ℝ E`,
`𝓕 (x ↦ exp (π i τ ‖x‖²)) y = (τ / i) ^ (-n / 2) * exp (π i (-1 / τ) ‖y‖²)`,
with the principal branch of the complex power; `τ / i` lies in the right half-plane. -/
theorem fourier_cexp_pi_mul_I_mul_norm_sq_mul {τ : ℂ} (hτ : 0 < τ.im) (y : E) :
    𝓕 (fun x : E ↦ cexp (π * I * (‖x‖ ^ 2 : ℝ) * τ)) y =
      (τ / I) ^ (-(finrank ℝ E : ℂ) / 2) * cexp (π * I * (‖y‖ ^ 2 : ℝ) * (-1 / τ)) := by
  have hb : 0 < (-(π * I * τ)).re := by simpa using mul_pos Real.pi_pos hτ
  have hτ₀ : τ ≠ 0 := by rintro rfl; simp at hτ
  have hfun : (fun x : E ↦ cexp (π * I * (‖x‖ ^ 2 : ℝ) * τ)) =
      fun x : E ↦ cexp (-(-(π * I * τ)) * ‖x‖ ^ 2) := by
    ext x
    push_cast
    ring_nf
  -- `τ / i` has positive real part, so it is off the branch cut of `cpow`.
  have harg : (τ / I).arg ≠ π := by
    rw [Ne, arg_eq_pi_iff, not_and_or, not_lt]
    left
    simpa [div_I] using hτ.le
  have hpow : π / -(π * I * τ) = (τ / I)⁻¹ := by
    field_simp
    ring_nf
    simp [I_sq]
  rw [hfun, fourier_gaussian_innerProductSpace hb, hpow, inv_cpow _ _ harg, neg_div, cpow_neg]
  congr 2
  field_simp
  ring_nf
  simp [I_sq]

/-- **The Fourier transform of the Gaussian `x ↦ exp (π i τ ‖x‖²)` in even rank**: if
`finrank ℝ E = 2 * k` and `0 < im τ`, then
`𝓕 (x ↦ exp (π i τ ‖x‖²)) y = ((-i) ^ k * τ ^ k)⁻¹ * exp (π i (-1 / τ) ‖y‖²)`. -/
theorem fourier_cexp_pi_mul_I_mul_norm_sq_mul_of_finrank_eq {k : ℕ}
    (hk : finrank ℝ E = 2 * k) {τ : ℂ} (hτ : 0 < τ.im) (y : E) :
    𝓕 (fun x : E ↦ cexp (π * I * (‖x‖ ^ 2 : ℝ) * τ)) y =
      ((-I) ^ k * τ ^ k)⁻¹ * cexp (π * I * (‖y‖ ^ 2 : ℝ) * (-1 / τ)) := by
  have hexp : -(finrank ℝ E : ℂ) / 2 = -(k : ℂ) := by
    rw [hk]
    push_cast
    ring
  rw [fourier_cexp_pi_mul_I_mul_norm_sq_mul hτ, hexp, cpow_neg, cpow_natCast, ← mul_pow, div_I]
  congr 2
  ring

end TauCeti
