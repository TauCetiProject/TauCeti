/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.InnerProductSpace.Calculus
import TauCeti.Analysis.SpecialFunctions.Exp.Deriv
import TauCeti.Analysis.SpecialFunctions.Gaussian.Basic

/-!
# Complex Gaussians as Schwartz functions

For `b : ℂ` with `0 < b.re`, the Gaussian `x ↦ exp (-b ‖x‖²)` on a real inner product space is a
Schwartz function, `SchwartzMap.gaussian`. The parameter is complex, so this covers both the real
heat-kernel Gaussians and the oscillating Gaussians `x ↦ exp (π i τ ‖x‖²)`, `0 < τ.im`, whose
lattice sums are theta series. The normalisation `-b * ‖x‖ ^ 2` is the one of Mathlib's
`fourier_gaussian_innerProductSpace`, which computes the Fourier transform of this function.
Translates of the Gaussian are Schwartz functions through Mathlib's
`SchwartzMap.compSubConstCLM`.

The decay estimate writes the Gaussian as `Complex.exp` composed with `x ↦ -b * ‖x‖ ^ 2`. Every
real iterated derivative of `Complex.exp` at `z` has norm `‖exp z‖`, and the inner function has
temperate growth (Mathlib's `Function.hasTemperateGrowth_norm_sq`), so the Faà di Bruno bound
`norm_iteratedFDeriv_comp_le` bounds the `n`-th derivative by a polynomial in `‖x‖` times
`exp (-b.re * ‖x‖ ^ 2)`. The two scalar inputs, `TauCeti.norm_iteratedFDeriv_real_cexp` and
`TauCeti.one_add_pow_mul_exp_neg_mul_sq_le`, live in `TauCeti.Analysis.SpecialFunctions.Exp.Deriv`
and `TauCeti.Analysis.SpecialFunctions.Gaussian.Basic`.

## Main declarations

* `SchwartzMap.gaussian`: the Gaussian `x ↦ exp (-b ‖x‖²)`, `0 < b.re`, as a Schwartz function.
* `SchwartzMap.gaussian_apply`: its values.
-/

public section

noncomputable section

open Complex Function
open scoped ContDiff Nat SchwartzMap

namespace SchwartzMap

open TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The Gaussian `x ↦ exp (-b ‖x‖²)` on a real inner product space, for `0 < b.re`, as a
Schwartz function. Its Fourier transform is computed by Mathlib's
`fourier_gaussian_innerProductSpace`. -/
def gaussian {b : ℂ} (hb : 0 < b.re) : 𝓢(V, ℂ) where
  toFun x := cexp (-b * ‖x‖ ^ 2)
  smooth' := by
    have h : ContDiff ℝ ∞ fun x : V ↦ ((‖x‖ ^ 2 : ℝ) : ℂ) :=
      ofRealCLM.contDiff.comp (contDiff_norm_sq ℝ)
    simp only [ofReal_pow] at h
    exact contDiff_exp.comp (contDiff_const.mul h)
  decay' k n := by
    -- The exponent `x ↦ -b * ‖x‖ ^ 2` has temperate growth.
    set f : V → ℂ := fun x ↦ -b * (‖x‖ : ℂ) ^ 2
    have hf : f.HasTemperateGrowth := by
      have : f = fun x ↦ (-b) * ((‖x‖ ^ 2 : ℝ) : ℂ) := by ext; simp [f]
      rw [this]
      exact (HasTemperateGrowth.const _).mul
        (Complex.hasTemperateGrowth_ofReal.comp (hasTemperateGrowth_norm_sq V))
    obtain ⟨k₁, C₁, hC₁, h₁⟩ := hf.norm_iteratedFDeriv_le_uniform n
    set m := k + k₁ * n
    refine ⟨n ! * (1 + C₁) ^ n * (m ! / (b.re / 2) ^ m * Real.exp b.re), fun x ↦ ?_⟩
    have hfx : ‖cexp (f x)‖ = Real.exp (-b.re * ‖x‖ ^ 2) := by
      rw [Complex.norm_exp]
      congr 1
      simp [f, ← ofReal_pow]
    -- Faà di Bruno for `Complex.exp ∘ f`, as in `Function.HasTemperateGrowth.comp'`.
    have hD : ∀ i, 1 ≤ i → i ≤ n →
        ‖iteratedFDeriv ℝ i f x‖ ≤ ((1 + C₁) * (1 + ‖x‖) ^ k₁) ^ i := by
      intro i hi hin
      calc ‖iteratedFDeriv ℝ i f x‖ ≤ C₁ * (1 + ‖x‖) ^ k₁ := h₁ i hin x
        _ ≤ (1 + C₁) * (1 + ‖x‖) ^ k₁ := by gcongr; simp
        _ ≤ _ := le_self_pow₀ (one_le_mul_of_one_le_of_one_le (by simp [hC₁])
            (one_le_pow₀ (by simp))) (by omega)
    have hcomp := norm_iteratedFDeriv_comp_le contDiff_exp hf.1 (mod_cast le_top) x
      (fun i _ ↦ (norm_iteratedFDeriv_real_cexp i (f x)).le) hD
    calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun x ↦ cexp (-b * ‖x‖ ^ 2)) x‖
        ≤ (1 + ‖x‖) ^ k *
            (n ! * Real.exp (-b.re * ‖x‖ ^ 2) * ((1 + C₁) * (1 + ‖x‖) ^ k₁) ^ n) := by
          rw [← hfx]
          gcongr
          · simp
          · exact hcomp
      _ = n ! * (1 + C₁) ^ n * ((1 + ‖x‖) ^ m * Real.exp (-b.re * ‖x‖ ^ 2)) := by
          simp only [m, mul_pow, ← pow_mul, pow_add]
          ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
          (one_add_pow_mul_exp_neg_mul_sq_le hb m (norm_nonneg x)) (by positivity)

/-- The value of the Schwartz Gaussian at `x` is `exp (-b ‖x‖²)`. -/
@[simp]
theorem gaussian_apply {b : ℂ} (hb : 0 < b.re) (x : V) :
    gaussian hb x = cexp (-b * ‖x‖ ^ 2) :=
  (rfl)

end SchwartzMap
