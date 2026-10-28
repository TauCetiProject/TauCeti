/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Distribution.TemperateGrowth
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# The complex Gaussian as a Schwartz function

On a real inner product space `E`, the Gaussian `x ↦ exp (-b ‖x‖²)` with a complex parameter `b`
of positive real part is a Schwartz function (`SchwartzMap.gaussian`). Its Fourier transform is
Mathlib's `fourier_gaussian_innerProductSpace`; packaging the Gaussian in `𝓢(E, ℂ)` is what lets
it enter statements about Schwartz functions, such as Poisson summation over a lattice. With
`b = -π i τ` for `τ` in the upper half-plane, it is the Gaussian `x ↦ exp (π i τ ‖x‖²)` whose
periodizations over a lattice are theta series.

The decay estimate is Faà di Bruno's bound `norm_iteratedFDeriv_comp_le` for `exp ∘ q` with
`q x = -b ‖x‖²`. The derivatives of `exp` at `q x` have norm `‖exp (q x)‖ = exp (-re b ‖x‖²)`, and
those of the quadratic polynomial `q` grow at most polynomially, so the `n`-th derivative of the
Gaussian is a polynomial in `‖x‖` times `exp (-re b ‖x‖²)`, which is bounded against every power
of `‖x‖`.
-/

public section

open Complex Real
open scoped Nat SchwartzMap

/-- The `n`-th real derivative of the complex exponential has the norm of the exponential. -/
theorem Complex.norm_iteratedFDeriv_real_exp (n : ℕ) (z : ℂ) :
    ‖iteratedFDeriv ℝ n cexp z‖ = ‖cexp z‖ := by
  rw [← ((Complex.contDiff_exp (𝕜 := ℂ) (n := n)).contDiffAt).restrictScalars_iteratedFDeriv
      (𝕜 := ℝ),
    Function.comp_apply, ContinuousMultilinearMap.norm_restrictScalars,
    norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate, Complex.iter_deriv_exp]

/-- A polynomial in `r ≥ 0` times the Gaussian `exp (-a r²)`, `a > 0`, is bounded:
`(1 + r)^m exp (-a r²) ≤ m! exp (1 + 1/(4a))`. -/
theorem Real.one_add_pow_mul_exp_neg_mul_sq_le {a : ℝ} (ha : 0 < a) (m : ℕ) {r : ℝ}
    (hr : 0 ≤ r) : (1 + r) ^ m * Real.exp (-a * r ^ 2) ≤ m ! * Real.exp (1 + (4 * a)⁻¹) := by
  have hpow : (1 + r) ^ m ≤ m ! * Real.exp (1 + r) := by
    have := pow_div_factorial_le_exp (1 + r) (by positivity) m
    rwa [div_le_iff₀ (by positivity), mul_comm] at this
  have hquad : 1 + r + -a * r ^ 2 ≤ 1 + (4 * a)⁻¹ := by
    have : 1 + (4 * a)⁻¹ - (1 + r + -a * r ^ 2) = a * (r - (2 * a)⁻¹) ^ 2 := by
      field_simp
      ring
    linarith [mul_nonneg ha.le (sq_nonneg (r - (2 * a)⁻¹))]
  calc (1 + r) ^ m * Real.exp (-a * r ^ 2) ≤ m ! * Real.exp (1 + r) * Real.exp (-a * r ^ 2) := by
        gcongr
    _ = m ! * Real.exp (1 + r + -a * r ^ 2) := by rw [Real.exp_add (1 + r)]; ring
    _ ≤ m ! * Real.exp (1 + (4 * a)⁻¹) := by gcongr

namespace SchwartzMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The Gaussian `x ↦ exp (-b ‖x‖²)` on a real inner product space, for `b : ℂ` with `0 < re b`,
as a Schwartz function. -/
noncomputable def gaussian (b : ℂ) (hb : 0 < b.re) : 𝓢(E, ℂ) where
  toFun x := cexp (-b * ‖x‖ ^ 2)
  smooth' := by
    have : (fun x : E ↦ cexp (-b * ‖x‖ ^ 2)) = fun x ↦ cexp (-b * ((‖x‖ ^ 2 : ℝ) : ℂ)) := by
      ext x
      push_cast
      rfl
    rw [this]
    exact Complex.contDiff_exp.comp (contDiff_const.mul (ofRealCLM.contDiff.comp
      (contDiff_norm_sq ℝ)))
  decay' k n := by
    set q : E → ℂ := fun x ↦ -b * ((‖x‖ ^ 2 : ℝ) : ℂ)
    have hfq : (fun x : E ↦ cexp (-b * ‖x‖ ^ 2)) = cexp ∘ q := by
      ext x
      simp [q]
    have hq : q.HasTemperateGrowth := by fun_prop
    obtain ⟨j, C₀, hC₀, hj⟩ := hq.norm_iteratedFDeriv_le_uniform n
    refine ⟨n ! * (1 + C₀) ^ n * ((k + j * n) ! * Real.exp (1 + (4 * b.re)⁻¹)), fun x ↦ ?_⟩
    -- Faà di Bruno: `‖D^n (exp ∘ q)(x)‖ ≤ n! ‖exp (q x)‖ D^n` with `D = (1 + C₀)(1 + ‖x‖)^j`.
    set D : ℝ := (1 + C₀) * (1 + ‖x‖) ^ j
    have hD₁ : 1 ≤ D := one_le_mul_of_one_le_of_one_le (by linarith) (one_le_pow₀ (by simp))
    have hcomp : ‖iteratedFDeriv ℝ n (cexp ∘ q) x‖ ≤ n ! * ‖cexp (q x)‖ * D ^ n := by
      refine norm_iteratedFDeriv_comp_le Complex.contDiff_exp hq.1 (by exact_mod_cast le_top) x
        (fun i _ ↦ (Complex.norm_iteratedFDeriv_real_exp i (q x)).le) (fun i hi hin ↦ ?_)
      exact (hj i hin x).trans ((mul_le_mul_of_nonneg_right (by linarith) (by positivity) :
        C₀ * (1 + ‖x‖) ^ j ≤ D).trans (le_self_pow₀ hD₁ (by omega)))
    have hexp : ‖cexp (q x)‖ = Real.exp (-b.re * ‖x‖ ^ 2) := by
      rw [Complex.norm_exp]
      congr 1
      simp only [q, Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
        Complex.ofReal_im]
      ring
    have hxk : ‖x‖ ^ k ≤ (1 + ‖x‖) ^ k := pow_le_pow_left₀ (norm_nonneg x) (by linarith) k
    rw [hfq]
    calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (cexp ∘ q) x‖
        ≤ (1 + ‖x‖) ^ k * (n ! * Real.exp (-b.re * ‖x‖ ^ 2) * D ^ n) := by
          rw [← hexp]
          gcongr
      _ = n ! * (1 + C₀) ^ n * ((1 + ‖x‖) ^ (k + j * n) * Real.exp (-b.re * ‖x‖ ^ 2)) := by
          simp only [D, mul_pow, pow_add, pow_mul]
          ring
      _ ≤ n ! * (1 + C₀) ^ n * ((k + j * n) ! * Real.exp (1 + (4 * b.re)⁻¹)) := by
          exact mul_le_mul_of_nonneg_left
            (Real.one_add_pow_mul_exp_neg_mul_sq_le hb _ (norm_nonneg x)) (by positivity)

/-- The underlying function of `SchwartzMap.gaussian b hb` is `x ↦ exp (-b ‖x‖²)`. -/
theorem coe_gaussian (b : ℂ) (hb : 0 < b.re) :
    ⇑(gaussian b hb : 𝓢(E, ℂ)) = fun x ↦ cexp (-b * ‖x‖ ^ 2) :=
  (rfl)

@[simp]
theorem gaussian_apply (b : ℂ) (hb : 0 < b.re) (x : E) :
    gaussian b hb x = cexp (-b * ‖x‖ ^ 2) :=
  (rfl)

end SchwartzMap
