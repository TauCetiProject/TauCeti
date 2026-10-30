/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import TauCeti.Analysis.Distribution.TemperateGrowth
import TauCeti.Analysis.SpecialFunctions.Gaussian.Bounds

/-!
# The complex Gaussian as a Schwartz function

On a real inner product space `E`, the Gaussian `x ↦ exp (-b ‖x‖²)` with a complex parameter `b`
of positive real part is a Schwartz function (`SchwartzMap.gaussian`). Its Fourier transform is
Mathlib's `fourier_gaussian_innerProductSpace`; packaging the Gaussian in `𝓢(E, ℂ)` is what lets
it enter statements about Schwartz functions, such as Poisson summation over a lattice. With
`b = -π i τ` for `τ` in the upper half-plane, it is the Gaussian `x ↦ exp (π i τ ‖x‖²)` whose
periodizations over a lattice are theta series. For this Gaussian the Fourier transform reads

`𝓕 (x ↦ exp (π i τ ‖x‖²)) y = (τ / i) ^ (-n/2) * exp (π i (-1/τ) ‖y‖²)`

in dimension `n`, with the principal branch of the complex power, and in even dimension `n = 2k`
the power is the integer power `((-i)^k τ^k)⁻¹`.

The decay estimate is Faà di Bruno's bound
`Function.HasTemperateGrowth.exists_norm_iteratedFDeriv_comp_le` for `exp ∘ q` with
`q x = -b ‖x‖²`. The derivatives of `exp` at `q x` have norm `‖exp (q x)‖ = exp (-re b ‖x‖²)`, and
those of the quadratic polynomial `q` grow at most polynomially, so the `n`-th derivative of the
Gaussian is a polynomial in `‖x‖` times `exp (-re b ‖x‖²)`, which is bounded against every power
of `‖x‖`.

## Main statements

* `SchwartzMap.gaussian`: the Gaussian `x ↦ exp (-b ‖x‖²)` as a Schwartz function.
* `SchwartzMap.coe_gaussian_neg_pi_mul_I_mul`: at `b = -π i τ` it is `x ↦ exp (π i τ ‖x‖²)`.
* `UpperHalfPlane.fourier_gaussian`: the Fourier transform of `x ↦ exp (π i τ ‖x‖²)`.
* `UpperHalfPlane.fourier_gaussian_of_finrank_eq_two_mul`: the same in even dimension, with an
  integer power.
-/

public section

open Complex Module Real
open scoped Nat FourierTransform SchwartzMap UpperHalfPlane

/-- The `n`-th real derivative of the complex exponential has the norm of the exponential. -/
theorem Complex.norm_iteratedFDeriv_real_exp (n : ℕ) (z : ℂ) :
    ‖iteratedFDeriv ℝ n cexp z‖ = ‖cexp z‖ := by
  rw [← ((Complex.contDiff_exp (𝕜 := ℂ) (n := n)).contDiffAt).restrictScalars_iteratedFDeriv
      (𝕜 := ℝ),
    Function.comp_apply, ContinuousMultilinearMap.norm_restrictScalars,
    norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate, Complex.iter_deriv_exp]

/-- For `τ` in the upper half-plane, the Gaussian `x ↦ exp (π i τ ‖x‖²)` is `x ↦ exp (-b ‖x‖²)` for
`b = -π i τ`, whose real part `π im τ` is positive. -/
theorem UpperHalfPlane.re_neg_pi_mul_I_mul_pos (τ : ℍ) : 0 < (-(π * Complex.I * (τ : ℂ))).re := by
  simpa using mul_pos Real.pi_pos τ.im_pos

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
    obtain ⟨j, C, hC, hcomp⟩ := hq.exists_norm_iteratedFDeriv_comp_le Complex.contDiff_exp n
    refine ⟨n ! * C ^ n * ((k + j * n) ! * Real.exp (1 + (4 * b.re)⁻¹)), fun x ↦ ?_⟩
    have hexp : ‖cexp (q x)‖ = Real.exp (-b.re * ‖x‖ ^ 2) := by
      rw [Complex.norm_exp]
      congr 1
      simp only [q, Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
        Complex.ofReal_im]
      ring
    have hxk : ‖x‖ ^ k ≤ (1 + ‖x‖) ^ k := pow_le_pow_left₀ (norm_nonneg x) (by linarith) k
    rw [hfq]
    calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (cexp ∘ q) x‖
        ≤ (1 + ‖x‖) ^ k * (n ! * Real.exp (-b.re * ‖x‖ ^ 2) * (C * (1 + ‖x‖) ^ j) ^ n) := by
          rw [← hexp]
          gcongr
          exact hcomp x _ fun i _ ↦ (Complex.norm_iteratedFDeriv_real_exp i (q x)).le
      _ = n ! * C ^ n * ((1 + ‖x‖) ^ (k + j * n) * Real.exp (-b.re * ‖x‖ ^ 2)) := by
          simp only [mul_pow, pow_add, pow_mul]
          ring
      _ ≤ n ! * C ^ n * ((k + j * n) ! * Real.exp (1 + (4 * b.re)⁻¹)) := by
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

/-- For `τ` in the upper half-plane, `SchwartzMap.gaussian` at `b = -π i τ` is the Gaussian
`x ↦ exp (π i τ ‖x‖²)`. -/
theorem coe_gaussian_neg_pi_mul_I_mul (τ : ℍ) :
    ⇑(gaussian (-(π * Complex.I * τ)) τ.re_neg_pi_mul_I_mul_pos : 𝓢(E, ℂ)) =
      fun x ↦ cexp (π * Complex.I * (‖x‖ ^ 2 : ℝ) * τ) := by
  ext x
  rw [gaussian_apply]
  push_cast
  ring_nf

end SchwartzMap

namespace UpperHalfPlane

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The **Fourier transform of the Gaussian** `x ↦ exp (π i τ ‖x‖²)` on a real inner product space
of dimension `n`, for `τ` in the upper half-plane:
`𝓕 (x ↦ exp (π i τ ‖x‖²)) y = (τ / i) ^ (-n/2) * exp (π i (-1/τ) ‖y‖²)`, with the principal
branch of the complex power (`τ / i = -iτ` has positive real part). -/
theorem fourier_gaussian (τ : ℍ) (y : E) :
    𝓕 (fun x : E ↦ cexp (π * Complex.I * (‖x‖ ^ 2 : ℝ) * τ)) y =
      ((τ : ℂ) / Complex.I) ^ (-(finrank ℝ E : ℂ) / 2) *
        cexp (π * Complex.I * (‖y‖ ^ 2 : ℝ) * (-1 / (τ : ℂ))) := by
  have hτ : (τ : ℂ) ≠ 0 := τ.ne_zero
  have hf : (fun x : E ↦ cexp (π * Complex.I * (‖x‖ ^ 2 : ℝ) * τ)) =
      fun x ↦ cexp (-(-(π * Complex.I * (τ : ℂ))) * ‖x‖ ^ 2) := by
    ext x
    push_cast
    ring_nf
  rw [hf, fourier_gaussian_innerProductSpace τ.re_neg_pi_mul_I_mul_pos]
  -- `π / b = (τ / i)⁻¹`, and `τ / i = -iτ` lies in the right half-plane, off the branch cut.
  have hb : (π : ℂ) / -(π * Complex.I * (τ : ℂ)) = ((τ : ℂ) / Complex.I)⁻¹ := by
    field_simp
    rw [I_sq]
  have harg : ((τ : ℂ) / Complex.I).arg ≠ π := by
    rw [Ne, arg_eq_pi_iff, div_I, not_and_or, not_lt]
    left
    simpa using τ.im_pos.le
  rw [hb, inv_cpow _ _ harg, ← cpow_neg, neg_div]
  congr 2
  push_cast
  field_simp
  rw [← neg_mul, I_sq]
  ring

/-- The **Fourier transform of the Gaussian** `x ↦ exp (π i τ ‖x‖²)` on a real inner product space
of even dimension `2k`, for `τ` in the upper half-plane:
`𝓕 (x ↦ exp (π i τ ‖x‖²)) y = ((-i)^k τ^k)⁻¹ * exp (π i (-1/τ) ‖y‖²)`. -/
theorem fourier_gaussian_of_finrank_eq_two_mul {k : ℕ} (hn : finrank ℝ E = 2 * k) (τ : ℍ)
    (y : E) :
    𝓕 (fun x : E ↦ cexp (π * Complex.I * (‖x‖ ^ 2 : ℝ) * τ)) y =
      ((-Complex.I) ^ k * (τ : ℂ) ^ k)⁻¹ *
        cexp (π * Complex.I * (‖y‖ ^ 2 : ℝ) * (-1 / (τ : ℂ))) := by
  rw [fourier_gaussian, hn, ← mul_pow, show -(((2 * k : ℕ) : ℂ)) / 2 = -(k : ℂ) by push_cast; ring,
    cpow_neg, cpow_natCast, div_I]
  ring_nf

end UpperHalfPlane
