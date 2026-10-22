/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Distribution.TemperateGrowth

/-!
# The Gaussian of the upper half-plane as a Schwartz function

For `τ` in the upper half-plane `ℍ` and a finite-dimensional real inner product space `E`, the
Gaussian `x ↦ exp (π i τ ‖x‖²)` has modulus `exp (-π (im τ) ‖x‖²)`, so it decays rapidly, and so
do all of its derivatives: it is a Schwartz function `SchwartzMap.gaussian τ : 𝓢(E, ℂ)`. Every
complex Gaussian `x ↦ exp (-b ‖x‖²)` with `0 < re b` is of this form, for `τ = i b / π`.

Its Fourier transform is again such a Gaussian, at `-1 / τ`:

`𝓕 (gaussian τ) y = (τ / i) ^ (-n / 2) * exp (π i (-1 / τ) ‖y‖²)`,

where `n` is the dimension of `E` and the power is the principal one; `τ / i` lies in the right
half-plane, so the principal branch is the one continuous in `τ`. When `n = 2 k` is even the
factor is the integer power `((-i) ^ k * τ ^ k)⁻¹`. This is the Gaussian input to the inversion
law of a theta series: Poisson summation applied to `gaussian τ` (and to its translates, which are
Schwartz by `SchwartzMap.compSubConstCLM`) relates a theta series at `τ` to the theta series of
the dual lattice at `-1 / τ`.

The decay of the derivatives is Faà di Bruno's estimate `norm_iteratedFDeriv_comp_le` for
`exp ∘ q`, with `q x = π i τ ‖x‖²` of temperate growth; the Fourier transform is Mathlib's
`fourier_gaussian_innerProductSpace`.

## Main definitions

* `SchwartzMap.gaussian τ`: the Schwartz function `x ↦ exp (π i τ ‖x‖²)` for `τ : ℍ`.

## Main statements

* `SchwartzMap.gaussian_apply`: the defining formula.
* `SchwartzMap.gaussian_neg`: the Gaussian is even.
* `SchwartzMap.fourier_gaussian`: its Fourier transform, in any dimension.
* `SchwartzMap.fourier_gaussian_of_finrank_eq_two_mul`: the same in even dimension `2 k`, with the
  factor `((-i) ^ k * τ ^ k)⁻¹` an integer power.

## References

* J.-P. Serre, *A Course in Arithmetic*, Ch. VII §6.
* W. Ebeling, *Lattices and Codes*, Ch. 2.
-/

public section

noncomputable section

open Complex Module
open scoped Nat Real SchwartzMap FourierTransform UpperHalfPlane

namespace SchwartzMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The exponent `x ↦ π i τ ‖x‖²` of the Gaussian has temperate growth. -/
private theorem hasTemperateGrowth_gaussianExponent (τ : ℍ) :
    (fun x : E ↦ π * I * (‖x‖ ^ 2 : ℝ) * τ).HasTemperateGrowth := by
  have : (fun x : E ↦ π * I * (‖x‖ ^ 2 : ℝ) * τ) =
      (fun _ ↦ (π * I * τ : ℂ)) * (Complex.ofReal ∘ fun x : E ↦ ‖x‖ ^ 2) :=
    funext fun x ↦ by simp only [Pi.mul_apply, Function.comp_apply]; ring
  rw [this]
  exact (Function.HasTemperateGrowth.const _).mul
    (Complex.hasTemperateGrowth_ofReal.comp (Function.hasTemperateGrowth_norm_sq E))

/-- Every derivative of `x ↦ exp (π i τ ‖x‖²)` decays faster than every power of `‖x‖`. -/
private theorem gaussian_decay (τ : ℍ) (k n : ℕ) : ∃ C : ℝ, ∀ x : E,
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun x : E ↦ cexp (π * I * (‖x‖ ^ 2 : ℝ) * τ)) x‖ ≤ C := by
  set q : E → ℂ := fun x ↦ π * I * (‖x‖ ^ 2 : ℝ) * τ
  have hq : q.HasTemperateGrowth := hasTemperateGrowth_gaussianExponent τ
  set a : ℝ := π * τ.im
  have ha : 0 < a := mul_pos Real.pi_pos τ.im_pos
  have hnorm : ∀ x, ‖cexp (q x)‖ = Real.exp (-a * ‖x‖ ^ 2) := fun x ↦ by
    rw [Complex.norm_exp]
    congr 1
    simp only [q, a, mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im, UpperHalfPlane.coe_re,
      UpperHalfPlane.coe_im]
    ring
  obtain ⟨j, C₀, hC₀, hj⟩ := hq.norm_iteratedFDeriv_le_uniform n
  refine ⟨n ! * (1 + C₀) ^ n * ((k + j * n) ! * Real.exp (1 + 1 / (4 * a))), fun x ↦ ?_⟩
  set r := ‖x‖
  -- Faà di Bruno: `‖D^n (exp ∘ q)(x)‖ ≤ n! ‖exp (q x)‖ D^n` with `D = (1 + C₀)(1 + ‖x‖)^j`.
  set D : ℝ := (1 + C₀) * (1 + r) ^ j
  have hD₁ : 1 ≤ D := one_le_mul_of_one_le_of_one_le (by linarith) (one_le_pow₀ (by simp [r]))
  have hcomp : ‖iteratedFDeriv ℝ n (cexp ∘ q) x‖ ≤ n ! * Real.exp (-a * r ^ 2) * D ^ n := by
    rw [← hnorm]
    refine norm_iteratedFDeriv_comp_le Complex.contDiff_exp hq.1 (by exact_mod_cast le_top) x
      (fun i _ ↦ ?_) (fun i hi hin ↦ ?_)
    · -- The real derivatives of `exp` are its complex derivatives, all equal to `exp`.
      rw [← (Complex.contDiff_exp (𝕜 := ℂ) (n := i)).contDiffAt.restrictScalars_iteratedFDeriv
        (𝕜 := ℝ), Function.comp_apply, ContinuousMultilinearMap.norm_restrictScalars,
        norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate,
        Complex.iter_deriv_exp]
    · exact (hj i hin x).trans ((mul_le_mul_of_nonneg_right (by linarith) (by positivity) :
        C₀ * (1 + r) ^ j ≤ D).trans (le_self_pow₀ hD₁ (by omega)))
  -- `(1 + r)^m ≤ m! exp (1 + r)` and `r - a r² ≤ 1 / (4a)` absorb the polynomial weight.
  have hpow : (1 + r) ^ (k + j * n) ≤ (k + j * n) ! * Real.exp (1 + r) := by
    have := Real.pow_div_factorial_le_exp (1 + r) (by positivity) (k + j * n)
    rw [div_le_iff₀ (by positivity)] at this
    linarith
  have hquad : 1 + r + -a * r ^ 2 ≤ 1 + 1 / (4 * a) := by
    have : 1 + 1 / (4 * a) - (1 + r + -a * r ^ 2) = (2 * a * r - 1) ^ 2 / (4 * a) := by
      field_simp
      ring
    exact sub_nonneg.1 (this ▸ div_nonneg (sq_nonneg _) (by positivity))
  have hrk : r ^ k ≤ (1 + r) ^ k := pow_le_pow_left₀ (norm_nonneg x) (by linarith) k
  calc r ^ k * ‖iteratedFDeriv ℝ n (cexp ∘ q) x‖
      ≤ (1 + r) ^ k * (n ! * Real.exp (-a * r ^ 2) * D ^ n) := by gcongr
    _ = n ! * (1 + C₀) ^ n * ((1 + r) ^ (k + j * n) * Real.exp (-a * r ^ 2)) := by
        simp only [D, mul_pow, pow_add, pow_mul]
        ring
    _ ≤ n ! * (1 + C₀) ^ n * ((k + j * n) ! * Real.exp (1 + r) * Real.exp (-a * r ^ 2)) := by
        gcongr
    _ = n ! * (1 + C₀) ^ n * ((k + j * n) ! * Real.exp (1 + r + -a * r ^ 2)) := by
        rw [Real.exp_add (1 + r)]
        ring
    _ ≤ n ! * (1 + C₀) ^ n * ((k + j * n) ! * Real.exp (1 + 1 / (4 * a))) := by gcongr

/-- The Gaussian `x ↦ exp (π i τ ‖x‖²)` on a real inner product space, as a Schwartz function, for
`τ` in the upper half-plane. -/
def gaussian (τ : ℍ) : 𝓢(E, ℂ) where
  toFun x := cexp (π * I * (‖x‖ ^ 2 : ℝ) * τ)
  smooth' := Complex.contDiff_exp.comp (hasTemperateGrowth_gaussianExponent τ).1
  decay' := gaussian_decay τ

@[simp]
theorem gaussian_apply (τ : ℍ) (x : E) : gaussian τ x = cexp (π * I * (‖x‖ ^ 2 : ℝ) * τ) :=
  (rfl)

/-- The Gaussian is even. -/
theorem gaussian_neg (τ : ℍ) (x : E) : gaussian τ (-x) = gaussian τ x := by
  simp

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- **The Fourier transform of the Gaussian.** For `τ : ℍ`, the Fourier transform of
`x ↦ exp (π i τ ‖x‖²)` on a real inner product space of dimension `n` is
`y ↦ (τ / i) ^ (-n / 2) * exp (π i (-1 / τ) ‖y‖²)`, with the principal power. -/
theorem fourier_gaussian (τ : ℍ) (y : E) :
    𝓕 (gaussian τ : E → ℂ) y =
      ((τ : ℂ) / I) ^ (-(finrank ℝ E : ℂ) / 2) *
        cexp (π * I * (‖y‖ ^ 2 : ℝ) * (-1 / (τ : ℂ))) := by
  set b : ℂ := -(π * I * τ)
  have hτ : (τ : ℂ) ≠ 0 := τ.ne_zero
  have hb : 0 < b.re := by
    simpa [b] using mul_pos Real.pi_pos τ.im_pos
  have hfun : (gaussian τ : E → ℂ) = fun v ↦ cexp (-b * ‖v‖ ^ 2) :=
    funext fun v ↦ by simp only [gaussian_apply, b]; push_cast; ring_nf
  rw [hfun, fourier_gaussian_innerProductSpace hb]
  congr 1
  · -- `π / b = (τ / i)⁻¹`, and `τ / i` lies in the right half-plane, off the branch cut.
    have harg : ((τ : ℂ) / I).arg ≠ π := by
      have hre : 0 < ((τ : ℂ) / I).re := by simpa [div_I] using τ.im_pos
      linarith [Real.pi_pos, (abs_lt.1 (abs_arg_lt_pi_div_two_iff.2 (Or.inl hre))).2]
    have : (π : ℂ) / b = ((τ : ℂ) / I)⁻¹ := by
      have hb0 : b ≠ 0 := fun h ↦ by simp [h] at hb
      rw [inv_div, div_eq_div_iff hb0 hτ]
      simp only [b]
      linear_combination (π * τ : ℂ) * I_sq
    rw [this, inv_cpow _ _ harg, ← cpow_neg, neg_div]
  · congr 1
    simp only [b]
    field_simp
    push_cast
    linear_combination (‖y‖ : ℂ) ^ 2 * I_sq

/-- **The Fourier transform of the Gaussian in even dimension.** If `E` has dimension `2 k`, the
Fourier transform of `x ↦ exp (π i τ ‖x‖²)` is `y ↦ ((-i) ^ k τ ^ k)⁻¹ exp (π i (-1 / τ) ‖y‖²)`,
the factor being an integer power of `τ`. -/
theorem fourier_gaussian_of_finrank_eq_two_mul {k : ℕ} (hk : finrank ℝ E = 2 * k) (τ : ℍ)
    (y : E) :
    𝓕 (gaussian τ : E → ℂ) y =
      ((-I) ^ k * (τ : ℂ) ^ k)⁻¹ * cexp (π * I * (‖y‖ ^ 2 : ℝ) * (-1 / (τ : ℂ))) := by
  rw [fourier_gaussian, hk,
    show -(((2 * k : ℕ) : ℂ)) / 2 = -(k : ℂ) by push_cast; ring, cpow_neg, cpow_natCast,
    div_I, ← mul_pow]
  ring_nf

end SchwartzMap
