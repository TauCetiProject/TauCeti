/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars

/-!
# The Gaussian as a Schwartz function

For `τ` in the upper half-plane `ℍ` and a real inner product space `E`, the Gaussian

`x ↦ exp (π i τ ‖x‖²)`

has norm `exp (-π (im τ) ‖x‖²)`, and it is a Schwartz function on `E` (`UpperHalfPlane.gaussian`).
Every complex Gaussian `x ↦ exp (-b ‖x‖²)` with `0 < re b` arises this way, for `τ = i b / π`.

When `E` has finite dimension `n`, its Fourier transform is again a Gaussian, with `τ` replaced by
`-1 / τ` and an automorphy factor (`UpperHalfPlane.fourier_gaussian`):

`𝓕 (x ↦ exp (π i τ ‖x‖²)) y = (τ / i) ^ (-n / 2) * exp (π i (-1 / τ) ‖y‖²)`.

This is Mathlib's `fourier_gaussian_innerProductSpace`, rewritten in the upper half-plane
parameter, with the principal branch of the complex power. In even dimension
`n = 2 k` the factor is the integer power `((-i) ^ k * τ ^ k)⁻¹`
(`UpperHalfPlane.fourier_gaussian_of_finrank_eq_two_mul`).

Applied to the Gaussian, Poisson summation over a full lattice
(`SchwartzMap.tsum_eq_tsum_dual_fourier`) yields the inversion law `τ ↦ -1 / τ` of the theta
series of a lattice. Its translates `x ↦ exp (π i τ ‖x - γ‖²)` are again Schwartz functions, by
Mathlib's `SchwartzMap.compSubConstCLM`.

The Schwartz estimates come from Faà di Bruno's bound `norm_iteratedFDeriv_comp_le` for `exp`
composed with the exponent `π i τ ‖x‖²`. The exponent has temperate growth, and the iterated
derivatives of `exp` have norm `‖exp w‖ = exp (-π (im τ) ‖x‖²)`. A polynomial times this
Gaussian is bounded.

## References

* E. M. Stein and G. Weiss, *Introduction to Fourier Analysis on Euclidean Spaces*, Ch. I, §1.
-/

public section

open Complex Module
open scoped Real UpperHalfPlane FourierTransform SchwartzMap Nat

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace UpperHalfPlane

/-- The exponent `π i τ ‖x‖²` of the Gaussian has temperate growth. -/
private theorem hasTemperateGrowth_gaussianExponent (τ : ℍ) :
    (fun x : E ↦ π * Complex.I * (‖x‖ ^ 2 : ℝ) * τ).HasTemperateGrowth := by
  fun_prop

/-- The iterated derivatives of the Gaussian are bounded by a polynomial times the Gaussian
`exp (-π (im τ) ‖x‖²)`. -/
private theorem norm_iteratedFDeriv_gaussian_le (τ : ℍ) (n : ℕ) : ∃ (m : ℕ) (C : ℝ), 0 ≤ C ∧
    ∀ x : E, ‖iteratedFDeriv ℝ n (fun x : E ↦ cexp (π * Complex.I * (‖x‖ ^ 2 : ℝ) * τ)) x‖ ≤
      C * (1 + ‖x‖) ^ m * Real.exp (-(π * τ.im * ‖x‖ ^ 2)) := by
  -- The Gaussian has norm `exp (-π (im τ) ‖x‖²)`.
  have hnorm (x : E) :
      ‖cexp (π * Complex.I * (‖x‖ ^ 2 : ℝ) * τ)‖ = Real.exp (-(π * τ.im * ‖x‖ ^ 2)) := by
    rw [Complex.norm_exp]
    congr 1
    simp only [mul_re, mul_im, ofReal_re, ofReal_im, Complex.I_re, Complex.I_im, coe_re, coe_im]
    ring
  -- The real iterated derivatives of `exp : ℂ → ℂ` have norm `‖exp w‖`.
  have hexp (i : ℕ) (w : ℂ) : ‖iteratedFDeriv ℝ i cexp w‖ = ‖cexp w‖ := by
    rw [← ((contDiff_exp (𝕜 := ℂ) (n := i)).contDiffAt (x := w)).restrictScalars_iteratedFDeriv
        (𝕜 := ℝ), Function.comp_apply, ContinuousMultilinearMap.norm_restrictScalars,
      norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate, iter_deriv_exp]
  have hh := hasTemperateGrowth_gaussianExponent (E := E) τ
  obtain ⟨m, C, hC0, hC⟩ := hh.norm_iteratedFDeriv_le_uniform n
  refine ⟨m * n, n ! * (C + 1) ^ n, by positivity, fun x ↦ ?_⟩
  -- Faà di Bruno, with the derivatives of order `1 ≤ i ≤ n` of the exponent bounded by
  -- `D ^ i` for `D = (C + 1) (1 + ‖x‖) ^ m ≥ 1`.
  have hD1 : 1 ≤ (C + 1) * (1 + ‖x‖) ^ m :=
    one_le_mul_of_one_le_of_one_le (by linarith) (one_le_pow₀ (by simp))
  have hFdB := norm_iteratedFDeriv_comp_le (contDiff_exp (𝕜 := ℝ) (n := (⊤ : ℕ∞))) hh.1
    (mod_cast le_top) x (fun i _ ↦ ((hexp i _).trans (hnorm x)).le)
    fun i _ hin ↦ calc
      _ ≤ C * (1 + ‖x‖) ^ m := hC i hin x
      _ ≤ (C + 1) * (1 + ‖x‖) ^ m := by gcongr; linarith
      _ ≤ ((C + 1) * (1 + ‖x‖) ^ m) ^ i := le_self_pow₀ hD1 (by omega)
  refine hFdB.trans_eq ?_
  rw [mul_pow, ← pow_mul]
  ring

/-- A polynomial in `t ≥ 0` times the Gaussian `exp (-a t²)`, `0 < a`, is bounded. -/
private theorem one_add_pow_mul_exp_neg_mul_sq_le {a : ℝ} (ha : 0 < a) (p : ℕ) {t : ℝ}
    (ht : 0 ≤ t) : (1 + t) ^ p * Real.exp (-(a * t ^ 2)) ≤ p ! * (2 / a) ^ p * Real.exp a := by
  -- From `(a (1 + t)² / 2) ^ p / p! ≤ exp (a (1 + t)² / 2) ≤ exp (a + a t²)`.
  have h1 : (1 + t) ^ p ≤ ((1 + t) ^ 2) ^ p := by
    rw [← pow_mul]
    exact pow_le_pow_right₀ (by linarith) (by omega)
  have h2 := Real.pow_div_factorial_le_exp (x := a / 2 * (1 + t) ^ 2) (by positivity) p
  rw [div_le_iff₀ (by positivity)] at h2
  have h3 : Real.exp (a / 2 * (1 + t) ^ 2) ≤ Real.exp (a + a * t ^ 2) :=
    Real.exp_le_exp.2 (by nlinarith [sq_nonneg (1 - t)])
  have h4 : ((1 + t) ^ 2) ^ p ≤ p ! * (2 / a) ^ p * Real.exp a * Real.exp (a * t ^ 2) :=
    calc ((1 + t) ^ 2) ^ p = (a / 2 * (1 + t) ^ 2) ^ p * (2 / a) ^ p := by
          rw [← mul_pow]
          congr 1
          field_simp
      _ ≤ Real.exp (a + a * t ^ 2) * p ! * (2 / a) ^ p := by gcongr; exact h2.trans (by gcongr)
      _ = _ := by rw [Real.exp_add]; ring
  calc (1 + t) ^ p * Real.exp (-(a * t ^ 2))
      ≤ (p ! * (2 / a) ^ p * Real.exp a * Real.exp (a * t ^ 2)) * Real.exp (-(a * t ^ 2)) := by
        gcongr
        exact h1.trans h4
    _ = p ! * (2 / a) ^ p * Real.exp a := by
        rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]

/-- The Gaussian `x ↦ exp (π i τ ‖x‖²)` satisfies the decay estimates of a Schwartz function. -/
private theorem decay_gaussian (τ : ℍ) (k n : ℕ) : ∃ C : ℝ, ∀ x : E,
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun x : E ↦ cexp (π * Complex.I * (‖x‖ ^ 2 : ℝ) * τ)) x‖ ≤
      C := by
  obtain ⟨m, C, hC0, hC⟩ := norm_iteratedFDeriv_gaussian_le (E := E) τ n
  have ha : 0 < π * τ.im := by positivity
  refine ⟨C * ((k + m) ! * (2 / (π * τ.im)) ^ (k + m) * Real.exp (π * τ.im)), fun x ↦ ?_⟩
  calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun x : E ↦ cexp (π * Complex.I * (‖x‖ ^ 2 : ℝ) * τ)) x‖
      ≤ (1 + ‖x‖) ^ k * (C * (1 + ‖x‖) ^ m * Real.exp (-(π * τ.im * ‖x‖ ^ 2))) := by
        gcongr
        · linarith [norm_nonneg x]
        · exact hC x
    _ = C * ((1 + ‖x‖) ^ (k + m) * Real.exp (-(π * τ.im * ‖x‖ ^ 2))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
        (one_add_pow_mul_exp_neg_mul_sq_le ha _ (norm_nonneg x)) hC0

/-- The **Gaussian** `x ↦ exp (π i τ ‖x‖²)` attached to `τ` in the upper half-plane, as a Schwartz
function on a real inner product space `E`. Every complex Gaussian `x ↦ exp (-b ‖x‖²)` with
`0 < re b` is of this form, for `τ = i b / π`. -/
noncomputable def gaussian (τ : ℍ) : 𝓢(E, ℂ) where
  toFun x := cexp (π * Complex.I * (‖x‖ ^ 2 : ℝ) * τ)
  smooth' := (contDiff_exp (𝕜 := ℝ)).comp (hasTemperateGrowth_gaussianExponent τ).1
  decay' := decay_gaussian τ

/-- The Gaussian `gaussian τ` is the function `x ↦ exp (π i τ ‖x‖²)`. -/
@[simp]
theorem gaussian_apply (τ : ℍ) (x : E) :
    gaussian τ x = cexp (π * Complex.I * (‖x‖ ^ 2 : ℝ) * τ) :=
  (rfl)

/-- The Gaussian is an even function. -/
theorem gaussian_neg (τ : ℍ) (x : E) : gaussian τ (-x) = gaussian τ x := by
  simp

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The **Fourier transform of the Gaussian**: for `τ` in the upper half-plane and `n` the
dimension of `E`,
`𝓕 (x ↦ exp (π i τ ‖x‖²)) y = (τ / i) ^ (-n / 2) * exp (π i (-1 / τ) ‖y‖²)`,
with the principal branch of the complex power. Since `re (τ / i) = im τ > 0`, the factor is a
positive real number for `τ` on the imaginary axis. -/
theorem fourier_gaussian (τ : ℍ) (y : E) :
    𝓕 (gaussian τ : E → ℂ) y = ((τ : ℂ) / Complex.I) ^ (-(finrank ℝ E : ℂ) / 2) *
      cexp (π * Complex.I * (‖y‖ ^ 2 : ℝ) * (-1 / (τ : ℂ))) := by
  have hτ : (τ : ℂ) ≠ 0 := τ.ne_zero
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  -- Mathlib's Fourier transform of `x ↦ exp (-b ‖x‖²)`, at `b = -π i τ`.
  have hb : 0 < (-(π * Complex.I * τ)).re := by simpa using mul_pos Real.pi_pos τ.im_pos
  have hf : (gaussian τ : E → ℂ) = fun x ↦ cexp (-(-(π * Complex.I * τ)) * ‖x‖ ^ 2) := by
    ext x
    simp only [gaussian_apply, neg_neg, ofReal_pow]
    ring_nf
  -- The base `π / b = (τ / i)⁻¹` has positive real part, so it is off the branch cut.
  have harg : ((τ : ℂ) / Complex.I).arg ≠ π := by
    have hre : 0 < ((τ : ℂ) / Complex.I).re := by simpa [Complex.div_I] using τ.im_pos
    have := abs_lt.1 (abs_arg_lt_pi_div_two_iff.2 (Or.inl hre))
    linarith [Real.pi_pos]
  have hbase : (π : ℂ) / -(π * Complex.I * τ) = ((τ : ℂ) / Complex.I)⁻¹ := by
    rw [inv_div]
    field_simp
    ring_nf
    simp [Complex.I_sq]
  rw [hf, fourier_gaussian_innerProductSpace hb y, hbase, inv_cpow _ _ harg, neg_div, cpow_neg]
  congr 2
  field_simp
  ring_nf
  simp [Complex.I_sq]

/-- The Fourier transform of the Gaussian in **even dimension** `n = 2 k`, where the automorphy
factor is an integer power:
`𝓕 (x ↦ exp (π i τ ‖x‖²)) y = ((-i) ^ k * τ ^ k)⁻¹ * exp (π i (-1 / τ) ‖y‖²)`. -/
theorem fourier_gaussian_of_finrank_eq_two_mul {k : ℕ} (hn : finrank ℝ E = 2 * k) (τ : ℍ)
    (y : E) :
    𝓕 (gaussian τ : E → ℂ) y = ((-Complex.I) ^ k * (τ : ℂ) ^ k)⁻¹ *
      cexp (π * Complex.I * (‖y‖ ^ 2 : ℝ) * (-1 / (τ : ℂ))) := by
  have hk : -((2 * k : ℕ) : ℂ) / 2 = -(k : ℂ) := by push_cast; ring
  rw [fourier_gaussian, hn, hk, cpow_neg, cpow_natCast, Complex.div_I,
    show -((τ : ℂ) * Complex.I) = -Complex.I * τ by ring, mul_pow]

end UpperHalfPlane
