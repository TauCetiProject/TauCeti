/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.Distribution.TemperateGrowth
import TauCeti.Analysis.Distribution.TemperateGrowth
import TauCeti.Analysis.SpecialFunctions.Exp.IteratedFDeriv
import TauCeti.Analysis.SpecialFunctions.Gaussian.Bounds

/-!
# The Gaussian `exp (π i τ ‖x‖²)` as a Schwartz function

Let `E` be a finite-dimensional real inner product space of dimension `n` and `τ` a point of the
upper half-plane `ℍ`. The Gaussian `x ↦ exp (π i τ ‖x‖²)` has modulus `exp (-π (im τ) ‖x‖²)`, so
it decays rapidly, and so do all its derivatives: it is a Schwartz function
(`TauCeti.gaussian τ`). Its Fourier transform is again a Gaussian, at the parameter `-1/τ`:

`𝓕 (gaussian τ) y = (τ / i) ^ (-n/2) * exp (π i (-1/τ) ‖y‖²)`

(`TauCeti.fourier_gaussian`), with Mathlib's `𝓕 f w = ∫ x, exp (-2πi ⟪x, w⟫) f x` and the
principal branch of the complex power; `τ / i` has positive real part, so the branch is never
ambiguous. When `n = 2k` is even the power is the honest integer power
`(τ / i) ^ (-k) = ((-i) ^ k * τ ^ k)⁻¹` (`TauCeti.fourier_gaussian_of_finrank_eq_two_mul`).

These are the analytic inputs to the transformation law of a theta series under `τ ↦ -1/τ`: the
theta series of a lattice `L` is the sum `∑_{v ∈ L} gaussian τ v`, and Poisson summation over `L`
(`SchwartzMap.tsum_eq_tsum_dual_fourier`) turns it into a sum of `𝓕 (gaussian τ)` over the dual
lattice, which by the formula above is a theta series at `-1/τ`. The Gaussian is even
(`TauCeti.gaussian_neg`), so the sign convention of the phase in Poisson summation does not
matter for it. Its translates `x ↦ gaussian τ (x + v)`, whose lattice sums are the theta series of
the translates `v + L`, are Schwartz functions by `SchwartzMap.compSubConstCLM`.

The Schwartz bounds come from Faà di Bruno's estimate for the composite of `exp` with the
quadratic `x ↦ π i τ ‖x‖²`, which has temperate growth
(`Function.HasTemperateGrowth.exists_norm_iteratedFDeriv_comp_le`); every real iterated
derivative of `exp : ℂ → ℂ` at `z` has norm `‖exp z‖` (`Complex.norm_iteratedFDeriv_real_exp`),
and the polynomial weight is absorbed by the Gaussian through
`Real.one_add_pow_mul_exp_neg_mul_sq_le`. This decay argument follows the heat-kernel bounds
`TauCeti.exists_one_add_norm_pow_mul_heatKernel_le` and
`TauCeti.exists_norm_iteratedFDeriv_heatKernel_le` in
`TauCeti/Analysis/PDE/HeatKernel/Bounds.lean`, which use the same two estimates. The Fourier
transform is Mathlib's `fourier_gaussian_innerProductSpace` at `b = -π i τ`.

## Main definitions

* `TauCeti.gaussian τ`: the Schwartz function `x ↦ exp (π i τ ‖x‖²)` on `E`, for `τ : ℍ`.

## Main statements

* `TauCeti.gaussian_apply`, `TauCeti.norm_gaussian_apply`, `TauCeti.gaussian_neg`.
* `TauCeti.fourier_gaussian`: the Fourier transform of the Gaussian, in every dimension.
* `TauCeti.fourier_gaussian_of_finrank_eq_two_mul`: the same in even dimension `2k`, with
  the factor `((-i) ^ k * τ ^ k)⁻¹`.

## References

* E. M. Stein and R. Shakarchi, *Fourier Analysis: An Introduction*, Ch. 6 (the Fourier
  transform of the Gaussian on `ℝ^d`).
* J.-P. Serre, *A Course in Arithmetic*, Ch. VII §6 (theta functions of lattices).
-/

public section

open Complex Module
open scoped Nat Real UpperHalfPlane SchwartzMap FourierTransform

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The quadratic exponent `x ↦ π i ‖x‖² τ` of the Gaussian has temperate growth. -/
private theorem hasTemperateGrowth_gaussianExponent (τ : ℂ) :
    (fun x : E ↦ π * I * (‖x‖ ^ 2 : ℝ) * τ).HasTemperateGrowth := by
  have h : (fun x : E ↦ ((‖x‖ ^ 2 : ℝ) : ℂ)).HasTemperateGrowth :=
    Complex.hasTemperateGrowth_ofReal.comp (Function.hasTemperateGrowth_norm_sq E)
  convert ((Function.HasTemperateGrowth.const (π * I : ℂ)).mul h).mul
    (Function.HasTemperateGrowth.const τ) using 1

/-- The Gaussian `x ↦ exp (π i τ ‖x‖²)` on a real inner product space, for `τ` in the upper
half-plane, as a Schwartz function. -/
noncomputable def gaussian (τ : ℍ) : 𝓢(E, ℂ) where
  toFun x := cexp (π * I * (‖x‖ ^ 2 : ℝ) * τ)
  smooth' := contDiff_exp.comp (hasTemperateGrowth_gaussianExponent (τ : ℂ)).1
  decay' k n := by
    set a : ℝ := π * τ.im
    have ha : 0 < a := mul_pos Real.pi_pos τ.im_pos
    set q : E → ℂ := fun x ↦ π * I * (‖x‖ ^ 2 : ℝ) * τ
    have hq := hasTemperateGrowth_gaussianExponent (E := E) (τ : ℂ)
    have hnorm (x : E) : ‖cexp (q x)‖ = Real.exp (-a * ‖x‖ ^ 2) := by
      rw [norm_exp_pi_mul_I_mul_ofReal_mul, UpperHalfPlane.coe_im]
      congr 1
      ring
    obtain ⟨j, C₀, hC₀, hcomp⟩ := hq.exists_norm_iteratedFDeriv_comp_le contDiff_exp n
    refine ⟨n ! * (1 + C₀) ^ n * ((k + j * n) ! * Real.exp (1 + 1 / (4 * a))), fun x ↦ ?_⟩
    have hk : ‖x‖ ^ k ≤ (1 + ‖x‖) ^ k := by gcongr; linarith
    calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (cexp ∘ q) x‖
        ≤ (1 + ‖x‖) ^ k * (n ! * ‖cexp (q x)‖ * (1 + C₀) ^ n * (1 + ‖x‖) ^ (j * n)) := by
          gcongr
          exact hcomp x _ fun i _ ↦ (Complex.norm_iteratedFDeriv_real_exp i (q x)).le
      _ = n ! * (1 + C₀) ^ n * ((1 + ‖x‖) ^ (k + j * n) * Real.exp (-a * ‖x‖ ^ 2)) := by
        rw [hnorm, pow_add]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.one_add_pow_mul_exp_neg_mul_sq_le ha _ (norm_nonneg x)) (by positivity)

@[simp]
theorem gaussian_apply (τ : ℍ) (x : E) : gaussian τ x = cexp (π * I * (‖x‖ ^ 2 : ℝ) * τ) :=
  (rfl)

/-- The Gaussian has modulus `‖gaussian τ x‖ = exp (-π (im τ) ‖x‖²)`. This is a pre-simp lemma
(`simp↓`), so `simp` uses it before `gaussian_apply` unfolds the Gaussian inside the norm. -/
@[simp↓]
theorem norm_gaussian_apply (τ : ℍ) (x : E) :
    ‖gaussian τ x‖ = Real.exp (-(π * τ.im) * ‖x‖ ^ 2) := by
  rw [gaussian_apply, norm_exp_pi_mul_I_mul_ofReal_mul, UpperHalfPlane.coe_im]
  congr 1
  ring

/-- The Gaussian is even. -/
theorem gaussian_neg (τ : ℍ) (x : E) : gaussian τ (-x) = gaussian τ x := by
  simp

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The **Fourier transform of the Gaussian** on a real inner product space of dimension `n`:
`𝓕 (gaussian τ) y = (τ / i) ^ (-n/2) * exp (π i (-1/τ) ‖y‖²)`, with the principal branch of the
complex power. -/
theorem fourier_gaussian (τ : ℍ) (y : E) :
    𝓕 (gaussian τ : E → ℂ) y =
      ((τ : ℂ) / I) ^ (-(finrank ℝ E : ℂ) / 2) * cexp (π * I * (‖y‖ ^ 2 : ℝ) * (-1 / (τ : ℂ))) := by
  have hτ : (τ : ℂ) ≠ 0 := τ.ne_zero
  -- Mathlib's Gaussian `exp (-b ‖x‖²)` at `b = -π i τ`, which has real part `π im τ > 0`.
  set b : ℂ := -(π * I * τ)
  have hb : 0 < b.re := by
    simpa [b] using mul_pos Real.pi_pos τ.im_pos
  have hfun : (gaussian τ : E → ℂ) = fun x ↦ cexp (-b * ‖x‖ ^ 2) := by
    ext x
    simp only [gaussian_apply, b, ofReal_pow]
    ring_nf
  -- `π / b = (τ / i)⁻¹`, and `τ / i` has positive real part, so it is off the branch cut.
  have hπb : (π : ℂ) / b = ((τ : ℂ) / I)⁻¹ := by
    simp only [b]
    field_simp
    rw [I_sq]
  have harg : ((τ : ℂ) / I).arg ≠ π := by
    refine (arg_lt_pi_iff.2 (Or.inl ?_)).ne
    simpa [div_I] using τ.im_pos.le
  rw [hfun, fourier_gaussian_innerProductSpace hb, hπb, inv_cpow _ _ harg, ← cpow_neg, neg_div]
  congr 2
  simp only [b, ofReal_pow]
  field_simp
  rw [I_sq]
  ring

/-- The **Fourier transform of the Gaussian** in even dimension `2k`:
`𝓕 (gaussian τ) y = ((-i) ^ k * τ ^ k)⁻¹ * exp (π i (-1/τ) ‖y‖²)`. -/
theorem fourier_gaussian_of_finrank_eq_two_mul {k : ℕ} (hk : finrank ℝ E = 2 * k) (τ : ℍ)
    (y : E) :
    𝓕 (gaussian τ : E → ℂ) y =
      ((-I) ^ k * (τ : ℂ) ^ k)⁻¹ * cexp (π * I * (‖y‖ ^ 2 : ℝ) * (-1 / (τ : ℂ))) := by
  rw [fourier_gaussian, hk]
  congr 1
  have hExponent : -((2 * k : ℕ) : ℂ) / 2 = -(k : ℂ) := by push_cast; ring
  rw [hExponent, cpow_neg, cpow_natCast, div_I]
  ring

end TauCeti
